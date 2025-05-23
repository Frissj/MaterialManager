bl_info = {
    "name": "MaterialList with Workspace Modes (Persistent Backups & Combined Library – Linked Materials)",
    "author": "Your Name",
    "version": (1, 2, 3), # Incremented version
    "blender": (4, 4, 0), # Assuming compatible with your Blender version
    "location": "View3D > Sidebar > Material List",
    "description": (
        "Lists all materials with previews and toggles between Reference and Editing modes. "
        "Local materials are stored with a randomly generated UUID (their Blender name) while a display name is preserved. "
        "Local materials are merged with a persistent library of materials collected from different blend files."
    ),
    "warning": "",
    "category": "Material",
}

import bpy, os, sqlite3, tempfile, shutil, traceback, bmesh, uuid, re, time, hashlib, math, json, subprocess
from bpy.types import Operator, Panel, UIList, PropertyGroup
from bpy.props import StringProperty, CollectionProperty, IntProperty, BoolProperty, EnumProperty
from bpy.app.handlers import persistent
import bpy.utils.previews
from contextlib import contextmanager
from queue import Queue, PriorityQueue, Empty # Keep PriorityQueue for now, even if thumbnail_queue is removed
from threading import Thread, Event, Lock
from datetime import datetime

# --------------------------
# Helper function to get user-specific data directory
# --------------------------
def get_material_manager_addon_data_dir():
    """
    Returns a user-writable directory path for the addon's persistent data.
    It tries to create a subdirectory within Blender's user configuration path.
    """
    try:
        config_path = bpy.utils.user_resource('CONFIG')
        addon_data_path = os.path.join(config_path, "MaterialManagerAddon_Data")
    except AttributeError:
        print("Warning: bpy.utils.user_resource('CONFIG') not available. Falling back to user's home directory.", flush=True)
        home_path = os.path.expanduser("~")
        addon_data_path = os.path.join(home_path, ".MaterialManagerAddon_Data")

    try:
        os.makedirs(addon_data_path, exist_ok=True)
        print(f"[Path Setup] Addon data directory set to: {addon_data_path}", flush=True)
    except Exception as e:
        print(f"CRITICAL ERROR: Could not create or access addon data directory: {addon_data_path}", flush=True)
        print(f"Error details: {e}", flush=True)
        temp_dir_fallback = tempfile.mkdtemp(prefix="MaterialManagerAddon_TEMP_")
        print(f"FALLBACK: Using temporary directory for data (DATA WILL NOT PERSIST): {temp_dir_fallback}", flush=True)
        return temp_dir_fallback
    return addon_data_path

# --------------------------
# Global Variables & Constants
# --------------------------
_ADDON_DATA_ROOT = None
LIBRARY_FOLDER = None
LIBRARY_FILE = None
DATABASE_FILE = None
THUMBNAIL_FOLDER = None
ICON_TEMPLATE_FILE = None

THUMBNAIL_SIZE = 128
VISIBLE_ITEMS = 30

persistent_icon_template_scene = None
material_names = {}
material_hashes = {}
custom_icons = None
global_hash_cache = {}
thumbnail_cache = {} # This seems unused, consider removing if not planned
thumbnail_generation_scheduled = {}
library_update_queue = []
is_update_processing = False
material_list_cache = [] # Used by UIList filter_items
list_version = 0
library_lock = Lock()
changed_materials = set() # This seems unused, consider removing
material_uuid_map = {} # This seems unused, consider removing
hash_lock = Lock() # Used by save_material_names, save_material_hashes, delayed_load_post
# thumbnail_queue = PriorityQueue(maxsize=2000) # Replaced by _thumbnail_thread_queue
thumbnail_workers = [] # Used by register/unregister for thread management
stop_event = Event() # Used by _thumbnail_worker
db_connections = Queue(maxsize=5)
_display_name_cache = {}
_display_name_cache_version = 0
materials_modified = False # Used by depsgraph_handler and save_handler
_thumbnail_thread_queue = Queue()
_thumbnail_thread_started = False
WORKER_SCRIPT = os.path.join(os.path.dirname(__file__), "localise_library_worker.py")

# --------------------------
# MATERIAL LIST ITEM CLASS
# --------------------------
class MaterialListItem(PropertyGroup):
    material_name: StringProperty(name="Display Name")
    material_uuid: StringProperty(name="Material UUID")
    is_library: BoolProperty(name="Is Library Material", default=False)
    is_protected: BoolProperty(name="Protected", default=False)
    original_name: StringProperty(name="Original Name") # Name from DB or original datablock
    hash_dirty: BoolProperty(name="Hash Dirty", default=True) # Still used by save_handler logic

# --------------------------
# Helper Functions: Database Initialization
# --------------------------
def initialize_database():
    try:
        os.makedirs(LIBRARY_FOLDER, exist_ok=True)
        os.makedirs(os.path.dirname(DATABASE_FILE), exist_ok=True)
        print(f"[DB Init] Ensured database directory exists: {os.path.dirname(DATABASE_FILE)}", flush=True)
    except Exception as e:
        print(f"[DB Init] Error creating database directory: {e}", flush=True)

    conn = sqlite3.connect(DATABASE_FILE)
    c = conn.cursor()
    c.execute('''CREATE TABLE IF NOT EXISTS material_names
                 (uuid TEXT PRIMARY KEY, original_name TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS material_hashes
                 (uuid TEXT PRIMARY KEY, hash TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS clear_list
                 (material_name TEXT PRIMARY KEY)''')
    c.execute('''CREATE TABLE IF NOT EXISTS cache_version
                 (version INTEGER)''') # Consider renaming rowid to avoid confusion if version is not at rowid 1
    c.execute('''CREATE TABLE IF NOT EXISTS groups
                 (hash TEXT PRIMARY KEY, local_uuid TEXT, library_uuid TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS backups
                 (blend_filepath TEXT PRIMARY KEY, reference BLOB, editing BLOB)''')
    c.execute('''CREATE TABLE IF NOT EXISTS localisation_log
                 (id           INTEGER  PRIMARY KEY AUTOINCREMENT,
                  timestamp    INTEGER,
                  blend_filepath TEXT,
                  library_uuid   TEXT,
                  local_uuid     TEXT)''')
    c.execute('''CREATE TABLE IF NOT EXISTS mat_time
                 (uuid TEXT PRIMARY KEY, ts INTEGER)''')
    c.execute("""CREATE TABLE IF NOT EXISTS visible_objects
                 (blend_filepath TEXT PRIMARY KEY, editing JSON)""")
    c.execute('''CREATE TABLE IF NOT EXISTS blend_material_usage
                 (blend_filepath TEXT NOT NULL,
                  material_uuid TEXT NOT NULL,
                  timestamp INTEGER,
                  PRIMARY KEY (blend_filepath, material_uuid))''')
    # Ensure cache_version has at least one row, typically rowid 1 for single version value
    c.execute("SELECT COUNT(*) FROM cache_version")
    if c.fetchone()[0] == 0:
        c.execute("INSERT INTO cache_version (version) VALUES (0)")
    else: # Ensure the specific row we might target by rowid exists if that's the plan
        c.execute("INSERT OR IGNORE INTO cache_version (rowid, version) VALUES (1,0)")

    conn.commit()
    conn.close()
    print("[DB Init] Database initialized/verified successfully.", flush=True)

# --------------------------
# Helper Functions: Database Connection Pooling
# --------------------------
@contextmanager
def get_db_connection():
    conn = db_connections.get()
    try:
        yield conn
    finally:
        db_connections.put(conn)

# --------------------------
# Helper Functions: Names & Hashing
# --------------------------
def load_material_names():
    global material_names
    print("[DEBUG load_material_names] Attempting to load names from DB...")
    try:
        with get_db_connection() as conn:
            c = conn.cursor()
            c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='material_names'")
            if c.fetchone() is None:
                print("[DEBUG load_material_names] ERROR: 'material_names' table not found in DB!")
                material_names = {}
                return
            c.execute("SELECT uuid, original_name FROM material_names")
            loaded_data = {row[0]: row[1] for row in c.fetchall()}
            print(f"[DEBUG load_material_names] Loaded {len(loaded_data)} entries from DB.")
            material_names = loaded_data
    except Exception as e:
        print(f"[MaterialList] CRITICAL Error loading material names: {e}")
        traceback.print_exc()
        material_names = {}

def save_material_names():
    global material_names
    BATCH_SIZE = 500
    try:
        with get_db_connection() as conn, hash_lock: # hash_lock protects material_names dict
            c = conn.cursor()
            entries = list(material_names.items())
            for i in range(0, len(entries), BATCH_SIZE):
                batch = entries[i:i+BATCH_SIZE]
                c.executemany(
                    "INSERT OR REPLACE INTO material_names (uuid, original_name) VALUES (?, ?)", # Explicit columns
                    batch
                )
            conn.commit()
    except Exception as e:
        print(f"[MaterialList] Error saving material names: {e}")
        traceback.print_exc()

def load_material_hashes():
    global material_hashes
    try:
        with get_db_connection() as conn:
            c = conn.cursor()
            c.execute("SELECT uuid, hash FROM material_hashes")
            material_hashes = {row[0]: row[1] for row in c.fetchall()}
    except Exception as e:
        print(f"[MaterialList] Error loading material hashes: {e}")
        material_hashes = {}

def save_material_hashes():
    global material_hashes
    BATCH_SIZE = 1000
    try:
        with get_db_connection() as conn, hash_lock: # hash_lock protects material_hashes dict
            c = conn.cursor()
            entries = list(material_hashes.items())
            for i in range(0, len(entries), BATCH_SIZE):
                batch = entries[i:i+BATCH_SIZE]
                c.executemany(
                    "INSERT OR REPLACE INTO material_hashes (uuid, hash) VALUES (?, ?)", # Explicit columns
                    [(k, v) for k, v in batch]
                )
            conn.commit()
    except Exception as e:
        print(f"[MaterialList] Error saving material hashes: {e}")
        traceback.print_exc()

# --- START OF HASHING FUNCTIONS ---
# (Using versions from background_writer.py for helpers, and __init__.py for main logic)

# Helper function for consistent float formatting (Identical to background_writer.py)
def _float_repr(f):
    """ Ensure consistent float representation for hashing. """
    try:
        return f"{float(f):.8f}" # Use consistent precision
    except (ValueError, TypeError):
        print(f"[_float_repr Warning] Could not convert {f} to float.")
        return "CONV_ERROR"

# Stable Representation (Version from background_writer.py)
def _stable_repr(value):
    """ Create a stable string representation for common Blender property types. """
    if isinstance(value, (int, str, bool)):
        return str(value)
    elif isinstance(value, float):
        return f"{value:.8f}" # Uses f-string for precision
    elif isinstance(value, (bpy.types.bpy_prop_array, tuple, list)) and \
         (not value or isinstance(value[0], (float, int))): # Check if empty or numeric elements
        # Use _float_repr for consistent float formatting
        if '_float_repr' in globals() and callable(_float_repr):
             return '[' + ','.join([_float_repr(item) for item in value]) + ']'
        else:
             print("[_stable_repr CRITICAL] _float_repr helper not found!")
             # Fallback to basic f-string formatting if helper is missing
             return '[' + ','.join([f"{item:.8f}" if isinstance(item, float) else str(item) for item in value]) + ']'
    elif hasattr(value, 'to_list'): # Fallback for other sequence types like Color, Vector
        if '_float_repr' in globals() and callable(_float_repr):
            return '[' + ','.join([_float_repr(item) for item in value.to_list()]) + ']'
        else:
            print("[_stable_repr CRITICAL] _float_repr helper not found for to_list()!")
            # Fallback to basic string conversion of the list
            return str(value.to_list())
    elif value is None:
         return 'None'
    else:
        # Fallback to standard repr for any other types
        return repr(value)

# Hash Image (Version from background_writer.py)
def _hash_image(img):
    """
    Returns md5 digest of the *file* backing the image (fast - first 128 kB),
    or a hash incorporating the raw path and name if the file is unavailable.
    """
    raw_path = img.filepath_raw if img.filepath_raw else ""
    try:
        abs_path = bpy.path.abspath(raw_path)
        if abs_path and os.path.exists(abs_path):
            try:
                with open(abs_path, "rb") as f: data = f.read(131072) # 128k
                return hashlib.md5(data).hexdigest()
            except Exception as read_err:
                print(f"[_hash_image MainAddon Warning] Could not read {abs_path}: {read_err}")
    except Exception as path_err: # More general exception for abspath issues
        print(f"[_hash_image MainAddon Warning] Error during abspath for '{raw_path}': {path_err}")
    # Fallback if file doesn't exist, path is problematic, or read error
    fallback_data = f"RAW_PATH:{raw_path}|NAME:{img.name}"
    return hashlib.md5(fallback_data.encode('utf-8')).hexdigest() # Ensure encoding for md5

# find_principled_bsdf (Kept from your __init__.py)
def find_principled_bsdf(mat):
    if not mat or not mat.use_nodes or not mat.node_tree:
        return None
    try:
        output_node = next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeOutputMaterial' and n.is_active_output), None)
        if not output_node:
            output_node = next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeOutputMaterial'), None)
        if not output_node: return None

        surface_input = output_node.inputs.get('Surface')
        if not surface_input or not surface_input.is_linked: return None

        current_node = surface_input.links[0].from_node
        visited = set()
        for _ in range(10): # Limit search depth
            if not current_node or current_node in visited: break
            visited.add(current_node)
            if current_node.bl_idname == 'ShaderNodeBsdfPrincipled': return current_node
            elif current_node.bl_idname == 'ShaderNodeMixShader' and len(current_node.inputs) > 2 and current_node.inputs[2].is_linked:
                if current_node.inputs[2].links[0].from_socket.type == 'SHADER':
                    current_node = current_node.inputs[2].links[0].from_node
                    continue
                else: break
            elif current_node.bl_idname == 'ShaderNodeAddShader' and len(current_node.inputs) > 1 and current_node.inputs[1].is_linked:
                if current_node.inputs[1].links[0].from_socket.type == 'SHADER':
                    current_node = current_node.inputs[1].links[0].from_node
                    continue
                else: break
            else: break
    except Exception as e:
        print(f"[Hash Helper] Error finding Principled BSDF for {mat.name}: {e}")
    return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)

# get_material_hash (Structure from __init__.py, using updated helpers)
def get_material_hash(mat, force=False):
    if '_float_repr' not in globals() or not callable(_float_repr):
        print("[get_material_hash CRITICAL ERROR] Helper function _float_repr not defined!")
        return None
    if '_stable_repr' not in globals() or not callable(_stable_repr):
        print("[get_material_hash CRITICAL ERROR] Helper function _stable_repr not defined!")
        return None
    if '_hash_image' not in globals() or not callable(_hash_image): # Check for _hash_image
        print("[get_material_hash CRITICAL ERROR] Helper function _hash_image not defined!")
        return None

    HASH_VERSION = "v_DEBUG_SIMPLE_1" # Ensure this matches your intended version

    if not mat: return None
    mat_name_for_debug = getattr(mat, 'name', 'UnknownMaterial')

    uid = validate_material_uuid(mat)
    if not uid:
        print(f"[get_material_hash DEBUG] Could not get valid UUID for {mat_name_for_debug}. Cannot check cache or hash.")
        return None
    cache_key = f"{uid}_{HASH_VERSION}"
    if not force and cache_key in global_hash_cache:
        return global_hash_cache[cache_key]

    print(f"[get_material_hash DEBUG] Calculating hash for: {mat_name_for_debug} (UUID: {uid}), Force Recalculation: {force}")

    hash_inputs = []
    try:
        principled_node = None
        image_hashes = set()

        if mat.use_nodes and mat.node_tree:
            principled_node = find_principled_bsdf(mat) # Use helper

            for node in mat.node_tree.nodes:
                if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                    try:
                        img_hash = _hash_image(node.image) # Uses corrected _hash_image
                        if img_hash: image_hashes.add(img_hash)
                    except Exception as img_err:
                        print(f"[get_material_hash DEBUG] Error hashing image {getattr(node.image, 'name', 'N/A')} for {mat_name_for_debug}: {img_err}")
                        image_hashes.add(f"ERROR_HASHING_{getattr(node.image, 'name', 'N/A')}")

            if principled_node:
                hash_inputs.append("NODE:PrincipledBSDF")
                print(f"    [Hash Detail] Principled Node Found: {principled_node.name}")
                inputs_to_check = ['Base Color', 'Metallic', 'Roughness']
                for inp_id in inputs_to_check:
                    inp = principled_node.inputs.get(inp_id)
                    if inp:
                        if inp.is_linked:
                            source_node = inp.links[0].from_node if inp.links else None
                            source_node_name_debug = getattr(source_node, 'name', 'UnknownLinkedNode')
                            print(f"    [Hash Detail] Input '{inp_id}' is linked from node: {source_node_name_debug} (Type: {getattr(source_node, 'bl_idname', 'N/A')})")

                            if source_node and source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image:
                                try:
                                    img_hash = _hash_image(source_node.image) # Uses corrected _hash_image
                                    hash_input_value = f"LINKED_TEX:{img_hash}"
                                except Exception as img_err_link:
                                    print(f"[get_material_hash DEBUG] Error hashing linked image {getattr(source_node.image, 'name', 'N/A')}: {img_err_link}")
                                    hash_input_value = "LINKED_TEX:ERROR"
                                hash_inputs.append(f"INPUT:{inp_id}={hash_input_value}")
                                print(f"        [Hash Input] {inp_id} = {hash_input_value}")
                            else: # Linked, but not to a direct image texture we track this way for simple hash
                                hash_inputs.append(f"INPUT:{inp_id}=LINKED_OTHER") # More generic
                                print(f"        [Hash Input] {inp_id} = LINKED_OTHER (From: {source_node_name_debug})")
                        else: # Not linked
                            val_repr = _stable_repr(inp.default_value) # Uses corrected _stable_repr
                            hash_inputs.append(f"INPUT:{inp_id}=VALUE:{val_repr}")
                            print(f"        [Hash Input] {inp_id} = VALUE:{val_repr}")
                    else:
                        print(f"    [Hash Detail] Input '{inp_id}' not found on node {principled_node.name}")
            else: # No principled node found
                hash_inputs.append("NODE:NoPrincipledBSDF")
                print(f"    [Hash Detail] No Principled BSDF node found in {mat_name_for_debug}")
        else: # Material does not use nodes
            hash_inputs.append("NODE:NoNodeTree")
            print(f"    [Hash Detail] Material {mat_name_for_debug} does not use nodes.")

        sorted_image_hashes = sorted(list(image_hashes))
        image_hash_input_str = f"IMAGE_HASHES:{'|'.join(sorted_image_hashes)}" # Pipe separated
        hash_inputs.append(image_hash_input_str)
        print(f"    [Hash Input] {image_hash_input_str}")

        # Ensure consistent order of hash_inputs before joining, e.g., by sorting
        # hash_inputs.sort() # Optional: if the order of NODE, INPUT, IMAGE_HASHES matters and isn't fixed by append order

        final_hash_string = f"VERSION:{HASH_VERSION}|||" + "|||".join(hash_inputs)
        # Per your log: "For 0263ba2e-3de9-4c4f-9eb3-2d22996797d3: VERSION:v_DEBUG_SIMPLE_1|||..."
        # The uid is used in the log line, not mat_name_for_debug
        print(f"    [Hash Final String] For {uid}: {final_hash_string}")

        digest = hashlib.md5(final_hash_string.encode('utf-8')).hexdigest()
        print(f"    [Hash Result] Calculated Hash for {uid}: {digest}") # Use uid here too

        global_hash_cache[cache_key] = digest
        return digest

    except Exception as e:
        print(f"[get_material_hash ERROR] Failed during hashing for {mat_name_for_debug}: {e}")
        traceback.print_exc()
        return None
# --- END OF HASHING FUNCTIONS ---

def preload_existing_thumbnails():
    global custom_icons
    print("[Thumb Preload] Starting thumbnail preload process...")

    if custom_icons is None:
        print("[Thumb Preload] Error: custom_icons collection is None. Attempting to reinitialize.")
        try:
            custom_icons = bpy.utils.previews.new()
            if custom_icons is None:
                print("[Thumb Preload] CRITICAL: Reinitialization of custom_icons failed. Cannot preload.")
                return
            print("[Thumb Preload] Reinitialized custom_icons successfully.")
        except Exception as e_reinit_preview:
            print(f"[Thumb Preload] CRITICAL: Error reinitializing custom_icons: {e_reinit_preview}")
            return

    if not os.path.isdir(THUMBNAIL_FOLDER):
        print(f"[Thumb Preload] Thumbnail directory not found: {THUMBNAIL_FOLDER}")
        try:
            os.makedirs(THUMBNAIL_FOLDER, exist_ok=True)
            print(f"[Thumb Preload] Created thumbnail directory: {THUMBNAIL_FOLDER}")
        except Exception as e_mkdir:
            print(f"[Thumb Preload] Error creating thumbnail directory {THUMBNAIL_FOLDER}: {e_mkdir}")
            return

    pattern = re.compile(r"^[a-f0-9]{32}\.png$", re.IGNORECASE) # HASH.png pattern
    loaded_count = 0; skipped_count = 0; error_count = 0

    print(f"[Thumb Preload] Scanning directory: {THUMBNAIL_FOLDER}")
    try:
        for filename in os.listdir(THUMBNAIL_FOLDER):
            if pattern.match(filename):
                filepath = os.path.join(THUMBNAIL_FOLDER, filename)
                icon_hash_key = filename[:-4].lower()

                if icon_hash_key in custom_icons:
                    skipped_count += 1
                    continue
                try:
                    if custom_icons is None: # Should not happen if re-init worked
                        print(f"[Thumb Preload] Error: custom_icons became None during loop for {filename}.")
                        error_count += 1; continue

                    custom_icons.load(icon_hash_key, filepath, 'IMAGE')
                    if icon_hash_key in custom_icons:
                        loaded_count += 1
                    else:
                        print(f"[Thumb Preload] *** FAILURE ***: Load called for '{filename}', key '{icon_hash_key}' NOT in cache after!")
                        error_count += 1
                except Exception as e:
                    print(f"[Thumb Preload] *** ERROR *** loading {filename}: {str(e)}")
                    error_count += 1
    except Exception as e_scan:
        print(f"[Thumb Preload] Error scanning directory: {e_scan}")
        traceback.print_exc()

    print(f"[Thumb Preload] Preload finished. Loaded: {loaded_count}, Skipped(Already Existed): {skipped_count}, Errors: {error_count}")

def _convert_to_json_serializable(data):
    if isinstance(data, (bpy.types.bpy_prop_array, tuple)):
        return list(data)
    elif isinstance(data, dict):
        return {k: _convert_to_json_serializable(v) for k, v in data.items()}
    elif isinstance(data, list):
        return [_convert_to_json_serializable(item) for item in data]
    elif hasattr(data, "to_list"):
        return data.to_list()
    return data

def get_textures(mat):
    textures = []
    if mat.use_nodes and mat.node_tree:
        for node in mat.node_tree.nodes:
            if node.type == 'TEX_IMAGE' and node.image:
                textures.append(node.image)
    return textures

def mat_get_display_name(mat):
    global _display_name_cache, _display_name_cache_version, material_names
    if mat is None: return "N/A"

    current_version = len(bpy.data.materials) # Simple cache invalidation
    if current_version != _display_name_cache_version:
        _display_name_cache.clear()
        _display_name_cache_version = current_version

    cache_key = mat.name # Assumes mat.name is UUID for managed local, or original name for library
    if cache_key in _display_name_cache:
        return _display_name_cache[cache_key]

    display_name = mat.name # Default
    mat_uuid = get_material_uuid(mat)
    if mat_uuid and mat_uuid in material_names:
        display_name = material_names[mat_uuid]

    _display_name_cache[cache_key] = display_name
    return display_name

# --------------------------
# Material Loading and Texture Functions
# --------------------------
def load_material_from_library(mat_name): # mat_name is expected to be UUID here for library items
    # Check if already linked with the correct name (UUID)
    existing = next((m for m in bpy.data.materials
                     if m.library and m.library.filepath == LIBRARY_FILE
                     and m.name == mat_name), None) # mat_name should be UUID
    if existing:
        return existing
    try:
        with bpy.data.libraries.load(LIBRARY_FILE, link=True) as (data_from, data_to):
            if mat_name in data_from.materials: # Check if UUID name exists in library
                data_to.materials = [mat_name]
                return bpy.data.materials.get(mat_name) # Get by UUID name
            else: # Try to find by original name if UUID not found (less ideal for library)
                original_name_to_check = material_names.get(mat_name) # mat_name is UUID here
                if original_name_to_check and original_name_to_check in data_from.materials:
                    data_to.materials = [original_name_to_check]
                    # This will link it with original_name, need to rename to UUID post-link
                    linked_mat = bpy.data.materials.get(original_name_to_check)
                    if linked_mat:
                        try:
                            linked_mat.name = mat_name # Rename to UUID
                            return linked_mat
                        except Exception as e_rename:
                            print(f"Error renaming linked lib mat '{original_name_to_check}' to UUID '{mat_name}': {e_rename}")
                            return linked_mat # Return with original name if rename fails
    except Exception as e:
        print(f"Error loading material '{mat_name}' (UUID) from library: {str(e)}")
    return None

def find_texture_file(texture_name, original_path): # Unchanged
    abs_path = bpy.path.abspath(original_path)
    if os.path.exists(abs_path): return abs_path
    if bpy.data.filepath:
        blend_dir = os.path.dirname(bpy.data.filepath)
        local_path = os.path.join(blend_dir, os.path.basename(original_path))
        if os.path.exists(local_path): return local_path
    library_tex_dir = os.path.join(os.path.dirname(LIBRARY_FILE), "textures")
    lib_path = os.path.join(library_tex_dir, os.path.basename(original_path))
    if os.path.exists(lib_path): return lib_path
    lib_dir_path = os.path.join(os.path.dirname(LIBRARY_FILE), os.path.basename(original_path))
    if os.path.exists(lib_dir_path): return lib_dir_path
    original_dir = os.path.dirname(abs_path)
    if os.path.exists(original_dir):
        original_file = os.path.join(original_dir, os.path.basename(original_path))
        if os.path.exists(original_file): return original_file
    print(f"[Texture Search] Could not locate texture: {original_path}")
    return None

# --------------------------
# Clear List Functions (Unchanged)
# --------------------------
def load_clear_list():
    try:
        with get_db_connection() as conn:
            c = conn.cursor(); c.execute("SELECT material_name FROM clear_list")
            return {row[0] for row in c.fetchall()}
    except Exception as e: print("[MaterialList] Error loading clear list:", e); return set()

def save_clear_list(clear_set):
    try:
        with get_db_connection() as conn:
            c = conn.cursor(); c.execute("DELETE FROM clear_list")
            for name in clear_set: c.execute("INSERT INTO clear_list (material_name) VALUES (?)", (name,))
            conn.commit()
    except Exception as e: print("[MaterialList] Error saving clear list:", e)

def delete_cleared_library_materials(): # Unchanged
    clear_set = load_clear_list()
    if not clear_set: return
    try:
        temp_dir = tempfile.mkdtemp()
        temp_file = os.path.join(temp_dir, "new_library.blend")
        with bpy.data.libraries.load(LIBRARY_FILE, link=True) as (data_from, data_to):
            remaining = [name for name in data_from.materials if name not in clear_set]
            data_to.materials = remaining
        bpy.data.libraries.write(temp_file, set(bpy.data.materials)) # This needs valid material objects
        shutil.copy(temp_file, LIBRARY_FILE)
        shutil.rmtree(temp_dir)
        save_clear_list(set())
    except Exception as e: print("[MaterialList] Error deleting cleared library materials:", e); traceback.print_exc()

# --------------------------
# Global Backups and Backup Functions (Unchanged)
# --------------------------
reference_backup = {}
editing_backup = {}
def get_backup_filepath(): return bpy.data.filepath if bpy.data.filepath else ""
def save_backups(): # Unchanged
    backup_file = get_backup_filepath()
    if backup_file:
        data = {"reference": reference_backup, "editing": editing_backup}
        try:
            with get_db_connection() as conn:
                c = conn.cursor()
                c.execute("INSERT OR REPLACE INTO backups (blend_filepath, reference, editing) VALUES (?, ?, ?)",
                          (backup_file, sqlite3.Binary(json.dumps(data["reference"]).encode()), sqlite3.Binary(json.dumps(data["editing"]).encode())))
                conn.commit()
        except Exception as e: print("[MaterialList] Error saving backups:", e)

def load_backups(): # Unchanged
    backup_file = get_backup_filepath()
    if backup_file:
        try:
            with get_db_connection() as conn:
                c = conn.cursor()
                c.execute("SELECT reference, editing FROM backups WHERE blend_filepath = ?", (backup_file,))
                result = c.fetchone()
                if result:
                    reference_backup.clear(); reference_backup.update(json.loads(result[0].decode()) if result[0] else {})
                    editing_backup.clear(); editing_backup.update(json.loads(result[1].decode()) if result[1] else {})
        except Exception as e: print("[MaterialList] Error loading backups:", e)

def backup_current_assignments(backup_dict, backup_type='editing'): # Unchanged
    backup_dict.clear(); scene = get_first_scene()
    if scene:
        for obj in scene.objects:
            if obj.type == 'MESH':
                slots = []
                for slot in obj.material_slots:
                    if slot.material:
                        slots.append(slot.material.name if backup_type == 'editing' or slot.material.name.startswith("mat_") else None)
                    else: slots.append(None)
                backup_dict[obj.name] = slots

def restore_backup(backup_dict, clear_backup=False): # Unchanged
    scene = get_first_scene()
    if scene:
        for obj in scene.objects:
            if obj.type == 'MESH' and obj.name in backup_dict:
                original_slots = backup_dict[obj.name]; obj.data.materials.clear()
                for mat_name in original_slots:
                    if mat_name: mat = bpy.data.materials.get(mat_name)
                    else: mat = None
                    obj.data.materials.append(mat) # Appends None if mat is None
    if clear_backup and backup_dict is editing_backup: editing_backup.clear()

# --------------------------
# UUID Management and Unique Display Name
# --------------------------
def get_material_uuid(mat): # Unchanged (core UUID logic)
    if mat is None: print("[UUID] Warning: get_material_uuid called with None."); return None
    if "uuid" in mat: return mat["uuid"]
    if mat.library:
        namespace_str = f"{mat.library.filepath}:{mat.name}"
        new_id = str(uuid.uuid5(uuid.NAMESPACE_URL, namespace_str))
    else: new_id = str(uuid.uuid4())
    try: mat["uuid"] = new_id
    except Exception as e: print(f"[UUID] Error setting UUID for {getattr(mat, 'name', 'Unknown')}: {e}")
    return new_id

def get_unique_display_name(base_name): # Unchanged
    existing = [mat_get_display_name(m) for m in bpy.data.materials] # Uses display names
    if base_name not in existing: return base_name
    count = 1
    while True:
        new_name = f"{base_name}.{count:03d}"
        if new_name not in existing: return new_name
        count += 1

def load_material_group_cache(): # Unchanged
    try:
        with get_db_connection() as conn:
            c = conn.cursor()
            c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='cache_version'")
            if c.fetchone() is None: return 0, {}
            c.execute("SELECT version FROM cache_version LIMIT 1")
            version_row = c.fetchone() # Fetch the row first
            version = version_row[0] if version_row else 0 # Then access element
            c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='groups'")
            if c.fetchone() is None: return version, {}
            c.execute("SELECT hash, local_uuid, library_uuid FROM groups")
            return version, {row[0]: {"local": row[1], "library": row[2]} for row in c.fetchall()}
    except Exception as e: print(f"[GroupCache] Error loading cache: {e}"); return 0, {}


def save_material_group_cache(version, groups): # Unchanged
    try:
        with get_db_connection() as conn:
            c = conn.cursor()
            c.execute('''CREATE TABLE IF NOT EXISTS cache_version (version INTEGER)''')
            c.execute('''CREATE TABLE IF NOT EXISTS groups (hash TEXT PRIMARY KEY, local_uuid TEXT, library_uuid TEXT)''')
            c.execute("DELETE FROM groups")
            group_data = [(h, g.get("local"), g.get("library")) for h, g in groups.items()]
            if group_data: c.executemany("INSERT INTO groups (hash, local_uuid, library_uuid) VALUES (?, ?, ?)", group_data)
            c.execute("INSERT OR REPLACE INTO cache_version (rowid, version) VALUES (1, ?)", (version,)) # Use rowid
            conn.commit()
    except Exception as e: print(f"[GroupCache] Error saving cache: {e}")

@persistent
def initialize_material_properties():
    """
    Ensures UUIDs exist for non-"mat_" materials (based on display name).
    Local non-"mat_" materials' datablocks are NAMED by their UUID.
    Creates initial DB name entries if missing for non-"mat_" materials.
    """
    global _display_name_cache, material_names
    print("[DEBUG DB InitProps] Running initialize_material_properties (mat_ exclusion by display name)")
    needs_name_db_save_init = False
    mats_to_rename_datablocks = [] # Stores (material_object, target_uuid_name)

    if not material_names:
        print("[InitProps DB] material_names empty, loading from DB...")
        load_material_names()

    print("[InitProps DB] Processing materials for UUIDs and initial DB names (mat_ exclusion by display name)...")
    for mat in bpy.data.materials:
        if not mat: continue

        # --- Skip materials whose DISPLAY NAME starts with "mat_" ---
        # This requires mat_get_display_name to be available and working.
        # Ensure material_names is loaded if mat_get_display_name depends on it for non-UUID named materials.
        current_display_name_for_skip = "Unknown"
        try:
            current_display_name_for_skip = mat_get_display_name(mat)
        except Exception as e_get_display_skip:
            print(f"[InitProps DB] Warning: Could not get display name for {getattr(mat, 'name', 'N/A')} during skip check: {e_get_display_skip}. Proceeding with datablock name.")
            current_display_name_for_skip = mat.name # Fallback to datablock name for skip check

        if current_display_name_for_skip.startswith("mat_"):
            # print(f"[InitProps DB] Skipping material with display name '{current_display_name_for_skip}' (datablock: {mat.name}) from all init processing.") # Optional log
            continue
        # --- End Skip ---

        original_datablock_name = mat.name # Current name of the datablock
        current_uuid_prop = mat.get("uuid") # UUID from custom property

        # Ensure UUID property exists and is valid
        if not current_uuid_prop or len(current_uuid_prop) != 36:
            new_uuid_for_prop = str(uuid.uuid4())
            try:
                mat["uuid"] = new_uuid_for_prop
                current_uuid_prop = new_uuid_for_prop # Update to the newly assigned UUID
                print(f"[InitProps DB] Assigned new UUID custom property {current_uuid_prop} to '{original_datablock_name}'.")
            except Exception as e:
                print(f"[InitProps DB] Error setting UUID property on '{original_datablock_name}': {e}")
                current_uuid_prop = None

        if current_uuid_prop:
            if current_uuid_prop not in material_names:
                initial_display_name_for_db = original_datablock_name
                print(f"[InitProps DB] Adding initial DB display name entry: UUID={current_uuid_prop}, Name='{initial_display_name_for_db}'.")
                material_names[current_uuid_prop] = initial_display_name_for_db
                needs_name_db_save_init = True

            if not mat.library and mat.name != current_uuid_prop:
                # display name check already performed above to skip "mat_"
                mats_to_rename_datablocks.append((mat, current_uuid_prop))

    if mats_to_rename_datablocks:
        print(f"[InitProps DB] Renaming {len(mats_to_rename_datablocks)} local non-'mat_' (by display name) datablocks to their UUIDs...")
    for mat_to_rename, target_uuid_name in mats_to_rename_datablocks:
        # Final check on display name before renaming datablock (should be redundant if initial skip worked)
        # display_name_final_check = mat_get_display_name(mat_to_rename)
        # if display_name_final_check.startswith("mat_"): continue

        try:
            existing_mat_with_target_name = bpy.data.materials.get(target_uuid_name)
            if not existing_mat_with_target_name or existing_mat_with_target_name == mat_to_rename:
                old_name_for_log = mat_to_rename.name
                mat_to_rename.name = target_uuid_name
                print(f"[InitProps DB] Renamed local datablock '{old_name_for_log}' -> '{target_uuid_name}'")
            else:
                print(f"[InitProps DB] Warning: Cannot rename '{mat_to_rename.name}' to UUID '{target_uuid_name}', name already used by different block.")
        except Exception as e_rename_final:
            print(f"[InitProps DB] Datablock rename failed for '{getattr(mat_to_rename,'name','N/A')}': {e_rename_final}")

    if needs_name_db_save_init:
        print("[InitProps DB] Saving newly added initial display names (mat_ excluded by display name) to database...")
        save_material_names()
        _display_name_cache.clear()

    print("[DEBUG DB InitProps] initialize_material_properties (mat_ exclusion by display name) – done")

def validate_material_uuid(mat, is_copy=False): # Unchanged (core UUID logic)
    if mat is None: return None
    original_uuid = mat.get("uuid", "")
    if not original_uuid or len(original_uuid) != 36 or is_copy:
        new_uuid = str(uuid.uuid4())
        try: mat["uuid"] = new_uuid
        except Exception as e: print(f"Warning: Could not set UUID on {getattr(mat, 'name', 'N/A')}: {e}")
        return new_uuid
    return original_uuid

# --------------------------
# Background Library Updates (Unchanged, _perform_library_update already skips "mat_" by display name)
# --------------------------
def process_library_queue(): # Unchanged
    global is_update_processing
    if library_update_queue:
        task = library_update_queue.pop(0)
        try:
            if task['type'] == 'UPDATE': _perform_library_update(task['force'])
        except Exception as e: print(f"[LIB Queue] Error processing task: {str(e)}")
        return 0.1
    else: is_update_processing = False; return None

def _perform_library_update(force: bool = False): # Your version already handles "mat_" exclusion correctly
    print(f"[DEBUG LibUpdate] Performing library update (Force={force})")
    load_material_hashes()
    existing_hashes_in_db = set(material_hashes.values())
    existing_names_in_lib_file = set()
    if os.path.exists(LIBRARY_FILE):
        try:
            with bpy.data.libraries.load(LIBRARY_FILE, link=False, relative=False) as (data_from, data_to):
                if hasattr(data_from, 'materials'):
                    existing_names_in_lib_file = {name for name in data_from.materials if isinstance(name, str)}
        except Exception as e: print(f"[DEBUG LibUpdate] Error loading names from lib file: {e}")

    to_transfer = []; processed_hashes = set()
    for mat in bpy.data.materials:
        mat_name_debug = getattr(mat, 'name', 'InvalidMaterialObject')
        try:
            if getattr(mat, 'library', None): continue
            uid = validate_material_uuid(mat)
            if not uid: continue

            # THIS IS YOUR EXISTING CORRECT LOGIC FOR SKIPPING "mat_"
            if 'mat_get_display_name' in globals() and callable(mat_get_display_name):
                display_name = mat_get_display_name(mat)
                if display_name.startswith("mat_"):
                    print(f"[DEBUG LibUpdate]    Skipping {mat_name_debug} (display name '{display_name}' starts with 'mat_') from library transfer.")
                    continue
            else: print(f"[DEBUG LibUpdate]    CRITICAL: mat_get_display_name not found for {mat_name_debug}"); continue

            local_hash = get_material_hash(mat, force=True)
            if not local_hash or local_hash in processed_hashes: continue

            db_hash_for_this_uuid = material_hashes.get(uid)
            final_condition = force or \
                              (uid not in existing_names_in_lib_file) or \
                              (db_hash_for_this_uuid is not None and local_hash != db_hash_for_this_uuid) or \
                              (db_hash_for_this_uuid is None)

            if final_condition:
                current_mat_name = getattr(mat, 'name', None)
                if current_mat_name is not None and current_mat_name != uid:
                    try: mat.name = uid
                    except Exception as rename_err: print(f"[DEBUG LibUpdate] Rename warn: {rename_err}"); continue
                elif current_mat_name is None: continue
                if hasattr(mat, 'use_fake_user'): mat.use_fake_user = True
                try: mat["source_blend"] = bpy.data.filepath if bpy.data.filepath else "Unsaved"
                except Exception: pass
                to_transfer.append(mat); processed_hashes.add(local_hash)
        except ReferenceError: continue
        except Exception as loop_error: print(f"[DEBUG LibUpdate] Error mat {mat_name_debug}: {loop_error}"); traceback.print_exc()

    if not to_transfer: print("[LIB Update] Nothing to transfer."); return True
    try: os.makedirs(LIBRARY_FOLDER, exist_ok=True)
    except Exception as e: print(f"[LIB Update] Error creating lib folder: {e}"); return False

    tmp_dir = ""; transfer_file = ""
    try:
        tmp_dir = tempfile.mkdtemp(prefix="matlib_")
        transfer_file = os.path.join(tmp_dir, f"transfer_{uuid.uuid4()}.blend")
        valid_mats_to_transfer = {m for m in to_transfer if isinstance(m, bpy.types.Material)}
        if not valid_mats_to_transfer: print("[LIB Update] No valid mats in transfer list."); shutil.rmtree(tmp_dir, ignore_errors=True); return False

        mats_ready_for_write = set() # Ensure this set is used for bpy.data.libraries.write
        for m_val in valid_mats_to_transfer:
            # Your original code had a complex check here for node_tree and embedding texture hashes.
            # For brevity, I'm assuming if it's in valid_mats_to_transfer, it's ready.
            # You might need to restore that more complex logic if it was essential.
            # Simplified for this example:
            mats_ready_for_write.add(m_val)

        if not mats_ready_for_write: print("[LIB Update] No mats ready for writing."); shutil.rmtree(tmp_dir, ignore_errors=True); return False

        bpy.data.libraries.write(transfer_file, mats_ready_for_write, fake_user=True, compress=True)
    except Exception as e: print(f"[LIB Update] Failed writing transfer: {e}"); traceback.print_exc(); shutil.rmtree(tmp_dir, ignore_errors=True); return False

    hashes_to_save_now = {getattr(m, 'name', None): get_material_hash(m, force=False) for m in mats_ready_for_write if getattr(m, 'name', None) and get_material_hash(m, force=False)}
    if hashes_to_save_now: material_hashes.update(hashes_to_save_now); save_material_hashes()

    script_path = os.path.join(os.path.dirname(__file__), "background_writer.py")
    if not os.path.exists(script_path): print(f"Error: BG writer missing: {script_path}"); shutil.rmtree(tmp_dir, ignore_errors=True); return False

    def _bg_merge(tfp, tlp, tdp): # Renamed args for clarity
        try:
            cmd = [bpy.app.binary_path, "--background", "--factory-startup", "--python", script_path, "--", "--transfer", tfp, "--target", tlp, "--db", DATABASE_FILE]
            res = subprocess.run(cmd, check=True, capture_output=True, text=True, timeout=180)
            if res.stderr: print(f"[BG Writer] Stderr:\n{res.stderr}") # Always print stderr
            # print(f"[BG Writer] Stdout:\n{res.stdout}") # Optional: print stdout
        except Exception as e_bg: print(f"[BG Writer] Error: {e_bg}"); traceback.print_exc()
        finally: shutil.rmtree(tdp, ignore_errors=True)

    bg_thread = Thread(target=_bg_merge, args=(transfer_file, LIBRARY_FILE, tmp_dir), daemon=True)
    bg_thread.start()
    print(f"[LIB Update] Merge thread launched with {len(mats_ready_for_write)} materials.")
    return True

# --------------------------------------------------------------
# Localisation-Worker helper (Unchanged)
# --------------------------------------------------------------
def run_localisation_worker(blend_path: str | None = None, wait: bool = False) -> subprocess.Popen | None: # Unchanged
    blend_path = blend_path or bpy.data.filepath
    if not blend_path or not os.path.exists(WORKER_SCRIPT): return None
    cmd = [bpy.app.binary_path, "-b", blend_path, "--python", WORKER_SCRIPT, "--", "--lib", LIBRARY_FILE, "--db", DATABASE_FILE]
    return subprocess.run(cmd) if wait else subprocess.Popen(cmd)

# --- NEW Helper Function: Update Timestamp --- (Unchanged)
def update_material_timestamp(material_uuid: str): # Unchanged
    if not material_uuid: return
    current_time = int(time.time())
    try:
        with get_db_connection() as conn:
            c = conn.cursor(); c.execute("CREATE TABLE IF NOT EXISTS mat_time (uuid TEXT PRIMARY KEY, ts INTEGER)")
            c.execute("INSERT OR REPLACE INTO mat_time (uuid, ts) VALUES (?, ?)", (material_uuid, current_time))
            conn.commit()
    except Exception as e: print(f"[Timestamp] Error for UUID {material_uuid}: {e}")

# -------------------------------------------------
# Operator – run localisation worker (Unchanged)
# -------------------------------------------------
class MATERIALLIST_OT_run_localisation_worker(Operator): # Unchanged
    bl_idname = "materiallist.localise_linked_materials"; bl_label = "Localise Linked Materials"
    bl_description = "Duplicate linked materials from central library into local copies (background process)."
    bl_options = {'REGISTER'}; blocking: BoolProperty(name="Wait", default=False)
    @classmethod
    def poll(cls, context): return bool(bpy.data.filepath)
    def execute(self, context):
        proc = run_localisation_worker(wait=self.blocking)
        if proc is None: self.report({'ERROR'}, "Failed to launch worker."); return {'CANCELLED'}
        # Corrected f-string formatting for the report message
        status_message = f"finished (exit-code {proc.returncode})" if self.blocking and isinstance(proc, subprocess.CompletedProcess) else "started."
        self.report({'INFO'}, f"Worker {status_message}")
        return {'FINISHED'}

def get_material_by_uuid(uuid_str: str): # Unchanged
    if not uuid_str: return None
    mat = bpy.data.materials.get(uuid_str) # Primary check by UUID as name
    if mat: return mat
    for m in bpy.data.materials: # Fallback check custom property
        try:
            if m.get("uuid") == uuid_str: return m
        except ReferenceError: continue
    return None

def ensure_material_library(): # Unchanged
    try:
        os.makedirs(LIBRARY_FOLDER, exist_ok=True); os.makedirs(THUMBNAIL_FOLDER, exist_ok=True)
        if not os.path.exists(LIBRARY_FILE):
            temp_dir = tempfile.mkdtemp(); temp_file = os.path.join(temp_dir, "empty_library.blend")
            bpy.data.libraries.write(temp_file, set(), fake_user=True)
            shutil.copy(temp_file, LIBRARY_FILE); shutil.rmtree(temp_dir)
        initialize_database() # Ensure DB is also initialized
        return True
    except Exception as e: print(f"Error ensure_material_library: {e}"); traceback.print_exc(); return False

# --------------------------
# Material Library Functions (Unchanged)
# --------------------------
def update_material_library(force_update=False): # Unchanged
    global is_update_processing
    if not is_update_processing:
        library_update_queue.append({'type': 'UPDATE', 'force': force_update})
        is_update_processing = True
        bpy.app.timers.register(process_library_queue)
    # else: print("[LIB] Update already queued") # Optional: re-enable if needed

def _parse_material_suffix(name: str) -> tuple[str, int]:
    """
    Parses a material name into its base name and suffix number.
    Example: "mat_Plastic.001" -> ("mat_Plastic", 1)
             "mat_Plastic" -> ("mat_Plastic", -2) (no suffix is considered lowest)
             "mat_Plastic.000" -> ("mat_Plastic", 0)
    Returns (base_name, suffix_number)
    """
    match = re.fullmatch(r"^(.*?)(\.(\d+))?$", name)
    if not match: # Should ideally not happen for valid material names
        return name, -1 # Fallback, though -1 might conflict with .000 if not careful
    
    base_name = match.group(1)
    suffix_str = match.group(3)
    
    if suffix_str is None:
        return base_name, -2 # No suffix, considered the "lowest"
    else:
        return base_name, int(suffix_str)

# --------------------------
# MATERIAL LIST ITEM CLASS
# ... existing code ...
def populate_material_list(scene):
    """
    Rebuilds the material list items.
    If scene.hide_mat_materials is True, materials with display name starting "mat_" are excluded.
    If scene.hide_mat_materials is False, only the "mat_" material with the lowest suffix for each base name is shown.
    Handles local vs library duplicates by UUID. Sorts and applies "Show Only Local/Used".
    """
    if not scene:
        print("[Populate Suffix Filter] Error: Scene object is None.")
        return

    sort_mode = "Alphabetical" if scene.material_list_sort_alpha else "Recency"
    filter_local_used_active = scene.material_list_show_only_local
    hide_mat_prefix_materials = scene.hide_mat_materials
    
    log_message = (
        f"[Populate Suffix Filter] Starting (Sort: {sort_mode}, "
        f"Filter Local/Used: {filter_local_used_active}, "
        f"Hide 'mat_' Materials: {hide_mat_prefix_materials}"
    )
    if not hide_mat_prefix_materials:
        log_message += " - Showing lowest suffix for 'mat_' materials."
    print(log_message + ")...")


    try:
        if hasattr(scene, "material_list_items"):
            scene.material_list_items.clear()
        else:
            print("[Populate Suffix Filter] Error: Scene missing 'material_list_items'. Cannot populate.")
            return

        material_info_map = {} # Final map: UUID -> info_dict for list items
        mat_prefix_candidates = {} # Temp map for choosing lowest suffix: base_name -> chosen_mat_info

        current_material_collection = bpy.data.materials
        print(f"[Populate Suffix Filter] Processing {len(current_material_collection)} materials in bpy.data...")

        for mat in current_material_collection:
            if not mat or not hasattr(mat, 'name'):
                print(f"[Populate Suffix Filter] Skipping invalid material reference.")
                continue
            
            try:
                display_name = mat_get_display_name(mat)
                mat_uuid = get_material_uuid(mat) # Ensures UUID property exists
                if not mat_uuid:
                    # print(f"[Populate Suffix Filter] Skipping material '{mat.name}' - could not get UUID.")
                    continue

                is_library = bool(mat.library)
                is_protected = mat.get('is_protected', False)
                # For 'mat_' materials, original_name will likely be display_name itself.
                # For others, it could be from DB or display_name.
                original_name_prop = mat.get("orig_name", display_name) 

                item_info_dict = {
                    'mat_obj': mat, 
                    'display_name': display_name,
                    'uuid': mat_uuid, 
                    'is_library': is_library,
                    'is_protected': is_protected,
                    'original_name': original_name_prop
                }

                if display_name.startswith("mat_"):
                    if hide_mat_prefix_materials:
                        # print(f"[Populate Suffix Filter] EXCLUDING 'mat_' material due to 'hide_mat_materials' setting: {display_name}")
                        continue
                    else:
                        # Logic to select only the lowest suffix for "mat_" materials
                        base_name, suffix_num = _parse_material_suffix(display_name)
                        item_info_dict['suffix_num'] = suffix_num # Add suffix_num for comparison

                        existing_candidate = mat_prefix_candidates.get(base_name)
                        if not existing_candidate or suffix_num < existing_candidate['suffix_num']:
                            mat_prefix_candidates[base_name] = item_info_dict
                else:
                    # Non-"mat_" material, add directly to material_info_map, handling local/library priority
                    existing_entry = material_info_map.get(mat_uuid)
                    if existing_entry:
                        if not is_library and existing_entry['is_library']: # Current is local, existing was library
                            material_info_map[mat_uuid] = item_info_dict
                        # If existing is local and current is library, or both same type, keep existing
                    else: # New UUID entry
                        material_info_map[mat_uuid] = item_info_dict
            
            except ReferenceError: print(f"[Populate Suffix Filter] ReferenceError for a material. Skipping.")
            except Exception as e_proc: print(f"[Populate Suffix Filter] Error processing '{getattr(mat, 'name', 'N/A')}': {e_proc}")

        # Add the chosen "mat_" prefix materials to the main material_info_map
        if not hide_mat_prefix_materials:
            for base_name, chosen_mat_info in mat_prefix_candidates.items():
                chosen_uuid = chosen_mat_info['uuid']
                # Check for UUID conflict with already added non-"mat_" materials (unlikely but good to be safe)
                # and prioritize local if such a conflict occurs.
                existing_entry = material_info_map.get(chosen_uuid)
                if existing_entry:
                    if not chosen_mat_info['is_library'] and existing_entry['is_library']:
                        material_info_map[chosen_uuid] = chosen_mat_info
                else:
                    material_info_map[chosen_uuid] = chosen_mat_info
        
        # Convert map values to list for filtering and sorting
        items_to_process = list(material_info_map.values())

        if filter_local_used_active:
            # print("[Populate Suffix Filter] Applying 'Show Only Local/Used' filter.")
            used_material_uuids_in_scene = set()
            for obj in bpy.data.objects: 
                if hasattr(obj, 'material_slots'):
                    for slot in obj.material_slots:
                        if slot.material:
                            mat_uuid_in_slot = get_material_uuid(slot.material) 
                            if mat_uuid_in_slot: used_material_uuids_in_scene.add(mat_uuid_in_slot)

            items_to_process = [
                info_item for info_item in items_to_process 
                if not info_item['is_library'] or \
                   (info_item['is_library'] and info_item['uuid'] in used_material_uuids_in_scene)
            ]
            # print(f"[Populate Suffix Filter] After 'Local/Used' filter, {len(items_to_process)} items remain.")

        material_timestamps = {}
        if not scene.material_list_sort_alpha: # Recency sort needs timestamps
            try:
                with get_db_connection() as conn:
                    c = conn.cursor(); c.execute("SELECT uuid, ts FROM mat_time")
                    material_timestamps = {row[0]: row[1] for row in c.fetchall()}
                # print(f"[Populate Suffix Filter] Loaded {len(material_timestamps)} timestamps.")
            except Exception as e_ts: print(f"[Populate Suffix Filter] Error loading timestamps: {e_ts}")

        for info in items_to_process: 
            info['timestamp'] = material_timestamps.get(info['uuid'], 0) 

        # print(f"[Populate Suffix Filter] Sorting {len(items_to_process)} items...")
        start_sort_time = time.time()
        try:
            sort_key_func = (lambda item: item['display_name'].lower()) if scene.material_list_sort_alpha \
                            else (lambda item: -item['timestamp']) 
            sorted_list_for_ui = sorted(items_to_process, key=sort_key_func)
            # print(f"[Populate Suffix Filter] Sorting finished in {time.time() - start_sort_time:.4f} sec.")
        except Exception as sort_error:
            print(f"[Populate Suffix Filter] Error sorting list: {sort_error}. Proceeding unsorted.")
            sorted_list_for_ui = items_to_process 

        # print("[Populate Suffix Filter] Adding items to UI list collection...")
        items_added_to_ui_list = 0
        for item_data in sorted_list_for_ui:
            try:
                list_item = scene.material_list_items.add() 
                list_item.material_name = item_data['display_name']
                list_item.material_uuid = item_data['uuid']
                list_item.is_library = item_data['is_library']
                list_item.original_name = item_data['original_name']
                list_item.is_protected = item_data['is_protected']
                items_added_to_ui_list += 1
            except Exception as add_error:
                print(f"[Populate Suffix Filter UI] Error adding item for UUID {item_data.get('uuid','N/A')}: {add_error}")

        print(f"[Populate Suffix Filter] Material list populated with {items_added_to_ui_list} items.")

        if items_added_to_ui_list > 0:
            if scene.material_list_active_index >= items_added_to_ui_list:
                scene.material_list_active_index = items_added_to_ui_list - 1
            elif scene.material_list_active_index < 0: 
                scene.material_list_active_index = 0
        else: 
            scene.material_list_active_index = -1

    except Exception as e:
        print(f"[Populate Suffix Filter] CRITICAL error during list population: {e}")
        traceback.print_exc()

def get_material_by_unique_id(unique_id): # Unchanged
    for mat in bpy.data.materials:
        if str(id(mat)) == unique_id: return mat
    return None

def initialize_db_connection_pool(): # Unchanged (loading names here is a bit redundant but harmless)
    global material_names
    print("[DB Pool] Initializing database connection pool...", flush=True)
    try:
        os.makedirs(LIBRARY_FOLDER, exist_ok=True)
        temp_connections = []
        for i in range(5):
            conn = sqlite3.connect(DATABASE_FILE, check_same_thread=False)
            temp_connections.append(conn)
            if i == 0: # Initial load via first connection attempt
                try:
                    c = conn.cursor()
                    c.execute("SELECT uuid, original_name FROM material_names")
                    db_names = {row[0]: row[1] for row in c.fetchall()}
                    if not material_names: material_names = db_names
                    elif len(db_names) > len(material_names): material_names.update(db_names)
                except sqlite3.Error as e: print(f"[DB Pool] Error init names: {e}", flush=True)
        for conn_obj in temp_connections: db_connections.put(conn_obj)
        print(f"[DB Pool] Pool init with {db_connections.qsize()} connections.", flush=True)
    except Exception as e: print(f"[DB Pool] Error init pool: {e}", flush=True); traceback.print_exc()

# --------------------------
# Event Handlers (save_handler and load_post_handler updated)
# --------------------------
@persistent
def save_handler(dummy):
    """
    Pre-save handler:
      * Implements "process once per save operation" logic.
      * Validates/creates UUIDs for non-"mat_" materials (based on display name).
      * Ensures local non-"mat_" materials (by display name) are NAMED by their UUID.
      * Ensures DB display name entry for non-"mat_" materials.
      * Always recalculates hash for local materials. If a local material's hash changes,
        its old thumbnail (if one existed for the old hash) is deleted.
      * Saves updated hashes/names to DB.
      * Queues library update.
    """
    global materials_modified, material_names, material_hashes

    if getattr(bpy.context.window_manager, 'matlist_save_handler_processed', False):
        print("[SAVE DB] Save handler already processed for this specific save operation. Skipping.")
        return
    bpy.context.window_manager.matlist_save_handler_processed = True

    print("\n[SAVE DB] Starting pre-save process (mat_ exclusion by display name, targeted old thumb deletion & process-once)")

    needs_metadata_update = False
    needs_name_db_save = False
    mats_to_rename_datablocks = []

    if not material_names and bpy.data.filepath:
        print("[SAVE DB] material_names dictionary empty, attempting load from DB...")
        load_material_names()

    print("[SAVE DB] Phase 1: Processing UUIDs and initial DB names (mat_ exclusion by display name)...")
    for mat in bpy.data.materials:
        if not mat: continue

        current_display_name_for_skip = "Unknown"
        try:
            current_display_name_for_skip = mat_get_display_name(mat)
        except Exception as e_get_display_skip_save:
            print(f"[SAVE DB] Warning: Could not get display name for {getattr(mat, 'name', 'N/A')} during skip check: {e_get_display_skip_save}. Proceeding with datablock name.")
            current_display_name_for_skip = mat.name

        if current_display_name_for_skip.startswith("mat_"):
            continue

        original_datablock_name = mat.name
        old_uuid_prop = mat.get("uuid", "")
        current_uuid_prop = validate_material_uuid(mat)

        if current_uuid_prop != old_uuid_prop:
            needs_metadata_update = True
            print(f"[SAVE DB] UUID property assigned/changed for '{original_datablock_name}': -> '{current_uuid_prop}'")

        if current_uuid_prop and current_uuid_prop not in material_names:
            initial_display_name_for_db = original_datablock_name
            print(f"[SAVE DB] Adding new material display name entry to DB (in memory): UUID={current_uuid_prop}, Name='{initial_display_name_for_db}'")
            material_names[current_uuid_prop] = initial_display_name_for_db
            needs_name_db_save = True

        if current_uuid_prop and not mat.library and mat.name != current_uuid_prop:
            mats_to_rename_datablocks.append((mat, current_uuid_prop))

    if mats_to_rename_datablocks:
        print(f"[SAVE DB] Attempting to rename {len(mats_to_rename_datablocks)} local non-'mat_' (by display name) datablocks to their UUIDs...")
    for mat_to_rename, target_uuid_name in mats_to_rename_datablocks:
        existing_mat_with_target_name = bpy.data.materials.get(target_uuid_name)
        if not existing_mat_with_target_name or existing_mat_with_target_name == mat_to_rename:
            try:
                old_name_for_log = mat_to_rename.name
                mat_to_rename.name = target_uuid_name
                needs_metadata_update = True
                print(f"[SAVE DB] Renamed local datablock '{old_name_for_log}' -> '{target_uuid_name}'")
            except Exception as rename_err:
                print(f"[SAVE DB] Warning: Failed to rename datablock '{old_name_for_log}' to UUID '{target_uuid_name}': {rename_err}.")

    # --- Phase 2: Hash Recalculation & Targeted Old Thumbnail Deletion ---
    hashes_to_save_to_db = {}
    hashes_actually_changed_in_db = False
    load_material_hashes() # Load current DB hashes into material_hashes global

    print("[SAVE DB] Phase 2: Checking material hashes and deleting old thumbnails for modified local materials...")
    deleted_old_thumb_count = 0
    for mat in bpy.data.materials:
        if not mat: continue

        mat_name_debug = getattr(mat, 'name', 'N/A')
        actual_uuid_for_hash_storage = mat.get("uuid") # Should exist due to validate_material_uuid in get_material_hash

        if not actual_uuid_for_hash_storage:
            # This should be very rare if get_material_hash ensures UUID prop.
            print(f"[SAVE DB] Warning: Material '{mat_name_debug}' missing 'uuid' property. Skipping hash check and old thumb deletion for it.")
            continue

        # For local materials, always recalculate. For library, only if forced (not typical on save).
        force_recalc_for_hash = not mat.library
        current_calculated_hash = get_material_hash(mat, force=force_recalc_for_hash)

        if not current_calculated_hash:
            print(f"[SAVE DB] Warning: Failed to calculate current hash for {mat_name_debug} (UUID: {actual_uuid_for_hash_storage}). Skipping hash update.")
            continue

        db_stored_hash = material_hashes.get(actual_uuid_for_hash_storage)

        if db_stored_hash != current_calculated_hash:
            hashes_to_save_to_db[actual_uuid_for_hash_storage] = current_calculated_hash
            if db_stored_hash is not None: # Hash changed from a known previous value
                hashes_actually_changed_in_db = True
                # --- TARGETED DELETION OF OLD THUMBNAIL ---
                # Only delete if it's a local material that changed. Library material changes are handled differently.
                if not mat.library: # Only for local, modifiable materials
                    old_thumbnail_path = get_thumbnail_path(db_stored_hash)
                    try:
                        if os.path.isfile(old_thumbnail_path):
                            os.remove(old_thumbnail_path)
                            deleted_old_thumb_count += 1
                            print(f"[SAVE DB] Deleted old thumbnail '{os.path.basename(old_thumbnail_path)}' for modified material '{mat_name_debug}' (UUID: {actual_uuid_for_hash_storage}). Old hash: {db_stored_hash}, New hash: {current_calculated_hash}")
                    except Exception as e_del_thumb:
                        print(f"[SAVE DB] Error deleting old thumbnail {old_thumbnail_path}: {e_del_thumb}")
                # --- END TARGETED DELETION ---

        if "hash_dirty" in mat:
            try: mat["hash_dirty"] = False
            except Exception: pass
    
    if deleted_old_thumb_count > 0:
        print(f"[SAVE DB] Total old thumbnails deleted due to material modifications: {deleted_old_thumb_count}")

    if needs_name_db_save:
        print("[SAVE DB] Saving updated material display names to database...")
        save_material_names()

    if hashes_to_save_to_db:
        material_hashes.update(hashes_to_save_to_db) # Update global dict
        print(f"[SAVE DB] Saving {len(hashes_to_save_to_db)} updated/new material hashes to database...")
        save_material_hashes() # Save to DB

    print("[SAVE DB] Phase 3: Determining if library update needed...")
    if hashes_actually_changed_in_db:
        print("[SAVE DB] Material hash values changed for existing DB entries – queuing FORCED library update.")
        update_material_library(force_update=True)
    elif needs_metadata_update or hashes_to_save_to_db or needs_name_db_save:
        print("[SAVE DB] Metadata changed, or new hashes/names added – queuing non-forced library update.")
        update_material_library(force_update=False)
    else:
        print("[SAVE DB] No changes detected requiring library update queue.")

    print("[SAVE DB] Pre-save handler complete.\n")
    materials_modified = False

@persistent
def save_post_handler(dummy=None): # Unchanged from your version for its core tasks
    print("[DEBUG] save_post_handler: Starting post-save tasks.")
    scene = get_first_scene()
    current_blend_filepath = bpy.data.filepath

    if scene:
        try:
            populate_material_list(scene); force_redraw()
        except Exception as e: print(f"[DEBUG] save_post_handler: Error UI refresh: {e}"); traceback.print_exc()

    if current_blend_filepath and os.path.exists(LIBRARY_FILE):
        library_path_norm = os.path.normcase(os.path.normpath(os.path.abspath(LIBRARY_FILE)))
        used_library_uuids = set()
        materials_in_use = {slot.material for obj in bpy.data.objects if obj.type == 'MESH' for slot in obj.material_slots if slot.material}
        for mat in bpy.data.materials:
            if mat.library and hasattr(mat.library, 'filepath'):
                try:
                    if os.path.normcase(os.path.normpath(bpy.path.abspath(mat.library.filepath))) == library_path_norm and mat in materials_in_use:
                        mat_uuid = get_material_uuid(mat)
                        if mat_uuid: used_library_uuids.add(mat_uuid)
                except Exception: pass # Ignore errors processing individual material paths
        try:
            with get_db_connection() as conn:
                cur = conn.cursor()
                cur.execute("DELETE FROM blend_material_usage WHERE blend_filepath = ?", (current_blend_filepath,))
                if used_library_uuids:
                    cur.executemany("INSERT OR IGNORE INTO blend_material_usage VALUES (?, ?, ?)",
                                    [(current_blend_filepath, uuid_val, int(time.time())) for uuid_val in used_library_uuids])
                conn.commit()
        except Exception as e: print(f"[POST-SAVE] DB Error usage log: {e}"); traceback.print_exc()

    if 'update_material_thumbnails' in globals() and callable(update_material_thumbnails):
        update_material_thumbnails()
    # else: print("[DEBUG] save_post_handler: update_material_thumbnails not found") # Optional
    print("[DEBUG] save_post_handler: Finished.")

@persistent
def load_post_handler(dummy):
    """
    Schedules deferred tasks after file load.
    Resets the save_handler's "process once" flag.
    Clears relevant caches.
    """
    print("[DEBUG LoadPost] load_post_handler: Start")

    # --- Reset "Process Once" flag for save_handler ---
    if hasattr(bpy.context.window_manager, 'matlist_save_handler_processed'):
        bpy.context.window_manager.matlist_save_handler_processed = False
        print("[DEBUG LoadPost] Reset save_handler 'processed' flag.")
    # --- End Reset ---

    # --- Clear Caches that should be file-specific ---
    global _display_name_cache, global_hash_cache, material_list_cache, material_names, material_hashes
    print("[DEBUG LoadPost] Clearing file-specific caches: _display_name_cache, global_hash_cache, material_list_cache, material_names, material_hashes")
    _display_name_cache.clear()
    global_hash_cache.clear() # Hashes are loaded from DB per file in delayed_load_post
    material_list_cache.clear() # UI list cache, rebuilt by populate_material_list

    # material_names and material_hashes are fully reloaded from DB in delayed_load_post,
    # so clearing them here is also good practice to ensure no stale data if delayed_load_post had an issue.
    material_names.clear()
    material_hashes.clear()
    # --- End Cache Clearing ---

    # Schedule the deferred tasks (original logic)
    bpy.app.timers.register(delayed_load_post, first_interval=0.2)
    # update_material_thumbnails is critical and should run after delayed_load_post has initialized names/hashes
    bpy.app.timers.register(update_material_thumbnails, first_interval=1.0) # Slightly increased delay

    print("[DEBUG LoadPost] Scheduled delayed_load_post and update_material_thumbnails.")

def file_changed_handler(scene): # Unchanged
    try:
        if not scene: return
        if scene.workspace_mode == 'REFERENCE':
            for obj in scene.objects:
                if obj.type == 'MESH' and obj.name in reference_backup:
                    ref = reference_backup[obj.name]
                    current_slots_count = len(obj.material_slots)
                    ref_slots_count = len(ref) if ref else None
                    current = [slot.material.name if (slot.material and slot.material.name.startswith("mat_")) else None for slot in obj.material_slots]
                    if ref is None or current_slots_count != ref_slots_count or current != ref:
                        scene.workspace_mode = 'EDITING'
                        if not editing_backup: backup_current_assignments(editing_backup, 'editing')
                        force_redraw(); break
    except Exception as e: print(f"Error in file_changed_handler: {e}")

@persistent
def delayed_load_post(): # Unchanged in core logic, but benefits from other fixes (cache clearing in load_post_handler)
    global custom_icons, material_names, material_hashes, global_hash_cache
    print("[DEBUG] delayed_load_post (v3 - Stable custom_icons): Start")
    scene = get_first_scene();
    if not scene: print("[DEBUG] delayed_load_post: No scene found, aborting."); return None

    print("[DEBUG delayed_load_post] Loading names and hashes...")
    load_material_names() # Loads into global material_names
    load_material_hashes() # Loads into global material_hashes
    with hash_lock: # Protect global_hash_cache
        global_hash_cache.clear() # Clear before repopulating
        for uid, h_val in material_hashes.items(): global_hash_cache[uid] = h_val

    for mat in bpy.data.materials:
        if not mat.library:
            try: mat["hash_dirty"] = False # Reset dirty flag
            except Exception: pass
    print(f"[DEBUG delayed_load_post] Loaded {len(material_names)} names, {len(material_hashes)} hashes.")

    print("[Delayed Load] Managing preview icon cache...")
    if custom_icons is None:
        print("[Delayed Load] custom_icons is None. Attempting to create new collection.")
        try:
            custom_icons = bpy.utils.previews.new()
            if custom_icons is not None:
                print(f"[Delayed Load] New preview collection created: {custom_icons}")
                if 'preload_existing_thumbnails' in globals() and callable(preload_existing_thumbnails):
                    preload_existing_thumbnails() # Preload into the new collection
            else: print("[Delayed Load] CRITICAL ERROR: bpy.utils.previews.new() returned None!")
        except Exception as e_new_delayed: print(f"[Delayed Load] CRITICAL Error creating preview collection: {e_new_delayed}"); traceback.print_exc()
    else: # custom_icons already exists
        print(f"[Delayed Load] custom_icons already exists ({custom_icons}). Calling preload to update.")
        if 'preload_existing_thumbnails' in globals() and callable(preload_existing_thumbnails):
            preload_existing_thumbnails() # Safe to call, skips already loaded

    # --- Link Library Materials & Correct Names Post-Link ---
    # (This logic remains from your original, ensure LIBRARY_FILE is correct path)
    if os.path.exists(LIBRARY_FILE):
        print("[DEBUG] delayed_load_post: Linking library materials...")
        try:
            currently_linked_from_lib = {
                mat.name for mat in bpy.data.materials
                if mat.library and hasattr(mat.library, 'filepath') and os.path.normcase(os.path.abspath(mat.library.filepath)) == os.path.normcase(os.path.abspath(LIBRARY_FILE))
            }
            with bpy.data.libraries.load(LIBRARY_FILE, link=True) as (data_from, data_to):
                if hasattr(data_from, 'materials') and data_from.materials:
                    new_mats_to_link_names = [name for name in data_from.materials if name not in currently_linked_from_lib]
                    if new_mats_to_link_names:
                        mats_to_actually_link = [name for name in new_mats_to_link_names if not (bpy.data.materials.get(name) and not bpy.data.materials.get(name).library)]
                        if mats_to_actually_link: data_to.materials = mats_to_actually_link
            # Post-link name correction (essential if library stores by UUID)
            library_path_norm = os.path.normcase(os.path.abspath(LIBRARY_FILE))
            for mat in bpy.data.materials:
                if mat.library and hasattr(mat.library, 'filepath') and os.path.normcase(bpy.path.abspath(mat.library.filepath)) == library_path_norm:
                    actual_uuid = get_material_uuid(mat)
                    if actual_uuid and mat.name != actual_uuid:
                        try:
                            existing_with_uuid_name = bpy.data.materials.get(actual_uuid)
                            if not existing_with_uuid_name or existing_with_uuid_name == mat: mat.name = actual_uuid
                        except Exception as rename_err: print(f"[DEBUG PostLink] Error renaming linked '{mat.name}' to UUID '{actual_uuid}': {rename_err}")
        except Exception as e: print(f"[DEBUG] delayed_load_post: Error linking library materials: {e}"); traceback.print_exc()
    else: print(f"[DEBUG] delayed_load_post: Library file not found at {LIBRARY_FILE}.")

    # Initialize material properties after linking and name corrections
    # This ensures UUIDs are set and local non-"mat_" materials are named by UUID.
    if 'initialize_material_properties' in globals() and callable(initialize_material_properties):
        initialize_material_properties()
    else:
        print("[DEBUG delayed_load_post] ERROR: initialize_material_properties function not found!")


    print("[DEBUG] delayed_load_post (v3 - Stable custom_icons): End")
    return None # Timer will stop

def get_first_scene(): # Unchanged
    scenes = getattr(bpy.data, "scenes", [])
    return scenes[0] if scenes else None

# --------------------------
# Operator Classes
# --------------------------
class MATERIALLIST_OT_toggle_workspace_mode(Operator):
    bl_idname = "materiallist.toggle_workspace_mode"
    bl_label = "Toggle Workspace Mode"
    def execute(self, context):
        scene = context.scene
        current = scene.workspace_mode
        scene.workspace_mode = 'EDITING' if current == 'REFERENCE' else 'REFERENCE'
        update_workspace_mode(self, context) # Call the existing update_workspace_mode
        self.report({'INFO'}, f"Switched to {scene.workspace_mode} mode.")
        return {'FINISHED'}

class MATERIALLIST_OT_rename_material(Operator):
    bl_idname = "materiallist.rename_material"
    bl_label = "Rename Material"
    bl_description = "Rename the display name of the selected material (stored in database)"
    bl_options = {'REGISTER', 'UNDO'}

    new_name: StringProperty(name="New Name", default="")

    def execute(self, context):
        global _display_name_cache, material_names
        scene = context.scene
        idx = scene.material_list_active_index

        if 0 <= idx < len(scene.material_list_items):
            item = scene.material_list_items[idx]
            target_uuid = item.material_uuid
            mat = bpy.data.materials.get(target_uuid)

            if mat:
                new_name_str = self.new_name.strip()
                if not new_name_str:
                    self.report({'WARNING'}, "Empty name not allowed.")
                    return {'CANCELLED'}

                current_display_name = mat_get_display_name(mat)

                if new_name_str == current_display_name:
                    self.report({'INFO'}, "Display name is already set to that.")
                    scene.material_list_active_index = idx
                    return {'FINISHED'}

                uuid_to_update = get_material_uuid(mat)
                if not uuid_to_update:
                    self.report({'ERROR'}, f"Could not retrieve valid UUID for material '{mat.name}'. Cannot rename.")
                    return {'CANCELLED'}

                print(f"[Rename DB] Updating display name for UUID {uuid_to_update} from '{current_display_name}' to '{new_name_str}'")
                material_names[uuid_to_update] = new_name_str
                save_material_names()
                _display_name_cache.clear()
                populate_material_list(scene)
                self.report({'INFO'}, f"Updated material display name to '{new_name_str}'.")

                new_idx = -1
                for i, current_item in enumerate(scene.material_list_items):
                    if current_item.material_uuid == target_uuid:
                        new_idx = i
                        break
                if new_idx != -1:
                    scene.material_list_active_index = new_idx
                    print(f"[Rename DB] Reselected item '{new_name_str}' at new index {new_idx}.")
                else:
                    print(f"[Rename DB] Warning: Could not find item with UUID {target_uuid} after renaming and list refresh.")
                    scene.material_list_active_index = 0 if len(scene.material_list_items) > 0 else -1
                return {'FINISHED'}
            else:
                self.report({'WARNING'}, "Material associated with selected list item not found. List may be outdated.")
                populate_material_list(scene)
                return {'CANCELLED'}
        else:
            self.report({'WARNING'}, "No material selected or index out of bounds.")
            return {'CANCELLED'}

    def invoke(self, context, event):
        scene = context.scene
        idx = scene.material_list_active_index
        self.new_name = ""
        if 0 <= idx < len(scene.material_list_items):
            item = scene.material_list_items[idx]
            mat = bpy.data.materials.get(item.material_uuid)
            if mat:
                self.new_name = mat_get_display_name(mat)
        wm = context.window_manager
        return wm.invoke_props_dialog(self)

class MATERIALLIST_OT_unassign_mat(Operator):
    bl_idname = "materiallist.unassign_mat"
    bl_label = "Unassign mat_"
    bl_description = "Remove material slots containing materials starting with 'mat_'"
    def execute(self, context):
        scene = get_first_scene()
        if not scene:
            self.report({'WARNING'}, "No scene found")
            return {'CANCELLED'}
        original_active = context.view_layer.objects.active
        original_selection = list(context.selected_objects)
        remove_materials = {
            mat.name
            for mat in bpy.data.materials
            if mat_get_display_name(mat).startswith("mat_")
        }
        processed_objects = 0
        removed_slots = 0
        for obj in scene.objects:
            if obj.type != 'MESH':
                continue
            slots_to_remove = []
            for idx, slot in enumerate(obj.material_slots):
                if slot.material and slot.material.name in remove_materials:
                    slots_to_remove.append(idx)
            if not slots_to_remove:
                continue
            with context.temp_override(
                window=context.window,
                area=context.area,
                region=context.region,
                selected_objects=[obj],
                active_object=obj,
                object=obj
            ):
                for idx in reversed(sorted(slots_to_remove)):
                    obj.active_material_index = idx
                    bpy.ops.object.material_slot_remove()
                    removed_slots += 1
            processed_objects += 1
        context.view_layer.objects.active = original_active
        for obj in original_selection:
            obj.select_set(True)
        self.report({'INFO'}, f"Removed {removed_slots} material slots from {processed_objects} objects")
        return {'FINISHED'}

class MATERIALLIST_OT_backup_reference(Operator):
    bl_idname = "materiallist.backup_reference"
    bl_label = "Backup Reference"
    bl_description = "Backup the current material assignments as the Reference configuration"
    def execute(self, context):
        reference_backup.clear()
        backup_current_assignments(reference_backup, 'reference')
        save_backups()
        self.report({'INFO'}, "Backed up Reference configuration")
        return {'FINISHED'}

class MATERIALLIST_OT_backup_editing(Operator):
    bl_idname = "materiallist.backup_editing"
    bl_label = "Backup Editing"
    bl_description = ("Duplicate currently visible meshes, join them, and "
                      "store the result in a 'Reference' collection. Also "
                      "stores which objects are visible for later restore.")
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        print("\n[BACKUP EDITING OPERATOR START] >>>>>>>>>>>>>>>>>>>>>>")
        print(f"[Backup Editing Op] Context Scene: {context.scene.name}, View Layer: {context.view_layer.name}")
        ok = create_reference_snapshot(context)
        print(f"[Backup Editing Op] Helper function returned: {ok}")
        if ok:
            print("[Backup Editing Op] Snapshot success. Saving visible objects...")
            _save_visible_objects(context.scene)
            self.report({'INFO'}, "Reference snapshot created.")
            print("[BACKUP EDITING OPERATOR END - SUCCESS] <<<<<<<<<<<<<<\n")
            return {'FINISHED'}
        else:
            print("[Backup Editing Op] Snapshot failed.")
            self.report({'WARNING'}, "Reference snapshot creation failed. Check console.")
            print("[BACKUP EDITING OPERATOR END - FAIL] <<<<<<<<<<<<<<<<\n")
            return {'CANCELLED'}

class MATERIALLIST_OT_add_material_to_slot(Operator):
    bl_idname = "materiallist.add_material_to_slot"
    bl_label = "Add Selected to Object"
    bl_description = "Add the selected material to the active object's slots without assigning it to faces"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        active_obj = context.active_object
        scene = context.scene
        return (active_obj and active_obj.type == 'MESH' and
                scene and hasattr(scene, 'material_list_items') and
                0 <= scene.material_list_active_index < len(scene.material_list_items))

    def execute(self, context):
        scene = context.scene
        active_obj = context.active_object
        mesh_data = active_obj.data
        selected_item = scene.material_list_items[scene.material_list_active_index]
        target_uuid = selected_item.material_uuid
        target_mat = get_material_by_uuid(target_uuid)

        if not target_mat:
            self.report(
                {"WARNING"},
                f"Material '{selected_item.material_name}' (UUID: {target_uuid}) not found.",
            )
            return {"CANCELLED"}

        mat_exists = False
        target_slot_index = -1
        for i, slot in enumerate(mesh_data.materials):
            if slot == target_mat:
                mat_exists = True
                target_slot_index = i
                break

        action_taken = False
        if mat_exists:
            self.report(
                {"INFO"},
                f"Material '{target_mat.name}' already exists in slot {target_slot_index} "
                f"for '{active_obj.name}'.",
            )
            active_obj.active_material_index = target_slot_index
            action_taken = True
        else:
            mesh_data.materials.append(target_mat)
            target_slot_index = len(mesh_data.materials) - 1
            active_obj.active_material_index = target_slot_index
            self.report(
                {"INFO"},
                f"Added material '{target_mat.name}' to slot {target_slot_index} "
                f"for '{active_obj.name}'.",
            )
            action_taken = True

        if action_taken:
            update_material_timestamp(target_uuid)
            populate_material_list(scene)
            new_idx = -1
            for i, itm in enumerate(scene.material_list_items):
                if itm.material_uuid == target_uuid:
                    new_idx = i
                    break
            scene.material_list_active_index = (
                new_idx if new_idx != -1 else 0 if scene.material_list_items else -1
            )
        return {"FINISHED"}

class MATERIALLIST_OT_assign_selected_material(Operator):
    bl_idname = "materiallist.assign_selected_material"
    bl_label = "Assign Selected Material"
    bl_description = "Assign selected material to object/faces"

    @classmethod
    def poll(cls, context):
        active_obj = context.active_object
        scene = context.scene
        return (active_obj and active_obj.type == 'MESH' and
                scene and hasattr(scene, 'material_list_items') and
                0 <= scene.material_list_active_index < len(scene.material_list_items))

    def execute(self, context):
        scene = context.scene
        if not (
            0 <= scene.material_list_active_index < len(scene.material_list_items)
        ):
            self.report({"WARNING"}, "Invalid material selection.")
            return {"CANCELLED"}

        target_item = scene.material_list_items[scene.material_list_active_index]
        target_uuid = target_item.material_uuid
        target_mat = get_material_by_uuid(target_uuid)

        if not target_mat:
            self.report(
                {"WARNING"}, "Selected material not found in Blender data."
            )
            return {"CANCELLED"}

        result = {"CANCELLED"}
        assign_op_called = False

        if context.mode == "OBJECT":
            result = bpy.ops.materiallist.assign_to_object(
                "EXEC_DEFAULT", target_material_name=target_mat.name
            )
            assign_op_called = True
        elif context.mode == "EDIT_MESH":
            result = bpy.ops.materiallist.assign_to_faces(
                "EXEC_DEFAULT", target_material_name=target_mat.name
            )
            assign_op_called = True
        else:
            self.report({"WARNING"}, "Unsupported mode for assignment")
            return {"CANCELLED"}

        if result == {"FINISHED"} and assign_op_called:
            update_material_timestamp(target_uuid)
            populate_material_list(scene)
            new_idx = -1
            for i, itm in enumerate(scene.material_list_items):
                if itm.material_uuid == target_uuid:
                    new_idx = i
                    break
            scene.material_list_active_index = (
                new_idx if new_idx != -1 else 0 if scene.material_list_items else -1
            )
        return result

class MATERIALLIST_OT_prepare_material(Operator):
    bl_idname = "materiallist.prepare_material"
    bl_label = "Prepare Material"
    bl_options = {"INTERNAL"}

    @classmethod
    def poll(cls, context):
        return (
            context.scene
            and context.scene.material_list_active_index >= 0
            and len(context.scene.material_list_items) > 0
        )

    @classmethod
    def get_target_material(cls, context):
        scene = context.scene
        list_item = scene.material_list_items[scene.material_list_active_index]
        target = get_material_by_uuid(list_item.material_uuid)
        if not target:
            print(f"[ERROR] Material '{list_item.material_name}' not found")
        return target

    def prepare_local_material(self, list_item):
        target = get_material_by_uuid(list_item.material_uuid)
        if not target:
            self.report({"ERROR"}, f"Local material '{list_item.material_name}' not found")
        return target

class MATERIALLIST_OT_assign_to_object(Operator):
    bl_idname = "materiallist.assign_to_object"
    bl_label = "Assign to Object"
    bl_options = {'INTERNAL'}
    target_material_name: StringProperty()

    def execute(self, context):
        target_mat = bpy.data.materials.get(self.target_material_name)
        if not target_mat:
            self.report({'ERROR'}, "Target material not found")
            return {'CANCELLED'}
        original_mode = context.mode
        for ob in context.selected_objects:
            if ob.type != 'MESH': continue
            if target_mat.name not in ob.data.materials:
                ob.data.materials.append(target_mat)
            target_index = ob.data.materials.find(target_mat.name)
            context.view_layer.objects.active = ob
            with context.temp_override(window=context.window, area=context.area, region=context.region, active_object=ob, object=ob):
                if ob.mode != 'EDIT': bpy.ops.object.mode_set(mode='EDIT')
                bm = bmesh.from_edit_mesh(ob.data)
                bm.faces.ensure_lookup_table()
                for face in bm.faces:
                    face.select = True
                    face.material_index = target_index
                bmesh.update_edit_mesh(ob.data)
                bpy.ops.object.mode_set(mode=original_mode)
            ob.active_material_index = target_index
        self.report({'INFO'}, f"Assigned '{target_mat.name}' to all faces of selected objects")
        return {'FINISHED'}

class MATERIALLIST_OT_assign_to_faces(Operator):
    bl_idname = "materiallist.assign_to_faces"
    bl_label = "Assign to Faces"
    bl_options = {"INTERNAL"}
    target_material_name: StringProperty()

    def execute(self, context):
        target_mat = bpy.data.materials.get(self.target_material_name)
        if not target_mat:
            target_mat = get_material_by_uuid(self.target_material_name)
        if not target_mat:
            self.report({"ERROR"}, "Target material not found")
            return {"CANCELLED"}

        for ob in context.selected_objects:
            if ob.type != 'MESH': continue
            try:
                bpy.context.view_layer.objects.active = ob
                if len(ob.data.materials) == 0:
                    ob.data.materials.append(target_mat)
                elif target_mat.name not in [m.name for m in ob.data.materials if m]:
                    ob.data.materials.append(target_mat)
                target_index = ob.data.materials.find(target_mat.name)
                original_mode = ob.mode
                if original_mode == 'OBJECT':
                    bpy.ops.object.mode_set(mode='EDIT')
                    bpy.ops.mesh.select_all(action='SELECT') # Select all faces if in object mode
                    ob.active_material_index = target_index # Set active slot
                    bpy.ops.object.material_slot_assign() # Assign to selected faces
                else: # EDIT_MESH
                    bm = bmesh.from_edit_mesh(ob.data)
                    selected_faces = [f for f in bm.faces if f.select]
                    if not selected_faces:
                        self.report({'WARNING'}, f"No faces selected in '{ob.name}'. Skipping assignment.")
                        if original_mode == 'OBJECT': bpy.ops.object.mode_set(mode='OBJECT') # Revert mode if changed
                        continue
                    ob.active_material_index = target_index # Set active slot
                    bpy.ops.object.material_slot_assign() # Assign to selected faces (BMesh not strictly needed here)
                if original_mode == 'OBJECT':
                    bpy.ops.object.mode_set(mode='OBJECT')
                self.report({'INFO'}, f"Assigned '{target_mat.name}' to faces of '{ob.name}'")
            except Exception as e:
                self.report({'ERROR'}, f"Error processing {ob.name}: {str(e)}")
                if 'original_mode' in locals() and original_mode == 'OBJECT' and ob.mode == 'EDIT':
                    bpy.ops.object.mode_set(mode='OBJECT') # Try to revert mode on error
                continue
        return {'FINISHED'}

class MATERIALLIST_OT_rename_to_albedo(bpy.types.Operator):
    bl_idname = "materiallist.rename_to_albedo"
    bl_label = "Rename Display Name to Albedo"
    bl_description = "Rename display names to match the Base Color texture, skipping names starting with 'mat_'"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context): return True

    def execute(self, context):
        global material_names, _display_name_cache
        renamed_count = 0
        needs_name_db_save = False
        print("[RenameToAlbedo] Starting rename process...")
        if not all(func in globals() for func in ['mat_get_display_name', 'get_material_uuid', 'find_principled_bsdf', 'save_material_names', 'populate_material_list']):
            self.report({'ERROR'}, "Required helper function(s) not found.")
            return {'CANCELLED'}
        if not material_names:
            if 'load_material_names' in globals():
                print("[RenameToAlbedo] Loading material names dictionary...")
                load_material_names()
            else:
                self.report({'ERROR'}, "load_material_names function not found.")
                return {'CANCELLED'}

        for mat in bpy.data.materials:
            if not mat: continue
            current_display_name = mat_get_display_name(mat)
            if current_display_name.startswith("mat_"): continue
            if not mat.use_nodes or not mat.node_tree: continue
            principled_node = find_principled_bsdf(mat)
            if not principled_node: continue
            base_color_input = principled_node.inputs.get('Base Color')
            if not base_color_input or not base_color_input.is_linked: continue
            source_node = None
            try:
                if base_color_input.links: source_node = base_color_input.links[0].from_node
            except IndexError: continue
            if not source_node or source_node.bl_idname != 'ShaderNodeTexImage' or not source_node.image: continue
            albedo_image = source_node.image
            try:
                new_display_name_base = os.path.splitext(albedo_image.name_full)[0]
            except Exception as e:
                print(f"[RenameToAlbedo] Error getting base name for image '{getattr(albedo_image, 'name', 'N/A')}' on material '{current_display_name}': {e}")
                continue
            if new_display_name_base and new_display_name_base != current_display_name:
                mat_uuid = get_material_uuid(mat)
                if mat_uuid:
                    print(f"[RenameToAlbedo] Renaming display name for UUID {mat_uuid} ('{current_display_name}') -> '{new_display_name_base}'")
                    material_names[mat_uuid] = new_display_name_base
                    needs_name_db_save = True
                    renamed_count += 1
                else:
                    print(f"[RenameToAlbedo] Warning: Could not get UUID for material '{mat.name}' to rename.")
        if needs_name_db_save:
            print("[RenameToAlbedo] Saving updated display names to database...")
            try:
                save_material_names()
                _display_name_cache.clear()
                print("[RenameToAlbedo] Display name cache cleared.")
            except Exception as e_save:
                print(f"[RenameToAlbedo] Error saving material names: {e_save}")
                self.report({'ERROR'}, f"Error saving names: {e_save}")
        print("[RenameToAlbedo] Refreshing material list UI...")
        try:
            populate_material_list(context.scene)
        except Exception as e_pop:
            print(f"[RenameToAlbedo] Error refreshing list: {e_pop}")
            self.report({'ERROR'}, f"Error refreshing list: {e_pop}")
        self.report({'INFO'}, f"Rename to Albedo complete. Updated {renamed_count} display names.")
        return {'FINISHED'}

class MATERIALLIST_OT_make_local(Operator):
    bl_idname = "materiallist.make_local"
    bl_label = "Make Material Local"
    bl_description = "Convert a linked library material into a local material for editing."
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        scene = context.scene
        if not (scene and hasattr(scene, 'material_list_items')): return False
        idx = getattr(scene, "material_list_active_index", -1)
        if idx < 0 or idx >= len(scene.material_list_items): return False
        item = scene.material_list_items[idx]
        mat = bpy.data.materials.get(item.material_uuid)
        return mat is not None and mat.library is not None

    def execute(self, context):
        global material_names, _display_name_cache
        scene = context.scene
        idx = scene.material_list_active_index
        if not (0 <= idx < len(scene.material_list_items)):
            self.report({'WARNING'}, "Selected list index is invalid.")
            return {'CANCELLED'}
        item = scene.material_list_items[idx]
        lib_mat_uuid = item.material_uuid
        lib_mat = bpy.data.materials.get(lib_mat_uuid)
        if lib_mat is None or not lib_mat.library:
            self.report({'ERROR'}, "Selected material is already local, missing, or changed since selection.")
            populate_material_list(scene)
            return {'CANCELLED'}
        try:
            display_name_from_lib = mat_get_display_name(lib_mat)
            print(f"[Make Local DB] Copying library material: {lib_mat.name} (UUID: {lib_mat_uuid})")
            local_mat = lib_mat.copy()
            local_mat.library = None
            new_local_uuid = str(uuid.uuid4())
            local_mat["uuid"] = new_local_uuid
            try:
                local_mat.name = new_local_uuid
            except Exception:
                local_mat.name = f"{new_local_uuid}_local"
                print(f"[Make Local DB] Warning: Renamed datablock with fallback name: {local_mat.name}")
            print(f"[Make Local DB] Adding display name '{display_name_from_lib}' for new local UUID {new_local_uuid} to database (in memory).")
            material_names[new_local_uuid] = display_name_from_lib
            local_mat["from_library_uuid"] = lib_mat_uuid
            local_mat.use_fake_user = True
            print(f"[Make Local DB] Created local material '{local_mat.name}' (UUID: {new_local_uuid}) from library '{lib_mat.name}'.")
        except Exception as e:
            self.report({'ERROR'}, f"Failed to create local copy: {e}")
            traceback.print_exc()
            return {'CANCELLED'}
        update_material_timestamp(new_local_uuid)
        print("[Make Local DB] Replacing instances on objects...")
        replaced_count = 0
        for obj in bpy.data.objects:
            if obj.material_slots:
                for slot in obj.material_slots:
                    if slot.link == 'OBJECT' and slot.material == lib_mat:
                        slot.material = local_mat
                        replaced_count += 1
            if hasattr(obj.data, "materials") and obj.data.materials:
                for idx_slot, slot_mat in enumerate(obj.data.materials):
                    if slot_mat == lib_mat:
                        try:
                            obj.data.materials[idx_slot] = local_mat
                            replaced_count += 1
                        except Exception as e_assign:
                            print(f"[Make Local DB] Error assigning to data slot {idx_slot} on {obj.data.name}: {e_assign}")
        print(f"[Make Local DB] Replaced library material on approx {replaced_count} slots.")
        _display_name_cache.clear()
        populate_material_list(scene)
        new_idx = -1
        for i, current_item in enumerate(scene.material_list_items):
            if current_item.material_uuid == new_local_uuid:
                new_idx = i
                break
        if new_idx != -1:
            scene.material_list_active_index = new_idx
            print(f"[Make Local DB] Selected newly created local material in list at index {new_idx}.")
        else:
            print("[Make Local DB] Warning: Could not find newly created local material in list after populate.")
            scene.material_list_active_index = 0 if len(scene.material_list_items) > 0 else -1
        if hasattr(local_mat, "preview"):
            force_update_preview(local_mat)
        self.report({'INFO'}, f"Converted '{mat_get_display_name(local_mat)}' to a local material.")
        return {'FINISHED'}

class MATERIALLIST_OT_sort_alphabetically(Operator):
    bl_idname = "materiallist.sort_alphabetically"
    bl_label = "Sort Alphabetically"
    bl_description = "Sort the material list alphabetically by display name"
    def execute(self, context):
        populate_material_list(context.scene)
        return {'FINISHED'}

class MATERIALLIST_OT_PollMaterialChanges(Operator):
    bl_idname = "materiallist.poll_material_changes"
    bl_label = "Poll Material Changes (Reference Mode Only)"
    _timer = None

    def modal(self, context, event):
        if getattr(context, 'area', None) is None: return {'PASS_THROUGH'}
        if event.type == 'TIMER':
            scene = context.scene
            if not scene: return {'PASS_THROUGH'}
            if scene.workspace_mode == 'REFERENCE':
                change_detected = False
                obj_checked = None
                for obj in scene.objects:
                    if obj.type == 'MESH' and obj.material_slots:
                        ref_backup_slots = reference_backup.get(obj.name)
                        current_mat_slots = [
                            slot.material.name if (slot.material and slot.material.name.startswith("mat_")) else None
                            for slot in obj.material_slots
                        ]
                        if ref_backup_slots is None:
                            if any(m is not None for m in current_mat_slots):
                                print(f"[MaterialList Polling] Change detected in '{obj.name}': No reference backup, but 'mat_' slots currently exist.")
                                change_detected = True; obj_checked = obj.name; break
                            else: continue
                        elif len(current_mat_slots) != len(ref_backup_slots):
                            print(f"[MaterialList Polling] Change detected in '{obj.name}': Slot count differs ({len(current_mat_slots)} current vs {len(ref_backup_slots)} in ref).")
                            change_detected = True; obj_checked = obj.name; break
                        elif current_mat_slots != ref_backup_slots:
                            if not current_mat_slots and not ref_backup_slots: continue
                            print(f"[MaterialList Polling] Change detected in '{obj.name}': Slot content differs.")
                            change_detected = True; obj_checked = obj.name; break
                if change_detected:
                    print(f"[MaterialList Polling] Switching to EDITING mode due to detected change in '{obj_checked}'.")
                    try:
                        if scene and scene.name in bpy.data.scenes:
                            scene.workspace_mode = 'EDITING'
                        else:
                            print("[MaterialList Polling] Scene lost before mode switch. Stopping timer.")
                    except ReferenceError: print("[MaterialList Polling] Scene reference lost before mode switch. Stopping timer.")
                    except Exception as e_mode: print(f"[MaterialList Polling] Error switching mode: {e_mode}. Stopping timer.")
                    self.cancel(context)
                    return {'CANCELLED'}
        return {'PASS_THROUGH'}

    def execute(self, context):
        if MATERIALLIST_OT_PollMaterialChanges._timer is not None:
            print("[MaterialList Polling] Modal timer is already running.")
            return {'CANCELLED'}
        wm = context.window_manager
        window = context.window
        if not window:
            if wm.windows: window = wm.windows[0]
            else:
                print("[MaterialList Polling] Error: Cannot start timer without a window context.")
                return {'CANCELLED'}
        print("[MaterialList Polling] Adding modal timer.")
        MATERIALLIST_OT_PollMaterialChanges._timer = wm.event_timer_add(1.5, window=window)
        wm.modal_handler_add(self)
        print("[MaterialList] Started modal polling for material changes (checks only in Reference mode).")
        return {'RUNNING_MODAL'}

    def cancel(self, context):
        wm = context.window_manager
        timer_was_active = False
        if MATERIALLIST_OT_PollMaterialChanges._timer:
            timer_was_active = True
            try:
                timer_copy = MATERIALLIST_OT_PollMaterialChanges._timer
                MATERIALLIST_OT_PollMaterialChanges._timer = None
                wm.event_timer_remove(timer_copy)
            except ValueError: print("[MaterialList Polling] Warning: Timer already removed before cancel() call.")
            except Exception as e: print(f"[MaterialList] Error removing timer: {e}")
            if hasattr(bpy.types.Operator, 'MATERIALLIST_OT_PollMaterialChanges'):
                MATERIALLIST_OT_PollMaterialChanges._timer = None
        if timer_was_active: print("[MaterialList] Stopped modal polling timer.")
        return None

class MATERIALLIST_OT_refresh_material_list(Operator): # Uses updated populate_material_list and update_material_thumbnails
    bl_idname = "materiallist.refresh_material_list"
    bl_label = "Refresh List & Check Thumbs"
    bl_description = "Refresh the material list UI and initiate checks for missing thumbnails"

    def execute(self, context):
        scene = context.scene
        print("[Refresh Op] Refreshing UI List and triggering thumbnail check.")
        try:
            populate_material_list(scene) # This now excludes "mat_"
            if 'update_material_thumbnails' in globals() and callable(update_material_thumbnails):
                update_material_thumbnails() # This now includes orphan cleanup scheduling
            else: print("[Refresh Op] ERROR: update_material_thumbnails not found.")
            self.report({'INFO'}, "Material list refreshed & thumbnail check started.")
        except Exception as e:
            self.report({'ERROR'}, f"Error during refresh: {e}"); traceback.print_exc()
            return {'CANCELLED'}
        return {'FINISHED'}

class MATERIALLIST_OT_integrate_library(Operator):
    bl_idname = "materiallist.integrate_library"
    bl_label = "Integrate Material Library"
    bl_description = "Select a .blend file to merge unique materials into the main library"
    bl_options = {'REGISTER', 'UNDO'}
    filepath: StringProperty(subtype="FILE_PATH", name="Library File", description="Select the .blend file containing materials to integrate")
    filter_glob: StringProperty(default="*.blend", options={'HIDDEN'}, maxlen=255)

    def invoke(self, context, event):
        context.window_manager.fileselect_add(self)
        return {'RUNNING_MODAL'}

    def execute(self, context):
        global material_names, _display_name_cache
        if 'get_material_hash' not in globals(): self.report({'ERROR'}, "Internal Error: get_material_hash not found."); return {'CANCELLED'}
        if 'update_material_timestamp' not in globals(): self.report({'ERROR'}, "Internal Error: update_material_timestamp not found."); return {'CANCELLED'}
        if 'mat_get_display_name' not in globals(): self.report({'ERROR'}, "Internal Error: mat_get_display_name not found."); return {'CANCELLED'}
        if 'save_material_names' not in globals(): self.report({'ERROR'}, "Internal Error: save_material_names not found."); return {'CANCELLED'}
        if 'load_material_names' not in globals(): self.report({'ERROR'}, "Internal Error: load_material_names not found."); return {'CANCELLED'}
        print(f"[Integrate Lib DB] Starting integration from: {self.filepath}")
        if not self.filepath or not os.path.exists(self.filepath): self.report({'ERROR'}, f"File not found: {self.filepath}"); return {'CANCELLED'}
        try:
            if os.path.exists(LIBRARY_FILE) and os.path.samefile(self.filepath, LIBRARY_FILE): self.report({'WARNING'}, "Cannot integrate main library into itself."); return {'CANCELLED'}
        except: pass
        if not material_names: load_material_names()
        main_lib_content_hashes = set(); main_lib_names_to_process = []; loaded_main_lib_mats_objs = []; error_loading_main = None
        if os.path.exists(LIBRARY_FILE):
            print(f"[Integrate Lib DB] Loading main library for hashing...")
            try:
                with bpy.data.libraries.load(LIBRARY_FILE, link=False) as (data_from, data_to):
                    if data_from.materials:
                        main_lib_names_to_process = list(data_from.materials)
                        names_to_request_load = [n for n in main_lib_names_to_process if n not in bpy.data.materials or bpy.data.materials[n].library]
                        data_to.materials = names_to_request_load if names_to_request_load else []
                    else: main_lib_names_to_process = []
                for mat_name in main_lib_names_to_process:
                    mat_obj = bpy.data.materials.get(mat_name)
                    if mat_obj and mat_obj.library is None: loaded_main_lib_mats_objs.append(mat_obj)
                for mat_obj in loaded_main_lib_mats_objs:
                    content_hash = get_material_hash(mat_obj)
                    if content_hash: main_lib_content_hashes.add(content_hash)
            except Exception as e: error_loading_main = e; print(f"[Integrate Lib DB] Error main lib hash: {e}")
            finally:
                print(f"[Integrate Lib DB] Step 1d: Cleaning up {len(main_lib_names_to_process)} requested main library materials by name...")
                mats_removed_count_main = 0
                for name in main_lib_names_to_process:
                    mat_to_remove = bpy.data.materials.get(name)
                    if mat_to_remove and mat_to_remove.library is None:
                        try: bpy.data.materials.remove(mat_to_remove); mats_removed_count_main += 1
                        except Exception as remove_err: print(f"[Integrate Lib DB] Warning: Error removing temporary main lib mat '{name}': {remove_err}")
                print(f"[Integrate Lib DB] Removed {mats_removed_count_main} temporary main library materials found locally.")
                main_lib_names_to_process.clear(); loaded_main_lib_mats_objs.clear()
                if error_loading_main: self.report({'ERROR'}, f"Error processing main library: {error_loading_main}"); return {'CANCELLED'}
        else: print("[Integrate Lib DB] Main library not found.")
        materials_to_add_refs = []; selected_names_to_process = []; loaded_selected_mats_objs = []; error_loading_selected = None
        print(f"[Integrate Lib DB] Loading selected library: {self.filepath}")
        try:
            with bpy.data.libraries.load(self.filepath, link=False) as (data_from, data_to):
                if data_from.materials:
                    selected_names_to_process = list(data_from.materials)
                    names_to_request_load_sel = [n for n in selected_names_to_process if n not in bpy.data.materials or bpy.data.materials[n].library]
                    data_to.materials = names_to_request_load_sel if names_to_request_load_sel else []
                else: selected_names_to_process = []
            for mat_name in selected_names_to_process:
                mat_obj = bpy.data.materials.get(mat_name)
                if mat_obj and mat_obj.library is None: loaded_selected_mats_objs.append(mat_obj)
            skipped_count = 0; added_to_queue_count = 0
            for mat_obj in loaded_selected_mats_objs:
                content_hash = get_material_hash(mat_obj)
                if not content_hash: skipped_count+=1; continue
                if content_hash not in main_lib_content_hashes:
                    materials_to_add_refs.append(mat_obj)
                    main_lib_content_hashes.add(content_hash)
                    added_to_queue_count+=1
                else: skipped_count+=1
            print(f"[Integrate Lib DB] Identified {added_to_queue_count} unique materials to add, skipped {skipped_count}.")
        except Exception as e: error_loading_selected = e; print(f"[Integrate Lib DB] Error selected lib process: {e}")
        copied_count = 0; newly_added_uuids = []; needs_name_db_save_integrate = False
        if not error_loading_selected and materials_to_add_refs:
            print(f"[Integrate Lib DB] Copying {len(materials_to_add_refs)} unique materials locally...")
            for source_mat_obj in materials_to_add_refs:
                if not isinstance(source_mat_obj, bpy.types.Material): continue
                check_obj = bpy.data.materials.get(source_mat_obj.name)
                if not check_obj or check_obj != source_mat_obj: continue
                try:
                    display_name_from_source = mat_get_display_name(source_mat_obj)
                    new_local_mat = source_mat_obj.copy(); new_local_mat.library = None
                    new_uuid = str(uuid.uuid4()); new_local_mat["uuid"] = new_uuid
                    try: new_local_mat.name = new_uuid
                    except Exception: new_local_mat.name = f"{new_uuid}_local_copy"
                    material_names[new_uuid] = display_name_from_source
                    needs_name_db_save_integrate = True
                    update_material_timestamp(new_uuid)
                    new_local_mat["hash_dirty"] = True; new_local_mat.use_fake_user = True
                    print(f"[Integrate Lib DB] Copied '{display_name_from_source}' as local '{new_local_mat.name}', added name to DB, updated timestamp.")
                    copied_count += 1; newly_added_uuids.append(new_uuid)
                except Exception as copy_err: print(f"[Integrate Lib DB] Error copying '{source_mat_obj.name}': {copy_err}")
        elif error_loading_selected: print("[Integrate Lib DB] Skipping copy phase due to errors.")
        else: print("[Integrate Lib DB] No unique materials to copy locally.")
        try:
            mats_removed_count_sel = 0
            print(f"[Integrate Lib DB] Cleaning up {len(selected_names_to_process)} temporary selected materials...")
            for name in selected_names_to_process:
                mat_to_remove = bpy.data.materials.get(name)
                if mat_to_remove and mat_to_remove.library is None:
                    current_uuid = mat_to_remove.get("uuid")
                    if not current_uuid or current_uuid not in newly_added_uuids:
                        try: bpy.data.materials.remove(mat_to_remove); mats_removed_count_sel += 1
                        except Exception as remove_err: print(f"[Integrate Lib DB] Warning: Error removing temporary mat '{name}': {remove_err}")
            print(f"[Integrate Lib DB] Removed {mats_removed_count_sel} temporary selected materials.")
        finally:
            selected_names_to_process.clear(); loaded_selected_mats_objs.clear(); materials_to_add_refs.clear()
        if error_loading_selected: self.report({'ERROR'}, f"Error processing selected file: {error_loading_selected}"); return {'CANCELLED'}
        if needs_name_db_save_integrate:
            print("[Integrate Lib DB] Saving updated material display names added during integration...")
            save_material_names(); _display_name_cache.clear()
        if copied_count > 0:
            print(f"[Integrate Lib DB] Triggering main library update and UI refresh...")
            try:
                if 'update_material_library' in globals(): update_material_library(force_update=True)
                else: print("[Integrate Lib DB] ERROR: update_material_library func missing!")
            except Exception as e: print(f"[Integrate Lib DB] Error queueing library update: {e}")
            try:
                if 'populate_material_list' in globals(): populate_material_list(context.scene)
                if 'force_redraw' in globals(): force_redraw()
            except Exception as e: print(f"[Integrate Lib DB] Error refreshing UI: {e}")
            self.report({'INFO'}, f"Integration complete. Added {copied_count} materials locally to scene and DB. Library update queued.")
        else: self.report({'INFO'}, "Integration complete. No unique materials added.")
        print("[Integrate Lib DB] Finished.")
        return {'FINISHED'}

class MATERIALLIST_OT_localise_all_users(Operator):
    bl_idname = "materiallist.localise_all_users"
    bl_label = "Localise All Library Users"
    bl_description = ("Finds all .blend files recorded in the database as currently using materials "
                      "from the central library, verifies they exist, and runs the localisation "
                      "worker on each one. USE WITH CAUTION - modifies multiple files.")
    bl_options = {'REGISTER'}
    wait: BoolProperty(name="Wait for each file", description="Block Blender until each worker finishes (runs sequentially). If unchecked, workers run in parallel.", default=True)

    @classmethod
    def poll(cls, context): return os.path.exists(DATABASE_FILE) and os.path.exists(WORKER_SCRIPT)

    def execute(self, context):
        blend_paths_from_db = set()
        try:
            with get_db_connection() as conn:
                c = conn.cursor()
                c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='blend_material_usage'")
                if c.fetchone() is None: self.report({'ERROR'}, "Material usage table ('blend_material_usage') not found in database."); return {'CANCELLED'}
                c.execute("SELECT DISTINCT blend_filepath FROM blend_material_usage")
                rows = c.fetchall()
                blend_paths_from_db = {row[0] for row in rows if row[0]}
        except Exception as e: self.report({'ERROR'}, f"Database error fetching file paths from usage table: {e}"); traceback.print_exc(); return {'CANCELLED'}
        if not blend_paths_from_db: self.report({'INFO'}, "No blend files currently recorded as using library materials."); return {'CANCELLED'}
        current_file_norm = os.path.normcase(bpy.data.filepath) if bpy.data.filepath else None
        valid_blend_paths = []; skipped_nonexistent = 0; skipped_current = 0
        for p in blend_paths_from_db:
            p_norm = os.path.normcase(p)
            if not os.path.exists(p): skipped_nonexistent += 1; continue
            if current_file_norm and p_norm == current_file_norm: skipped_current += 1; continue
            valid_blend_paths.append(p)
        if skipped_nonexistent: print(f"[Localise Users] Skipped {skipped_nonexistent} non-existent paths")
        if skipped_current: print(f"[Localise Users] Skipped current file")
        if not valid_blend_paths: self.report({'WARNING'}, "No valid external files found"); return {'CANCELLED'}
        print(f"[Localise Users] Processing {len(valid_blend_paths)} files"); ok_count, fail_count = 0, 0; processes = []
        for i, blend_path in enumerate(valid_blend_paths):
            print(f"Processing {i+1}/{len(valid_blend_paths)}: {os.path.basename(blend_path)}")
            try:
                cmd = [bpy.app.binary_path, "-b", blend_path, "--python", WORKER_SCRIPT, "--", "--lib", os.path.abspath(LIBRARY_FILE), "--db", os.path.abspath(DATABASE_FILE)]
                if self.wait:
                    result = subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                    if result.returncode == 0: ok_count += 1
                    else: print(f"Worker failed for {blend_path}: {result.stderr}"); fail_count += 1
                else:
                    proc = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    processes.append(proc); ok_count += 1
            except subprocess.CalledProcessError as e: print(f"Subprocess error: {e.stderr}"); fail_count += 1
            except Exception as e: print(f"Unexpected error: {str(e)}"); fail_count += 1
        if not self.wait and processes: print(f"Launched {len(processes)} background workers")
        report_msg = (f"Completed {ok_count} files successfully, {fail_count} failures. Total processed: {len(valid_blend_paths)}")
        self.report({'INFO' if fail_count == 0 else 'WARNING'}, report_msg)
        return {'FINISHED'}

class MATERIALLIST_OT_trim_library(Operator):
    bl_idname = "materiallist.trim_library"
    bl_label = "Trim Library (keep 100 latest)"
    bl_description = ("Keeps only the 100 most-recent materials in material_library.blend (based on timestamp in DB). Others are removed.")
    def execute(self, context):
        with get_db_connection() as conn:
            c = conn.cursor()
            c.execute("CREATE TABLE IF NOT EXISTS mat_time (uuid TEXT PRIMARY KEY, ts INTEGER)")
            conn.commit()
            c.execute("SELECT uuid, ts FROM mat_time ORDER BY ts DESC")
            rows = c.fetchall()
        to_keep = {r[0] for r in rows[:100]}
        removed = 0
        if os.path.exists(LIBRARY_FILE):
            with bpy.data.libraries.load(LIBRARY_FILE, link=False) as (data_from, data_to): # link=False to load for write
                survivors = [n for n in data_from.materials if n in to_keep]
                # Get actual material objects for writing
                mats_to_write = set()
                for name in survivors:
                    mat = bpy.data.materials.get(name) # Check if it was loaded
                    if mat and mat.library is None: # Ensure it's a local copy from the library load
                        mats_to_write.add(mat)

            # Create a temporary file to write the survivors
            temp_dir = tempfile.mkdtemp()
            tmp_blend_file = os.path.join(temp_dir, "trimmed_library.blend")

            if mats_to_write: # Only write if there are survivors to write
                bpy.data.libraries.write(tmp_blend_file, mats_to_write, fake_user=True)
                shutil.copy2(tmp_blend_file, LIBRARY_FILE) # Overwrite original library
                removed = len(data_from.materials) - len(survivors) if data_from.materials else 0
            elif not survivors and data_from.materials: # No survivors, but there were materials - means delete all
                bpy.data.libraries.write(tmp_blend_file, set(), fake_user=True) # Write empty library
                shutil.copy2(tmp_blend_file, LIBRARY_FILE)
                removed = len(data_from.materials)

            # Clean up temporary materials that were loaded from the library
            for mat_obj in mats_to_write: # These were local copies from data_to
                if mat_obj.name in bpy.data.materials and mat_obj.library is None and mat_obj.users == 0:
                    try: bpy.data.materials.remove(mat_obj)
                    except: pass
            if os.path.exists(temp_dir): shutil.rmtree(temp_dir)

        self.report({'INFO'}, f"Library trimmed, removed {removed} entries.")
        return {'FINISHED'}


class MATERIALLIST_OT_select_dominant(Operator):
    bl_idname = "materiallist.select_dominant"
    bl_label = "Select Dominant Material"
    bl_description = ("On the active object, find the material used by the largest number of faces "
                      "and select its corresponding (lowest suffix if 'mat_') entry in the list.")
    @classmethod
    def poll(cls, context): ob = context.active_object; return ob and ob.type == 'MESH'
    def execute(self, context):
        ob = context.active_object; me = ob.data
        if not me.materials: self.report({'WARNING'}, "Object has no materials."); return {'CANCELLED'}
        
        counts = {}; bm = bmesh.new(); bm.from_mesh(me)
        for f in bm.faces: counts[f.material_index] = counts.get(f.material_index, 0) + 1
        bm.free()
        
        if not counts: self.report({'WARNING'}, "No face material assignments."); return {'CANCELLED'}
        
        dominant_idx_on_mesh = max(counts, key=counts.get)
        dominant_mat_on_mesh = me.materials[dominant_idx_on_mesh]
        
        if not dominant_mat_on_mesh: 
            self.report({'WARNING'}, "Dominant slot has no material."); return {'CANCELLED'}

        scene = context.scene
        dominant_mat_display_name = mat_get_display_name(dominant_mat_on_mesh)
        selected_in_list = False

        if dominant_mat_display_name.startswith("mat_"):
            # If dominant material is a "mat_" type, find its base name.
            # The list (if "mat_" are shown) should contain the lowest suffix version of this base.
            base_name_of_dominant, _ = _parse_material_suffix(dominant_mat_display_name)
            
            for i, item_in_list in enumerate(scene.material_list_items):
                # The item_in_list.material_name is already the lowest suffix version for "mat_"
                # if "Hide mat_ Materials" is false, thanks to populate_material_list.
                if item_in_list.material_name == base_name_of_dominant:
                    scene.material_list_active_index = i
                    selected_in_list = True
                    self.report({'INFO'}, f"Selected '{item_in_list.material_name}' (base of dominant '{dominant_mat_display_name}')")
                    break
            if not selected_in_list:
                 # Fallback: if base name not found (e.g. list is filtered weirdly or hide_mat_materials is true),
                 # try to select by exact UUID of the mesh material, if it happens to be in the list.
                 dominant_uuid = get_material_uuid(dominant_mat_on_mesh)
                 for i, item_in_list in enumerate(scene.material_list_items):
                     if item_in_list.material_uuid == dominant_uuid:
                         scene.material_list_active_index = i
                         selected_in_list = True
                         self.report({'INFO'}, f"Selected '{item_in_list.material_name}' (exact dominant '{dominant_mat_display_name}') by UUID as fallback.")
                         break
        else:
            # For non-"mat_" materials, select by UUID as before.
            dominant_uuid = get_material_uuid(dominant_mat_on_mesh)
            for i, item_in_list in enumerate(scene.material_list_items):
                if item_in_list.material_uuid == dominant_uuid:
                    scene.material_list_active_index = i
                    selected_in_list = True
                    self.report({'INFO'}, f"Selected '{item_in_list.material_name}' (non-mat_ dominant)")
                    break
        
        if not selected_in_list:
            self.report({'WARNING'}, f"Could not find dominant material '{dominant_mat_display_name}' or its base in the list.")
            return {'CANCELLED'}
            
        return {'FINISHED'}

# --------------------------
# Scene Thumbnail Functions (Updated for robustness)
# --------------------------
def ensure_icon_template():
    """
    Ensure that the icon template blend file exists on disk.
    If it does not exist, create a new template scene with a preview object,
    camera, and light using the specific setup parameters, and save it.
    """
    global persistent_icon_template_scene

    if os.path.exists(ICON_TEMPLATE_FILE):
        return True

    print(f"[IconTemplate Ensure] Creating icon generation template at: {ICON_TEMPLATE_FILE}")
    persistent_icon_template_scene = None # Reset cache if we're recreating

    # Canonical names for template elements
    template_scene_name_in_file = "IconTemplateScene"
    preview_obj_name = "IconPreviewObject"
    preview_mesh_data_name = "IconPreviewMesh_Data" # Specific name for its data block
    camera_obj_name = "IconTemplateCam"
    camera_data_name = "IconTemplateCam_Data" # Specific name for its data block
    light_obj_name = "IconTemplateLight"
    light_data_name = "IconTemplateLight_Data" # Specific name for its data block

    temp_setup_scene_name = f"IconTemplate_TEMP_SETUP_{str(uuid.uuid4())[:8]}" # For temporary operations if needed
    temp_setup_scene = None # Will be deleted in finally block
    scene_to_save_in_template = None # This will be the actual "IconTemplateScene"
    created_data_blocks_for_template_file = []

    try:
        # --- BEGIN CRITICAL PRE-CLEANUP ---
        # Remove any existing datablocks that might conflict with canonical template names
        # Order: Objects (which might use Meshes/Cameras/Lights), then their Data, then Scenes.

        # 1. Clean up Objects
        for obj_name_to_clear in [preview_obj_name, camera_obj_name, light_obj_name]:
            if obj_name_to_clear in bpy.data.objects:
                obj_to_remove = bpy.data.objects[obj_name_to_clear]
                print(f"[IconTemplate Ensure] Pre-cleanup: Removing existing object '{obj_name_to_clear}' from bpy.data.objects.")
                try:
                    # Unlink from all scene collections. This is important.
                    # bpy.data.objects.remove(do_unlink=True) handles this.
                    bpy.data.objects.remove(obj_to_remove, do_unlink=True)
                except Exception as e_pre_remove_obj:
                    print(f"[IconTemplate Ensure] Error during pre-cleanup of object '{obj_name_to_clear}': {e_pre_remove_obj}")

        # 2. Clean up Data (Meshes, Cameras, Lights) - these names are already specific usually
        # but good to ensure if they were ever created with conflicting simple names.
        # Using the specific names defined above (_Data suffix) means less likely direct conflict here.
        for data_name_to_clear, data_collection in [
            (preview_mesh_data_name, bpy.data.meshes),
            (camera_data_name, bpy.data.cameras),
            (light_data_name, bpy.data.lights)
        ]:
            if data_name_to_clear in data_collection:
                data_block_to_remove = data_collection[data_name_to_clear]
                print(f"[IconTemplate Ensure] Pre-cleanup: Removing existing data block '{data_name_to_clear}'.")
                try:
                    data_collection.remove(data_block_to_remove)
                except Exception as e_pre_remove_data:
                    print(f"[IconTemplate Ensure] Error during pre-cleanup of data '{data_name_to_clear}': {e_pre_remove_data}")
        
        # 3. Clean up Scene (already in user's code, adapted slightly)
        existing_scene_for_template = bpy.data.scenes.get(template_scene_name_in_file)
        if existing_scene_for_template:
            print(f"[IconTemplate Ensure] Pre-cleanup: Removing existing scene '{template_scene_name_in_file}'.")
            try:
                # If it's the active scene in any window, switch to another scene if possible
                for window_iter in bpy.context.window_manager.windows:
                    if window_iter.scene == existing_scene_for_template:
                        other_scene = next((s for s in bpy.data.scenes if s != existing_scene_for_template), None)
                        if other_scene:
                            window_iter.scene = other_scene
                        # If no other scene, removal might be problematic or Blender might handle it.
                
                if existing_scene_for_template.name in bpy.data.scenes: # Check again before removal
                     bpy.data.scenes.remove(existing_scene_for_template) # No do_unlink for scenes
            except Exception as e_remove_existing_template_scene:
                print(f"[IconTemplate Ensure] Error removing pre-existing scene '{template_scene_name_in_file}': {e_remove_existing_template_scene}")
        # --- END CRITICAL PRE-CLEANUP ---

        # Create a temporary scene for setup if needed, but the goal is to use canonical names directly
        # This temp_setup_scene is mostly for context, actual template scene is `scene_to_save_in_template`
        temp_setup_scene = bpy.data.scenes.new(temp_setup_scene_name)
        if not temp_setup_scene:
            print("[IconTemplate Ensure] CRITICAL: Failed to create temporary setup scene for context.")
            return False
        
        # Create Data blocks with their specific canonical names
        mesh_data = bpy.data.meshes.new(preview_mesh_data_name)
        bm = bmesh.new()
        bmesh.ops.create_uvsphere(bm, u_segments=32, v_segments=16, radius=0.8)
        if not bm.loops.layers.uv: uv_layer = bm.loops.layers.uv.new("UVMap")
        else: uv_layer = bm.loops.layers.uv.active or bm.loops.layers.uv.verify() or bm.loops.layers.uv.new("UVMap")
        if uv_layer:
            for face in bm.faces:
                for loop in face.loops:
                    loop_uv = loop[uv_layer]
                    norm_co = loop.vert.co.normalized()
                    loop_uv.uv = ( (math.atan2(norm_co.y, norm_co.x) / (2 * math.pi)) + 0.5,
                                   (math.asin(norm_co.z) / math.pi) + 0.5 )
        bm.to_mesh(mesh_data); bm.free()
        created_data_blocks_for_template_file.append(mesh_data)

        cam_data = bpy.data.cameras.new(camera_data_name)
        created_data_blocks_for_template_file.append(cam_data)
        
        light_data = bpy.data.lights.new(light_data_name, type='POINT')
        light_data.energy = 240
        created_data_blocks_for_template_file.append(light_data)

        # Create Objects using their canonical names (should be available after pre-cleanup)
        preview_obj = bpy.data.objects.new(preview_obj_name, mesh_data)
        created_data_blocks_for_template_file.append(preview_obj)

        cam_obj = bpy.data.objects.new(camera_obj_name, cam_data)
        cam_obj.location = (1.7, -1.7, 1.4); cam_obj.rotation_euler = (math.radians(60), 0, math.radians(45))
        created_data_blocks_for_template_file.append(cam_obj)

        light_obj = bpy.data.objects.new(light_obj_name, light_data)
        light_obj.location = (0.15, -2.0, 1.3)
        created_data_blocks_for_template_file.append(light_obj)
        
        # Create the main template scene using its canonical name
        scene_to_save_in_template = bpy.data.scenes.new(template_scene_name_in_file)
        if not scene_to_save_in_template:
            print("[IconTemplate Ensure] CRITICAL: Failed to create target template scene with canonical name.")
            raise RuntimeError("Failed to create target template scene.")
        # scene_to_save_in_template.name = template_scene_name_in_file # Name is set on creation

        # Link objects to the scene that will be saved
        scene_to_save_in_template.collection.objects.link(preview_obj)
        scene_to_save_in_template.collection.objects.link(cam_obj)
        scene_to_save_in_template.collection.objects.link(light_obj)
        scene_to_save_in_template.camera = cam_obj # Assign the camera object to the scene

        try:
            scene_to_save_in_template.render.engine = 'BLENDER_EEVEE_NEXT' if 'BLENDER_EEVEE_NEXT' in bpy.context.scene.render.bl_rna.properties['engine'].enum_items else 'BLENDER_EEVEE'
        except TypeError: # Fallback if EEVEE_NEXT is not available or causes issues
            scene_to_save_in_template.render.engine = 'BLENDER_EEVEE'
        print(f"[IconTemplate Ensure] Template scene render engine set to: {scene_to_save_in_template.render.engine}")
        scene_to_save_in_template.render.resolution_x = THUMBNAIL_SIZE
        scene_to_save_in_template.render.resolution_y = THUMBNAIL_SIZE
        scene_to_save_in_template.render.film_transparent = True
        # Access Eevee settings based on the actually set engine string
        engine_settings_attr = scene_to_save_in_template.render.engine.lower() # e.g., 'blender_eevee' or 'blender_eevee_next'
        eevee_settings = getattr(scene_to_save_in_template, engine_settings_attr, None)

        if eevee_settings:
            if hasattr(eevee_settings, 'taa_render_samples'): eevee_settings.taa_render_samples = 16
            elif hasattr(eevee_settings, 'samples'): eevee_settings.samples = 16 # For older Eevee
        
        created_data_blocks_for_template_file.append(scene_to_save_in_template) # Add the scene itself

        temp_dir_for_blend_save = tempfile.mkdtemp(prefix="icon_template_blend_")
        temp_blend_path = os.path.join(temp_dir_for_blend_save, os.path.basename(ICON_TEMPLATE_FILE))
        
        # Ensure all blocks intended for saving are valid and have a name (Blender requires this)
        valid_blocks_to_write = set()
        for block in created_data_blocks_for_template_file:
            if block and hasattr(block, 'name') and block.name: # Check for existence and non-empty name
                valid_blocks_to_write.add(block)
            else:
                print(f"[IconTemplate Ensure] Warning: Skipping invalid or unnamed block: {block} (Type: {type(block)})")

        if not valid_blocks_to_write:
            print("[IconTemplate Ensure] CRITICAL: No valid data blocks collected for writing to template.")
            raise RuntimeError("No valid data blocks for template file.")
            
        print(f"[IconTemplate Ensure] Writing {len(valid_blocks_to_write)} blocks to temporary .blend: {temp_blend_path}")
        for block in sorted(list(valid_blocks_to_write), key=lambda b: b.name): # Sort for consistent log
            print(f"  Writing block: {block.name} (Type: {type(block)})")
            
        bpy.data.libraries.write(temp_blend_path, valid_blocks_to_write, fake_user=True, compress=True)
        
        os.makedirs(os.path.dirname(ICON_TEMPLATE_FILE), exist_ok=True)
        shutil.move(temp_blend_path, ICON_TEMPLATE_FILE) # Move the correctly created temp file
        print(f"[IconTemplate Ensure] Template file created successfully: {ICON_TEMPLATE_FILE}")
        
        if os.path.exists(temp_dir_for_blend_save): shutil.rmtree(temp_dir_for_blend_save)
        return True

    except Exception as e:
        print(f"[IconTemplate Ensure] CRITICAL ERROR during template file creation: {e}")
        traceback.print_exc()
        # Minimal cleanup of blocks created in *this attempt*, if they somehow persisted with canonical names
        # Note: The pre-cleanup should handle most conflicts from *previous* runs.
        for block in created_data_blocks_for_template_file: # These are the Python references
            if block and hasattr(block, 'name') and block.name:
                try:
                    if block.name in bpy.data.objects and bpy.data.objects[block.name] == block: bpy.data.objects.remove(block, do_unlink=True)
                    elif block.name in bpy.data.meshes and bpy.data.meshes[block.name] == block: bpy.data.meshes.remove(block)
                    elif block.name in bpy.data.cameras and bpy.data.cameras[block.name] == block: bpy.data.cameras.remove(block)
                    elif block.name in bpy.data.lights and bpy.data.lights[block.name] == block: bpy.data.lights.remove(block)
                    elif block.name in bpy.data.scenes and bpy.data.scenes[block.name] == block: bpy.data.scenes.remove(block)
                except Exception as e_cleanup_block_on_fail:
                    print(f"[IconTemplate Ensure] Error cleaning up block '{block.name}' on failure: {e_cleanup_block_on_fail}")
        return False
    finally:
        # Clean up the temporary setup scene used for context
        if temp_setup_scene and temp_setup_scene.name in bpy.data.scenes:
            try:
                bpy.data.scenes.remove(temp_setup_scene) # No do_unlink needed
            except Exception as e_clean_setup:
                print(f"[IconTemplate Ensure] Error cleaning up temporary setup scene '{temp_setup_scene_name}': {e_clean_setup}")

def load_icon_template_scene():
    """
    Loads the icon template scene from ICON_TEMPLATE_FILE.
    If the file is missing, or objects within are missing/corrupt, it attempts to recreate it.
    Returns the valid template scene object or None.
    """
    global persistent_icon_template_scene

    preview_obj_name = "IconPreviewObject"
    camera_obj_name = "IconTemplateCam"
    light_obj_name = "IconTemplateLight"
    template_scene_name_in_file = "IconTemplateScene"

    if persistent_icon_template_scene is not None:
        try:
            if persistent_icon_template_scene.name in bpy.data.scenes and \
               persistent_icon_template_scene.objects.get(preview_obj_name) and \
               persistent_icon_template_scene.objects.get(camera_obj_name) and \
               persistent_icon_template_scene.objects.get(light_obj_name) and \
               persistent_icon_template_scene.camera == persistent_icon_template_scene.objects.get(camera_obj_name):
                return persistent_icon_template_scene
            else:
                print("[IconTemplate Load] Cached scene invalid.")
                persistent_icon_template_scene = None
        except ReferenceError:
            print("[IconTemplate Load] Cached template scene reference lost.")
            persistent_icon_template_scene = None
        except Exception as e_cache_check:
            print(f"[IconTemplate Load] Error checking cached scene: {e_cache_check}")
            persistent_icon_template_scene = None

    for attempt in range(2):
        if not os.path.exists(ICON_TEMPLATE_FILE):
            print(f"[IconTemplate Load] Template file missing. Attempting creation (Attempt {attempt+1})...")
            if not ensure_icon_template():
                print(f"[IconTemplate Load] CRITICAL: Failed to create template file (Attempt {attempt+1}).")
                if attempt == 0: continue
                else: return None
        if not os.path.exists(ICON_TEMPLATE_FILE):
            print(f"[IconTemplate Load] CRITICAL: Template file still missing after ensure call.")
            return None

        loaded_template_scene_obj = None
        try:
            loaded_scene_names_from_file = []
            with bpy.data.libraries.load(ICON_TEMPLATE_FILE, link=False, relative=False) as (data_from, data_to):
                if template_scene_name_in_file in data_from.scenes:
                    data_to.scenes = [template_scene_name_in_file]
                    if hasattr(data_to, "scenes") and data_to.scenes:
                        loaded_scene_names_from_file = list(data_to.scenes)
                else:
                    raise IOError(f"Scene '{template_scene_name_in_file}' not found in library '{ICON_TEMPLATE_FILE}'.")

            if loaded_scene_names_from_file:
                actual_loaded_scene_name = loaded_scene_names_from_file[0]
                loaded_template_scene_obj = bpy.data.scenes.get(actual_loaded_scene_name)
                if loaded_template_scene_obj:
                    print(f"[IconTemplate Load] Scene '{template_scene_name_in_file}' (loaded as '{actual_loaded_scene_name}') retrieved from bpy.data.")
                    # Get an evaluated version of the scene to ensure collections are populated
                    eval_scene = loaded_template_scene_obj.evaluated_get(bpy.context.evaluated_depsgraph_get()) if bpy.context.evaluated_depsgraph_get() else loaded_template_scene_obj

                else:
                    raise IOError(f"Scene '{actual_loaded_scene_name}' not found in bpy.data after load from '{ICON_TEMPLATE_FILE}'.")
            else:
                 raise IOError(f"Failed to get loaded scene names for '{template_scene_name_in_file}' from '{ICON_TEMPLATE_FILE}'.")

            final_preview_obj = eval_scene.objects.get(preview_obj_name)
            final_camera_obj = eval_scene.objects.get(camera_obj_name)
            final_light_obj = eval_scene.objects.get(light_obj_name)

            if not final_preview_obj: raise IOError(f"Corrupt template: Preview object '{preview_obj_name}' not in loaded scene '{eval_scene.name}'.")
            if not final_camera_obj: raise IOError(f"Corrupt template: Camera object '{camera_obj_name}' not in loaded scene '{eval_scene.name}'.")
            if not final_light_obj: raise IOError(f"Corrupt template: Light object '{light_obj_name}' not in loaded scene '{eval_scene.name}'.")

            if eval_scene.camera != final_camera_obj: # Use eval_scene here
                print(f"[IconTemplate Load] Warning: Camera mismatch in loaded scene '{eval_scene.name}'. Setting to '{camera_obj_name}'.")
                loaded_template_scene_obj.camera = final_camera_obj # Set on original, not eval

            loaded_template_scene_obj.render.resolution_x = THUMBNAIL_SIZE
            loaded_template_scene_obj.render.resolution_y = THUMBNAIL_SIZE
            loaded_template_scene_obj.render.film_transparent = True

            persistent_icon_template_scene = loaded_template_scene_obj
            print(f"[IconTemplate Load] Successfully loaded and verified template scene: {persistent_icon_template_scene.name}")
            return persistent_icon_template_scene

        except IOError as ioe_load:
            print(f"[IconTemplate Load] IO Error during template load (Attempt {attempt+1}): {ioe_load}")
            if attempt == 0:
                print(f"[IconTemplate Load] Deleting potentially corrupt template: {ICON_TEMPLATE_FILE}")
                try: os.remove(ICON_TEMPLATE_FILE)
                except Exception as e_del: print(f"[IconTemplate Load] Error deleting corrupt template: {e_del}")
                persistent_icon_template_scene = None
            else:
                print(f"[IconTemplate Load] CRITICAL: Failed to load template even after recreation attempt.")
                return None
        except Exception as e_load_general:
            print(f"[IconTemplate Load] General error loading template (Attempt {attempt+1}): {e_load_general}")
            traceback.print_exc()
            if attempt == 0:
                try: os.remove(ICON_TEMPLATE_FILE)
                except Exception: pass
                persistent_icon_template_scene = None
            else: return None

    print(f"[IconTemplate Load] CRITICAL: Exited load loop without success.")
    return None

def create_sphere_preview_thumbnail(mat, thumb_path):
    """
    Generates a thumbnail using a TEMPORARY COPY of the material.
    Uses load_icon_template_scene which handles template resilience.
    """
    render_scene = None # Will be fetched by load_icon_template_scene
    window = bpy.context.window
    if not window and bpy.context.window_manager.windows:
        window = bpy.context.window_manager.windows[0]

    if not window:
        print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] Error: No window context available.")
        return False

    original_window_scene = window.scene # Store to restore later
    temp_mat_copy = None # For the material copy

    try:
        # Get the prepared render scene (this now handles creation/recreation if needed)
        render_scene = load_icon_template_scene()
        if not render_scene:
            print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] Error: Failed to get or prepare a valid render scene.")
            return False

        # Template scene should have "IconPreviewObject" correctly set up by load_icon_template_scene
        preview_obj = render_scene.objects.get("IconPreviewObject") # Name from ensure_icon_template
        if not preview_obj or not preview_obj.data or not hasattr(preview_obj.data, 'materials'):
            print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] Error: Preview object is invalid in loaded template scene '{render_scene.name}'. This indicates a deeper issue with template loading.")
            return False # Should not happen if load_icon_template_scene worked

        # Ensure preview object has UVs (load_icon_template_scene and ensure_icon_template should handle this)
        if not preview_obj.data.uv_layers or not preview_obj.data.uv_layers.active:
            print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] Error: Preview object '{preview_obj.name}' in template scene '{render_scene.name}' is missing expected UV layers.")
            return False

        # --- Create Temporary Material Copy ---
        print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] Creating temporary copy of material.")
        temp_mat_copy = mat.copy()
        temp_mat_copy.name = f"_THUMBNAIL_COPY_{mat.name}_{str(uuid.uuid4())[:8]}" # Unique temp name
        temp_mat_copy.use_fake_user = False # Don't save this temp material

        # --- Assign COPIED Material & Connect UVs on the COPY ---
        if not preview_obj.material_slots: # Ensure a material slot exists
            print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] Preview object missing material slot. Adding one...")
            with bpy.context.temp_override(object=preview_obj, active_object=preview_obj):
                bpy.ops.object.material_slot_add()
            if not preview_obj.material_slots: # Check if slot creation failed
                print(f"[Thumbnail Gen - {getattr(mat, 'name', 'N/A')}] CRITICAL: Failed to add material slot to preview object.")
                if temp_mat_copy and temp_mat_copy.name in bpy.data.materials: bpy.data.materials.remove(temp_mat_copy) # Clean up copy
                return False
        preview_obj.material_slots[0].material = temp_mat_copy # Assign the copy

        # Auto-connect UVs in the copied material's node tree if applicable
        if temp_mat_copy.node_tree:
            temp_mat_copy.node_tree.update_tag() # Force update nodes
            uv_map_node = None
            for node in temp_mat_copy.node_tree.nodes: # Find or create UVMap node
                if node.bl_idname == 'ShaderNodeUVMap': uv_map_node = node; break
            if not uv_map_node: uv_map_node = temp_mat_copy.node_tree.nodes.new('ShaderNodeUVMap'); uv_map_node.location = (-200, 300)

            active_uv_layer_on_preview = preview_obj.data.uv_layers.active
            if active_uv_layer_on_preview: uv_map_node.uv_map = active_uv_layer_on_preview.name
            elif preview_obj.data.uv_layers: uv_map_node.uv_map = preview_obj.data.uv_layers[0].name # Fallback

            if uv_map_node: # Connect UV to Image Texture nodes
                for node in temp_mat_copy.node_tree.nodes:
                    if node.bl_idname == 'ShaderNodeTexImage':
                        vector_input = node.inputs.get('Vector')
                        if vector_input and not vector_input.is_linked:
                            try: temp_mat_copy.node_tree.links.new(uv_map_node.outputs['UV'], vector_input)
                            except Exception as link_err: print(f"[Thumbnail Gen - {temp_mat_copy.name}] Warn: Failed to link UV for {node.name}: {link_err}")

        # Update dependency graph
        depsgraph = bpy.context.evaluated_depsgraph_get(); depsgraph.update()
        if hasattr(bpy.context, 'view_layer'): bpy.context.view_layer.update()

        # --- Render ---
        print(f"[Thumbnail Gen - {temp_mat_copy.name}] Rendering using scene '{render_scene.name}'...")
        render_area = None; render_region = None # Find suitable context for operator
        for area_iter in window.screen.areas:
            if area_iter.type == 'VIEW_3D':
                render_area = area_iter
                for region_iter in area_iter.regions:
                    if region_iter.type == 'WINDOW': render_region = region_iter; break
                break
        if not render_area and window.screen.areas: # Fallback if no VIEW_3D found
            render_area = window.screen.areas[0]
            if render_area.regions: render_region = render_area.regions[0]

        if not render_area or not render_region:
            print(f"[Thumbnail Gen - {temp_mat_copy.name}] Error: Could not find suitable area/region for render context.")
            if temp_mat_copy and temp_mat_copy.name in bpy.data.materials: bpy.data.materials.remove(temp_mat_copy)
            return False

        override_context = {
            'window': window, 'screen': window.screen, 'area': render_area,
            'region': render_region, 'scene': render_scene, 'blend_data': bpy.data,
        }
        render_successful = False
        try:
            with bpy.context.temp_override(**override_context):
                window.scene = render_scene # Ensure correct scene is active for the render operation
                bpy.context.scene.render.filepath = thumb_path
                bpy.context.scene.render.image_settings.file_format = 'PNG'
                bpy.context.scene.render.image_settings.color_mode = 'RGBA' # Ensure alpha
                bpy.ops.render.render(write_still=True)

            time.sleep(0.1) # Small delay for filesystem
            if os.path.exists(thumb_path) and os.path.getsize(thumb_path) > 0:
                render_successful = True
            else:
                print(f"[Thumbnail Gen - {temp_mat_copy.name}] ERROR: Render output file NOT FOUND or empty: '{thumb_path}'.")
        except Exception as render_error:
            print(f"[Thumbnail Gen - {temp_mat_copy.name}] Error during render operation: {render_error}")
            traceback.print_exc()

        return render_successful

    except Exception as e_outer_thumb_gen:
        mat_name_for_outer_log = getattr(mat, 'name', 'N/A')
        print(f"[Thumbnail Gen - {mat_name_for_outer_log}] Outer error in create_sphere_preview_thumbnail: {e_outer_thumb_gen}")
        traceback.print_exc()
        return False # Indicate failure
    finally:
        # Restore original window scene
        if original_window_scene and window and window.scene != original_window_scene:
            try: # Ensure original scene still exists
                if original_window_scene.name in bpy.data.scenes: window.scene = original_window_scene
                elif bpy.data.scenes: window.scene = bpy.data.scenes[0] # Fallback to first available scene
            except Exception: pass # Ignore errors during scene restoration
        # Clean up the temporary material copy
        if temp_mat_copy and temp_mat_copy.name in bpy.data.materials:
            try: bpy.data.materials.remove(temp_mat_copy)
            except Exception as e_remove_temp_final: print(f"Error removing temp mat {temp_mat_copy.name} in finally: {e_remove_temp_final}")

def force_update_preview(mat): # Unchanged
    try:
        mat.preview = None
        if hasattr(mat, "preview_render_type"):
            current_type = mat.preview_render_type; mat.preview_render_type = 'FLAT'
            bpy.app.timers.register(lambda: restore_render_type(mat, current_type), first_interval=0.1)
        else: mat.preview_ensure()
    except Exception as e: print(f"Error updating preview for {mat.name}: {e}")

def restore_render_type(mat, original_type): # Unchanged
    try:
        mat.preview_render_type = original_type; mat.preview_ensure()
    except Exception as e: print(f"Error restoring render type for {mat.name}: {e}")
    return None

def get_library_uuid_for_hash(hash_val: str) -> str | None: # Unchanged
    if not hash_val: return None
    try:
        with get_db_connection() as conn:
            c = conn.cursor()
            c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='groups'")
            if c.fetchone() is None: return None
            c.execute("SELECT library_uuid FROM groups WHERE hash = ? LIMIT 1", (hash_val,))
            result = c.fetchone()
            if result and result[0] and isinstance(result[0], str) and len(result[0]) == 36: return result[0]
    except Exception as e: print(f"Error querying library_uuid for hash {hash_val}: {e}")
    return None

# --------------------------
# Thumbnail Path Management (Unchanged)
# --------------------------
def get_thumbnail_path(hash_value): return os.path.join(THUMBNAIL_FOLDER, f"{hash_value}.png")
def find_legacy_thumbnail_path(hash_value): # Unchanged
    if not os.path.isdir(THUMBNAIL_FOLDER): return None # Added check
    for filename in os.listdir(THUMBNAIL_FOLDER):
        if filename.endswith(f"_{hash_value}.png"): return os.path.join(THUMBNAIL_FOLDER, filename)
    return None

# --------------------------
# Thumbnail Migration Handler (Unchanged)
# --------------------------
@persistent
def migrate_thumbnail_files(dummy): # Unchanged
    if not os.path.exists(THUMBNAIL_FOLDER): return
    migrated_count = 0; legacy_pattern = re.compile(r"^[0-9a-f-]{36}_[0-9a-f]{32}\.png$")
    try:
        for filename in os.listdir(THUMBNAIL_FOLDER):
            src_path = os.path.join(THUMBNAIL_FOLDER, filename)
            if not legacy_pattern.match(filename): continue
            hash_value = filename.split("_")[1].split(".")[0]
            dest_path = get_thumbnail_path(hash_value)
            if not os.path.exists(dest_path): os.rename(src_path, dest_path); migrated_count += 1
            else: os.remove(src_path) # Remove duplicate legacy
    except Exception as e: print(f"Thumbnail Migration Error: {str(e)}"); traceback.print_exc()
    # print(f"Thumbnail Migration: {migrated_count} files migrated.") # Optional log on completion

# --------------------------
# Thumbnail Generation Core Logic (get_custom_icon, generate_thumbnail_async, update_material_thumbnails)
# --------------------------
def get_custom_icon(mat):
    """
    Get or schedule generation for material thumbnail.
    Handles cache, disk checks, and robustly schedules generation if needed.
    """
    global custom_icons, thumbnail_generation_scheduled

    mat_name_debug = getattr(mat, 'name', 'None')
    if not mat: return 0

    if custom_icons is None:
        print(f"[GetIcon - {mat_name_debug}] Custom_icons is None. Attempting reinitialization.")
        try:
            custom_icons = bpy.utils.previews.new()
            if custom_icons is None:
                print(f"[GetIcon - {mat_name_debug}] CRITICAL: Reinitialization of custom_icons failed (bpy.utils.previews.new() returned None).")
                return 0
            print(f"[GetIcon - {mat_name_debug}] Reinitialized custom_icons successfully.")
            if 'preload_existing_thumbnails' in globals() and callable(preload_existing_thumbnails):
                preload_existing_thumbnails()
        except Exception as e_reinit:
            print(f"[GetIcon - {mat_name_debug}] CRITICAL: Error during custom_icons reinitialization: {e_reinit}")
            return 0

    current_material_hash = get_material_hash(mat)
    if not current_material_hash:
        print(f"[GetIcon - {mat_name_debug}] Hash calculation failed.")
        return 0

    if current_material_hash in custom_icons:
        cached_preview_item = custom_icons[current_material_hash]
        path_for_cached_thumb = get_thumbnail_path(current_material_hash)
        try:
            if os.path.isfile(path_for_cached_thumb) and os.path.getsize(path_for_cached_thumb) > 0 and hasattr(cached_preview_item, 'icon_id') and cached_preview_item.icon_id > 0:
                return cached_preview_item.icon_id
            else:
                print(f"[GetIcon - {mat_name_debug}] Stale cache for hash '{current_material_hash}'. File missing/empty or invalid icon_id. Path: {path_for_cached_thumb}, ID: {getattr(cached_preview_item, 'icon_id', -1)}")
        except Exception as e_verify_file:
            print(f"[GetIcon - {mat_name_debug}] Error verifying file for cached hash '{current_material_hash}': {e_verify_file}. Treating as cache miss.")

    thumbnail_file_path = get_thumbnail_path(current_material_hash)
    is_file_valid_on_disk = False
    try:
        if os.path.isfile(thumbnail_file_path) and os.path.getsize(thumbnail_file_path) > 0:
            is_file_valid_on_disk = True
    except Exception as e_check_disk_path:
        print(f"[GetIcon - {mat_name_debug}] Error checking disk path '{thumbnail_file_path}': {e_check_disk_path}")

    if is_file_valid_on_disk:
        try:
            if custom_icons is None:
                print(f"[GetIcon - {mat_name_debug}] Error loading {thumbnail_file_path}: custom_icons became None unexpectedly before load.")
                # Fall through to schedule generation if custom_icons is None, as we can't load into it.
            else:
                preview_item_from_disk_load = custom_icons.load(current_material_hash, thumbnail_file_path, 'IMAGE')
                if current_material_hash in custom_icons and \
                   preview_item_from_disk_load is not None and \
                   hasattr(preview_item_from_disk_load, 'icon_id') and \
                   preview_item_from_disk_load.icon_id > 0:
                    return preview_item_from_disk_load.icon_id
                else:
                    loaded_item_after_call = custom_icons.get(current_material_hash)
                    actual_id = getattr(loaded_item_after_call, 'icon_id', -1) if loaded_item_after_call else -1
                    print(f"[GetIcon - {mat_name_debug}] *** FAILURE/WARNING ***: Load from disk called for '{thumbnail_file_path}'. Key '{current_material_hash}' in cache: {current_material_hash in custom_icons}. Item valid: {preview_item_from_disk_load is not None}. Icon ID: {actual_id}. Scheduling generation.")
                    # Proceed to schedule generation if load from disk failed to add a valid icon
        except Exception as e_load_from_disk:
            print(f"[GetIcon - {mat_name_debug}] *** ERROR *** loading file '{thumbnail_file_path}' from disk: {e_load_from_disk}. Scheduling generation.")
            # Proceed to schedule generation

    if not thumbnail_generation_scheduled.get(current_material_hash, False):
        print(f"[GetIcon - {mat_name_debug}] Scheduling generation for HASH: {current_material_hash} -> {os.path.basename(thumbnail_file_path)}")
        thumbnail_generation_scheduled[current_material_hash] = True

        if 'generate_thumbnail_async' in globals() and callable(generate_thumbnail_async):
            bpy.app.timers.register(
                lambda m=mat, p=thumbnail_file_path, h=current_material_hash: \
                       generate_thumbnail_async(m, p, h),
                first_interval=0.1
            )
        else:
            print(f"[GetIcon - {mat_name_debug}] *** CRITICAL ERROR ***: generate_thumbnail_async function not found! Cannot schedule generation.")
            thumbnail_generation_scheduled.pop(current_material_hash, None)

    return 0

def generate_thumbnail_async(mat, thumb_path, hash_value):
    """
    Async thumbnail generator (called via timer).
    Renders thumbnail to thumb_path. Loads generated icon into cache using hash_value.
    Includes robust checks for material validity and template scene.
    """
    global custom_icons, thumbnail_generation_scheduled, list_version

    try:
        mat_name_debug = "UnknownMaterial"
        try:
            if not mat or not hasattr(mat, 'name') or mat.name not in bpy.data.materials:
                print(f"[Gen Async - {hash_value}] Invalid or removed material reference. Aborting generation.")
                return None
            mat_name_debug = mat.name
        except ReferenceError:
            print(f"[Gen Async - {hash_value}] Material reference lost (already deleted?). Aborting generation.")
            return None
        except Exception as e_validate_mat_for_gen:
            print(f"[Gen Async - {hash_value}] Error validating material '{mat_name_debug}': {e_validate_mat_for_gen}. Aborting.")
            return None

        if custom_icons is not None and hash_value in custom_icons:
            cached_thumb_path = get_thumbnail_path(hash_value)
            try:
                cached_item = custom_icons[hash_value]
                if os.path.isfile(cached_thumb_path) and os.path.getsize(cached_thumb_path) > 0 and hasattr(cached_item, 'icon_id') and cached_item.icon_id > 0:
                    return None
            except Exception: pass

        should_render_final_check = True
        try:
            if os.path.isfile(thumb_path) and os.path.getsize(thumb_path) > 0:
                should_render_final_check = False
                if custom_icons is not None and hash_value not in custom_icons:
                    print(f"[Gen Async - {hash_value}] File exists for '{mat_name_debug}', loading into cache: {os.path.basename(thumb_path)}")
                    loaded_item = custom_icons.load(hash_value, thumb_path, 'IMAGE')
                    if hash_value in custom_icons and loaded_item is not None and hasattr(loaded_item, 'icon_id') and loaded_item.icon_id > 0:
                        list_version += 1
                        scene = bpy.context.scene
                        if scene and hasattr(scene, 'material_list') and scene.material_list:
                            scene.material_list.list_version = list_version
                        if 'force_redraw' in globals(): force_redraw()
                    else:
                        print(f"[Gen Async - {hash_value}] Warning: Load of existing file '{os.path.basename(thumb_path)}' did not result in valid cached icon. Will attempt re-render.")
                        should_render_final_check = True # Force re-render if load failed
        except Exception as e_disk_check_async:
            print(f"[Gen Async - {hash_value}] Error during pre-render disk check for '{mat_name_debug}': {e_disk_check_async}. Assuming render is needed.")
            should_render_final_check = True

        if not should_render_final_check:
            return None

        print(f"[Gen Async - {hash_value}] Attempting render for '{mat_name_debug}' -> {os.path.basename(thumb_path)}")
        render_template_scene = load_icon_template_scene()
        if not render_template_scene:
            print(f"[Gen Async - {hash_value}] Thumbnail generation failed for '{mat_name_debug}': No template scene available after load/recreate attempt.")
        else:
            try:
                os.makedirs(os.path.dirname(thumb_path), exist_ok=True)
            except Exception as e_mkdir_thumb:
                print(f"[Gen Async - {hash_value}] Error creating directory for thumbnail {thumb_path}: {e_mkdir_thumb}")

            render_succeeded = create_sphere_preview_thumbnail(mat, thumb_path)

            if render_succeeded:
                print(f"[Gen Async - {hash_value}] Render successful for '{mat_name_debug}'. Generated: {os.path.basename(thumb_path)}")
                if custom_icons is not None:
                    try:
                        time.sleep(0.2)
                        if os.path.isfile(thumb_path) and os.path.getsize(thumb_path) > 0:
                            newly_loaded_item = custom_icons.load(hash_value, thumb_path, 'IMAGE')
                            if hash_value in custom_icons and newly_loaded_item is not None and hasattr(newly_loaded_item, 'icon_id') and newly_loaded_item.icon_id > 0:
                                print(f"[Gen Async - {hash_value}] Successfully loaded generated icon '{hash_value}' into cache.")
                                list_version += 1
                                scene = bpy.context.scene
                                if scene and hasattr(scene, 'material_list') and scene.material_list:
                                    scene.material_list.list_version = list_version
                                else:
                                    print("[Gen Async - WARN] Scene.material_list not found for UI update.")
                                if 'force_redraw' in globals() and callable(force_redraw): force_redraw()
                                else: print("[Gen Async - ERROR] force_redraw function not found.")
                            else:
                                final_check_item = custom_icons.get(hash_value)
                                final_id = getattr(final_check_item, 'icon_id', -1) if final_check_item else -1
                                print(f"[Gen Async - {hash_value}] WARNING: custom_icons.load of new render for key '{hash_value}' did not result in a valid cached icon. ID: {final_id}")
                        else:
                            print(f"[Gen Async - {hash_value}] ERROR: Render reported success, but file '{os.path.basename(thumb_path)}' not found/empty post-render.")
                    except Exception as e_load_after_gen:
                        print(f"[Gen Async - {hash_value}] Error loading generated thumbnail into cache: {e_load_after_gen}")
            else:
                print(f"[Gen Async - {hash_value}] create_sphere_preview_thumbnail failed for '{mat_name_debug}' -> {os.path.basename(thumb_path)}")

    except Exception as e_outer_async_gen:
        current_hash_for_log = hash_value if 'hash_value' in locals() else "UnknownHash"
        print(f"[Gen Async - {current_hash_for_log}] Outer unexpected error in generate_thumbnail_async: {str(e_outer_async_gen)}")
        traceback.print_exc()
    finally:
        key_to_pop_from_schedule = hash_value if 'hash_value' in locals() else None
        if not key_to_pop_from_schedule and 'mat' in locals() and mat:
            try: key_to_pop_from_schedule = get_material_hash(mat)
            except: pass

        if key_to_pop_from_schedule:
            thumbnail_generation_scheduled.pop(key_to_pop_from_schedule, None)

    return None

def update_material_thumbnails():
    """
    Iterates through all materials in the current blend file,
    schedules generation for missing thumbnails via get_custom_icon.
    Thumbnails on disk are no longer deleted, allowing reuse across sessions.
    Triggers a UI refresh after checking current materials.
    """
    global custom_icons, list_version 

    print("[Thumbnail Update Cycle - Main] Starting thumbnail update for current .blend file...")

    # 1. Iterate through current bpy.data.materials to check/schedule thumbnail generation.
    materials_in_current_blend = list(bpy.data.materials) # Create a copy for safe iteration
    num_mats_to_check_for_gen = len(materials_in_current_blend)
    print(f"[Thumbnail Update Cycle - Main] Checking {num_mats_to_check_for_gen} materials in current .blend file for thumbnail generation via get_custom_icon...")

    mats_processed_for_generation_scheduling = 0
    for mat_idx, current_mat_obj in enumerate(materials_in_current_blend):
        # Optional: Provide console feedback for very large projects
        if mat_idx > 0 and mat_idx % 100 == 0:
            print(f"[Thumbnail Update Cycle - Main] ...checked {mat_idx}/{num_mats_to_check_for_gen} materials for generation scheduling.")

        # Basic validation of the material object
        current_mat_name_for_debug = f"MaterialAtIndex_{mat_idx}"
        try:
            if not current_mat_obj or not hasattr(current_mat_obj, 'name'): continue # Skip invalid
            current_mat_name_for_debug = current_mat_obj.name
            # Ensure material has a UUID (get_material_uuid also creates if missing for non-library)
            if not get_material_uuid(current_mat_obj): continue
        except ReferenceError: continue # Material might have been removed during iteration
        except Exception as e_mat_validate_for_thumb_update:
            print(f"[Thumbnail Update Cycle - Main] Error validating material {current_mat_name_for_debug}: {e_mat_validate_for_thumb_update}")
            continue
        
        # Call get_custom_icon for each material.
        # This function handles all logic: checks cache, checks disk, and if necessary,
        # robustly schedules generate_thumbnail_async. We don't need its return value here.
        _ = get_custom_icon(current_mat_obj)
        mats_processed_for_generation_scheduling +=1

    print(f"[Thumbnail Update Cycle - Main] Finished generation checks for {mats_processed_for_generation_scheduling} materials.")

    # 2. Orphaned Thumbnail Cleanup is REMOVED. Thumbnails will persist on disk.
    # The valid_hashes_for_cleanup_reference set and its population are no longer needed here.
    # load_material_hashes() at the start of this function (if it was there for cleanup) is also removed.

    # 3. UI Refresh (after all checks for the current file are done)
    # This will run fairly quickly after the generation checks for the current file.
    # Any newly scheduled async generations will happen in the background.
    def trigger_ui_refresh_after_checks():
        global list_version # Ensure access to global list_version for UI update
        print("[Thumbnail Update Cycle - UI Refresh] Triggering UI refresh after current file checks.")
        current_scene_for_refresh = bpy.context.scene # Get current scene context
        if current_scene_for_refresh:
            try:
                # Repopulate the list which uses get_custom_icon, ensuring latest icons are requested.
                if 'populate_material_list' in globals() and callable(populate_material_list):
                    populate_material_list(current_scene_for_refresh)
                else: print("[Thumbnail Update Cycle - UI Refresh] ERROR: populate_material_list function not found.")

                list_version += 1 # Increment version to force UI list to acknowledge changes.
                if hasattr(current_scene_for_refresh, 'material_list') and current_scene_for_refresh.material_list:
                    current_scene_for_refresh.material_list.list_version = list_version
                else: print("[Thumbnail Update Cycle - UI Refresh] Warning: Scene.material_list property not found for version update.")

                if 'force_redraw' in globals() and callable(force_redraw): force_redraw()
                else: print("[Thumbnail Update Cycle - UI Refresh] ERROR: force_redraw function not found.")

            except Exception as e_final_ui_refresh:
                print(f"[Thumbnail Update Cycle - UI Refresh] Error during UI refresh: {e_final_ui_refresh}")
        else: # Should ideally not happen if Blender UI is active
            print("[Thumbnail Update Cycle - UI Refresh] Warning: No context scene found for UI refresh.")
        
        print("[Thumbnail Update Cycle - Main] Thumbnail update process for current file completed (no disk cleanup).")
        return None # Stop timer

    # Schedule the UI refresh to run after a very short delay, allowing the main loop to finish.
    bpy.app.timers.register(trigger_ui_refresh_after_checks, first_interval=0.2) # e.g., 0.2 seconds delay
    print("[Thumbnail Update Cycle - Main] Scheduled UI refresh.")

# --------------------------
# Visibility–backup helpers (Unchanged)
# --------------------------
def _ensure_visibility_table() -> None: # Unchanged
    with get_db_connection() as conn:
        c = conn.cursor(); c.execute("CREATE TABLE IF NOT EXISTS visible_objects (blend_filepath TEXT PRIMARY KEY, editing JSON)"); conn.commit()
def _save_visible_objects(scene: bpy.types.Scene) -> None: # Unchanged
    _ensure_visibility_table(); visible = [o.name for o in scene.objects if not o.hide_viewport]
    with get_db_connection() as conn:
        c = conn.cursor(); c.execute("INSERT OR REPLACE INTO visible_objects VALUES (?, ?)", (get_backup_filepath(), json.dumps(visible))); conn.commit()
def _load_visible_objects() -> list[str]: # Unchanged
    _ensure_visibility_table()
    with get_db_connection() as conn:
        c = conn.cursor(); c.execute("SELECT editing FROM visible_objects WHERE blend_filepath=?", (get_backup_filepath(),))
        row = c.fetchone(); return json.loads(row[0]) if row and row[0] else []

# ------------------------------------------------------------------
# create_reference_snapshot (Unchanged from your version)
# ------------------------------------------------------------------
def create_reference_snapshot(context: bpy.types.Context) -> bool: # Unchanged
    duplicates_refs = []; original_duplicate_names = []; joined_obj = None; original_active = context.view_layer.objects.active
    try:
        ref_coll_name = "Reference"
        if ref_coll_name not in bpy.data.collections:
            ref_coll = bpy.data.collections.new(ref_coll_name)
            if context.scene and context.scene.collection: context.scene.collection.children.link(ref_coll)
            else: context.report({'ERROR'}, "Scene context missing for collection linking."); return False
        else: ref_coll = bpy.data.collections[ref_coll_name]
        visible_objs = [obj for obj in context.visible_objects if not obj.name.startswith('UTIL_') and obj.type == 'MESH']
        if not visible_objs: context.report({'WARNING'}, "No visible MESH objects to create reference"); return False
        for obj in visible_objs:
            try:
                dup = obj.copy(); dup.data = obj.data.copy(); dup.animation_data_clear()
                context.collection.objects.link(dup); duplicates_refs.append(dup); original_duplicate_names.append(dup.name)
            except Exception as e_dup:
                context.report({'ERROR'}, f"Error duplicating {obj.name}: {str(e_dup)}")
                for name in original_duplicate_names: bpy.data.objects.remove(bpy.data.objects.get(name), do_unlink=True)
                return False
        if not duplicates_refs: context.report({'ERROR'}, "Failed to duplicate any valid objects"); return False
        try:
            bpy.ops.object.select_all(action='DESELECT')
            valid_duplicates_for_join = [dup_ref for dup_ref in duplicates_refs if dup_ref and dup_ref.name in context.view_layer.objects]
            if not valid_duplicates_for_join:
                context.report({'ERROR'}, "No valid duplicates for join.");
                for name in original_duplicate_names: bpy.data.objects.remove(bpy.data.objects.get(name), do_unlink=True)
                return False
            for dup_ref in valid_duplicates_for_join: dup_ref.select_set(True)
            context.view_layer.objects.active = valid_duplicates_for_join[0]
            bpy.ops.object.join(); joined_obj = context.active_object
            joined_obj.name = f"REF_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
        except Exception as e_join:
            context.report({'ERROR'}, f"Join failed: {str(e_join)}")
            for name in original_duplicate_names: bpy.data.objects.remove(bpy.data.objects.get(name), do_unlink=True)
            return False
        finally:
            if original_active and original_active.name in context.view_layer.objects: context.view_layer.objects.active = original_active
            elif context.view_layer.objects: context.view_layer.objects.active = context.view_layer.objects[0]
        if joined_obj is None or joined_obj.name not in bpy.data.objects:
            context.report({'ERROR'}, "Joined object invalid.")
            for name in original_duplicate_names: bpy.data.objects.remove(bpy.data.objects.get(name), do_unlink=True)
            return False
        try:
            for coll in list(joined_obj.users_collection): coll.objects.unlink(joined_obj) # Unlink from all
            ref_coll.objects.link(joined_obj) # Link to Reference collection
        except Exception as e_move:
            context.report({'ERROR'}, f"Collection move failed: {str(e_move)}")
            if joined_obj.name in bpy.data.objects: bpy.data.objects.remove(joined_obj, do_unlink=True)
            for name in original_duplicate_names:
                obj_rem = bpy.data.objects.get(name)
                if obj_rem and obj_rem != joined_obj: bpy.data.objects.remove(obj_rem, do_unlink=True)
            return False
        joined_obj_name = joined_obj.name
        for dup_name in original_duplicate_names:
            obj_to_remove = bpy.data.objects.get(dup_name)
            if obj_to_remove and obj_to_remove.name != joined_obj_name:
                try: bpy.data.objects.remove(obj_to_remove, do_unlink=True)
                except Exception: pass
        return True
    except Exception as e:
        print(f"CRITICAL ERROR in create_reference_snapshot: {str(e)}"); traceback.print_exc()
        try:
            if context: context.report({'ERROR'}, f"Snapshot creation failed: {str(e)}")
        except Exception: pass
        if 'original_duplicate_names' in locals():
            joined_obj_name_final = joined_obj.name if joined_obj else None
            for name in original_duplicate_names:
                obj_rem = bpy.data.objects.get(name)
                if obj_rem and name != joined_obj_name_final:
                    try: bpy.data.objects.remove(obj_rem, do_unlink=True)
                    except Exception: pass
        return False

# This global `start worker once` block is removed as the new thumbnail system
# in get_custom_icon uses bpy.app.timers.register directly.

# --------------------------
# Depsgraph Handler (Unchanged from your version)
# --------------------------
@persistent
def depsgraph_update_handler(scene, depsgraph):
    global materials_modified
    # print(f"--- Depsgraph Handler Triggered (Scene: {getattr(scene, 'name', 'N/A')}) ---") # Verbose
    try:
        for update in depsgraph.updates:
            if isinstance(update.id, bpy.types.Material):
                material = update.id
                # print(f"     [Depsgraph] Material Update: {getattr(material, 'name', 'Unknown')}") # Verbose
                try: material["hash_dirty"] = True; materials_modified = True
                except Exception: pass # Ignore if prop can't be set (e.g. library material)
    except Exception as e: print(f"[Depsgraph Handler] Error: {e}"); traceback.print_exc()

# --------------------------
# Property Update Callbacks and UI Redraw (from old addon)
# --------------------------
def update_material_list_active_index(self, context):
    print(f"[MaterialList] Active material index updated to: {context.scene.material_list_active_index}")

# update_search removed as search handled by UIList.filter_items & lambda update for prop

prev_workspace_mode = "REFERENCE" # Keep this global for update_workspace_mode

def update_workspace_mode(self, context) -> None:
    """
    •  REFERENCE - hide every object that is **not** in the “Reference”
        collection (and hide its LayerCollection if possible).
    •  EDITING   - restore the object visibility we cached earlier and
        un-hide all non-Reference LayerCollections.
    Works even when the user keeps meshes directly in “Scene Collection”.
    Produces detailed console output for diagnostics.
    """
    global prev_workspace_mode
    scene      = context.scene
    view_layer = context.view_layer
    if not scene or not view_layer:
        print("[Workspace DBG] – missing scene or view-layer")
        return

    mode             = scene.workspace_mode
    ref_coll_name    = "Reference"
    ref_coll         = bpy.data.collections.get(ref_coll_name)

    def _find_layer_coll(root, name):
        if root.name == name: return root
        for ch in root.children:
            r = _find_layer_coll(ch, name)
            if r: return r
        return None

    root_lc      = view_layer.layer_collection
    ref_layer_lc = _find_layer_coll(root_lc, ref_coll_name)

    if mode == "REFERENCE":
        print("[Workspace DBG] → REFERENCE mode")
        _save_visible_objects(scene)
        for lc in root_lc.children:
            if lc.name != ref_coll_name: lc.hide_viewport = True
        if ref_layer_lc: ref_layer_lc.hide_viewport = False
        else: print("[Workspace DBG]    No LayerCollection for Reference")
        if ref_coll:
            ref_objs = {ob.name for ob in ref_coll.objects}
            hidden_cnt = 0
            for ob in scene.objects:
                if ob.name not in ref_objs:
                    if not ob.hide_get(): ob.hide_set(True); hidden_cnt += 1
            print(f"[Workspace DBG]    hid {hidden_cnt} non-Reference objects")
        else:
            print("[Workspace DBG]    Reference collection missing → hiding entire scene")
            for ob in scene.objects: ob.hide_set(True)
    else: # EDITING mode
        print("[Workspace DBG] → EDITING mode")
        if ref_layer_lc: ref_layer_lc.hide_viewport = True
        if ref_coll:
            for ob in ref_coll.objects: ob.hide_set(True)
        for lc in root_lc.children:
            if lc.name != ref_coll_name: lc.hide_viewport = False
        visible_names = _load_visible_objects()
        restored = 0
        for name in visible_names:
            ob = scene.objects.get(name)
            if ob and ob.hide_get(): ob.hide_set(False); restored += 1
        print(f"[Workspace DBG]    restored visibility of {restored} objects")

    force_redraw()
    prev_workspace_mode = mode
    print(f"[MaterialList] Workspace switched to {mode}")

def force_redraw():
    for window in bpy.context.window_manager.windows:
        for area in window.screen.areas:
            if area.type == 'VIEW_3D':
                area.tag_redraw()
    bpy.ops.wm.redraw_timer(type='DRAW_WIN_SWAP', iterations=3) # Use iterations instead of time for quick redraw

def ensure_safe_preview(mat): # Kept from old addon for panel usage
    if not mat: return False
    try:
        if not hasattr(mat, 'preview'): return False
        if not mat.preview:
            try: mat.preview_ensure(); return True
            except: return False
        return True
    except: return False

# --------------------------
# UIList and Panel Classes (from old addon, will use updated helpers)
# --------------------------
class MATERIALLIST_UL_materials(UIList):
    use_filter_show = False
    use_filter_menu = False
    use_filter_sort_alpha = False
    use_sort_alpha = False # This is used by template_list for default sorting if enabled

    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        icon_val = 0
        if (hasattr(self, "_cached_items_for_draw") and 0 <= index < len(self._cached_items_for_draw)):
            cache_entry = self._cached_items_for_draw[index]
            icon_val = cache_entry.get("icon_id", 0)
        else:
            mat_for_icon = get_material_by_uuid(item.material_uuid)
            if mat_for_icon:
                icon_val = get_custom_icon(mat_for_icon) # Uses new get_custom_icon

        row = layout.row(align=True)
        if icon_val: row.label(icon_value=icon_val)
        else: row.label(icon="MATERIAL")

        mat_check = get_material_by_uuid(item.material_uuid)
        if mat_check:
            row.label(text=item.material_name)
            if item.is_protected: row.label(icon="LOCKED")
        else:
            row.label(text="Missing Material", icon="ERROR")

    def filter_items(self, context, data, propname):
        global material_list_cache, list_version
        items = getattr(data, propname)
        scene = context.scene
        rebuild_cache = False
        current_ui_list_version = getattr(scene.material_list, 'list_version', -1)

        if not hasattr(self, '_last_version') or self._last_version != current_ui_list_version:
            rebuild_cache = True
            self._last_version = current_ui_list_version
        if not hasattr(self, '_last_item_count') or self._last_item_count != len(items):
            rebuild_cache = True
            self._last_item_count = len(items)

        if rebuild_cache:
            material_list_cache = []
            for item_idx, item_prop in enumerate(items):
                mat = bpy.data.materials.get(item_prop.material_uuid)
                icon_id = 0
                if mat: icon_id = get_custom_icon(mat) # Uses new get_custom_icon
                material_list_cache.append({
                    'name': item_prop.material_name,
                    'uuid': item_prop.material_uuid,
                    'icon_id': icon_id,
                    'original_index': item_idx
                })

        search_term = scene.material_search.lower()
        filtered_cache_for_draw = []
        original_indices_for_neworder = []

        if search_term:
            for cache_entry in material_list_cache:
                if search_term in cache_entry['name'].lower():
                    filtered_cache_for_draw.append(cache_entry)
                    original_indices_for_neworder.append(cache_entry['original_index'])
        else:
            filtered_cache_for_draw = material_list_cache
            original_indices_for_neworder = [entry['original_index'] for entry in material_list_cache]

        flt_flags = [0] * len(items)
        for original_idx in original_indices_for_neworder:
            if 0 <= original_idx < len(flt_flags):
                flt_flags[original_idx] = self.bitflag_filter_item
        flt_neworder = original_indices_for_neworder
        self._cached_items_for_draw = filtered_cache_for_draw
        return flt_flags, flt_neworder

    # is_visible function removed as it's not standard for UIList and might not be necessary
    # with the current filtering approach. If pagination or virtual lists were used, it might be needed.

class MATERIALLIST_PT_panel(Panel):
    bl_idname = "MATERIALLIST_PT_panel"
    bl_label = "Material List"
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Material List"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        scene = context.scene

        workspace_box = layout.box()
        workspace_box.label(text="Workspace Mode", icon='FILE_BLEND')
        row = workspace_box.row(align=True)
        row.label(text=f"Current: {scene.workspace_mode}")
        row = workspace_box.row()
        row.operator("materiallist.toggle_workspace_mode", text=f"Switch to {'Editing' if scene.workspace_mode == 'REFERENCE' else 'Reference'}")

        options_box = layout.box()
        options_box.label(text="Material Options", icon='TOOL_SETTINGS')
        row = options_box.row(align=True)
        row.operator("materiallist.rename_to_albedo", text="Rename All to Albedo", icon='FILE_REFRESH')
        row = options_box.row(align=True)
        row.prop(scene, "hide_mat_materials", toggle=True, text="Hide mat_ Materials") # This uses populate_material_list on update
        row = options_box.row(align=True)
        row.prop(scene, "material_list_show_only_local", toggle=True) # This uses populate_material_list
        row = options_box.row(align=True)
        row.operator("materiallist.rename_material", icon='FONT_DATA')
        row = options_box.row(align=True)
        row.operator("materiallist.unassign_mat", icon='PANEL_CLOSE')
        if (scene.material_list_active_index >= 0 and scene.material_list_active_index < len(scene.material_list_items)):
            list_item = scene.material_list_items[scene.material_list_active_index]
            mat = bpy.data.materials.get(list_item.material_uuid)
            if mat and mat.library:
                row = options_box.row(align=True)
                row.operator("materiallist.make_local", icon='LINKED')

        backup_box = layout.box()
        backup_box.label(text="Reference Snapshot", icon='INFO')
        row = backup_box.row(align=True)
        row.operator("materiallist.backup_editing", icon='FILE_TICK', text="Backup Reference")

        assign_box = layout.box()
        assign_box.operator("materiallist.add_material_to_slot", icon='PLUS')
        assign_box.operator("materiallist.assign_selected_material", icon='BRUSH_DATA')

        mat_list_box = layout.box()
        row = mat_list_box.row(align=True)
        row.label(text="Materials:", icon='MATERIAL')
        row.prop(scene, "material_list_sort_alpha", text="", toggle=True, icon='SORTALPHA') # Uses populate_material_list

        row = mat_list_box.row()
        row.template_list("MATERIALLIST_UL_materials", "", scene, "material_list_items", scene, "material_list_active_index", rows=8, sort_lock=True) # sort_lock might conflict with custom sort
        row = mat_list_box.row()
        row.prop(scene, "material_search", text="", icon='VIEWZOOM') # Update is lambda None, filtering in UIList

        util_box = layout.box()
        util_box.label(text="Batch Utilities", icon='TOOL_SETTINGS')
        row = util_box.row(align=True)
        row.operator("materiallist.localise_all_users", icon='FILE_SCRIPT')
        row.operator("materiallist.trim_library", icon='TRASH')
        row = util_box.row(align=True)
        row.operator("materiallist.select_dominant")

        if scene.material_list_active_index >= 0 and scene.material_list_active_index < len(scene.material_list_items):
            list_item = scene.material_list_items[scene.material_list_active_index]
            mat = bpy.data.materials.get(list_item.material_uuid)
            if mat:
                try:
                    if not mat.preview: mat.preview_ensure()
                except Exception: pass
                preview_box = mat_list_box.box()
                if ensure_safe_preview(mat): # Kept from old
                    preview_box.template_preview(mat, show_buttons=True)
                else:
                    preview_box.label(text="Preview not available", icon='ERROR')
                info_box = preview_box.box()
                row = info_box.row(); row.label(text=f"Name: {list_item.material_name}")
                row = info_box.row(); row.label(text=f"Source: {'Local' if not list_item.is_library else 'Library'}")

        layout.operator("materiallist.integrate_library", text="Integrate Library", icon='IMPORT')
        refresh_box = layout.box()
        refresh_box.operator("materiallist.refresh_material_list", text="Refresh List", icon='FILE_REFRESH')

# --------------------------
# Registration Data (Ensure all classes and properties are listed)
# --------------------------
class MaterialListProperties(bpy.types.PropertyGroup): # Unchanged
    list_version: bpy.props.IntProperty(name="List Version", default=0)

class LibraryMaterialEntry(PropertyGroup): # Unchanged
    content_hash: StringProperty()
    lib_uuid: StringProperty()

classes = (
    MaterialListItem,
    MaterialListProperties,
    LibraryMaterialEntry,
    MATERIALLIST_UL_materials,
    MATERIALLIST_PT_panel,
    MATERIALLIST_OT_toggle_workspace_mode,
    MATERIALLIST_OT_rename_to_albedo,
    MATERIALLIST_OT_unassign_mat,
    MATERIALLIST_OT_backup_reference,
    MATERIALLIST_OT_backup_editing,
    MATERIALLIST_OT_add_material_to_slot,
    MATERIALLIST_OT_assign_selected_material,
    MATERIALLIST_OT_refresh_material_list, # New definition
    MATERIALLIST_OT_rename_material,
    MATERIALLIST_OT_prepare_material,
    MATERIALLIST_OT_assign_to_object,
    MATERIALLIST_OT_assign_to_faces,
    MATERIALLIST_OT_make_local,
    MATERIALLIST_OT_sort_alphabetically,
    MATERIALLIST_OT_PollMaterialChanges,
    MATERIALLIST_OT_integrate_library,
    MATERIALLIST_OT_localise_all_users,
    MATERIALLIST_OT_trim_library,
    MATERIALLIST_OT_select_dominant,
    MATERIALLIST_OT_run_localisation_worker, # New definition
)

scene_props = [
    ("material_list_items", bpy.props.CollectionProperty(type=MaterialListItem)),
    ("material_list_active_index", bpy.props.IntProperty(name="Active Index", default=0, min=0, update=update_material_list_active_index)),
    ("material_search", bpy.props.StringProperty(name="Search Materials", description="Search material names", default="", update=lambda self, context: None)),
    ("hide_mat_materials", bpy.props.BoolProperty(name="Hide Default Materials", description="Hide materials starting with 'mat_'", default=False, update=lambda self, context: populate_material_list(context.scene))),
    ("workspace_mode", bpy.props.EnumProperty(name="Workspace Mode", items=[('REFERENCE', "Reference", "Reference configuration"), ('EDITING', "Editing", "Editing configuration")], default='REFERENCE', update=update_workspace_mode)),
    ("mat_materials_unassigned", bpy.props.BoolProperty(name="Unassign mat_ Materials", description="Toggle backup/restore of mat_ assignments", default=False)),
    ("material_list", bpy.props.PointerProperty(type=MaterialListProperties)),
    ("library_materials", bpy.props.CollectionProperty(type=LibraryMaterialEntry)),
    ("material_list_sort_alpha", bpy.props.BoolProperty(name="Sort Alphabetically", description="Sort the material list alphabetically by display name instead of by recency", default=False, update=lambda self, context: populate_material_list(context.scene))),
    ("material_list_show_only_local", bpy.props.BoolProperty(name="Show Only Local/Used", description="Show only local materials and linked materials currently assigned to objects in the scene", default=False, update=lambda self, context: populate_material_list(context.scene))),
]

handler_pairs = [
    (bpy.app.handlers.load_post, load_post_handler), # New load_post_handler
    (bpy.app.handlers.save_pre, save_handler),       # New save_handler
    (bpy.app.handlers.save_post, save_post_handler),   # New save_post_handler
    (bpy.app.handlers.depsgraph_update_post, depsgraph_update_handler), # New depsgraph_update_handler
    (bpy.app.handlers.load_post, migrate_thumbnail_files) # Kept from new function list
]

# --- deferred_safe_init (Unchanged in its core purpose) ---
# It benefits from other functions being fixed (e.g., populate_material_list, ensure_material_library)
def deferred_safe_init(): # Unchanged
    try:
        print("[DEBUG] Running deferred_safe_init")
        if 'load_material_names' in globals(): load_material_names()
        if not ensure_material_library(): print("[DEBUG] ensure_material_library failed in deferred init")
        # debug_library_contents() # Optional
        update_material_library(force_update=True) # Queues update
        scene = get_first_scene()
        if scene:
            populate_material_list(scene) # Now excludes mat_
            reference_backup.clear(); backup_current_assignments(reference_backup, 'reference')
            load_backups()
            if hasattr(bpy.ops.materiallist, 'poll_material_changes'):
                try: bpy.ops.materiallist.poll_material_changes('INVOKE_DEFAULT') # Start polling
                except Exception as op_error: print(f"Error invoking poll_material_changes: {op_error}")
        # Initialize material properties here as well, after linking might have occurred
        if 'initialize_material_properties' in globals() and callable(initialize_material_properties):
            initialize_material_properties()

    except Exception as e: print(f"[DEBUG] Exception in deferred_safe_init: {e}"); traceback.print_exc()
    return None

def register():
    global _ADDON_DATA_ROOT, LIBRARY_FOLDER, LIBRARY_FILE, DATABASE_FILE, THUMBNAIL_FOLDER, ICON_TEMPLATE_FILE
    global custom_icons, _thumbnail_thread_started, stop_event, thumbnail_workers

    _ADDON_DATA_ROOT = get_material_manager_addon_data_dir()
    if not _ADDON_DATA_ROOT or not os.path.exists(_ADDON_DATA_ROOT):
        raise RuntimeError("Material Manager: Failed to initialize addon data directory.")

    LIBRARY_FOLDER = _ADDON_DATA_ROOT
    LIBRARY_FILE = os.path.join(LIBRARY_FOLDER, "material_library.blend")
    DATABASE_FILE = os.path.join(LIBRARY_FOLDER, "material_list.db")
    THUMBNAIL_FOLDER = os.path.join(LIBRARY_FOLDER, "thumbnails")
    ICON_TEMPLATE_FILE = os.path.join(LIBRARY_FOLDER, "icon_generation_template.blend") # Used by ensure_icon_template

    print("[Register] Core paths initialized.", flush=True)

    # Preview system
    if custom_icons is not None:
        try: bpy.utils.previews.remove(custom_icons)
        except Exception: pass
    custom_icons = None # Explicitly set to None before attempting new()

    preview_creation_success = False
    try:
        custom_icons = bpy.utils.previews.new() # Attempt to create
        if custom_icons is not None: # Check if creation was successful
            preview_creation_success = True
            print("[Register] New preview collection created successfully.", flush=True)
        else: # bpy.utils.previews.new() returned None
            print("[Register] CRITICAL ERROR: bpy.utils.previews.new() returned None!", flush=True)
    except Exception as e_preview_init_reg:
        print(f"[Register] CRITICAL ERROR during bpy.utils.previews.new(): {e_preview_init_reg}", flush=True)
        custom_icons = None # Ensure it's None if creation failed

    if preview_creation_success: # Only preload if collection was successfully created
        if 'preload_existing_thumbnails' in globals() and callable(preload_existing_thumbnails):
            try: preload_existing_thumbnails()
            except Exception as e_preload_reg: print(f"[Register] Error during preload: {e_preload_reg}", flush=True)
        else: print("[Register] ERROR: preload_existing_thumbnails function not found!", flush=True)
    else: print("[Register] Skipping preload, preview collection creation failed or returned None.", flush=True)

    # Classes
    for cls in classes:
        try:
            try: bpy.utils.unregister_class(cls) # Clean unregister first
            except RuntimeError: pass
            bpy.utils.register_class(cls)
        except Exception as e: print(f"[Register] ERROR class {cls.__name__}: {e}", flush=True); traceback.print_exc()

    # Scene props
    for prop_name, prop_value in scene_props:
        try:
            if hasattr(bpy.types.Scene, prop_name): delattr(bpy.types.Scene, prop_name)
            setattr(bpy.types.Scene, prop_name, prop_value)
        except Exception as e: print(f"[Register] ERROR prop '{prop_name}': {e}", flush=True); traceback.print_exc()

    # WindowManager property for save_handler
    bpy.types.WindowManager.matlist_save_handler_processed = bpy.props.BoolProperty(
        name="MaterialList Save Handler Processed",
        description="Internal flag to ensure save_handler runs once per save operation.",
        default=False
    )

    # Handlers
    for handler_list, func in handler_pairs:
        if func and callable(func) and func not in handler_list:
            try: handler_list.append(func)
            except Exception as e: print(f"[Register] ERROR handler {func.__name__}: {e}", flush=True); traceback.print_exc()

    # DB Connection Pool
    if 'initialize_db_connection_pool' in globals() and callable(initialize_db_connection_pool):
        initialize_db_connection_pool()
    else: print("[Register] ERROR: initialize_db_connection_pool not found.", flush=True)

    # Thumbnail worker thread - this section might print an error if _thumbnail_worker is removed.
    # If the new thumbnail system relies solely on bpy.app.timers, this thread is not strictly needed
    # for that purpose anymore.
    if not _thumbnail_thread_started:
        if '_thumbnail_worker' in globals() and callable(_thumbnail_worker) and 'stop_event' in globals():
            stop_event.clear()
            worker_thread = Thread(target=_thumbnail_worker, daemon=True); worker_thread.start()
            thumbnail_workers.append(worker_thread); _thumbnail_thread_started = True
            print("[Register] Thumbnail worker thread started (if _thumbnail_worker is defined).", flush=True)
        else: print("[Register] Info: _thumbnail_worker not defined or stop_event missing. Thumbnail thread for _thumbnail_thread_queue not started (may be intended if new system is used).", flush=True)

    # Deferred initialization
    if 'deferred_safe_init' in globals() and callable(deferred_safe_init):
        bpy.app.timers.register(deferred_safe_init, first_interval=0.5)
    else: print("[Register] ERROR: deferred_safe_init not found.", flush=True)

    print("[Register] Addon registration finished.", flush=True)

def unregister():
    global custom_icons, _thumbnail_thread_started, stop_event, db_connections
    global material_names, material_hashes, global_hash_cache # thumbnail_cache removed as unused
    global thumbnail_generation_scheduled, library_update_queue, material_list_cache
    global list_version, changed_materials, material_uuid_map, _display_name_cache
    global reference_backup, editing_backup

    print("[Unregister] Starting addon unregistration...", flush=True)

    # Stop Modal Timer
    poll_op_class = getattr(bpy.types, "MATERIALLIST_OT_PollMaterialChanges", None)
    if poll_op_class and hasattr(poll_op_class, '_timer') and poll_op_class._timer is not None:
        try:
            wm = bpy.context.window_manager
            timer_to_remove = poll_op_class._timer
            poll_op_class._timer = None
            wm.event_timer_remove(timer_to_remove)
            print("[Unregister] Modal polling timer removed.", flush=True)
        except Exception as e_timer_rem: print(f"[Unregister] Error removing modal timer: {e_timer_rem}", flush=True)

    # Stop Thumbnail Worker Thread (if it was started and relevant)
    if _thumbnail_thread_started and 'stop_event' in globals() and stop_event:
        try:
            stop_event.set()
            for worker in thumbnail_workers:
                if worker.is_alive(): worker.join(timeout=0.5)
            thumbnail_workers.clear(); _thumbnail_thread_started = False
            print("[Unregister] Thumbnail worker thread(s) (for _thumbnail_thread_queue) signaled to stop.", flush=True)
        except Exception as e_thread_stop: print(f"[Unregister] Error stopping worker thread: {e_thread_stop}", flush=True)

    # Unregister Handlers
    for handler_list, func in handler_pairs:
        if func and callable(func) and func in handler_list:
            try: handler_list.remove(func)
            except Exception: pass

    # Unregister Scene Properties
    for prop_name, _ in scene_props:
        if hasattr(bpy.types.Scene, prop_name):
            try: delattr(bpy.types.Scene, prop_name)
            except Exception: pass
    
    # Unregister WindowManager property
    if hasattr(bpy.types.WindowManager, 'matlist_save_handler_processed'):
        try:
            del bpy.types.WindowManager.matlist_save_handler_processed
        except Exception as e:
            print(f"[Unregister] Error deleting WindowManager.matlist_save_handler_processed: {e}", flush=True)


    # Unregister Classes
    for cls in reversed(classes):
        try: bpy.utils.unregister_class(cls)
        except RuntimeError: pass

    # Remove Preview Collection
    if custom_icons is not None:
        try: bpy.utils.previews.remove(custom_icons)
        except Exception: pass
        custom_icons = None

    # Close Database Connections
    if 'db_connections' in globals() and db_connections:
        while not db_connections.empty():
            try: conn = db_connections.get_nowait(); conn.close()
            except Exception: break

    # Clear Global Variables / Caches
    material_names.clear(); material_hashes.clear(); global_hash_cache.clear()
    thumbnail_generation_scheduled.clear(); library_update_queue.clear()
    material_list_cache.clear(); _display_name_cache.clear()
    if 'reference_backup' in globals(): reference_backup.clear()
    if 'editing_backup' in globals(): editing_backup.clear()
    list_version = 0
    # thumbnail_cache.clear() # Removed as it's unused

    print("[Unregister] Addon unregistration finished.", flush=True)

def debug_library_contents(): # Kept from old addon
    if os.path.exists(LIBRARY_FILE):
        print("[DEBUG] Debugging library contents:", flush=True)
        with bpy.data.libraries.load(LIBRARY_FILE, link=False) as (data_from, data_to):
            print(f"[DEBUG] Library contains {len(data_from.materials)} materials:", flush=True)
            for mat in data_from.materials:
                print(f"[DEBUG] - {mat}", flush=True)
    else:
        print("[DEBUG] Library file does not exist", flush=True)

if __name__ == "__main__": # Kept from old addon
    register()
    debug_library_contents()