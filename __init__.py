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

import bpy, os, sqlite3, tempfile, shutil, traceback, bmesh, uuid, re, time, hashlib, math, json, subprocess, sys
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
THUMBNAIL_MAX_RETRIES = 2
persistent_icon_template_scene = None
material_names = {}
material_hashes = {}
custom_icons = None
global_hash_cache = {}
thumbnail_generation_scheduled = {}
library_update_queue = []
is_update_processing = False
material_list_cache = [] # Used by UIList filter_items
list_version = 0
library_lock = Lock()
changed_materials = set() # This seems unused, consider removing
material_uuid_map = {} # This seems unused, consider removing
hash_lock = Lock() # Used by save_material_names, save_material_hashes, delayed_load_post
thumbnail_workers = [] # Used by register/unregister for thread management
db_connections = Queue(maxsize=5)
_display_name_cache = {}
_display_name_cache_version = 0
materials_modified = False # Used by depsgraph_handler and save_handler
WORKER_SCRIPT = os.path.join(os.path.dirname(__file__), "localise_library_worker.py")

BACKGROUND_WORKER_PY = None # Will point to your background_writer.py
thumbnail_task_queue = Queue()
thumbnail_worker_pool = [] # Stores Popen objects and task info
MAX_CONCURRENT_THUMBNAIL_WORKERS = 5
#MAX_CONCURRENT_THUMBNAIL_WORKERS = max(1, (os.cpu_count() or 4) // 2) # Default, more aggressive
THUMBNAIL_BATCH_SIZE_PER_WORKER = 5 # Number of thumbnails one worker process will try to generate
thumbnail_pending_on_disk_check = {} # hash: {task_details} - Tracks hashes whose generation is actively awaited
thumbnail_monitor_timer_active = False # Flag to control the monitor timer

# --- New Globals for Batch Processing System ---
g_thumbnail_process_ongoing = False
g_material_creation_timestamp_at_process_start = 0.0
# g_tasks_for_current_run: List of ALL individual task_dicts for the current "run".
# Tasks are removed from here as they are dispatched. Retries are added back here.
g_tasks_for_current_run = []
g_dispatch_lock = Lock()
g_library_update_pending = False
g_current_run_task_hashes_being_processed = set() # Tracks hashes in current run batches to avoid re-queueing by get_custom_icon
# --- End New Globals ---

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
    c.execute('''CREATE TABLE IF NOT EXISTS library_material_origins
                 (library_material_uuid TEXT PRIMARY KEY,
                  source_blend_filepath TEXT,
                  source_material_name_in_file TEXT, 
                  source_material_uuid_in_file TEXT,
                  timestamp_added_to_library INTEGER)''')
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
        return f"{value:.8f}"
    elif isinstance(value, (bpy.types.bpy_prop_array, tuple, list)):
        if not value: return '[]'
        try: # Attempt to treat as numeric list
            if all(isinstance(x, (int, float)) for x in value):
                 return '[' + ','.join([_float_repr(item) for item in value]) + ']'
        except TypeError: # If 'in' fails on an item that's not iterable, or other type issues
            pass # Fall through to general repr
        return repr(value) # Fallback for mixed types or non-numeric lists
    elif hasattr(value, 'to_list'):
        list_val = value.to_list()
        if not list_val: return '[]' # Handle empty to_list() result
        if '_float_repr' in globals() and callable(_float_repr):
            return '[' + ','.join([_float_repr(item) for item in list_val]) + ']'
        else:
            print("[_stable_repr CRITICAL] _float_repr helper not found for to_list()!")
            return str(list_val) # Fallback to string of list if helper missing
    elif value is None:
        return 'None'
    else:
        # Fallback to standard repr for any other types
        return repr(value)

# _hash_image (Version from background_writer.py)
def _hash_image(img):
    """
    Returns md5 digest.
    For packed images: hashes the first 128KB of img.packed_file.data.
    For external files: hashes the first 128KB of the file content.
    Handles library materials by resolving '//' paths relative to the library file.
    Falls back to metadata-based hash if content cannot be accessed.
    """
    if not img: 
        return "NO_IMAGE_DATABLOCK"

    # 1. Handle PACKED images first by hashing their actual data
    if hasattr(img, 'packed_file') and img.packed_file and hasattr(img.packed_file, 'data') and img.packed_file.data:
        try:
            # Hash the first 128KB of packed data for consistency and performance
            # img.packed_file.data is a bpy_prop_array of bytes
            data_to_hash = bytes(img.packed_file.data[:131072]) # Ensure it's plain bytes
            return hashlib.md5(data_to_hash).hexdigest()
        except Exception as e_pack_hash:
            print(f"[_hash_image Warning] Could not hash packed_file.data for image '{getattr(img, 'name', 'N/A')}': {e_pack_hash}", file=sys.stderr)
            # Fall through to metadata-based fallback if direct data hashing fails

    # 2. Handle EXTERNAL images (original logic for non-packed or if packed failed above)
    raw_path = img.filepath_raw if hasattr(img, 'filepath_raw') and img.filepath_raw else ""
    resolved_abs_path = ""
    try:
        if hasattr(img, 'library') and img.library and hasattr(img.library, 'filepath') and img.library.filepath and raw_path.startswith('//'):
            library_blend_abs_path = bpy.path.abspath(img.library.filepath)
            library_dir = os.path.dirname(library_blend_abs_path)
            path_relative_to_lib_root = raw_path[2:]
            path_relative_to_lib_root = path_relative_to_lib_root.replace('\\', os.sep).replace('/', os.sep)
            resolved_abs_path = os.path.join(library_dir, path_relative_to_lib_root)
        elif raw_path: # For non-library images or non-// paths in library images (e.g. absolute paths)
            resolved_abs_path = bpy.path.abspath(raw_path) # Resolves relative to current .blend if path is relative
        
        if resolved_abs_path and os.path.exists(resolved_abs_path) and os.path.isfile(resolved_abs_path):
            try:
                with open(resolved_abs_path, "rb") as f: 
                    data_from_file = f.read(131072) # Read first 128k
                return hashlib.md5(data_from_file).hexdigest()
            except Exception as read_err:
                print(f"[_hash_image Warning] Could not read external file '{resolved_abs_path}' (from raw '{raw_path}', image '{getattr(img, 'name', 'N/A')}'): {read_err}", file=sys.stderr)
    except Exception as path_err: 
        print(f"[_hash_image Warning] Error during path resolution/check for external file '{raw_path}' (image '{getattr(img, 'name', 'N/A')}'): {path_err}", file=sys.stderr)
    
    # 3. Fallback if neither packed data nor external file content could be successfully hashed
    img_name_for_fallback = getattr(img, 'name_full', getattr(img, 'name', 'UnknownImage'))
    is_packed_for_fallback = hasattr(img, 'packed_file') and (img.packed_file is not None)
    source_for_fallback = getattr(img, 'source', 'UNKNOWN_SOURCE')
    
    fallback_data = f"FALLBACK_HASH_FOR_IMG|NAME:{img_name_for_fallback}|RAW_PATH:{raw_path}|IS_PACKED_STATE:{is_packed_for_fallback}|SOURCE:{source_for_fallback}"
    # print(f"[_hash_image Fallback] Using fallback for image '{img_name_for_fallback}'. Data: {fallback_data}", file=sys.stderr) # Optional: for debugging
    return hashlib.md5(fallback_data.encode('utf-8')).hexdigest()

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
        visited_nodes = set()
        for _ in range(20): # Limit search depth (increased to match BG worker)
            if not current_node or current_node in visited_nodes: break
            visited_nodes.add(current_node)
            if current_node.bl_idname == 'ShaderNodeBsdfPrincipled': return current_node
            
            potential_shader_inputs = []
            if hasattr(current_node, 'inputs'):
                # Check common specific names first
                shader_input_names = ["Shader", "Shader1", "Shader2"]
                for name in shader_input_names:
                    if name in current_node.inputs:
                        potential_shader_inputs.append(current_node.inputs[name])
                
                # Generic check for any other input of type SHADER
                for inp in current_node.inputs:
                    if inp.type == 'SHADER' and inp not in potential_shader_inputs:
                        potential_shader_inputs.append(inp)
            
            found_next_shader_link = False
            for inp_socket in potential_shader_inputs:
                if inp_socket.is_linked and inp_socket.links and inp_socket.links[0].from_socket.type == 'SHADER':
                    current_node = inp_socket.links[0].from_node
                    found_next_shader_link = True
                    break 
            if not found_next_shader_link: break
        
        # If traversal fails, fall back to a direct search (like BG worker's implied fallback)
        return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)
    except Exception as e:
        print(f"[Hash Helper Main Addon] Error finding Principled BSDF for {getattr(mat, 'name', 'N/A')}: {e}")
        # Fallback to direct search on any error during traversal
        return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)

# get_material_hash (Structure from __init__.py, using updated helpers)
def get_material_hash(mat, force=True):
    # IMPORTANT: New HASH_VERSION to indicate the change to content-only hashing
    HASH_VERSION = "v_RTX_REMIX_PBR_COMPREHENSIVE_2_CONTENT_ONLY"

    if not mat: return None
    # Use a generic name for logging if mat.name isn't reliable here
    mat_name_for_debug = getattr(mat, 'name_full', getattr(mat, 'name', 'UnknownMaterial'))


    hash_inputs = []
    pbr_image_hashes = set() # Use a set to automatically handle duplicate image hashes

    try:
        principled_node = None
        material_output_node = None

        if mat.use_nodes and mat.node_tree:
            principled_node = find_principled_bsdf(mat) # Assumes your find_principled_bsdf is defined
            for node_out_check in mat.node_tree.nodes:
                if node_out_check.bl_idname == 'ShaderNodeOutputMaterial' and node_out_check.is_active_output:
                    material_output_node = node_out_check
                    break
            if not material_output_node:
                for node_out_check in mat.node_tree.nodes:
                    if node_out_check.bl_idname == 'ShaderNodeOutputMaterial':
                        material_output_node = node_out_check
                        break
        else:
            hash_inputs.append("NON_NODE_MATERIAL")
            hash_inputs.append(f"DiffuseColor:{_stable_repr(mat.diffuse_color)}")
            hash_inputs.append(f"Metallic:{_stable_repr(mat.metallic)}")
            hash_inputs.append(f"Roughness:{_stable_repr(mat.roughness)}")
            # Add other relevant non-node properties if they affect appearance

        if principled_node:
            hash_inputs.append(f"SHADER_TYPE:{principled_node.bl_idname}")
            inputs_to_process = [
                ("Base Color", "color_texture"), ("Metallic", "value_texture"), ("Roughness", "value_texture"),
                ("IOR", "value_only"), ("Alpha", "value_texture"), ("Normal", "normal_texture_special"),
                ("Emission Color", "color_texture"), ("Emission Strength", "value_only"),
                ("Subsurface Weight", "value_texture"), ("Subsurface Color", "color_texture"),
                ("Subsurface Radius", "vector_value_only"), ("Subsurface Scale", "value_only"),
                ("Subsurface IOR", "value_only"), ("Subsurface Anisotropy", "value_only"),
                ("Clearcoat Weight", "value_texture"), ("Clearcoat Tint", "color_texture"), # Added Clearcoat Tint
                ("Clearcoat Roughness", "value_texture"),
                ("Clearcoat Normal", "normal_texture_special"),
                ("Specular IOR Level", "value_texture"), ("Specular Tint", "color_texture"),
                ("Sheen Weight", "value_texture"), ("Sheen Tint", "color_texture"),
                ("Sheen Roughness", "value_texture"),
                ("Transmission Weight", "value_texture"), ("Transmission Roughness", "value_texture"),
                ("Anisotropic", "value_texture"),("Anisotropic Rotation", "value_texture"),
            ]
            # Dynamically add Coat inputs if they exist (for Principled BSDF v2 / Blender 3.0+)
            coat_inputs_to_check = [
                ("Coat Weight", "value_texture"), ("Coat Roughness", "value_texture"),
                ("Coat IOR", "value_only"), ("Coat Tint", "color_texture"),
                ("Coat Normal", "normal_texture_special")
            ]
            for coat_input_name, coat_processing_type in coat_inputs_to_check:
                if coat_input_name in principled_node.inputs:
                    inputs_to_process.append((coat_input_name, coat_processing_type))

            for input_name, processing_type in inputs_to_process:
                inp = principled_node.inputs.get(input_name)
                if not inp:
                    continue

                input_key_str = f"INPUT:{input_name}"
                if inp.is_linked:
                    link = inp.links[0]
                    source_node = link.from_node
                    source_socket_name = link.from_socket.name

                    if processing_type == "normal_texture_special":
                        if source_node.bl_idname == 'ShaderNodeNormalMap':
                            nm_strength_input = source_node.inputs.get("Strength")
                            nm_strength = nm_strength_input.default_value if nm_strength_input and hasattr(nm_strength_input, 'default_value') else 1.0
                            nm_color_input = source_node.inputs.get("Color")
                            tex_hash = "NO_TEX_IN_NORMALMAP"
                            if nm_color_input and nm_color_input.is_linked and nm_color_input.links[0].from_node.bl_idname == 'ShaderNodeTexImage':
                                tex_node = nm_color_input.links[0].from_node
                                if tex_node.image:
                                    img_hash = _hash_image(tex_node.image) # _hash_image needs to be robust
                                    if img_hash: pbr_image_hashes.add(img_hash)
                                    tex_hash = img_hash if img_hash else f"TEX_NORMALMAP_IMG_NO_HASH_{getattr(tex_node.image, 'name', 'Unnamed')}"
                            hash_inputs.append(f"{input_key_str}=NORMALMAP(Strength:{_stable_repr(nm_strength)},Tex:{tex_hash})")
                        elif source_node.bl_idname == 'ShaderNodeBump':
                            bump_strength_input = source_node.inputs.get("Strength")
                            bump_distance_input = source_node.inputs.get("Distance")
                            bump_strength = bump_strength_input.default_value if bump_strength_input and hasattr(bump_strength_input, 'default_value') else 1.0
                            bump_distance = bump_distance_input.default_value if bump_distance_input and hasattr(bump_distance_input, 'default_value') else 0.1
                            bump_height_input = source_node.inputs.get("Height")
                            tex_hash = "NO_TEX_IN_BUMPMAP"
                            if bump_height_input and bump_height_input.is_linked and bump_height_input.links[0].from_node.bl_idname == 'ShaderNodeTexImage':
                                tex_node = bump_height_input.links[0].from_node
                                if tex_node.image:
                                    img_hash = _hash_image(tex_node.image)
                                    if img_hash: pbr_image_hashes.add(img_hash)
                                    tex_hash = img_hash if img_hash else f"TEX_BUMP_IMG_NO_HASH_{getattr(tex_node.image, 'name', 'Unnamed')}"
                            hash_inputs.append(f"{input_key_str}=BUMPMAP(Strength:{_stable_repr(bump_strength)},Distance:{_stable_repr(bump_distance)},Tex:{tex_hash})")
                        elif source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image:
                            img_hash = _hash_image(source_node.image)
                            if img_hash: pbr_image_hashes.add(img_hash)
                            tex_hash = img_hash if img_hash else f"TEX_NORMAL_IMG_NO_HASH_{getattr(source_node.image, 'name', 'Unnamed')}"
                            hash_inputs.append(f"{input_key_str}=TEX:{tex_hash}")
                        else:
                            hash_inputs.append(f"{input_key_str}=LINKED_NODE:{source_node.bl_idname}_SOCKET:{source_socket_name}")
                    elif source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image:
                        img_hash = _hash_image(source_node.image)
                        if img_hash: pbr_image_hashes.add(img_hash)
                        tex_hash = img_hash if img_hash else f"TEX_{input_name.replace(' ','')}_IMG_NO_HASH_{getattr(source_node.image, 'name', 'Unnamed')}"
                        hash_inputs.append(f"{input_key_str}=TEX:{tex_hash}")
                    else:
                        hash_inputs.append(f"{input_key_str}=LINKED_NODE:{source_node.bl_idname}_SOCKET:{source_socket_name}")
                else:
                    hash_inputs.append(f"{input_key_str}=VALUE:{_stable_repr(inp.default_value)}")

        if material_output_node:
            disp_input = material_output_node.inputs.get("Displacement")
            if disp_input and disp_input.is_linked:
                link = disp_input.links[0]; source_node = link.from_node; source_socket_name = link.from_socket.name
                if source_node.bl_idname == 'ShaderNodeDisplacement':
                    disp_height_input = source_node.inputs.get("Height")
                    disp_midlevel_input = source_node.inputs.get("Midlevel")
                    disp_scale_input = source_node.inputs.get("Scale")
                    disp_midlevel = disp_midlevel_input.default_value if disp_midlevel_input and hasattr(disp_midlevel_input, 'default_value') else 0.5
                    disp_scale = disp_scale_input.default_value if disp_scale_input and hasattr(disp_scale_input, 'default_value') else 1.0
                    tex_hash = "NO_TEX_IN_DISPLACEMENT_NODE"
                    if disp_height_input and disp_height_input.is_linked and disp_height_input.links[0].from_node.bl_idname == 'ShaderNodeTexImage':
                        tex_node = disp_height_input.links[0].from_node
                        if tex_node.image:
                            img_hash = _hash_image(tex_node.image)
                            if img_hash: pbr_image_hashes.add(img_hash)
                            tex_hash = img_hash if img_hash else f"TEX_DISP_IMG_NO_HASH_{getattr(tex_node.image, 'name', 'Unnamed')}"
                    hash_inputs.append(f"MAT_OUTPUT_DISPLACEMENT=DISP_NODE(Mid:{_stable_repr(disp_midlevel)},Scale:{_stable_repr(disp_scale)},Tex:{tex_hash})")
                elif source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image:
                    img_hash = _hash_image(source_node.image)
                    if img_hash: pbr_image_hashes.add(img_hash)
                    tex_hash = img_hash if img_hash else f"TEX_DISP_DIRECT_IMG_NO_HASH_{getattr(source_node.image, 'name', 'Unnamed')}"
                    hash_inputs.append(f"MAT_OUTPUT_DISPLACEMENT=TEX:{tex_hash}")
                else:
                    hash_inputs.append(f"MAT_OUTPUT_DISPLACEMENT=LINKED_NODE:{source_node.bl_idname}_SOCKET:{source_socket_name}")

        if mat.use_nodes and mat.node_tree:
            for node in mat.node_tree.nodes:
                if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                    img_hash_general = _hash_image(node.image)
                    if img_hash_general:
                        pbr_image_hashes.add(img_hash_general)

        if pbr_image_hashes:
            sorted_pbr_image_hashes = sorted(list(pbr_image_hashes))
            hash_inputs.append(f"ALL_UNIQUE_IMAGE_HASHES_COMBINED:{'|'.join(sorted_pbr_image_hashes)}")

        # The HASH_IDENTITY_UID line is INTENTIONALLY REMOVED for pure content hashing.

        final_hash_string = f"VERSION:{HASH_VERSION}|||" + "|||".join(sorted(hash_inputs))
        digest = hashlib.md5(final_hash_string.encode('utf-8')).hexdigest()
        return digest

    except Exception as e:
        print(f"[get_material_hash - CONTENT_ONLY] Error hashing mat '{mat_name_for_debug}': {type(e).__name__} - {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        return None

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

def _perform_library_update(force: bool = False):
    print(f"[DEBUG LibUpdate MainAddon] Attempting library update. Force_flag_received: {force}")

    global g_thumbnail_process_ongoing, g_library_update_pending, material_names, material_hashes # Ensure globals are accessible

    if g_thumbnail_process_ongoing:
        print("[DEBUG LibUpdate MainAddon] Thumbnail generation is ongoing. Deferring library update.")
        g_library_update_pending = True
        if force: # If the deferred update was forced, keep that forced status
            if hasattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced'):
                bpy.context.window_manager.matlist_pending_lib_update_is_forced = True
        return False # Indicate update was deferred

    # Check if a previously deferred update was forced
    effective_force = force
    if hasattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced') and bpy.context.window_manager.matlist_pending_lib_update_is_forced:
        print("[DEBUG LibUpdate MainAddon] Pending library update was flagged as forced. Applying force.")
        effective_force = True
        bpy.context.window_manager.matlist_pending_lib_update_is_forced = False # Reset the flag

    print(f"[DEBUG LibUpdate MainAddon] Effective force for this run: {effective_force}")

    # Load current material hashes from DB (material_hashes global is populated)
    # These hashes are now purely content-based.
    load_material_hashes()
    # existing_hashes_in_db_for_uuid = material_hashes # More descriptive name, it's {uuid: content_hash}

    existing_names_in_lib_file = set() # Stores UUIDs (datablock names) present in material_library.blend

    if os.path.exists(LIBRARY_FILE):
        try:
            with bpy.data.libraries.load(LIBRARY_FILE, link=False, assets_only=True) as (data_from_lib_names, _):
                if hasattr(data_from_lib_names, 'materials'):
                    # These names in the library file ARE the UUIDs of the library materials
                    existing_names_in_lib_file = {name for name in data_from_lib_names.materials if isinstance(name, str)}
            # print(f"[DEBUG LibUpdate MainAddon] Names (UUIDs) found in existing library file '{os.path.basename(LIBRARY_FILE)}': {existing_names_in_lib_file if existing_names_in_lib_file else 'None'}")
        except Exception as e:
            print(f"[DEBUG LibUpdate MainAddon] Error loading names from library file '{LIBRARY_FILE}': {e}")
            # Decide if you want to proceed or return False if library is inaccessible
    else:
        print(f"[DEBUG LibUpdate MainAddon] Library file '{LIBRARY_FILE}' does not exist. `existing_names_in_lib_file` will be empty.")

    to_transfer = [] # List of material objects from current scene to transfer
    # This set prevents adding multiple local materials that have the *same content hash*
    # to the *same single transfer file operation*. The worker will handle further logic.
    processed_content_hashes_for_this_transfer_op = set()

    print(f"[DEBUG LibUpdate MainAddon] Iterating {len(bpy.data.materials)} materials in current .blend file for potential transfer.")
    for mat_idx, mat in enumerate(bpy.data.materials):
        mat_name_debug = getattr(mat, 'name', f'InvalidMaterialObject_idx_{mat_idx}')
        try:
            if getattr(mat, 'library', None):
                # print(f"  Skipping '{mat_name_debug}': Is a library material itself (linked from elsewhere).")
                continue

            # Ensure material has a "uuid" custom property and its datablock name is that UUID
            # This should have been handled by save_handler or initialize_material_properties for local, non-"mat_" materials.
            # For "mat_" materials, they might still have their descriptive names, but should have a "uuid" prop.
            # The key is that the 'uid' used here should be the persistent identifier for this datablock.
            uid = mat.get("uuid") # Get the persistent UUID from custom property
            if not uid:
                uid = validate_material_uuid(mat) # Ensure "uuid" prop exists, get or create it
                try:
                    mat["uuid"] = uid # Make sure it's set on the object if validate_material_uuid just returned it
                except Exception as e_setuuid_loop:
                    print(f"  Warning: Could not set 'uuid' property on {mat_name_debug} during lib update check: {e_setuuid_loop}")


            # If datablock name is not its UUID (common for "mat_" or newly created before save_handler rename)
            # it's fine, as worker will use "uuid" prop if name isn't UUID.
            # For transfer, materials are typically renamed to their UUID if they are local non-"mat_".
            # The crucial part is that 'uid' variable holds the intended persistent ID for this material datablock.

            if not uid:
                # print(f"  Skipping '{mat_name_debug}': Could not get/assign valid persistent UUID for processing.")
                continue

            # Skip "mat_" prefixed materials (by display name) from being added to library,
            # unless you specifically want them in the library.
            # This uses mat_get_display_name which relies on 'material_names' global.
            display_name = mat_get_display_name(mat) # Ensure material_names is loaded
            if display_name.startswith("mat_"):
                # print(f"  Skipping '{mat_name_debug}' (display name '{display_name}'): Starts with 'mat_'.")
                continue

            # Get current content hash (now purely content-based)
            # Force recalculation for local materials being considered for transfer
            current_content_hash = get_material_hash(mat, force=True)

            if not current_content_hash:
                # print(f"  Skipping '{mat_name_debug}' (UUID: {uid}): Failed to calculate its content_hash.")
                continue

            # Avoid adding multiple *different local materials* that happen to have the
            # *same content hash* to this single transfer operation.
            # The worker will decide if this content (under its new UUID) needs to be added to the library.
            if current_content_hash in processed_content_hashes_for_this_transfer_op and not effective_force:
                # print(f"  Skipping '{mat_name_debug}' (UUID: {uid}, ContentHash: {current_content_hash[:8]}): This content hash already added to transfer list this run from another local material.")
                continue

            # Check conditions for transferring this material (identified by 'uid')
            # 1. Is this 'uid' already a datablock name in material_library.blend?
            uid_is_in_library_file = uid in existing_names_in_lib_file

            # 2. What is the hash stored in our DB for this 'uid'?
            db_hash_for_this_uid = material_hashes.get(uid) # material_hashes is {uuid: content_hash}

            # Conditions to decide if this material (by its 'uid') needs to be transferred for add/update
            should_transfer = False
            reason_for_transfer = []

            if effective_force:
                should_transfer = True
                reason_for_transfer.append("ForcedUpdate")
            else:
                if not uid_is_in_library_file:
                    should_transfer = True # It's a new UUID to the library
                    reason_for_transfer.append("NewUUIDToLibrary")
                elif db_hash_for_this_uid is None: # UUID known in lib file, but not in our DB hash cache (should be rare if lib is consistent)
                    should_transfer = True
                    reason_for_transfer.append("UUIDInLibFileButNotInDBHashCache")
                elif current_content_hash != db_hash_for_this_uid:
                    should_transfer = True # Content of this known UUID has changed
                    reason_for_transfer.append("ContentChangedForExistingUUID")
                # No explicit 'else: skip' here, should_transfer remains false if no condition met

            # print(f"  Checking {mat_name_debug} (UUID: {uid}, ContentHash: {current_content_hash[:8]}, DBHashForUUID: {db_hash_for_this_uid[:8] if db_hash_for_this_uid else 'None'}):")
            # print(f"    IsUIDInLibFile ({uid}): {uid_is_in_library_file}")
            # print(f"    ShouldTransfer: {should_transfer} (Reasons: {', '.join(reason_for_transfer) if reason_for_transfer else 'None'})")

            if should_transfer:
                # Before adding to transfer, ensure its datablock name IS its UUID.
                # This is crucial for the worker, which expects materials in the transfer file
                # (and later in the library file) to be named by their UUID.
                if mat.name != uid:
                    try:
                        # print(f"    Renaming datablock '{mat.name}' to its UUID '{uid}' for transfer.")
                        # Check if a material with the target UUID name already exists AND IS DIFFERENT
                        existing_mat_with_target_name = bpy.data.materials.get(uid)
                        if existing_mat_with_target_name and existing_mat_with_target_name != mat:
                            print(f"    WARNING: Cannot rename '{mat.name}' to UUID '{uid}' for transfer. Target name exists and is a different datablock. Skipping this material.")
                            continue # Skip this problematic material
                        mat.name = uid
                    except Exception as rename_err:
                        print(f"    WARNING: Failed to rename datablock '{mat.name}' to UUID '{uid}' for transfer: {rename_err}. Skipping this material.")
                        continue # Skip if rename fails

                if hasattr(mat, 'use_fake_user'):
                    mat.use_fake_user = True

                # Stamp origin information
                try:
                    current_filepath_for_origin = bpy.data.filepath if bpy.data.filepath else "UnsavedOrUnknown"
                    # 'uid' is the persistent UUID of the source material datablock
                    # 'display_name' is the source material's display name
                    mat["ml_origin_blend_file"] = current_filepath_for_origin
                    mat["ml_origin_mat_name"] = display_name # Store the original display name from source
                    mat["ml_origin_mat_uuid"] = uid # Store the UUID of the source material datablock

                    # print(f"    Stamping origin on '{mat.name}': File='{os.path.basename(current_filepath_for_origin)}', SourceOrigName='{display_name}', SourceUUID='{uid}'")
                except Exception as e_set_origin_prop:
                    print(f"    Warning: Could not set origin custom properties on '{mat.name}': {e_set_origin_prop}")

                print(f"    >>> ADDING '{mat.name}' (orig display name: '{display_name}', ContentHash: {current_content_hash[:8]}) TO TRANSFER LIST. Reason: {reason_for_transfer}")
                to_transfer.append(mat)
                processed_content_hashes_for_this_transfer_op.add(current_content_hash)
                # Update material_hashes in memory (and later save to DB) for this UUID with its current content hash
                material_hashes[uid] = current_content_hash # This ensures cond_hash_changed works correctly next time

        except ReferenceError:
            # print(f"  Skipping material at index {mat_idx}: ReferenceError (material likely deleted during iteration).")
            continue
        except Exception as loop_error:
            print(f"[DEBUG LibUpdate MainAddon] Error processing material {mat_name_debug} in loop: {loop_error}")
            traceback.print_exc()

    if not to_transfer:
        print("[DEBUG LibUpdate MainAddon] Nothing to transfer to library.")
        # Save material_hashes if any were updated in memory even if nothing transferred (e.g. hash changed but no transfer needed)
        # This would be if a material was skipped due to processed_content_hashes_for_this_transfer_op
        # but its individual material_hashes[uid] was updated.
        save_material_hashes() # Ensure any in-memory changes to material_hashes are persisted
        return True # Indicate completion (nothing to do)

    print(f"[DEBUG LibUpdate MainAddon] Preparing to transfer {len(to_transfer)} materials.")
    try:
        os.makedirs(LIBRARY_FOLDER, exist_ok=True)
    except Exception as e_mkdir_lib:
        print(f"[DEBUG LibUpdate MainAddon] Error creating library folder '{LIBRARY_FOLDER}': {e_mkdir_lib}. Cannot proceed with transfer.")
        return False

    tmp_dir_for_transfer = ""
    transfer_blend_file_path = ""
    actual_mats_written_to_transfer_file = set()

    try:
        tmp_dir_for_transfer = tempfile.mkdtemp(prefix="matlib_transfer_")
        transfer_blend_file_path = os.path.join(tmp_dir_for_transfer, f"transfer_data_{uuid.uuid4().hex[:8]}.blend")

        # Ensure all materials in 'to_transfer' are valid Material type objects
        valid_mats_for_bpy_write = {m for m in to_transfer if isinstance(m, bpy.types.Material)}

        if not valid_mats_for_bpy_write:
            print("[DEBUG LibUpdate MainAddon] No valid material objects in the transfer list after filtering. Nothing to write.")
            if tmp_dir_for_transfer and os.path.exists(tmp_dir_for_transfer):
                shutil.rmtree(tmp_dir_for_transfer, ignore_errors=True)
            save_material_hashes() # Persist any hash updates
            return True # Nothing written, but process completed.

        # The materials in valid_mats_for_bpy_write are the ones that will be written.
        # Their names should be their UUIDs by now.
        actual_mats_written_to_transfer_file = valid_mats_for_bpy_write

        print(f"[DEBUG LibUpdate MainAddon] Writing {len(actual_mats_written_to_transfer_file)} materials to transfer file: {transfer_blend_file_path}")
        bpy.data.libraries.write(transfer_blend_file_path, actual_mats_written_to_transfer_file, fake_user=True, compress=True)
        print(f"[DEBUG LibUpdate MainAddon] Successfully wrote materials to transfer file.")

    except Exception as e_write_transfer:
        print(f"[DEBUG LibUpdate MainAddon] Failed during writing of transfer file: {e_write_transfer}")
        traceback.print_exc()
        if tmp_dir_for_transfer and os.path.exists(tmp_dir_for_transfer):
            shutil.rmtree(tmp_dir_for_transfer, ignore_errors=True)
        save_material_hashes() # Persist any hash updates
        return False # Indicate failure

    # --- Staging textures for the transfer file ---
    if actual_mats_written_to_transfer_file and tmp_dir_for_transfer:
        print(f"[DEBUG LibUpdate MainAddon] Staging textures for transfer file '{os.path.basename(transfer_blend_file_path)}' into temp dir: {tmp_dir_for_transfer}")
        unique_images_to_stage = {} # {original_abs_path_in_main_session: target_abs_path_in_temp_dir_for_worker}

        for mat_in_transfer_file in actual_mats_written_to_transfer_file:
            if mat_in_transfer_file.use_nodes and mat_in_transfer_file.node_tree:
                for node in mat_in_transfer_file.node_tree.nodes:
                    if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                        img_datablock = node.image
                        if img_datablock.packed_file:
                            # print(f"  Image '{img_datablock.name}' is packed. Will be handled by library write.")
                            continue
                        if not img_datablock.filepath_raw:
                            # print(f"  Image '{img_datablock.name}' has no filepath_raw. Skipping staging.")
                            continue

                        original_stored_path_in_datablock = img_datablock.filepath_raw
                        source_abs_path_in_main_blender_session = ""
                        try:
                            # This resolves relative to the *current main .blend file* being saved
                            source_abs_path_in_main_blender_session = bpy.path.abspath(original_stored_path_in_datablock)
                        except Exception as e_abs_main_session:
                            print(f"  WARNING: Could not resolve abspath for '{original_stored_path_in_datablock}' (image '{img_datablock.name}') in main session: {e_abs_main_session}. Skipping staging for this texture.")
                            continue

                        if not os.path.exists(source_abs_path_in_main_blender_session):
                            print(f"  WARNING: Source texture file for staging not found at '{source_abs_path_in_main_blender_session}' (from raw '{original_stored_path_in_datablock}', image '{img_datablock.name}'). Cannot stage.")
                            continue
                        
                        # The worker will expect textures relative to the transfer_blend_file_path if they are '//'
                        # So, if the original_stored_path_in_datablock was `//textures/mytex.png`,
                        # we need to copy `source_abs_path_in_main_blender_session` to
                        # `tmp_dir_for_transfer/textures/mytex.png`.
                        target_abs_path_in_temp_staging_dir = ""
                        if original_stored_path_in_datablock.startswith('//'):
                            relative_part_from_blend_root = original_stored_path_in_datablock[2:]
                            # Normalize for os.path.join, important if paths came from different OS
                            normalized_relative_part = relative_part_from_blend_root.replace('\\', os.sep).replace('/', os.sep)
                            target_abs_path_in_temp_staging_dir = os.path.join(tmp_dir_for_transfer, normalized_relative_part)
                            
                            if source_abs_path_in_main_blender_session not in unique_images_to_stage: # Avoid redundant copy instructions
                                unique_images_to_stage[source_abs_path_in_main_blender_session] = target_abs_path_in_temp_staging_dir
                        # else: Absolute paths in image datablocks are left as is; worker will try to find them.
                        # If they were relative but not `//` (e.g. `textures/mytex.png`), bpy.path.abspath resolved them.
                        # The worker, when loading transfer_blend_file_path, will see these as absolute.
                        # This behavior might need refinement if non-// relative paths are common and need to be staged.
                        # For now, only `//` paths are explicitly staged into the temp dir structure.

        if unique_images_to_stage:
            print(f"[DEBUG LibUpdate MainAddon] Copying {len(unique_images_to_stage)} unique relatively-pathed ('//') image files to temp staging area for worker...")
            staged_count = 0; failed_copy_count = 0
            for src_path, temp_dest_path in unique_images_to_stage.items():
                try:
                    os.makedirs(os.path.dirname(temp_dest_path), exist_ok=True)
                    shutil.copy2(src_path, temp_dest_path) # copy2 preserves metadata like timestamps
                    staged_count +=1
                except Exception as e_stage_copy:
                    print(f"    ERROR STAGING: Failed to copy '{src_path}' to '{temp_dest_path}': {e_stage_copy}")
                    failed_copy_count +=1
            print(f"[DEBUG LibUpdate MainAddon] Staging of {staged_count} relatively-pathed images complete. Failed copies: {failed_copy_count}.")
    # --- End Staging Textures ---

    # Save material_hashes (which contains {uuid: content_hash}) to DB.
    # This includes hashes for materials that were just added to to_transfer.
    save_material_hashes()
    print(f"[DEBUG LibUpdate MainAddon] Updated and saved material_hashes to DB for materials processed in this update.")

    if not BACKGROUND_WORKER_PY or not os.path.exists(BACKGROUND_WORKER_PY):
        print(f"[DEBUG LibUpdate MainAddon] CRITICAL Error: Background worker script missing or path invalid: {BACKGROUND_WORKER_PY}")
        if tmp_dir_for_transfer and os.path.exists(tmp_dir_for_transfer):
            shutil.rmtree(tmp_dir_for_transfer, ignore_errors=True)
        return False # Cannot launch worker

    # --- Launch Background Worker Thread ---
    def _bg_merge_thread_target(transfer_file, target_library, database_path_for_worker, temp_dir_to_cleanup_after_worker):
        try:
            db_file_abs_for_worker = os.path.abspath(database_path_for_worker) if database_path_for_worker else None
            if not db_file_abs_for_worker or not os.path.exists(db_file_abs_for_worker):
                print(f"[BG Merge Thread] WARNING: Database file not found at '{db_file_abs_for_worker}' for worker's use. Origin/timestamps might not be updated by worker.", file=sys.stderr)
                # Worker can still proceed with merge if DB is only for secondary info.

            cmd = [
                bpy.app.binary_path,
                "--background", # Run Blender in background
                "--factory-startup", # Start with a clean state, no user prefs or startup file
                # The transfer_file itself is NOT loaded via command line here.
                # The worker script will load it using bpy.data.libraries.load()
                # This is important if transfer_file contains materials that might conflict with factory startup scene.
                "--python", BACKGROUND_WORKER_PY,
                "--", # Separator for script arguments
                "--operation", "merge_library",
                "--transfer", transfer_file, # Path to the .blend file with materials to merge
                "--target", target_library, # Path to the main material_library.blend
            ]
            if db_file_abs_for_worker: # Only pass DB path if it's valid
                 cmd.extend(["--db", db_file_abs_for_worker])

            print(f"[BG Merge Thread] Executing worker command: {' '.join(cmd)}", flush=True)
            # Increased timeout as library operations can be slow
            res = subprocess.run(cmd, check=False, capture_output=True, text=True, timeout=600) # 10 minutes

            if res.stdout:
                print(f"[BG Merge Thread - Worker Stdout For {os.path.basename(transfer_file)}]:\n{res.stdout}", flush=True)
            if res.stderr:
                print(f"[BG Merge Thread - Worker Stderr For {os.path.basename(transfer_file)}]:\n{res.stderr}", flush=True)
            
            if res.returncode != 0:
                print(f"[BG Merge Thread] Error: Worker command for transfer '{os.path.basename(transfer_file)}' exited with code {res.returncode}.", flush=True)
            else:
                print(f"[BG Merge Thread] Worker for transfer '{os.path.basename(transfer_file)}' completed successfully (Code 0).", flush=True)

        except subprocess.TimeoutExpired:
            print(f"[BG Merge Thread] Error: Worker command for transfer '{os.path.basename(transfer_file)}' timed out after 600 seconds.", flush=True)
            traceback.print_exc()
        except Exception as e_bg_thread:
            print(f"[BG Merge Thread] General Error in background merge thread for '{os.path.basename(transfer_file)}': {e_bg_thread}", flush=True)
            traceback.print_exc()
        finally:
            if temp_dir_to_cleanup_after_worker and os.path.exists(temp_dir_to_cleanup_after_worker):
                try:
                    shutil.rmtree(temp_dir_to_cleanup_after_worker, ignore_errors=False) # Try to raise error if cleanup fails
                    print(f"[BG Merge Thread] Cleaned up temp directory: {temp_dir_to_cleanup_after_worker}", flush=True)
                except Exception as e_clean_final:
                    print(f"[BG Merge Thread] Warning: Error cleaning up temp directory '{temp_dir_to_cleanup_after_worker}': {e_clean_final}", flush=True)
                    # This might indicate files are locked, which could be an issue.
    # --- End Background Worker Thread ---

    library_file_abs_path = os.path.abspath(LIBRARY_FILE)
    db_file_abs_path_for_main = os.path.abspath(DATABASE_FILE) # For the worker

    # Launch the background merge operation in a separate thread
    # The worker process itself is a separate Blender instance.
    bg_thread = Thread(target=_bg_merge_thread_target, args=(
        transfer_blend_file_path,
        library_file_abs_path,
        db_file_abs_path_for_main, # Pass the DB path to the worker
        tmp_dir_for_transfer # Pass the whole temp dir for cleanup
    ), daemon=True)
    bg_thread.start()

    print(f"[DEBUG LibUpdate MainAddon] Background merge thread launched for {len(actual_mats_written_to_transfer_file)} materials. Transfer file: {os.path.basename(transfer_blend_file_path)}, Target Library: {os.path.basename(library_file_abs_path)}")
    return True # Update process initiated

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
    # print(f"[DEBUG get_material_by_uuid] Called for UUID: '{uuid_str}'") # Keep initial call log for now
    if not uuid_str:
        # print(f"[DEBUG get_material_by_uuid]   Input UUID is None or empty. Returning None.") # Keep for basic None check
        return None

    # Primary check by datablock name matching the UUID string
    # print(f"[DEBUG get_material_by_uuid]   Attempting direct name lookup for: '{uuid_str}'")
    mat_by_name = bpy.data.materials.get(uuid_str)
    if mat_by_name:
        # is_lib_by_name = mat_by_name.library is not None
        # uuid_prop_by_name = mat_by_name.get("uuid", "N/A")
        # print(f"[DEBUG get_material_by_uuid]     FOUND by name: '{mat_by_name.name}'. Is Library: {is_lib_by_name}. Has UUID Prop: '{uuid_prop_by_name}'.")
        # print(f"[DEBUG get_material_by_uuid]   RETURNING material found by name: '{mat_by_name.name}'")
        return mat_by_name
    # else:
        # print(f"[DEBUG get_material_by_uuid]     NOT found by direct name lookup.")

    # Fallback: Iterate all materials to check the "uuid" custom property
    # print(f"[DEBUG get_material_by_uuid]   Fallback: Iterating all materials to check 'uuid' custom property for '{uuid_str}'...")
    for m_iter in bpy.data.materials:
        try:
            # mat_name_iter = getattr(m_iter, 'name', 'Unknown/Invalid Material')
            # is_lib_iter = m_iter.library is not None if hasattr(m_iter, 'library') else 'N/A (no library attr)'
            uuid_prop_iter = m_iter.get("uuid", "N/A")

            # print(f"[DEBUG get_material_by_uuid]     Checking material: '{mat_name_iter}'. Is Library: {is_lib_iter}. Has UUID Prop: '{uuid_prop_iter}'.") # Can be very verbose

            if uuid_prop_iter == uuid_str:
                #print(f"[DEBUG get_material_by_uuid]       MATCH found by custom property 'uuid'=='{uuid_str}' on material: '{mat_name_iter}'. Is Library: {is_lib_iter}.")
                #print(f"[DEBUG get_material_by_uuid]   RETURNING material found by custom property: '{mat_name_iter}'")
                return m_iter
        except ReferenceError:
            #print(f"[DEBUG get_material_by_uuid]     ReferenceError while checking a material, skipping.")
            continue
        except Exception as e_iter:
            # mat_name_for_err_log = getattr(m_iter, 'name', 'Unknown/Invalid Material during error')
            # print(f"[DEBUG get_material_by_uuid]     Exception while checking material '{mat_name_for_err_log}': {e_iter}")
            continue

    # print(f"[DEBUG get_material_by_uuid]   Material with UUID '{uuid_str}' NOT FOUND after all checks. Returning None.") # Keep final failure log
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
def populate_material_list(scene, *, called_from_finalize_run=False):
    """
    Rebuilds the material list items.
    If scene.hide_mat_materials is True, materials with display name starting "mat_" are excluded.
    If scene.hide_mat_materials is False, only the "mat_" material with the lowest suffix is shown.
    Sorts and applies "Show Only Local/Used".
    **Now allows both local and library materials with the same content hash to be listed (if their UUIDs differ).**
    Triggers a thumbnail update check after populating.
    """
    if not scene:
        print("[Populate List] Error: Scene object is None.")
        return

    sort_mode = "Alphabetical" if scene.material_list_sort_alpha else "Recency"
    filter_local_used_active = scene.material_list_show_only_local
    hide_mat_prefix_materials = scene.hide_mat_materials

    log_message = (
        f"[Populate List] Starting (Sort: {sort_mode}, "
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
            print("[Populate List] Error: Scene missing 'material_list_items'. Cannot populate.")
            return

        current_material_collection = bpy.data.materials
        # print(f"[Populate List] Initial scan of {len(current_material_collection)} materials...")

        all_mats_data = [] # Store dicts: {'mat_obj':mat, 'display_name':str, 'uuid':str, ...}
        for mat_idx, mat in enumerate(current_material_collection):
            if not mat or not hasattr(mat, 'name'):
                continue
            try:
                display_name = mat_get_display_name(mat) # Uses DB for display names
                mat_uuid = get_material_uuid(mat) # Ensures "uuid" custom prop
                if not mat_uuid: # Should not happen if get_material_uuid is robust
                    print(f"[Populate List] Warning: Could not get UUID for material '{mat.name}'. Skipping.")
                    continue

                # Get content hash (now purely content-based)
                # Use force=False to leverage cache if available, as this is for display filtering primarily
                content_hash = get_material_hash(mat, force=False)
                if not content_hash:
                    print(f"[Populate List] Warning: Could not get content hash for '{mat.name}' (UUID: {mat_uuid}).")
                    # Decide if unhashable materials should be excluded or handled differently
                    # For now, they will proceed but might not participate in content-based logic correctly

                all_mats_data.append({
                    'mat_obj': mat, # Keep reference for now, for filters like "is_used"
                    'display_name': display_name,
                    'uuid': mat_uuid,
                    'is_library': bool(mat.library),
                    'is_protected': mat.get('is_protected', False),
                    'original_name': mat.get("orig_name", display_name), # Fallback for original name
                    'content_hash': content_hash
                })
            except ReferenceError:
                print(f"[Populate List] ReferenceError for a material during initial scan. Skipping.")
            except Exception as e_proc_scan:
                print(f"[Populate List] Error processing '{getattr(mat, 'name', 'N/A')}' during initial scan: {e_proc_scan}")

        # Removed: local_content_hashes set and the logic that used it to suppress library items.
        # Library items will now proceed even if a local material has the same content hash.

        material_info_map = {} # Stores {uuid: item_info_dict} to ensure one entry per UUID
        mat_prefix_candidates = {} # For "mat_" suffix filtering: {base_name: best_item_info_dict}

        # print(f"[Populate List] Processing {len(all_mats_data)} collected material data items for UI list...")
        for item_info_dict in all_mats_data:
            mat_uuid_for_map = item_info_dict['uuid']
            display_name_for_map = item_info_dict['display_name']

            # Logic for "mat_" prefixed materials (hiding or choosing lowest suffix)
            if display_name_for_map.startswith("mat_"):
                if hide_mat_prefix_materials:
                    continue # Skip if "mat_" materials are hidden
                else: # Find the "mat_" material with the lowest suffix for each base name
                    base_name, suffix_num = _parse_material_suffix(display_name_for_map)
                    item_info_dict['suffix_num'] = suffix_num # Store suffix for comparison
                    existing_candidate = mat_prefix_candidates.get(base_name)
                    if not existing_candidate or suffix_num < existing_candidate['suffix_num']:
                        mat_prefix_candidates[base_name] = item_info_dict
                    # If current is higher suffix, it's ignored for now.
                    # If it has a different UUID than the existing_candidate, it won't overwrite unless chosen.
            else: # Not "mat_" prefixed material
                existing_entry = material_info_map.get(mat_uuid_for_map)
                if existing_entry: # UUID collision
                    # Prefer local over library if UUIDs happen to collide (should be rare with unique UUIDs)
                    if not item_info_dict['is_library'] and existing_entry['is_library']:
                        material_info_map[mat_uuid_for_map] = item_info_dict
                else: # No collision for this UUID yet
                    material_info_map[mat_uuid_for_map] = item_info_dict

        # Merge chosen "mat_" candidates into the main map, respecting UUID uniqueness
        # and local-over-library preference for UUID collisions.
        if not hide_mat_prefix_materials:
            for base_name, chosen_mat_info in mat_prefix_candidates.items():
                chosen_uuid = chosen_mat_info['uuid']
                existing_entry_in_map = material_info_map.get(chosen_uuid)
                if existing_entry_in_map: # This "mat_" item's UUID might already be in map (e.g., if it wasn't "mat_" before rename)
                    if not chosen_mat_info['is_library'] and existing_entry_in_map['is_library']:
                        material_info_map[chosen_uuid] = chosen_mat_info # Prefer local
                    # else, keep the existing one (e.g. if existing was non-"mat_" or also local "mat_")
                else: # No UUID collision, safe to add the chosen "mat_" item
                    material_info_map[chosen_uuid] = chosen_mat_info

        items_to_process_for_ui = list(material_info_map.values())

        # Apply "Show Only Local/Used" filter if active
        if filter_local_used_active:
            used_material_uuids_in_scene = set()
            for obj in bpy.data.objects: # Consider all objects, not just scene.objects
                if hasattr(obj, 'material_slots'):
                    for slot in obj.material_slots:
                        if slot.material:
                            slot_mat_uuid = get_material_uuid(slot.material)
                            if slot_mat_uuid:
                                used_material_uuids_in_scene.add(slot_mat_uuid)
            
            items_to_process_for_ui = [
                info_item for info_item in items_to_process_for_ui
                if not info_item['is_library'] or \
                   (info_item['is_library'] and info_item['uuid'] in used_material_uuids_in_scene)
            ]

        # Load timestamps for recency sorting
        material_timestamps = {}
        if not scene.material_list_sort_alpha: # Only load if sorting by recency
            try:
                with get_db_connection() as conn:
                    c = conn.cursor()
                    c.execute("SELECT uuid, ts FROM mat_time") # Assumes mat_time table exists
                    material_timestamps = {row[0]: row[1] for row in c.fetchall()}
            except Exception as e_ts:
                print(f"[Populate List] Error loading timestamps: {e_ts}")

        for info in items_to_process_for_ui: # Add timestamp to each item for sorting
            info['timestamp'] = material_timestamps.get(info['uuid'], 0) # Default to 0 if no timestamp

        # Sort the final list
        try:
            sort_key_func = (lambda item: item['display_name'].lower()) if scene.material_list_sort_alpha \
                else (lambda item: -item['timestamp']) # Negative for descending recency
            sorted_list_for_ui = sorted(items_to_process_for_ui, key=sort_key_func)
        except Exception as sort_error:
            print(f"[Populate List] Error sorting list: {sort_error}. Proceeding with current order.")
            sorted_list_for_ui = items_to_process_for_ui # Fallback

        # Add sorted items to the scene's material_list_items CollectionProperty
        items_added_to_ui_list_count = 0
        for item_data_final in sorted_list_for_ui:
            try:
                list_item = scene.material_list_items.add()
                list_item.material_name = item_data_final['display_name']
                list_item.material_uuid = item_data_final['uuid']
                list_item.is_library = item_data_final['is_library']
                list_item.original_name = item_data_final['original_name']
                list_item.is_protected = item_data_final['is_protected']
                # list_item.hash_dirty is not directly used by list item itself, but by save_handler
                items_added_to_ui_list_count += 1
            except Exception as add_error:
                print(f"[Populate List UI] Error adding item for UUID {item_data_final.get('uuid','N/A')}: {add_error}")

        print(f"[Populate List] Material list populated with {items_added_to_ui_list_count} items.")

        # Adjust active index if out of bounds
        if items_added_to_ui_list_count > 0:
            if scene.material_list_active_index >= items_added_to_ui_list_count:
                scene.material_list_active_index = items_added_to_ui_list_count - 1
            elif scene.material_list_active_index < 0 : # If it was -1 (empty list before)
                 scene.material_list_active_index = 0
        else: # List is empty
            scene.material_list_active_index = -1 # No valid index

        # Trigger thumbnail generation/check
        if not called_from_finalize_run:
            if 'update_material_thumbnails' in globals() and callable(update_material_thumbnails):
                # print(f"[Populate List] Calling update_material_thumbnails after list population.")
                update_material_thumbnails()

    except Exception as e:
        print(f"[Populate List] CRITICAL error during list population: {e}")
        traceback.print_exc()

def get_material_by_unique_id(unique_id): # Unchanged
    for mat in bpy.data.materials:
        if str(id(mat)) == unique_id: return mat
    return None

def initialize_db_connection_pool(): # MODIFIED
    # global material_names # No longer loads names here
    print("[DB Pool] Initializing database connection pool...", flush=True)
    try:
        # Ensure LIBRARY_FOLDER is valid before trying to use DATABASE_FILE
        if not LIBRARY_FOLDER or not os.path.isdir(LIBRARY_FOLDER):
            # Attempt to create it if _ADDON_DATA_ROOT is valid
            if _ADDON_DATA_ROOT and os.path.isdir(_ADDON_DATA_ROOT):
                os.makedirs(LIBRARY_FOLDER, exist_ok=True)
                print(f"[DB Pool] Created LIBRARY_FOLDER: {LIBRARY_FOLDER}")
            else:
                print(f"[DB Pool] CRITICAL: LIBRARY_FOLDER ('{LIBRARY_FOLDER}') is not a valid directory. Cannot initialize pool for '{DATABASE_FILE}'.")
                return # Cannot proceed if library folder isn't valid

        temp_connections = []
        for i in range(5): # Create 5 connections
            # Ensure DATABASE_FILE path is valid and directory exists
            db_dir = os.path.dirname(DATABASE_FILE)
            if not os.path.isdir(db_dir):
                print(f"[DB Pool] Database directory '{db_dir}' does not exist. Attempting to create.")
                os.makedirs(db_dir, exist_ok=True)

            conn = sqlite3.connect(DATABASE_FILE, check_same_thread=False, timeout=10) # Added timeout
            temp_connections.append(conn)
            # REMOVED: Initial read from material_names table

        for conn_obj in temp_connections:
            db_connections.put(conn_obj)
        print(f"[DB Pool] Pool initialized with {db_connections.qsize()} connections for '{os.path.basename(DATABASE_FILE)}'.", flush=True)
    except Exception as e:
        print(f"[DB Pool] Error initializing pool: {e}", flush=True)
        traceback.print_exc()

# --------------------------
# Event Handlers (save_handler and load_post_handler updated)
# --------------------------
@persistent
def save_handler(dummy):
    """
    Pre-save handler:
      * Implements "process once per save operation" logic.
      * Validates/creates UUIDs for ALL materials (including "mat_" prefixed ones by display name).
      * Ensures local non-"mat_" materials (by display name) are NAMED by their UUID *before file save*.
      * Ensures DB display name entry for non-"mat_" materials.
      * Always recalculates hash for local materials. If a local material's hash changes,
        its old thumbnail (if one existed for the old hash) is deleted.
      * **NEW**: Updates timestamp for materials with changed hashes.
      * Saves updated hashes/names to DB.
      * Queues library update.
    """
    global materials_modified, material_names, material_hashes

    if getattr(bpy.context.window_manager, 'matlist_save_handler_processed', False):
        print("[SAVE DB] Save handler already processed for this specific save operation. Skipping.")
        return
    bpy.context.window_manager.matlist_save_handler_processed = True

    print("\n[SAVE DB] Starting pre-save process (mat_ exclusion for RENAME only, targeted old thumb deletion & process-once)")

    needs_metadata_update = False # Flag if any UUID or name change happens
    needs_name_db_save = False    # Flag if material_names dict is updated
    timestamp_updated_for_recency = False # NEW: Flag if any timestamp was updated

    if not material_names and bpy.data.filepath:
        print("[SAVE DB] material_names dictionary empty, attempting load from DB...")
        load_material_names()

    print("[SAVE DB] Phase 1: Processing UUIDs, display names, and DATABLOCK RENAMES (mat_ exclusion for RENAME only)...")
    for mat in bpy.data.materials:
        if not mat: continue

        original_datablock_name = mat.name
        old_uuid_prop = mat.get("uuid", "")
        current_uuid_prop = validate_material_uuid(mat, is_copy=False)

        if current_uuid_prop != old_uuid_prop:
            needs_metadata_update = True
            print(f"[SAVE DB] UUID property assigned/changed for '{original_datablock_name}': '{old_uuid_prop}' -> '{current_uuid_prop}'")

        current_display_name_for_processing = "Unknown"
        try:
            current_display_name_for_processing = mat_get_display_name(mat)
        except Exception as e_get_display_save:
            print(f"[SAVE DB] Warning: Could not get display name for {getattr(mat, 'name', 'N/A')} during main processing: {e_get_display_save}. Proceeding with datablock name.")
            current_display_name_for_processing = mat.name

        if not current_display_name_for_processing.startswith("mat_"):
            if current_uuid_prop:
                if current_uuid_prop not in material_names:
                    initial_display_name_for_db = original_datablock_name
                    print(f"[SAVE DB] Adding new non-'mat_' material display name entry: UUID={current_uuid_prop}, Name='{initial_display_name_for_db}'")
                    material_names[current_uuid_prop] = initial_display_name_for_db
                    needs_name_db_save = True
                    needs_metadata_update = True
                if not mat.library and mat.name != current_uuid_prop:
                    print(f"[SAVE DB] Attempting to rename local non-'mat_' datablock '{mat.name}' to UUID '{current_uuid_prop}'...")
                    try:
                        existing_mat_with_target_name = bpy.data.materials.get(current_uuid_prop)
                        if not existing_mat_with_target_name or existing_mat_with_target_name == mat:
                            mat.name = current_uuid_prop
                            needs_metadata_update = True
                            print(f"[SAVE DB] Successfully renamed local non-'mat_' datablock '{original_datablock_name}' -> '{current_uuid_prop}'")
                        else:
                            print(f"[SAVE DB] WARNING: Cannot rename non-'mat_' '{original_datablock_name}' to UUID '{current_uuid_prop}'. Another material uses this name.")
                    except Exception as rename_err:
                        print(f"[SAVE DB] ERROR: Failed to rename non-'mat_' datablock '{original_datablock_name}' to UUID '{current_uuid_prop}': {rename_err}.")
            else:
                print(f"[SAVE DB] CRITICAL: Could not get or assign a valid UUID for non-'mat_' material '{original_datablock_name}'. Skipping DB name/rename.")

        if not mat.library:
            try:
                if not mat.use_fake_user:
                    mat.use_fake_user = True
                    print(f"[SAVE DB] Ensured use_fake_user=True for local material '{mat.name}'.")
            except Exception as e_fake:
                print(f"[SAVE DB] Warning: Could not set use_fake_user for local material '{mat.name}': {e_fake}")

    hashes_to_save_to_db = {}
    hashes_actually_changed_in_db = False
    load_material_hashes()

    print("[SAVE DB] Phase 2: Checking material hashes, updating timestamps, and deleting old thumbnails for modified local materials...")
    deleted_old_thumb_count = 0
    for mat in bpy.data.materials:
        if not mat: continue

        mat_name_debug = getattr(mat, 'name', 'N/A')
        actual_uuid_for_hash_storage = mat.get("uuid")

        if not actual_uuid_for_hash_storage:
            print(f"[SAVE DB] Warning: Material '{mat_name_debug}' missing 'uuid' property. Skipping hash check and old thumb deletion for it.")
            continue

        force_recalc_for_hash = not mat.library
        current_calculated_hash = get_material_hash(mat, force=force_recalc_for_hash)

        if not current_calculated_hash:
            print(f"[SAVE DB] Warning: Failed to calculate current hash for {mat_name_debug} (UUID: {actual_uuid_for_hash_storage}). Skipping hash update.")
            continue

        db_stored_hash = material_hashes.get(actual_uuid_for_hash_storage)

        if db_stored_hash != current_calculated_hash:
            hashes_to_save_to_db[actual_uuid_for_hash_storage] = current_calculated_hash
            if db_stored_hash is not None:
                hashes_actually_changed_in_db = True
                if not mat.library:
                    old_thumbnail_path = get_thumbnail_path(db_stored_hash)
                    try:
                        if os.path.isfile(old_thumbnail_path):
                            os.remove(old_thumbnail_path)
                            deleted_old_thumb_count += 1
                            print(f"[SAVE DB] Deleted old thumbnail '{os.path.basename(old_thumbnail_path)}' for modified material '{mat_name_debug}' (UUID: {actual_uuid_for_hash_storage}). Old hash: {db_stored_hash}, New hash: {current_calculated_hash}")
                    except Exception as e_del_thumb:
                        print(f"[SAVE DB] Error deleting old thumbnail {old_thumbnail_path}: {e_del_thumb}")
            
            # NEW: Update timestamp if hash changed (for recency sort)
            if 'update_material_timestamp' in globals() and callable(update_material_timestamp):
                print(f"[SAVE DB] Hash for material '{mat_name_debug}' (UUID: {actual_uuid_for_hash_storage}) changed/added. Updating timestamp.")
                update_material_timestamp(actual_uuid_for_hash_storage)
                timestamp_updated_for_recency = True
            else:
                print(f"[SAVE DB] WARNING: update_material_timestamp function not found. Cannot update timestamp for '{mat_name_debug}'.")


        if "hash_dirty" in mat:
            try: mat["hash_dirty"] = False
            except Exception: pass

    if deleted_old_thumb_count > 0:
        print(f"[SAVE DB] Total old thumbnails deleted due to material modifications: {deleted_old_thumb_count}")

    if needs_name_db_save:
        print("[SAVE DB] Saving updated material display names to database...")
        save_material_names()

    if hashes_to_save_to_db:
        material_hashes.update(hashes_to_save_to_db)
        print(f"[SAVE DB] Saving {len(hashes_to_save_to_db)} updated/new material hashes to database...")
        save_material_hashes()

    print("[SAVE DB] Phase 3: Determining if library update needed...")
    # Condition for forcing library update can be if hashes *actually changed in DB* or if important metadata changed
    if hashes_actually_changed_in_db or needs_metadata_update:
        print("[SAVE DB] Material hash values or metadata changed – queuing FORCED library update.")
        update_material_library(force_update=True)
    elif hashes_to_save_to_db or needs_name_db_save or timestamp_updated_for_recency: # If new hashes/names added or timestamp updated
        print("[SAVE DB] New hashes/names added or timestamps updated – queuing non-forced library update.")
        update_material_library(force_update=False)
    else:
        print("[SAVE DB] No changes detected requiring library update queue.")

    print("[SAVE DB] Pre-save handler complete.\n")
    materials_modified = False # Reset the flag from depsgraph

@persistent
def save_post_handler(dummy=None): # Unchanged from your version for its core tasks
    print("[DEBUG] save_post_handler: Starting post-save tasks.")
    scene = bpy.context.scene
    if not scene:
        # Fallback if bpy.context.scene is somehow None in this handler,
        # though it should generally be available.
        print("[DEBUG] save_post_handler: bpy.context.scene is None, falling back to get_first_scene().")
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

    # Reset the save handler flag here to ensure it's ready for the next distinct save operation
    if hasattr(bpy.context.window_manager, 'matlist_save_handler_processed'):
        bpy.context.window_manager.matlist_save_handler_processed = False
        print("[DEBUG save_post_handler] Reset save_handler 'processed' flag for next save.")

@persistent
def load_post_handler(dummy):
    print("[DEBUG LoadPost] load_post_handler: Start")
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_tasks_for_current_run, g_library_update_pending, g_current_run_task_hashes_being_processed


    if hasattr(bpy.context.window_manager, 'matlist_save_handler_processed'):
        bpy.context.window_manager.matlist_save_handler_processed = False
        # print("[DEBUG LoadPost] Reset save_handler 'processed' flag.")

    # --- AGGRESSIVE THUMBNAIL SYSTEM RESET FOR NEW FILE ---
    global thumbnail_monitor_timer_active, thumbnail_worker_pool, thumbnail_task_queue
    global thumbnail_pending_on_disk_check, thumbnail_generation_scheduled
    global persistent_icon_template_scene


    # print("[DEBUG LoadPost] Aggressively resetting thumbnail system state for new file...")

    if bpy.app.timers.is_registered(process_thumbnail_tasks):
        try:
            bpy.app.timers.unregister(process_thumbnail_tasks)
            # print("[DEBUG LoadPost] Unregistered existing thumbnail monitor timer.")
        except ValueError: pass # Timer was not registered
        except Exception as e_tmr_unreg_load:
            print(f"[DEBUG LoadPost] Error unregistering thumbnail timer: {e_tmr_unreg_load}")
    thumbnail_monitor_timer_active = False 

    if thumbnail_worker_pool: # Check if pool has entries
        # print(f"[DEBUG LoadPost] Terminating {len(thumbnail_worker_pool)} active thumbnail workers from previous file context...")
        for worker_info in list(thumbnail_worker_pool): # Iterate copy
            process = worker_info.get('process')
            if process and hasattr(process, 'poll') and process.poll() is None:
                try:
                    # print(f"  Terminating worker PID: {process.pid} for batch: {worker_info.get('hash_value', 'N/A_BATCH')[:8]}")
                    process.terminate()
                    process.wait(timeout=0.5) 
                    if process.poll() is None:
                        process.kill()
                        process.wait(timeout=0.2)
                except Exception as e_term:
                    print(f"  Error terminating worker (PID: {process.pid if hasattr(process,'pid') else 'N/A'}): {e_term}")
        thumbnail_worker_pool.clear()
        # print("[DEBUG LoadPost] Active worker pool cleared.")

    thumbnail_task_queue = Queue() # New, empty queue
    thumbnail_pending_on_disk_check.clear()
    thumbnail_generation_scheduled.clear()
    persistent_icon_template_scene = None # Reset cached template scene in main addon
    # print("[DEBUG LoadPost] Thumbnail task queue, tracking dicts, and cached template scene cleared.")
    
    # Reset batch processing globals
    g_thumbnail_process_ongoing = False
    g_material_creation_timestamp_at_process_start = 0.0
    g_tasks_for_current_run.clear()
    g_library_update_pending = False
    g_current_run_task_hashes_being_processed.clear()
    print("[DEBUG LoadPost] Thumbnail batch processing globals reset.")
    # --- END THUMBNAIL SYSTEM RESET ---


    # --- Clear Caches that should be file-specific (as before) ---
    global _display_name_cache, global_hash_cache, material_list_cache, material_names, material_hashes, list_version, _display_name_cache_version
    # print("[DEBUG LoadPost] Clearing file-specific caches: _display_name_cache, global_hash_cache, material_list_cache, material_names, material_hashes")
    _display_name_cache.clear()
    _display_name_cache_version = 0
    global_hash_cache.clear()
    material_list_cache.clear() 
    material_names.clear()
    material_hashes.clear()
    list_version = 0 # Reset UI list version as well


    if not bpy.app.timers.is_registered(delayed_load_post):
        bpy.app.timers.register(delayed_load_post, first_interval=0.3) 

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
    scene = get_first_scene(); # Get scene early
    if not scene:
        print("[DEBUG] delayed_load_post: No scene found, aborting.");
        return None

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
    if os.path.exists(LIBRARY_FILE):
        print("[DEBUG] delayed_load_post: Linking library materials...")
        try:
            library_path_norm = os.path.normcase(os.path.abspath(LIBRARY_FILE))
            existing_local_material_uuids = set()
            for local_mat_check in bpy.data.materials:
                if not local_mat_check.library: 
                    local_uuid_prop = local_mat_check.get("uuid")
                    if local_uuid_prop:
                        existing_local_material_uuids.add(local_uuid_prop)
            if existing_local_material_uuids:
                print(f"[DEBUG PostLink] Found existing local material UUIDs: {existing_local_material_uuids}")
            else:
                print(f"[DEBUG PostLink] No existing local materials with UUID properties found.")
            
            currently_linked_from_lib_by_uuid_prop = { 
                mat.get("uuid") for mat in bpy.data.materials
                if mat.library and hasattr(mat.library, 'filepath') and
                   os.path.normcase(bpy.path.abspath(mat.library.filepath)) == library_path_norm and
                   mat.get("uuid") 
            }
            if currently_linked_from_lib_by_uuid_prop:
                print(f"[DEBUG PostLink] Found materials ALREADY LINKED from this library (by UUID prop): {currently_linked_from_lib_by_uuid_prop}")

            with bpy.data.libraries.load(LIBRARY_FILE, link=True) as (data_from, data_to):
                if hasattr(data_from, 'materials') and data_from.materials:
                    mats_to_link_by_name = []
                    print(f"[DEBUG PostLink] Considering materials from library file ({LIBRARY_FILE}): {list(data_from.materials)}")
                    for lib_mat_name in data_from.materials:
                        uuid_of_material_in_library = lib_mat_name
                        if uuid_of_material_in_library in existing_local_material_uuids:
                            print(f"[DEBUG PostLink] SKIPPING link for '{lib_mat_name}': A local material with UUID '{uuid_of_material_in_library}' already exists.")
                            continue 
                        if uuid_of_material_in_library in currently_linked_from_lib_by_uuid_prop:
                            print(f"[DEBUG PostLink] SKIPPING link for '{lib_mat_name}': Already linked from this library (checked by UUID prop).")
                            continue 
                        local_material_with_same_name = bpy.data.materials.get(lib_mat_name)
                        if local_material_with_same_name and not local_material_with_same_name.library:
                            print(f"[DEBUG PostLink] SKIPPING link for '{lib_mat_name}': A local material with the same DATABLOCK NAME exists (and has no UUID prop or wasn't caught by previous UUID check).")
                            continue
                        mats_to_link_by_name.append(lib_mat_name)
                    if mats_to_link_by_name:
                        print(f"[DEBUG PostLink] Requesting link for names (after filtering): {mats_to_link_by_name}")
                        data_to.materials = mats_to_link_by_name
                    else:
                        print(f"[DEBUG PostLink] No materials left to link after filtering.")

            for mat in bpy.data.materials:
                if mat.library and hasattr(mat.library, 'filepath') and \
                   os.path.normcase(bpy.path.abspath(mat.library.filepath)) == library_path_norm:
                    base_uuid_from_datablock_name = mat.name.split('.')[0]
                    current_uuid_prop = mat.get("uuid")
                    if not current_uuid_prop:
                        try:
                            mat["uuid"] = base_uuid_from_datablock_name
                            print(f"[DEBUG PostLink] Set missing UUID custom property for linked '{mat.name}' to '{base_uuid_from_datablock_name}'.")
                        except Exception as e_set_uuid:
                            print(f"[DEBUG PostLink] Error setting UUID prop for linked '{mat.name}': {e_set_uuid}")
                    elif current_uuid_prop != base_uuid_from_datablock_name:
                        if len(current_uuid_prop) == 36 and current_uuid_prop != base_uuid_from_datablock_name:
                             print(f"[DEBUG PostLink] Warning: Linked mat '{mat.name}' has UUID prop '{current_uuid_prop}' "
                                   f"which differs from its datablock base name '{base_uuid_from_datablock_name}'. "
                                   f"Check consistency of material_library.blend.")
                        pass
        except Exception as e: print(f"[DEBUG] delayed_load_post: Error linking library materials: {e}"); traceback.print_exc()
    else: print(f"[DEBUG] delayed_load_post: Library file not found at {LIBRARY_FILE}.")

    # Initialize material properties (UUIDs, datablock names for local non-"mat_" materials)
    # This is crucial after initial file load and potential linking of library materials.
    # This is already being called per your logs for "New File" scenario.
    if 'initialize_material_properties' in globals() and callable(initialize_material_properties):
        print("[DEBUG delayed_load_post] Calling initialize_material_properties.")
        initialize_material_properties()
    else:
        print("[DEBUG delayed_load_post] ERROR: initialize_material_properties function not found!")

    # --- Key section for UI refresh and thumbnail initiation on ANY file load ---
    if 'populate_material_list' in globals() and callable(populate_material_list):
        print(f"[DEBUG delayed_load_post] Calling populate_material_list for scene '{scene.name}' on file load.")
        # The `called_from_finalize_run` flag will be False by default here,
        # so populate_material_list will call update_material_thumbnails.
        populate_material_list(scene)
    else:
        print("[DEBUG delayed_load_post] ERROR: populate_material_list function not found!")

    if 'force_redraw' in globals() and callable(force_redraw):
        print("[DEBUG delayed_load_post] Forcing redraw after populate_material_list.")
        force_redraw()
    # --- End key section ---

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
        global _display_name_cache, material_names # Ensure globals are accessible
        scene = context.scene
        idx = scene.material_list_active_index

        if not (0 <= idx < len(scene.material_list_items)):
            self.report({'WARNING'}, "No material selected or index out of bounds.")
            return {'CANCELLED'}

        selected_list_item = scene.material_list_items[idx]
        primary_material_uuid = selected_list_item.material_uuid # UUID of the material user wants to rename
        
        # Get the actual material object for the primary rename
        # It's important to use get_material_by_uuid as the datablock name might not be the UUID
        primary_mat_obj = get_material_by_uuid(primary_material_uuid)

        if not primary_mat_obj:
            self.report({'WARNING'}, f"Material for UUID '{primary_material_uuid}' not found in Blender data. List may be outdated.")
            populate_material_list(scene) # Refresh list if material is missing
            return {'CANCELLED'}

        new_display_name_str = self.new_name.strip()
        if not new_display_name_str:
            self.report({'WARNING'}, "Empty name not allowed.")
            return {'CANCELLED'}

        # Get the current display name of the primary material (the one being explicitly renamed)
        # This uses the mat_get_display_name helper which consults the material_names DB.
        current_primary_display_name = mat_get_display_name(primary_mat_obj)

        if new_display_name_str == current_primary_display_name:
            self.report({'INFO'}, "Display name is already set to that.")
            # Ensure the item remains selected after this "no-op"
            scene.material_list_active_index = idx
            return {'FINISHED'}

        # --- Start DB Update Logic for the selected material ---
        needs_db_names_save = False # Flag to track if material_names DB needs to be saved

        # 1. Update the primary material's display name in the material_names dictionary (in-memory)
        print(f"[Rename DB] Updating display name for primary UUID {primary_material_uuid} from '{current_primary_display_name}' to '{new_display_name_str}'")
        material_names[primary_material_uuid] = new_display_name_str
        needs_db_names_save = True
        
        # 2. Propagation Logic has been REMOVED as per your request.
        #    The display name change will now only apply to the selected material's UUID.

        # --- End DB Update Logic ---

        # 3. Save material_names to DB if any changes were made (primary name was changed)
        if needs_db_names_save:
            print("[Rename DB] Saving updated material display names to database.")
            save_material_names() # This saves the entire material_names dictionary

        # 4. Clear display name cache and refresh UI list to reflect all changes
        _display_name_cache.clear()
        populate_material_list(scene) # This will rebuild the list items based on new names from material_names
        
        # 5. Report results to the user
        report_message = f"Updated display name for selected material to '{new_display_name_str}'."
        self.report({'INFO'}, report_message)
        
        # Try to find the originally selected (primary) material in the newly populated list and select it
        new_idx_for_primary = -1
        for i, current_list_item_iter in enumerate(scene.material_list_items):
            if current_list_item_iter.material_uuid == primary_material_uuid:
                new_idx_for_primary = i
                break
        
        if new_idx_for_primary != -1:
            scene.material_list_active_index = new_idx_for_primary
            print(f"[Rename DB] Reselected primary renamed item '{new_display_name_str}' at new index {new_idx_for_primary}.")
        else:
            # Fallback if the primary item (somehow) isn't found after refresh.
            print(f"[Rename DB] Warning: Could not find primary item with UUID {primary_material_uuid} after renaming and list refresh. List may have changed significantly.")
            scene.material_list_active_index = 0 if len(scene.material_list_items) > 0 else -1
            
        return {'FINISHED'}

    def invoke(self, context, event):
        scene = context.scene
        idx = scene.material_list_active_index
        self.new_name = "" # Default to empty for the dialog

        if 0 <= idx < len(scene.material_list_items):
            item = scene.material_list_items[idx]
            # It's better to get the material object and then its display name
            # to ensure we're pre-filling with the most current display name.
            mat_obj = get_material_by_uuid(item.material_uuid)
            if mat_obj:
                self.new_name = mat_get_display_name(mat_obj)
            else: # Fallback if material object not found (e.g., list outdated)
                self.new_name = item.material_name 
        
        wm = context.window_manager
        return wm.invoke_props_dialog(self)
class MATERIALLIST_OT_duplicate_material(Operator):
    """Duplicate selected material as a new local material.
If original is from library, it's made local in the current file.
Textures use original file paths, not duplicated image files."""
    bl_idname = "materiallist.duplicate_material"
    bl_label = "Duplicate Selected Material (as Local)"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        scene = context.scene
        # Check if an item is selected in the list
        return scene and hasattr(scene, 'material_list_items') and \
               0 <= scene.material_list_active_index < len(scene.material_list_items)

    def execute(self, context):
        global material_names, _display_name_cache # Ensure global access
        scene = context.scene
        idx = scene.material_list_active_index
        
        if not (0 <= idx < len(scene.material_list_items)):
            self.report({'WARNING'}, "No material selected in the list.")
            return {'CANCELLED'}
            
        selected_list_item = scene.material_list_items[idx]
        original_mat_uuid_in_list = selected_list_item.material_uuid
        
        # Get the actual material datablock from Blender's data
        original_mat_datablock = get_material_by_uuid(original_mat_uuid_in_list)

        if not original_mat_datablock:
            self.report({'WARNING'}, f"Original material (UUID: {original_mat_uuid_in_list}) not found in current Blender data. List might be outdated.")
            populate_material_list(scene) # Refresh list
            return {'CANCELLED'}

        try:
            original_display_name = mat_get_display_name(original_mat_datablock)
            is_original_from_library_file = original_mat_datablock.library is not None

            # 1. Create the copy. 
            # If original_mat_datablock is from a library, .copy() makes it local to the current file.
            # If original_mat_datablock is local, .copy() creates another local one.
            new_mat = original_mat_datablock.copy()
            
            # new_mat.library will now be None, because it's a new datablock in the current file.
            # No need to explicitly set new_mat.library = None, which can cause errors if it's already None.

            # 2. Assign a new unique UUID to this new local material
            new_local_uuid = str(uuid.uuid4())
            new_mat["uuid"] = new_local_uuid
            
            # 3. Handle Textures: mat.copy() already ensures Image Texture nodes in new_mat
            # reference the same bpy.data.images datablocks (and thus same filepaths) as original_mat_datablock.
            # This fulfills "Use the original texture file, do not duplicate that."

            # 4. Set a display name for the new local material
            # Suggest a name based on the original, ensuring uniqueness
            new_display_name_base = original_display_name
            if is_original_from_library_file: # If duplicating from a library item
                suggested_suffix = "_local_copy"
            else: # If duplicating a local item
                suggested_suffix = ".copy"
            
            # Clean up potential multiple suffixes if any
            if new_display_name_base.endswith(suggested_suffix):
                 new_display_name_base = new_display_name_base[:-len(suggested_suffix)]
            if new_display_name_base.endswith(".copy"): # General cleanup
                 new_display_name_base = new_display_name_base[:-5]


            new_display_name = get_unique_display_name(f"{new_display_name_base}{suggested_suffix}")
            
            # 5. Set the Blender datablock name for the new material.
            # For non-"mat_" style materials, this is typically its UUID.
            # For "mat_" style, it would be its display name.
            # For simplicity and consistency with how local non-library materials are managed:
            prospective_datablock_name = new_local_uuid
            if bpy.data.materials.get(prospective_datablock_name) and \
               bpy.data.materials[prospective_datablock_name] != new_mat:
                # Extremely unlikely for a fresh UUID, but as a fallback:
                prospective_datablock_name = get_unique_display_name(new_display_name.replace(".", "_"))
                print(f"[Duplicate Mat] Warning: New UUID '{new_local_uuid}' was taken as a datablock name, using fallback '{prospective_datablock_name}'")
            new_mat.name = prospective_datablock_name


            # 6. Update addon's internal tracking and UI
            material_names[new_local_uuid] = new_display_name
            save_material_names() # Persist name changes
            _display_name_cache.clear() # Clear cache due to name change

            new_mat.use_fake_user = True # Ensure the new local material is saved with the current .blend file
            update_material_timestamp(new_local_uuid) # For recency sort, so it appears at the top

            populate_material_list(scene) # Refresh the UI list

            # Find and select the newly duplicated material in the list
            new_list_idx = -1
            for i, item_in_list in enumerate(scene.material_list_items):
                if item_in_list.material_uuid == new_local_uuid:
                    new_list_idx = i
                    break
            
            if new_list_idx != -1:
                scene.material_list_active_index = new_list_idx
            else: # Fallback if not found (should not happen if populate_material_list worked)
                scene.material_list_active_index = 0 if scene.material_list_items else -1
            
            self.report({'INFO'}, f"Duplicated '{original_display_name}' as local material '{new_display_name}'")

        except Exception as e:
            self.report({'ERROR'}, f"Failed to duplicate material: {str(e)}")
            traceback.print_exc()
            # Attempt to clean up the new_mat if it was created but an error occurred later
            if 'new_mat' in locals() and new_mat and new_mat.name in bpy.data.materials:
                # Check if it's the one we potentially made and if it has no users other than the default fake user
                if bpy.data.materials[new_mat.name] == new_mat and new_mat.users <= (1 if new_mat.use_fake_user else 0):
                    try:
                        bpy.data.materials.remove(new_mat)
                        print(f"[Duplicate Mat] Cleaned up partially created material '{new_mat.name_full}' due to error.")
                    except Exception as e_clean:
                        print(f"[Duplicate Mat] Error during cleanup of partially created material: {e_clean}")
            return {'CANCELLED'}
        
        return {'FINISHED'}

class MATERIALLIST_OT_pack_library_textures(Operator):
    """Pack all linkable data into the main library file"""
    bl_idname = "materiallist.pack_library_textures"
    bl_label = "Pack All Library Data"
    bl_description = "Packs all file dependencies (images, etc.) into material_library.blend (background process)"
    bl_options = {'REGISTER'}

    _timer = None
    _proc = None
    _temp_script_dir = None # To store the path for cleanup

    @classmethod
    def poll(cls, context):
        return LIBRARY_FILE and os.path.exists(LIBRARY_FILE)

    def modal(self, context, event):
        if event.type == 'TIMER':
            if self._proc and self._proc.poll() is not None: # Process finished
                if self._timer: # Ensure timer exists before removing
                    context.window_manager.event_timer_remove(self._timer)
                    self._timer = None
                
                stdout_output = self._proc.stdout.read().decode() if self._proc.stdout else "No stdout"
                stderr_output = self._proc.stderr.read().decode() if self._proc.stderr else "No stderr"

                if self._proc.returncode == 0:
                    self.report({'INFO'}, f"Library packing process completed for {os.path.basename(LIBRARY_FILE)}.")
                    print(f"[Pack Lib Data] Worker stdout:\n{stdout_output}")
                    if stderr_output.strip(): # Only print stderr if it's not empty
                        print(f"[Pack Lib Data] Worker stderr:\n{stderr_output}")
                else:
                    self.report({'ERROR'}, f"Library packing process failed. Code: {self._proc.returncode}. See console.")
                    print(f"[Pack Lib Data] Worker stdout:\n{stdout_output}")
                    print(f"[Pack Lib Data] Worker stderr:\n{stderr_output}")
                
                self._proc = None
                self._cleanup_temp_dir()
                return {'FINISHED'}
            return {'PASS_THROUGH'} # Still running

        if event.type == 'ESC':
            if self._timer:
                context.window_manager.event_timer_remove(self._timer)
                self._timer = None
            if self._proc and self._proc.poll() is None:
                self._proc.terminate()
                try:
                    self._proc.wait(timeout=1.0) # Give it a moment to terminate
                except subprocess.TimeoutExpired:
                    self._proc.kill() # Force kill if necessary
                self._proc = None
                self.report({'INFO'}, "Library packing cancelled by user.")
            self._cleanup_temp_dir()
            return {'CANCELLED'}
            
        return {'PASS_THROUGH'}

    def _cleanup_temp_dir(self):
        if self._temp_script_dir and os.path.exists(self._temp_script_dir):
            try:
                shutil.rmtree(self._temp_script_dir)
                print(f"[Pack Lib Data] Cleaned up temp script directory: {self._temp_script_dir}")
                self._temp_script_dir = None
            except Exception as e_clean:
                print(f"[Pack Lib Data] Warning: Could not remove temp script dir {self._temp_script_dir}: {e_clean}")

    def execute(self, context):
        # Create a unique temporary directory for this run's script
        self._temp_script_dir = tempfile.mkdtemp(prefix="pack_lib_script_")
        
        # Define the simple worker script content
        pack_script_content = f"""
import bpy
import os
import sys

print("--- Library Data Packing Script Started ---", flush=True)
try:
    if not bpy.data.filepath:
        print("ERROR: This script must be run on a saved .blend file (the library).", flush=True)
        bpy.ops.wm.quit_blender()
        sys.exit(1)

    print(f"Packing all data for: {{bpy.data.filepath}}", flush=True)
    bpy.ops.file.pack_all()
    print("bpy.ops.file.pack_all() executed.", flush=True)
    
    print(f"Saving library file: {{bpy.data.filepath}}", flush=True)
    bpy.ops.wm.save_mainfile()
    print("SUCCESS: Library saved after packing all data.", flush=True)
    
except Exception as e:
    print(f"ERROR in packing script: {{e}}", flush=True)
    import traceback
    traceback.print_exc()
    bpy.ops.wm.quit_blender()
    sys.exit(2)

print("--- Library Data Packing Script Finished ---", flush=True)
bpy.ops.wm.quit_blender()
sys.exit(0)
"""
        script_file_path = os.path.join(self._temp_script_dir, "pack_library_data_worker.py")
        
        try:
            with open(script_file_path, 'w') as f:
                f.write(pack_script_content)
            
            cmd = [
                bpy.app.binary_path,
                "--background",
                LIBRARY_FILE, # Load the library file directly
                "--python",
                script_file_path
            ]
            print(f"[Pack Lib Data] Executing: {' '.join(cmd)}")
            # Using Popen for non-blocking execution monitored by modal timer
            self._proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            
            # Start the modal timer to check for process completion
            self._timer = context.window_manager.event_timer_add(0.5, window=context.window)
            context.window_manager.modal_handler_add(self)
            
            self.report({'INFO'}, "Library data packing process started in background.")
            return {'RUNNING_MODAL'}

        except Exception as e:
            self.report({'ERROR'}, f"Failed to start packing process: {e}")
            traceback.print_exc()
            self._cleanup_temp_dir() # Clean up if execute fails before modal starts
            return {'CANCELLED'}

class MATERIALLIST_OT_scroll_to_top(Operator):
    """Scroll the material list to the top"""
    bl_idname = "materiallist.scroll_to_top"
    bl_label = "Scroll to Top"
    bl_options = {'REGISTER'}

    def execute(self, context):
        scene = context.scene
        if scene.material_list_items:
            scene.material_list_active_index = 0
            # Force redraw to ensure UI updates, as active_index change might not always trigger list scroll immediately
            force_redraw() 
            self.report({'INFO'}, "Scrolled to top of material list.")
        else:
            self.report({'INFO'}, "Material list is empty.")
        return {'FINISHED'}

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

class MATERIALLIST_OT_pack_textures_externally(bpy.types.Operator):
    bl_idname = "materiallist.pack_textures_externally"
    bl_label = "Projects: Localise & Unpack Lib Textures Externally"
    bl_description = (
        "For all relevant project files (from DB usage): makes materials originally from the central library local, "
        "then unpacks their textures to a specified subfolder relative to each project file. "
        "This MODIFIES MULTIPLE .BLEND FILES. Use with caution."
    )
    bl_options = {'REGISTER'}

    wait: bpy.props.BoolProperty(
        name="Wait for each worker to finish",
        description="Block Blender UI until each file's processing completes (sequential). Uncheck for parallel background processing (faster, less direct feedback).",
        default=True
    )
    
    _processes: list = [] 

    @classmethod
    def poll(cls, context):
        if not DATABASE_FILE or not os.path.exists(DATABASE_FILE):
            cls.poll_message_set("Addon database file not found.")
            return False
        if not BACKGROUND_WORKER_PY or not os.path.exists(BACKGROUND_WORKER_PY): 
            cls.poll_message_set("Background worker script (BACKGROUND_WORKER_PY) not found.")
            return False
        # Ensure the path is not empty. The UI panel provides the string.
        # The property itself is a StringProperty, so it holds the path selected by the user.
        if not context.scene.material_list_external_unpack_dir.strip():
            cls.poll_message_set("Set 'External Output Folder' in panel first.")
            return False
        return True

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self, width=450)

    def draw(self, context):
        layout = self.layout
        layout.label(text="This will process multiple project .blend files found in the database.", icon='ERROR')
        layout.label(text="In each file, materials from the central library will be made local.")
        layout.label(text="Their packed textures will be UNPACKED to the specified subfolder.")
        # Display the raw path from the scene property
        layout.label(text=f"Target Output Path: '{context.scene.material_list_external_unpack_dir.strip()}'")
        layout.separator()
        layout.label(text="This operation modifies original project files. Ensure backups exist.")
        layout.prop(self, "wait")

    def execute(self, context):
        # Get the path directly from the scene property. This path is set by Blender's DIR_PATH selector.
        # It will be an absolute path or a path starting with '//' if the user types that.
        external_output_path_for_worker = context.scene.material_list_external_unpack_dir.strip()
        
        # The primary check for an empty path should be in poll and UI.
        # If it's somehow empty here, it's an issue.
        if not external_output_path_for_worker:
            self.report({'ERROR'}, "External output path is empty. Please set it in the panel.")
            return {'CANCELLED'}

        # REMOVED SANITIZATION: The path from the DIR_PATH subtype property is already what we need.
        # The background worker (V2.3) is designed to handle absolute paths or '//' style paths correctly.
        # external_unpack_dir_name = "".join(c for c in external_unpack_dir_name_raw if c.isalnum() or c in ('_', '-', ' '))
        # external_unpack_dir_name = external_unpack_dir_name.strip().replace(" ", "_") 
        # The above lines were causing the issue.

        print(f"[PackExternal Op] User confirmed. Path for worker: '{external_output_path_for_worker}'")

        blend_paths_from_db = set()
        try:
            with get_db_connection() as conn:
                c = conn.cursor()
                c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='blend_material_usage'")
                if c.fetchone() is None: 
                    self.report({'ERROR'}, "Material usage table ('blend_material_usage') not found in database.")
                    return {'CANCELLED'}
                c.execute("SELECT DISTINCT blend_filepath FROM blend_material_usage")
                blend_paths_from_db = {os.path.abspath(row[0]) for row in c.fetchall() if row[0] and os.path.isabs(row[0])}
        except Exception as e: 
            self.report({'ERROR'}, f"Database error fetching file paths: {e}")
            traceback.print_exc()
            return {'CANCELLED'}

        if not blend_paths_from_db: 
            self.report({'INFO'}, "No project files recorded in the database as using library materials.")
            return {'FINISHED'}
        
        current_blend_file_abs = os.path.abspath(bpy.data.filepath) if bpy.data.filepath else None
        paths_to_process = []
        skipped_non_existent = 0
        skipped_current_file = 0

        for path_from_db in blend_paths_from_db:
            if not os.path.exists(path_from_db):
                print(f"[PackExternal Op] INFO: Skipping non-existent path from DB: {path_from_db}")
                skipped_non_existent += 1
                continue
            if current_blend_file_abs and os.path.normcase(path_from_db) == os.path.normcase(current_blend_file_abs):
                print(f"[PackExternal Op] INFO: Skipping currently open .blend file to avoid conflicts: {path_from_db}")
                skipped_current_file += 1
                continue
            paths_to_process.append(path_from_db)
        
        if skipped_non_existent > 0:
            self.report({'WARNING'}, f"Skipped {skipped_non_existent} non-existent paths found in database.")
        if skipped_current_file > 0:
             self.report({'INFO'}, f"Skipped processing the currently open .blend file.")

        if not paths_to_process: 
            self.report({'INFO'}, "No valid project files found to process after filtering.")
            return {'FINISHED'}

        # Report the path that will be used by the worker.
        self.report({'INFO'}, f"Starting 'Pack to External' for {len(paths_to_process)} project files. Output path: '{external_output_path_for_worker}'.")
        print(f"[PackExternal Op] Will process {len(paths_to_process)} files. Output path for worker: '{external_output_path_for_worker}'")

        MATERIALLIST_OT_pack_textures_externally._processes.clear()
        successful_launches_or_completions = 0
        failed_launches_or_completions = 0
        worker_script_path = BACKGROUND_WORKER_PY

        for i, target_blend_abs_path in enumerate(paths_to_process):
            if self.wait:
                self.report({'INFO'}, f"Processing file {i+1}/{len(paths_to_process)}: {os.path.basename(target_blend_abs_path)}")
            
            print(f"  [PackExternal Op] Launching worker for: {target_blend_abs_path}")

            cmd = [
                bpy.app.binary_path,
                "--background",
                "--factory-startup",
                target_blend_abs_path, 
                "--python", worker_script_path,
                "--", 
                "--operation", "pack_to_external",
                # Pass the direct, un-sanitized (or correctly user-provided) path to the worker.
                "--external-dir-name", external_output_path_for_worker, 
                "--library-file", os.path.abspath(LIBRARY_FILE)
            ]

            try:
                if self.wait:
                    print(f"    Executing (wait): {' '.join(cmd)}")
                    sys.stdout.flush() 
                    sys.stderr.flush()
                    
                    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace')
                    stdout_data, stderr_data = process.communicate(timeout=600) 

                    print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' STDOUT:")
                    for line in (stdout_data or "").splitlines(): print(f"      {line}") 
                    sys.stdout.flush()
                    print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' STDERR:")
                    for line in (stderr_data or "").splitlines(): print(f"      {line}") 
                    sys.stderr.flush()

                    if process.returncode == 0:
                        successful_launches_or_completions += 1
                        print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' completed successfully.")
                    else:
                        failed_launches_or_completions += 1
                        print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' FAILED with code {process.returncode}.")
                else: 
                    print(f"    Executing (no wait): {' '.join(cmd)}")
                    sys.stdout.flush()
                    sys.stderr.flush()
                    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace')
                    MATERIALLIST_OT_pack_textures_externally._processes.append(proc) 
                    successful_launches_or_completions += 1 
                    print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' launched (PID: {proc.pid}).")

            except subprocess.TimeoutExpired:
                failed_launches_or_completions +=1
                print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' TIMED OUT after 600 seconds.")
                if self.wait and 'process' in locals() and process.poll() is None: 
                    try: process.kill(); process.wait(timeout=1) 
                    except Exception: pass
            except Exception as e:
                failed_launches_or_completions += 1
                print(f"    ERROR launching/managing worker for '{os.path.basename(target_blend_abs_path)}': {e}")
                traceback.print_exc()
        
        final_report_type = 'INFO'
        if failed_launches_or_completions > 0: final_report_type = 'WARNING'
        if failed_launches_or_completions == len(paths_to_process) and paths_to_process: final_report_type = 'ERROR'

        status_msg = (f"Finished 'Pack to External'. Attempted: {len(paths_to_process)}. "
                      f"Successful launches/completions: {successful_launches_or_completions}. "
                      f"Failures/Errors: {failed_launches_or_completions}.")
        self.report({final_report_type}, status_msg)
        print(f"[PackExternal Op] {status_msg}")
        if not self.wait and MATERIALLIST_OT_pack_textures_externally._processes: 
             print(f"[PackExternal Op] {len(MATERIALLIST_OT_pack_textures_externally._processes)} workers launched in background. Check console for their individual outputs over time.")
        return {'FINISHED'}

class MATERIALLIST_OT_pack_textures_internally(bpy.types.Operator):
    bl_idname = "materiallist.pack_textures_internally"
    bl_label = "Projects: Localise & Pack Lib Textures Internally"
    bl_description = (
        "For all relevant project files (from DB usage): makes materials originally from the central library local, "
        "then packs their external textures directly into each project .blend file. "
        "This MODIFIES MULTIPLE .BLEND FILES. Use with caution."
    )
    bl_options = {'REGISTER'}

    wait: bpy.props.BoolProperty(
        name="Wait for each worker to finish",
        description="Block Blender UI until each file's processing completes (sequential). Uncheck for parallel background processing.",
        default=True
    )
    _processes: list = [] # Class variable to store non-waiting Popen objects

    @classmethod
    def poll(cls, context):
        if not DATABASE_FILE or not os.path.exists(DATABASE_FILE): 
            cls.poll_message_set("Addon database file not found."); return False
        if not BACKGROUND_WORKER_PY or not os.path.exists(BACKGROUND_WORKER_PY): # Ensure BACKGROUND_WORKER_PY is correct global
            cls.poll_message_set("Background worker script (BACKGROUND_WORKER_PY) not found."); return False
        return True

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self, width=400)

    def draw(self, context):
        layout = self.layout
        layout.label(text="This will process multiple project .blend files found in the database.", icon='ERROR')
        layout.label(text="In each file, materials from the central library will be made local.")
        layout.label(text="Their external textures will be PACKED INTO the project .blend file.")
        layout.separator()
        layout.label(text="This operation modifies original project files. Ensure backups exist.")
        layout.prop(self, "wait")

    def execute(self, context):
        print(f"[PackInternal Op] User confirmed.")
        blend_paths_from_db = set()
        try:
            with get_db_connection() as conn: # Assumes get_db_connection is defined
                c = conn.cursor()
                c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='blend_material_usage'")
                if c.fetchone() is None: 
                    self.report({'ERROR'}, "Material usage table ('blend_material_usage') not found in database.")
                    return {'CANCELLED'}
                c.execute("SELECT DISTINCT blend_filepath FROM blend_material_usage")
                blend_paths_from_db = {os.path.abspath(row[0]) for row in c.fetchall() if row[0] and os.path.isabs(row[0])}
        except Exception as e: 
            self.report({'ERROR'}, f"Database error fetching file paths: {e}")
            traceback.print_exc()
            return {'CANCELLED'}

        if not blend_paths_from_db: 
            self.report({'INFO'}, "No project files recorded in the database as using library materials.")
            return {'FINISHED'}

        current_blend_file_abs = os.path.abspath(bpy.data.filepath) if bpy.data.filepath else None
        paths_to_process = []
        skipped_non_existent = 0
        skipped_current_file = 0

        for path_from_db in blend_paths_from_db:
            if not os.path.exists(path_from_db):
                skipped_non_existent += 1; continue
            if current_blend_file_abs and os.path.normcase(path_from_db) == os.path.normcase(current_blend_file_abs):
                skipped_current_file += 1; continue
            paths_to_process.append(path_from_db)
        
        if skipped_non_existent > 0: self.report({'WARNING'}, f"Skipped {skipped_non_existent} non-existent DB paths.")
        if skipped_current_file > 0: self.report({'INFO'}, f"Skipped current .blend file.")
        if not paths_to_process: self.report({'INFO'}, "No valid project files to process."); return {'FINISHED'}

        self.report({'INFO'}, f"Starting 'Pack Internally' for {len(paths_to_process)} files.")
        print(f"[PackInternal Op] Will process {len(paths_to_process)} files.")
        MATERIALLIST_OT_pack_textures_internally._processes.clear() # Use correct class name
        successful_launches_or_completions, failed_launches_or_completions = 0, 0
        worker_script_path = BACKGROUND_WORKER_PY # Ensure this global is correctly set in register()

        for i, target_blend_abs_path in enumerate(paths_to_process):
            if self.wait: self.report({'INFO'}, f"Processing {i+1}/{len(paths_to_process)}: {os.path.basename(target_blend_abs_path)}")
            print(f"  [PackInternal Op] Launching worker for: {target_blend_abs_path}")
            cmd = [
                bpy.app.binary_path,
                "--background",
                "--factory-startup",  # <--- ADDED THIS FLAG
                target_blend_abs_path,
                "--python", worker_script_path,
                "--",
                "--operation", "pack_to_internal",
                "--library-file", os.path.abspath(LIBRARY_FILE)
            ]
            try:
                if self.wait:
                    print(f"    Executing (wait): {' '.join(cmd)}")
                    sys.stdout.flush()
                    sys.stderr.flush()

                    # Use Popen with communicate for waiting
                    process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace')
                    stdout_data, stderr_data = process.communicate(timeout=600) # Wait for process to complete, 10 min timeout

                    print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' STDOUT:")
                    for line in (stdout_data or "").splitlines(): print(f"      {line}") # Add (or "") for safety
                    sys.stdout.flush()
                    print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' STDERR:")
                    for line in (stderr_data or "").splitlines(): print(f"      {line}") # Add (or "") for safety
                    sys.stderr.flush()
                    
                    if process.returncode == 0:
                        successful_launches_or_completions += 1
                        print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' completed successfully.")
                    else:
                        failed_launches_or_completions += 1
                        print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' FAILED with code {process.returncode}.")
                else: # Not waiting
                    print(f"    Executing (no wait): {' '.join(cmd)}")
                    sys.stdout.flush()
                    sys.stderr.flush()
                    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace')
                    MATERIALLIST_OT_pack_textures_internally._processes.append(proc) # Use correct class name
                    successful_launches_or_completions += 1
                    print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' launched (PID: {proc.pid}).")

            except subprocess.TimeoutExpired:
                failed_launches_or_completions +=1
                print(f"    Worker for '{os.path.basename(target_blend_abs_path)}' TIMED OUT after 600 seconds.")
                if self.wait and 'process' in locals() and process.poll() is None: # Ensure process exists and is running if Popen was used
                    try: process.kill(); process.wait(timeout=1) # Clean up timed out process
                    except Exception: pass
            except Exception as e:
                failed_launches_or_completions += 1
                print(f"    ERROR launching/managing worker for '{os.path.basename(target_blend_abs_path)}': {e}")
                traceback.print_exc()
        
        final_report_type = 'INFO'
        if failed_launches_or_completions > 0: final_report_type = 'WARNING'
        if failed_launches_or_completions == len(paths_to_process) and paths_to_process: final_report_type = 'ERROR'
        status_msg = (f"Finished 'Pack Internally'. Attempted: {len(paths_to_process)}. "
                      f"Successes: {successful_launches_or_completions}. "
                      f"Failures: {failed_launches_or_completions}.")
        self.report({final_report_type}, status_msg)
        print(f"[PackInternal Op] {status_msg}")
        if not self.wait and MATERIALLIST_OT_pack_textures_internally._processes: # Use correct class name
             print(f"[PackInternal Op] Launched {len(MATERIALLIST_OT_pack_textures_internally._processes)} background workers. Check console for outputs.")
        return {'FINISHED'}

class MATERIALLIST_OT_trim_library(bpy.types.Operator):
    bl_idname = "materiallist.trim_library"
    bl_label = "Trim Central Library (Keep Recent 100)"
    bl_description = (
        "Keeps only the 100 most-recent materials in the central material_library.blend "
        "(based on addon DB timestamp). Others, AND THEIR PACKED TEXTURES WITHIN THE LIBRARY, are removed. "
        "Ensure projects are up-to-date first (e.g., using 'Localise & Unpack/Pack' tools)."
    )
    bl_options = {'REGISTER'}

    def invoke(self, context, event):
        return context.window_manager.invoke_props_dialog(self, width=450) 

    def draw(self, context):
        layout = self.layout
        layout.label(text="WARNING: This operation is destructive!", icon='ERROR')
        layout.separator()
        col = layout.column(align=True)
        col.label(text="This will permanently modify your central 'material_library.blend'.")
        col.label(text="It keeps only the ~100 most recently used/updated materials.")
        col.label(text="All other materials AND THEIR PACKED TEXTURES within the")
        col.label(text="library file will be DELETED from 'material_library.blend'.")
        layout.separator()
        col = layout.column(align=True)
        col.label(text="IMPORTANT:", icon='INFO')
        box = layout.box()
        box.label(text="Have project files been processed with 'Localise & Unpack'")
        box.label(text="or 'Localise & Pack' tools first?")
        box.label(text="If not, trimming might break texture links in projects if they")
        box.label(text="relied on textures packed *only* within the central library.")
        layout.separator()
        layout.label(text="It is STRONGLY recommended to backup 'material_library.blend' before proceeding.")
        layout.separator()
        layout.label(text="Are you sure you want to trim the central library?")

    def execute(self, context):
        print("[Trim Library Op] User confirmed. Proceeding with library trim.")
        
        to_keep_uuids = set()
        initial_mat_count_in_lib = 0
        rows_from_db = []

        try:
            with get_db_connection() as conn: 
                c = conn.cursor()
                c.execute("CREATE TABLE IF NOT EXISTS mat_time (uuid TEXT PRIMARY KEY, ts INTEGER)")
                c.execute("SELECT uuid FROM mat_time ORDER BY ts DESC LIMIT 100") # Get top 100 directly
                rows_from_db = c.fetchall()
                to_keep_uuids = {r[0] for r in rows_from_db}
        except Exception as e_db:
            self.report({'ERROR'}, f"Database error: {str(e_db)}"); traceback.print_exc(); return {'CANCELLED'}

        if not rows_from_db: # No timestamps, or table empty
            self.report({'WARNING'}, "No material timestamps in DB, or DB empty. Cannot trim based on recency. Library NOT modified.")
            return {'CANCELLED'}
        
        print(f"[Trim Library Op] Will attempt to keep {len(to_keep_uuids)} materials based on DB timestamps.")

        if not os.path.exists(LIBRARY_FILE):
            self.report({'INFO'}, "Central library file does not exist. Nothing to trim."); return {'FINISHED'}

        temp_dir = tempfile.mkdtemp(prefix="lib_trim_")
        temp_trimmed_lib_path = os.path.join(temp_dir, os.path.basename(LIBRARY_FILE))
        survivor_mats_for_write = set()
        loaded_survivor_names_for_cleanup = []

        try:
            with bpy.data.libraries.load(LIBRARY_FILE, link=False, assets_only=True) as (data_from, data_to):
                if not hasattr(data_from, 'materials'):
                    self.report({'INFO'}, "Library file contains no material data section."); shutil.rmtree(temp_dir); return {'FINISHED'}
                
                initial_mat_count_in_lib = len(data_from.materials)
                survivor_names_in_lib = [name for name in data_from.materials if name in to_keep_uuids]
                
                if survivor_names_in_lib:
                    data_to.materials = survivor_names_in_lib
                    loaded_survivor_names_for_cleanup.extend(survivor_names_in_lib) # For cleanup later
                else:
                    data_to.materials = []
            
            for mat_name_survivor in loaded_survivor_names_for_cleanup:
                mat_obj = bpy.data.materials.get(mat_name_survivor)
                if mat_obj and not mat_obj.library: # Is a local copy we just loaded
                    mat_obj.use_fake_user = True
                    survivor_mats_for_write.add(mat_obj)
            
            print(f"[Trim Library Op] Writing {len(survivor_mats_for_write)} survivors to temp: {temp_trimmed_lib_path}")
            bpy.data.libraries.write(temp_trimmed_lib_path, survivor_mats_for_write, fake_user=True, compress=True)
            
            shutil.move(temp_trimmed_lib_path, LIBRARY_FILE)
            temp_trimmed_lib_path = None # Mark as moved

            removed_actual = initial_mat_count_in_lib - len(survivor_mats_for_write)
            self.report({'INFO'}, f"Library trimmed. Kept: {len(survivor_mats_for_write)}. Removed: {removed_actual} entries.")

        except Exception as e_trim_main:
            self.report({'ERROR'}, f"Error during library trim: {str(e_trim_main)}"); traceback.print_exc(); return {'CANCELLED'}
        finally:
            # Cleanup materials loaded into current session for the operation
            for name in loaded_survivor_names_for_cleanup:
                mat = bpy.data.materials.get(name)
                if mat and not mat.library and mat.users == 0 : # Only if it has no users after our write
                    try: bpy.data.materials.remove(mat)
                    except Exception: pass # Ignore if removal fails (e.g. still has users)
            
            if temp_trimmed_lib_path and os.path.exists(temp_trimmed_lib_path):
                try: os.remove(temp_trimmed_lib_path) # If move failed
                except Exception: pass
            if os.path.exists(temp_dir):
                try: shutil.rmtree(temp_dir)
                except Exception: pass
        
        populate_material_list(context.scene) # Assuming this function exists
        force_redraw() # Assuming this function exists
        return {'FINISHED'}

class MATERIALLIST_OT_select_dominant(Operator):
    bl_idname = "materiallist.select_dominant"
    bl_label = "Select Dominant Material"
    bl_description = ("On the active object, find the material used by the largest number of faces and select it in the list.")
    @classmethod
    def poll(cls, context): ob = context.active_object; return ob and ob.type == 'MESH'
    def execute(self, context):
        ob = context.active_object; me = ob.data
        if not me.materials: self.report({'WARNING'}, "Object has no materials."); return {'CANCELLED'}
        counts = {}; bm = bmesh.new(); bm.from_mesh(me)
        for f in bm.faces: counts[f.material_index] = counts.get(f.material_index, 0) + 1
        bm.free()
        if not counts: self.report({'WARNING'}, "No face material assignments."); return {'CANCELLED'}
        dominant_idx = max(counts, key=counts.get)
        dominant_mat = me.materials[dominant_idx]
        if not dominant_mat: self.report({'WARNING'}, "Dominant slot has no material."); return {'CANCELLED'}
        scene = context.scene
        # Use get_material_uuid to find the correct item in the list, as dominant_mat.name might be display name if not UUID named
        dominant_uuid = get_material_uuid(dominant_mat)
        for i, itm in enumerate(scene.material_list_items):
            if itm.material_uuid == dominant_uuid: # Compare UUIDs
                scene.material_list_active_index = i; break
        self.report({'INFO'}, f"Selected '{mat_get_display_name(dominant_mat)}'")
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
    global persistent_icon_template_scene, THUMBNAIL_SIZE
    template_scene_name_in_file = "IconTemplateScene"

    if os.path.exists(ICON_TEMPLATE_FILE):
        try:
            print(f"[IconTemplate Ensure - QuickVerify] Checking existing template '{ICON_TEMPLATE_FILE}' for scene '{template_scene_name_in_file}'.")
            # MODIFIED: Use assets_only=False for robust scene name checking
            with bpy.data.libraries.load(ICON_TEMPLATE_FILE, link=False, assets_only=False) as (data_from, _):
                # When assets_only=False and link=False, data_from.scenes is a list of scene names.
                available_scene_names = list(getattr(data_from, "scenes", []))
                print(f"[IconTemplate Ensure - QuickVerify] Scene names found in existing template (assets_only=False): {available_scene_names}")
                if template_scene_name_in_file in available_scene_names:
                    print(f"[IconTemplate Ensure - QuickVerify] SUCCESS: Scene '{template_scene_name_in_file}' found. Template is OK.")
                    return True
                else:
                    print(f"[IconTemplate Ensure - QuickVerify] FAILURE: Scene '{template_scene_name_in_file}' NOT found. Rebuilding.")
        except Exception as e_quick_verify:
            print(f"[IconTemplate Ensure - QuickVerify] ERROR quick-verifying existing template '{ICON_TEMPLATE_FILE}': {e_quick_verify}. Rebuilding.")
            traceback.print_exc()

        try:
            os.remove(ICON_TEMPLATE_FILE)
            print(f"[IconTemplate Ensure] Removed existing invalid/corrupt template file: {ICON_TEMPLATE_FILE}")
        except Exception as e_remove_old:
            print(f"[IconTemplate Ensure] Failed to remove existing invalid template file '{ICON_TEMPLATE_FILE}': {e_remove_old}. Creation might fail.")


    print(f"[IconTemplate Ensure] Creating icon generation template at: {ICON_TEMPLATE_FILE}")

    persistent_icon_template_scene = None  # Reset cache if we're recreating

    preview_obj_name = "IconPreviewObject"
    preview_mesh_data_name = "IconPreviewMesh_Data"
    camera_obj_name = "IconTemplateCam"
    camera_data_name = "IconTemplateCam_Data"
    light_obj_name = "IconTemplateLight"
    light_data_name = "IconTemplateLight_Data"

    temp_setup_scene_name = f"IconTemplate_TEMP_SETUP_{str(uuid.uuid4())[:8]}"
    temp_setup_scene = None
    scene_to_save_in_template = None
    created_data_blocks_for_template_file = []  # Store references to all created data

    try:
        # --- BEGIN CRITICAL PRE-CLEANUP of conflicting datablocks ---
        for obj_name_to_clear in [preview_obj_name, camera_obj_name, light_obj_name]:
            if obj_name_to_clear in bpy.data.objects:
                obj_to_remove = bpy.data.objects[obj_name_to_clear]
                print(f"[IconTemplate Ensure] Pre-cleanup: Removing existing object '{obj_name_to_clear}'.")
                try:
                    # Ensure no users before removing data if this object is the only user
                    if obj_to_remove.data and obj_to_remove.data.users == 1:
                        data_to_remove_internally = obj_to_remove.data
                        obj_to_remove.data = None # Unlink data from object
                        if data_to_remove_internally.name in bpy.data.meshes or \
                           data_to_remove_internally.name in bpy.data.cameras or \
                           data_to_remove_internally.name in bpy.data.lights:
                            if isinstance(data_to_remove_internally, bpy.types.Mesh) and data_to_remove_internally.name in bpy.data.meshes:
                                bpy.data.meshes.remove(data_to_remove_internally)
                            elif isinstance(data_to_remove_internally, bpy.types.Camera) and data_to_remove_internally.name in bpy.data.cameras:
                                bpy.data.cameras.remove(data_to_remove_internally)
                            elif isinstance(data_to_remove_internally, bpy.types.Light) and data_to_remove_internally.name in bpy.data.lights:
                                bpy.data.lights.remove(data_to_remove_internally)
                    bpy.data.objects.remove(obj_to_remove, do_unlink=True)
                except Exception as e:
                    print(f"[IconTemplate Ensure] Error pre-cleaning object '{obj_name_to_clear}': {e}")

        for data_name_to_clear, data_collection in [
            (preview_mesh_data_name, bpy.data.meshes),
            (camera_data_name, bpy.data.cameras),
            (light_data_name, bpy.data.lights)
        ]:
            if data_name_to_clear in data_collection:
                data_block_to_remove = data_collection[data_name_to_clear]
                if data_block_to_remove.users == 0:
                    print(f"[IconTemplate Ensure] Pre-cleanup: Removing existing data block '{data_name_to_clear}' (0 users).")
                    try:
                        data_collection.remove(data_block_to_remove)
                    except Exception as e:
                        print(f"[IconTemplate Ensure] Error pre-cleaning data '{data_name_to_clear}': {e}")
                else:
                    print(f"[IconTemplate Ensure] Pre-cleanup: Data block '{data_name_to_clear}' has users ({data_block_to_remove.users}), cannot remove directly. Will be handled by object removal if sole user.")

        scene_to_remove_name_check = template_scene_name_in_file
        while scene_to_remove_name_check in bpy.data.scenes:
            scene_obj_to_remove = bpy.data.scenes[scene_to_remove_name_check]
            print(f"[IconTemplate Ensure] Pre-cleanup: Attempting to remove existing scene '{scene_obj_to_remove.name}'. Target name for template is '{template_scene_name_in_file}'.")
            active_scene_switched = False
            for window_iter in bpy.context.window_manager.windows:
                if window_iter.scene == scene_obj_to_remove:
                    other_scene_to_activate = next((s for s in bpy.data.scenes if s != scene_obj_to_remove), None)
                    if other_scene_to_activate:
                        window_iter.scene = other_scene_to_activate
                        active_scene_switched = True
                        print(f"[IconTemplate Ensure]   Switched window '{window_iter}' to scene '{other_scene_to_activate.name}'.")
                    else:
                        print(f"[IconTemplate Ensure]   Warning: Cannot switch window '{window_iter}' from scene '{scene_obj_to_remove.name}', no other scene available yet.")
            try:
                bpy.data.scenes.remove(scene_obj_to_remove)
                print(f"[IconTemplate Ensure]   Pre-cleanup: Successfully removed scene '{scene_to_remove_name_check}'.")
            except Exception as e_remove_scene_robust:
                print(f"[IconTemplate Ensure]   Error during pre-cleanup of scene '{scene_to_remove_name_check}': {e_remove_scene_robust}. Template creation may result in a suffixed scene name.")
                break

        # --- END CRITICAL PRE-CLEANUP ---

        temp_setup_scene = bpy.data.scenes.new(temp_setup_scene_name)
        if not temp_setup_scene:
            print("[IconTemplate Ensure] CRITICAL: Failed to create temporary setup scene for context.")
            return False

        mesh_data = bpy.data.meshes.new(preview_mesh_data_name)
        bm = bmesh.new()
        bmesh.ops.create_uvsphere(bm, u_segments=32, v_segments=16, radius=0.8)
        uv_layer = bm.loops.layers.uv.verify() or bm.loops.layers.uv.new("UVMap")
        if uv_layer:
            for face in bm.faces:
                for loop in face.loops:
                    loop_uv = loop[uv_layer]
                    norm_co = loop.vert.co.normalized()
                    loop_uv.uv = (
                        (math.atan2(norm_co.y, norm_co.x) / (2 * math.pi)) + 0.5,
                        (math.asin(norm_co.z) / math.pi) + 0.5
                    )
        bm.to_mesh(mesh_data)
        bm.free()
        created_data_blocks_for_template_file.append(mesh_data)

        cam_data = bpy.data.cameras.new(camera_data_name)
        created_data_blocks_for_template_file.append(cam_data)

        light_data = bpy.data.lights.new(light_data_name, type='POINT')
        # Don't set energy yet
        created_data_blocks_for_template_file.append(light_data)

        preview_obj = bpy.data.objects.new(preview_obj_name, mesh_data)
        created_data_blocks_for_template_file.append(preview_obj)

        cam_obj = bpy.data.objects.new(camera_obj_name, cam_data)
        cam_obj.location = (1.7, -1.7, 1.4)
        cam_obj.rotation_euler = (math.radians(60), 0, math.radians(45))
        created_data_blocks_for_template_file.append(cam_obj)

        light_obj = bpy.data.objects.new(light_obj_name, light_data)
        light_obj.location = (0.15, -2.0, 1.3)
        created_data_blocks_for_template_file.append(light_obj)

        print(f"[IconTemplate Ensure] Creating scene for template file with target name: '{template_scene_name_in_file}'")
        scene_to_save_in_template = bpy.data.scenes.new(template_scene_name_in_file)
        if not scene_to_save_in_template:
            print(f"[IconTemplate Ensure] CRITICAL: Failed to create target template scene with name '{template_scene_name_in_file}'.")
            raise RuntimeError(f"Failed to create target template scene '{template_scene_name_in_file}'.")

        print(f"[IconTemplate Ensure] Scene created with actual name: '{scene_to_save_in_template.name}'. Intended: '{template_scene_name_in_file}'.")
        if scene_to_save_in_template.name != template_scene_name_in_file:
            print(f"[IconTemplate Ensure] CRITICAL WARNING: Created scene name '{scene_to_save_in_template.name}' "
                  f"does not match target '{template_scene_name_in_file}'. This will likely cause worker failure. "
                  "Check pre-cleanup logs for scene removal issues.")
            raise RuntimeError(f"Template scene created with incorrect name: {scene_to_save_in_template.name} vs target {template_scene_name_in_file}")

        scene_to_save_in_template.collection.objects.link(preview_obj)
        scene_to_save_in_template.collection.objects.link(cam_obj)
        scene_to_save_in_template.collection.objects.link(light_obj)
        scene_to_save_in_template.camera = cam_obj

        try:
            light_data.energy = 240
            print(f"[IconTemplate Ensure] Set light_data.energy = {light_data.energy} after linking object.")
        except AttributeError as e_energy:
            print(f"[IconTemplate Ensure] CRITICAL ERROR setting light energy even after linking: {e_energy}")
            traceback.print_exc()
            raise
        except Exception as e_generic_energy: # Catch any other exception during energy setting
            print(f"[IconTemplate Ensure] CRITICAL GENERIC ERROR setting light energy: {e_generic_energy}")
            traceback.print_exc()
            raise

        try:
            current_engine_options = bpy.context.scene.render.bl_rna.properties['engine'].enum_items.keys()
            if 'BLENDER_EEVEE_NEXT' in current_engine_options:
                scene_to_save_in_template.render.engine = 'BLENDER_EEVEE_NEXT'
            else:
                scene_to_save_in_template.render.engine = 'BLENDER_EEVEE'
        except Exception:
            scene_to_save_in_template.render.engine = 'BLENDER_EEVEE'  # Fallback

        print(f"[IconTemplate Ensure] Template scene render engine set to: {scene_to_save_in_template.render.engine}")
        scene_to_save_in_template.render.resolution_x = THUMBNAIL_SIZE
        scene_to_save_in_template.render.resolution_y = THUMBNAIL_SIZE
        scene_to_save_in_template.render.film_transparent = True

        eevee_settings = getattr(scene_to_save_in_template, scene_to_save_in_template.render.engine.lower(), None)
        if not eevee_settings and hasattr(scene_to_save_in_template.render, 'eevee'):
            eevee_settings = scene_to_save_in_template.render.eevee

        if eevee_settings:
            if hasattr(eevee_settings, 'taa_render_samples'):
                eevee_settings.taa_render_samples = 16
            elif hasattr(eevee_settings, 'samples'): # For older Eevee
                eevee_settings.samples = 16

        # CRITICAL: Add the scene and its collection to the list of items to be written
        created_data_blocks_for_template_file.append(scene_to_save_in_template)
        created_data_blocks_for_template_file.append(scene_to_save_in_template.collection)

        temp_dir_for_blend_save = tempfile.mkdtemp(prefix="icon_template_blend_")
        temp_blend_path = os.path.join(temp_dir_for_blend_save, os.path.basename(ICON_TEMPLATE_FILE))

        valid_blocks_to_write = set()
        for block in created_data_blocks_for_template_file:
            if block and hasattr(block, 'name') and block.name:
                valid_blocks_to_write.add(block)
            else:
                print(f"[IconTemplate Ensure] Warning: Skipping invalid/unnamed block for write: {block} (Type: {type(block)})")

        if not valid_blocks_to_write:
            print("[IconTemplate Ensure] CRITICAL: No valid data blocks collected for writing to template.")
            raise RuntimeError("No valid data blocks for template file.")

        print(f"[IconTemplate Ensure] Writing {len(valid_blocks_to_write)} blocks (incl. scene '{scene_to_save_in_template.name}') to temp .blend: {temp_blend_path}")
        # for block_to_log in sorted(list(valid_blocks_to_write), key=lambda b: b.name if hasattr(b,'name') and b.name else str(type(b))):
        #     print(f"  Preparing to write block: {getattr(block_to_log, 'name', 'UnnamedBlock')} (Type: {type(block_to_log)})")

        bpy.data.libraries.write(temp_blend_path, {scene_to_save_in_template}, fake_user=True, compress=True)

        # --- IMMEDIATE VERIFICATION of the temporary .blend file ---
        print(f"[IconTemplate Ensure - PostWriteVerify] Verifying temporary template file: {temp_blend_path}")
        has_scene_in_temp_file = False
        try:
            # MODIFIED: Use assets_only=False for robust scene name checking
            with bpy.data.libraries.load(temp_blend_path, link=False, assets_only=False) as (data_from_temp_check, _):
                # When assets_only=False and link=False, data_from.scenes is a list of scene names.
                available_scenes_in_temp_names = list(getattr(data_from_temp_check, "scenes", []))
                print(f"[IconTemplate Ensure - PostWriteVerify (assets_only=False)] Available scene names in temp file: {available_scenes_in_temp_names}")
                if template_scene_name_in_file in available_scenes_in_temp_names:
                    has_scene_in_temp_file = True
                    print(f"[IconTemplate Ensure - PostWriteVerify (assets_only=False)]   SUCCESS: Temporary template file '{os.path.basename(temp_blend_path)}' lists scene '{template_scene_name_in_file}'.")
                else:
                    print(f"[IconTemplate Ensure - PostWriteVerify (assets_only=False)]   FAILURE: Temporary template file '{os.path.basename(temp_blend_path)}' DOES NOT list scene '{template_scene_name_in_file}'.")
        except Exception as e_verify_temp_file:
            print(f"[IconTemplate Ensure - PostWriteVerify (assets_only=False)]   ERROR during verification of temporary template file: {e_verify_temp_file}")
            traceback.print_exc()

        if not has_scene_in_temp_file:
            print("[IconTemplate Ensure] CRITICAL POST-WRITE FAILURE: The temporary template .blend file is invalid (missing target scene). Aborting template finalization.")# Cleanup the temp directory
            if os.path.exists(temp_dir_for_blend_save):
                shutil.rmtree(temp_dir_for_blend_save, ignore_errors=True)
            # No need to clean up session datablocks here as the main exception handler will do it.
            raise RuntimeError("Failed to write a valid temporary template file.")
        # --- END IMMEDIATE VERIFICATION ---

        os.makedirs(os.path.dirname(ICON_TEMPLATE_FILE), exist_ok=True)
        shutil.move(temp_blend_path, ICON_TEMPLATE_FILE)
        print(f"[IconTemplate Ensure] Template file created successfully and verified: {ICON_TEMPLATE_FILE}")

        if os.path.exists(temp_dir_for_blend_save): # Should be empty now if move succeeded
            shutil.rmtree(temp_dir_for_blend_save, ignore_errors=True)
        return True

    except Exception as e:
        print(f"[IconTemplate Ensure] CRITICAL ERROR during template file creation: {e}")
        traceback.print_exc()
        # Cleanup of data blocks created in *this attempt* if an error occurred
        print("[IconTemplate Ensure] Cleaning up data blocks created in this failed attempt...")
        for block in reversed(created_data_blocks_for_template_file): # Reverse order for dependencies
            if block and hasattr(block, 'name') and block.name:
                block_name_for_cleanup = block.name
                try:
                    if isinstance(block, bpy.types.Object) and block_name_for_cleanup in bpy.data.objects:
                        bpy.data.objects.remove(bpy.data.objects[block_name_for_cleanup], do_unlink=True)
                    elif isinstance(block, bpy.types.Mesh) and block_name_for_cleanup in bpy.data.meshes:
                        bpy.data.meshes.remove(bpy.data.meshes[block_name_for_cleanup])
                    elif isinstance(block, bpy.types.Camera) and block_name_for_cleanup in bpy.data.cameras:
                        bpy.data.cameras.remove(bpy.data.cameras[block_name_for_cleanup])
                    elif isinstance(block, bpy.types.Light) and block_name_for_cleanup in bpy.data.lights:
                        bpy.data.lights.remove(bpy.data.lights[block_name_for_cleanup])
                    elif isinstance(block, bpy.types.Scene) and block_name_for_cleanup in bpy.data.scenes:
                         # Be careful removing scenes if they are active or last one
                        if len(bpy.data.scenes) > 1 and bpy.context.window and bpy.context.window.scene != block:
                             bpy.data.scenes.remove(bpy.data.scenes[block_name_for_cleanup])
                        elif len(bpy.data.scenes) == 1 and block_name_for_cleanup in bpy.data.scenes : # It's the only scene, can't remove
                            print(f"[IconTemplate Ensure] Cannot remove scene '{block_name_for_cleanup}', it's the only one.")
                        else: # It might be active in a window
                            print(f"[IconTemplate Ensure] Cannot remove scene '{block_name_for_cleanup}', might be active or only one.")
                    elif isinstance(block, bpy.types.Collection) and block_name_for_cleanup in bpy.data.collections:
                        bpy.data.collections.remove(bpy.data.collections[block_name_for_cleanup])
                except Exception as e_cleanup_block_on_fail:
                    print(f"[IconTemplate Ensure] Error cleaning up block '{block_name_for_cleanup}' on failure: {e_cleanup_block_on_fail}")
        return False
    finally:
        # Clean up the temporary setup scene (not the one intended for saving)
        if temp_setup_scene and temp_setup_scene.name in bpy.data.scenes:
            try:
                # Ensure it's not the active scene in any window before removing
                is_active_in_window = False
                if bpy.context.window: # Check if context has a window (might not in some script execution scenarios)
                    for window_iter in bpy.context.window_manager.windows:
                        if window_iter.scene == temp_setup_scene:
                            is_active_in_window = True
                            break

                if len(bpy.data.scenes) > 1 and not is_active_in_window :
                    bpy.data.scenes.remove(temp_setup_scene)
                elif len(bpy.data.scenes) == 1: # It's the only scene
                    print(f"[IconTemplate Ensure] Not removing temp_setup_scene '{temp_setup_scene_name}' as it's the only scene left.")
                else: # It's active in a window or some other reason prevents removal
                    print(f"[IconTemplate Ensure] Not removing temp_setup_scene '{temp_setup_scene_name}', it might be active or other issue.")

            except Exception as e_clean_setup:
                print(f"[IconTemplate Ensure] Error cleaning up temporary setup scene '{temp_setup_scene_name}': {e_clean_setup}")

def force_update_preview(mat):
    if not mat:
        print(f"FUP: Material object is None. Cannot update preview.") # FUP for ForceUpdatePreview
        return

    # Determine material properties for logging before any operations
    mat_name_for_log = "UnknownMaterial"
    try:
        mat_name_for_log = mat.name
    except ReferenceError: # Material might have been deleted
        print(f"FUP: Material '{mat_name_for_log}' (ref error) is invalid. Cannot update preview.")
        return

    is_lib = mat.library is not None # Explicit boolean check
    library_filepath_for_log = "N/A"
    if is_lib and mat.library: # Ensure mat.library itself isn't None before accessing filepath
        library_filepath_for_log = getattr(mat.library, 'filepath', 'N/A (Library object has no filepath attr)')

    print(f"FUP: Called for '{mat_name_for_log}'. Is Library: {is_lib}. Lib File: {library_filepath_for_log}")

    try:
        if not is_lib:
            print(f"FUP: Path for LOCAL material '{mat_name_for_log}'. Attempting to reset preview.")
            # For local materials, we can try to force a preview refresh
            mat.preview = None # This line is suspected if the error occurs for a material that IS a library type

            if hasattr(mat, "preview_render_type"):
                current_type = mat.preview_render_type
                # print(f"FUP: Local mat '{mat_name_for_log}' - current preview_render_type: {current_type}")
                mat.preview_render_type = 'FLAT'
                # print(f"FUP: Local mat '{mat_name_for_log}' - set preview_render_type to FLAT")
                # Schedule restoration back to original, which triggers another refresh
                bpy.app.timers.register(lambda: restore_render_type(mat, current_type), first_interval=0.05)
            else:
                # print(f"FUP: Local mat '{mat_name_for_log}' - calling preview_ensure() as fallback.")
                mat.preview_ensure() # Fallback if preview_render_type not available
            print(f"FUP: Local material '{mat_name_for_log}' preview reset/ensure called.")

        elif is_lib: # Explicitly elif for library materials
            if hasattr(mat, 'preview_ensure'):
                print(f"FUP: Path for LIBRARY material '{mat_name_for_log}'. Calling preview_ensure().")
                mat.preview_ensure()
            else: # Should not happen for valid materials
                print(f"FUP: LIBRARY material '{mat_name_for_log}' does not have preview_ensure attribute.")

        # No else needed, covers both cases.

    except ReferenceError: # Catch if 'mat' becomes invalid during processing
        print(f"FUP: ERROR - ReferenceError for '{mat_name_for_log}' during preview update. Material may have been removed.")
    except Exception as e:
        # This is the crucial error log
        print(f"FUP: ERROR for '{mat_name_for_log}' (Is Library: {is_lib}): {e}")
        # traceback.print_exc() # Keep traceback commented unless specifically needed for very deep errors

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
def get_custom_icon(mat, collect_mode=False):
    global custom_icons, thumbnail_generation_scheduled, thumbnail_task_queue, thumbnail_pending_on_disk_check
    global g_tasks_for_current_run, g_current_run_task_hashes_being_processed, THUMBNAIL_SIZE

    mat_name_debug = getattr(mat, 'name', 'None_Material_Name')

    if not mat:
        return 0

    try:
        if not _verify_icon_template():
            return 0
    except Exception as e_tpl_chk:
        # print(f"[GetIcon - {mat_name_debug}] Template-validation/rebuild error: {e_tpl_chk}. Ret 0.", flush=True)
        return 0

    if custom_icons is None:
        try:
            custom_icons = bpy.utils.previews.new()
            if custom_icons is None: return 0
            if 'preload_existing_thumbnails' in globals() and callable(preload_existing_thumbnails):
                preload_existing_thumbnails()
        except Exception:
            return 0

    current_material_hash = get_material_hash(mat)
    if not current_material_hash:
        return 0

    # 1. Check Blender's preview cache (custom_icons)
    if current_material_hash in custom_icons:
        cached_preview_item = custom_icons[current_material_hash]
        path_for_cached_thumb = get_thumbnail_path(current_material_hash)
        
        is_cached_item_genuinely_valid = False
        if hasattr(cached_preview_item, 'icon_id') and cached_preview_item.icon_id > 0:
            actual_w, actual_h = cached_preview_item.icon_size
            
            if actual_w <= 1 or actual_h <= 1: # Lenient: Only invalidate if basically zero-sized
                print(f"    [GetIcon - Cache VERY BAD SIZE] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Cached ID {cached_preview_item.icon_id} but size {actual_w}x{actual_h} is practically zero. Invalidating.", flush=True)
                if current_material_hash in custom_icons: # Ensure key exists before del
                    del custom_icons[current_material_hash]
            elif actual_w < THUMBNAIL_SIZE or actual_h < THUMBNAIL_SIZE: # Log if smaller than fully expected, but don't invalidate solely for this
                # print(f"    [GetIcon - Cache SMALLER SIZE] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Cached ID {cached_preview_item.icon_id}, size {actual_w}x{actual_h} (expected {THUMBNAIL_SIZE}x{THUMBNAIL_SIZE}). Checking file.", flush=True)
                # If size is smaller but reasonable (e.g. 32x32), ensure backing file still exists
                if not (os.path.isfile(path_for_cached_thumb) and os.path.getsize(path_for_cached_thumb) > 0):
                    print(f"    [GetIcon - Cache SMALLER SIZE NO FILE] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Backing file invalid. Invalidating.", flush=True)
                    if current_material_hash in custom_icons: del custom_icons[current_material_hash]
                else:
                    is_cached_item_genuinely_valid = True # Accept smaller, reasonable sizes if file is OK
            else: # Size is as expected (THUMBNAIL_SIZE x THUMBNAIL_SIZE)
                if not (os.path.isfile(path_for_cached_thumb) and os.path.getsize(path_for_cached_thumb) > 0):
                    print(f"    [GetIcon - Cache EXPECTED SIZE NO FILE] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Cached ID {cached_preview_item.icon_id}, size OK, but backing file invalid. Invalidating.", flush=True)
                    if current_material_hash in custom_icons: del custom_icons[current_material_hash]
                else:
                    is_cached_item_genuinely_valid = True
        
        if is_cached_item_genuinely_valid:
            return cached_preview_item.icon_id

    thumbnail_file_path = get_thumbnail_path(current_material_hash)

    # 2. Check if valid file exists on disk & attempt to load
    file_ok_on_disk = False
    if os.path.isfile(thumbnail_file_path):
        try:
            if os.path.getsize(thumbnail_file_path) > 0:
                file_ok_on_disk = True
        except OSError:
            file_ok_on_disk = False

    if file_ok_on_disk:
        try:
            if current_material_hash in custom_icons:
                 del custom_icons[current_material_hash]
            
            preview_item_from_disk_load = custom_icons.load(current_material_hash, thumbnail_file_path, 'IMAGE')
            is_genuinely_valid_from_disk = False

            if preview_item_from_disk_load and hasattr(preview_item_from_disk_load, 'icon_id') and preview_item_from_disk_load.icon_id > 0:
                actual_w, actual_h = preview_item_from_disk_load.icon_size

                if actual_w <= 1 or actual_h <= 1: # Lenient: Only invalidate if practically zero
                    print(f"    [GetIcon - DiskLoad VERY BAD SIZE] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Loaded ID {preview_item_from_disk_load.icon_id} from file, but size {actual_w}x{actual_h} is practically zero. Invalidating.", flush=True)
                    if current_material_hash in custom_icons:
                        del custom_icons[current_material_hash]
                elif actual_w < THUMBNAIL_SIZE or actual_h < THUMBNAIL_SIZE: # Log if smaller but don't auto-invalidate if reasonable
                    print(f"    [GetIcon - DiskLoad SMALLER SIZE] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Loaded ID {preview_item_from_disk_load.icon_id} from file, size {actual_w}x{actual_h} (expected {THUMBNAIL_SIZE}x{THUMBNAIL_SIZE}). Accepting it.", flush=True)
                    is_genuinely_valid_from_disk = True # Accept smaller, reasonable sizes
                else: # Size is as expected
                    is_genuinely_valid_from_disk = True
            
            if is_genuinely_valid_from_disk:
                return preview_item_from_disk_load.icon_id
            # else: Load failed or was deemed invalid by size check. Fall through to schedule.

        except RuntimeError as e_runtime_load_geticon:
             # print(f"    [GetIcon - DiskLoad RUNTIME ERROR] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}) for '{thumbnail_file_path}': {e_runtime_load_geticon}. Will schedule generation.", flush=True)
             pass
        except Exception as e_load_from_disk:
            # print(f"    [GetIcon - DiskLoad EXCEPTION] HASH {current_material_hash[:8]} (Mat: {mat_name_debug}): Error loading from disk file '{thumbnail_file_path}': {e_load_from_disk}. Will schedule generation.", flush=True)
            pass

    # 3. If not found/loaded validly, check if already scheduled or being processed
    if current_material_hash in g_current_run_task_hashes_being_processed or \
       current_material_hash in thumbnail_pending_on_disk_check:
        return 0 
    
    if thumbnail_generation_scheduled.get(current_material_hash, False) and not collect_mode:
        return 0

    # 4. Prepare task if not found/loaded validly
    blend_file_path_for_worker = None
    if mat.library and mat.library.filepath:
        blend_file_path_for_worker = bpy.path.abspath(mat.library.filepath)
    elif not mat.library and bpy.data.filepath:
        blend_file_path_for_worker = bpy.path.abspath(bpy.data.filepath)
    else:
        return 0

    if not blend_file_path_for_worker or not os.path.exists(blend_file_path_for_worker):
        return 0

    mat_uuid_for_task = mat.get("uuid")
    if not mat_uuid_for_task or len(mat_uuid_for_task) != 36:
        return 0

    if not mat.library:
        try:
            if mat.users == 0 and not mat.use_fake_user : mat.use_fake_user = True
        except Exception: pass

    task_details = {
        'blend_file': blend_file_path_for_worker,
        'mat_uuid': mat_uuid_for_task,
        'thumb_path': thumbnail_file_path,
        'hash_value': current_material_hash,
        'mat_name_debug': mat.name,
        'retries': 0
    }

    if collect_mode:
        return task_details
    else:
        update_material_thumbnails(specific_tasks_to_process=[task_details])
        return 0

def _verify_icon_template() -> bool:
    """
    Returns True when a usable template exists on disk.
    If the file is absent or contains zero scenes it is rebuilt with
    ensure_icon_template() before returning.
    """
    template_scene_name = "IconTemplateScene"
    try:
        need_rebuild = False

        if not os.path.exists(ICON_TEMPLATE_FILE):
            need_rebuild = True
        else:
            # MODIFIED: Use assets_only=False for robust scene name checking
            with bpy.data.libraries.load(ICON_TEMPLATE_FILE, link=False, assets_only=False) as (data_from, _):
                # When assets_only=False and link=False, data_from.scenes is a list of scene names.
                scene_names_in_template = list(getattr(data_from, "scenes", []))
                if template_scene_name not in scene_names_in_template:
                    print(f"[_verify_icon_template] Scene '{template_scene_name}' not found via assets_only=False. Found: {scene_names_in_template}. Rebuilding.")
                    need_rebuild = True
                # else: # Optional: log success if found
                #     print(f"[_verify_icon_template] Scene '{template_scene_name}' found via assets_only=False. Template is OK.")


        if need_rebuild:
            print("[ThumbMan] Icon-template missing or empty (or specific scene not found) – rebuilding …")
            if not ensure_icon_template():
                print("[ThumbMan]   ERROR: rebuild failed!")
                return False
        return True
    except Exception as err:
        print(f"[ThumbMan]   ERROR during template check: {err}")
        traceback.print_exc()
        return False

def _dispatch_collected_tasks():
    """
    Takes tasks from g_tasks_for_current_run, groups them by blend_file,
    creates batches, and puts them onto thumbnail_task_queue.
    Only dispatches what can be immediately processed by available workers.
    """
    global g_tasks_for_current_run, thumbnail_task_queue, g_dispatch_lock
    global THUMBNAIL_BATCH_SIZE_PER_WORKER, g_current_run_task_hashes_being_processed
    global MAX_CONCURRENT_THUMBNAIL_WORKERS, thumbnail_worker_pool # Added thumbnail_worker_pool here for clarity if used

    with g_dispatch_lock:
        if not g_tasks_for_current_run:
            return

        # Calculate how many new workers we can start (using active Popen objects)
        # This assumes thumbnail_worker_pool correctly tracks active Popen processes
        # If thumbnail_workers (the list of dicts with 'process' key) is the source of truth for active workers, use that instead.
        # For now, sticking to your existing use of thumbnail_worker_pool for this calculation.
        active_workers = 0
        # Let's assume thumbnail_worker_pool contains Popen objects directly
        # or dicts with a 'process' key that is a Popen object.
        # We need to check if they are alive.
        # A more robust way might be to count entries in `thumbnail_workers` if that's the primary tracker.
        # For this example, I'll base it on `len(thumbnail_worker_pool)` as per your code's implication.
        
        # The process_thumbnail_tasks uses `thumbnail_workers` to track running processes.
        # Let's use that for consistency if it's available and reliable.
        # If `thumbnail_workers` is the list of dicts {'process': Popen, ...}, then:
        # active_workers_count = len(thumbnail_workers)
        # available_worker_slots = MAX_CONCURRENT_THUMBNAIL_WORKERS - active_workers_count
        
        # Using your existing logic for available_worker_slots:
        available_worker_slots = MAX_CONCURRENT_THUMBNAIL_WORKERS - len(thumbnail_worker_pool) 
        
        queued_batches = thumbnail_task_queue.qsize()
        max_new_batches = max(0, available_worker_slots - queued_batches)
        
        if max_new_batches <= 0:
            return

        print(f"[_dispatch_collected_tasks] Starting. Tasks in g_tasks_for_current_run: {len(g_tasks_for_current_run)}, Can dispatch: {max_new_batches} batches")
        
        # Consider only tasks for the batches we can create
        tasks_to_consider_for_dispatch = []
        # Iterate through g_tasks_for_current_run to select tasks without modifying list during iteration
        temp_tasks_for_dispatch = []
        num_tasks_to_grab = max_new_batches * THUMBNAIL_BATCH_SIZE_PER_WORKER
        
        # Collect tasks to dispatch without removing them from g_tasks_for_current_run yet
        # We'll remove them specifically once confirmed they are put on queue
        potential_tasks_for_dispatch = g_tasks_for_current_run[:num_tasks_to_grab]

        if not potential_tasks_for_dispatch:
            return
            
        tasks_by_blend_file = {}
        for task in potential_tasks_for_dispatch:
            # Ensure 'blend_file' key exists, default if necessary
            blend_file = task.get('blend_file', bpy.data.filepath if bpy.data.filepath else "UNKNOWN_BLEND_FILE")
            if blend_file not in tasks_by_blend_file:
                tasks_by_blend_file[blend_file] = []
            tasks_by_blend_file[blend_file].append(task)

        print(f"[_dispatch_collected_tasks] Tasks grouped into {len(tasks_by_blend_file)} blend files.")

        batches_created_count = 0
        tasks_actually_put_on_queue = [] # Track tasks that are successfully put on the queue
        
        for blend_file, tasks_for_this_blend in tasks_by_blend_file.items():
            if batches_created_count >= max_new_batches:
                break
                
            print(f"  Processing {len(tasks_for_this_blend)} tasks for blend file: {os.path.basename(blend_file)}")
            
            for i in range(0, len(tasks_for_this_blend), THUMBNAIL_BATCH_SIZE_PER_WORKER):
                if batches_created_count >= max_new_batches:
                    break
                    
                current_batch_tasks = tasks_for_this_blend[i:i + THUMBNAIL_BATCH_SIZE_PER_WORKER]
                if current_batch_tasks:
                    # Generate a batch_id (e.g., based on the first task's hash and time)
                    # Ensure task dictionaries have 'hash_value'
                    first_task_hash = current_batch_tasks[0].get('hash_value', 'unknown_hash')
                    batch_id_source = first_task_hash + str(time.time())
                    batch_id = hashlib.md5(batch_id_source.encode()).hexdigest()[:8]

                    # This is the corrected part: put a dictionary on the queue
                    item_for_queue = {
                        "batch_id": batch_id,
                        "tasks": current_batch_tasks, # This is the list of task dictionaries for this batch
                        "blend_file": blend_file      # The blend file these tasks are associated with
                    }
                    thumbnail_task_queue.put(item_for_queue)
                    
                    print(f"    Putting batch '{batch_id}' of {len(current_batch_tasks)} tasks onto thumbnail_task_queue. First HASH: {first_task_hash[:8]}")
                    
                    batches_created_count += 1
                    
                    for task_in_batch in current_batch_tasks:
                        tasks_actually_put_on_queue.append(task_in_batch)
                        # Ensure 'hash_value' is the correct key
                        g_current_run_task_hashes_being_processed.add(task_in_batch['hash_value'])
                        thumbnail_generation_scheduled[task_in_batch['hash_value']] = True # Your existing logic

        # Remove only the dispatched tasks from g_tasks_for_current_run
        if tasks_actually_put_on_queue:
            # Create a set of unique identifiers for dispatched tasks to efficiently remove them
            # Assuming 'hash_value' is a reliable unique ID per task
            dispatched_task_ids = set(task['hash_value'] for task in tasks_actually_put_on_queue)
            
            new_g_tasks_for_current_run = []
            for task in g_tasks_for_current_run:
                if task['hash_value'] not in dispatched_task_ids:
                    new_g_tasks_for_current_run.append(task)
            g_tasks_for_current_run = new_g_tasks_for_current_run
            
            print(f"[_dispatch_collected_tasks] Dispatched {len(tasks_actually_put_on_queue)} tasks in {batches_created_count} batches. Remaining in g_tasks_for_current_run: {len(g_tasks_for_current_run)}")

        if batches_created_count > 0:
            # Make sure this function is defined and does what's expected (e.g., starts the bpy.app.timers.register)
            ensure_thumbnail_queue_processor_running()

def finalize_thumbnail_run():
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_library_update_pending, g_tasks_for_current_run, g_current_run_task_hashes_being_processed

    print("[Finalize Thumbnail Run] Current run completed.")
    g_current_run_task_hashes_being_processed.clear() # Clear for the next potential run

    # Check for new materials created during the run
    new_materials_found_since_start = False
    if DATABASE_FILE and os.path.exists(DATABASE_FILE) and g_material_creation_timestamp_at_process_start > 0:
        try:
            with get_db_connection() as conn:
                c = conn.cursor()
                # Check if mat_time table exists
                c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='mat_time'")
                if c.fetchone():
                    c.execute("SELECT COUNT(*) FROM mat_time WHERE ts > ?", (int(g_material_creation_timestamp_at_process_start),))
                    if c.fetchone()[0] > 0:
                        new_materials_found_since_start = True
                        print("[Finalize Thumbnail Run] New materials detected in DB since run start.")
                else:
                    print("[Finalize Thumbnail Run] mat_time table not found, cannot check for new materials.")
        except Exception as e_db_check:
            print(f"[Finalize Thumbnail Run] Error checking database for new materials: {e_db_check}")

    if new_materials_found_since_start:
        print("[Finalize Thumbnail Run] Rerunning thumbnail generation due to new materials.")
        g_thumbnail_process_ongoing = False # Temporarily allow update_material_thumbnails to start a new run
        update_material_thumbnails() # This will set g_thumbnail_process_ongoing = True again for the new run
    else:
        print("[Finalize Thumbnail Run] No new materials detected. Thumbnail process complete for this iteration.")
        g_thumbnail_process_ongoing = False # Mark the overall thumbnailing process as not active
        g_material_creation_timestamp_at_process_start = 0.0 # Reset timestamp

        # Process pending library update if any
        if g_library_update_pending:
            print("[Finalize Thumbnail Run] Processing deferred library update.")
            g_library_update_pending = False # Reset before calling
            force_pending_update = getattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced', False)
            _perform_library_update(force=force_pending_update)
            if hasattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced'):
                bpy.context.window_manager.matlist_pending_lib_update_is_forced = False

        # --- START OF SECTION THAT CALLS populate_material_list ---
        # After all thumbnail processing for this "run" is complete (no new materials triggered another run)
        # and any pending library update is handled, refresh the UI list.
        # This ensures the list reflects any newly generated/loaded thumbnails.
        scene = get_first_scene() # Helper to get current scene context
        if scene and 'populate_material_list' in globals() and callable(populate_material_list):
            print("[Finalize Thumbnail Run] Refreshing material list UI after thumbnail run completion and library update check.")
            try:
                # populate_material_list also calls update_material_thumbnails,
                # but g_thumbnail_process_ongoing is False now, so it won't start a new full scan unless necessary.
                populate_material_list(scene, called_from_finalize_run=True) # Pass the flag here
                if 'force_redraw' in globals() and callable(force_redraw):
                    force_redraw() # Ensure UI updates properly
            except Exception as e_populate_final:
                print(f"[Finalize Thumbnail Run] Error during final populate_material_list: {e_populate_final}")
                traceback.print_exc()
        # --- END OF SECTION ---

def ensure_thumbnail_queue_processor_running():
    global thumbnail_monitor_timer_active
    if not thumbnail_monitor_timer_active:
        if not bpy.app.timers.is_registered(process_thumbnail_tasks):
            # print("[ThumbMan] Starting thumbnail queue processor timer.")
            bpy.app.timers.register(process_thumbnail_tasks, first_interval=0.5) # Short first interval
            thumbnail_monitor_timer_active = True
        else: # Timer is registered but flag was false, correct it
            thumbnail_monitor_timer_active = True
            # print("[ThumbMan] Thumbnail queue processor timer already registered but flag was false.")

def process_thumbnail_tasks():
    global thumbnail_worker_pool, g_tasks_for_current_run, thumbnail_task_queue
    global list_version, thumbnail_generation_scheduled, thumbnail_monitor_timer_active
    global custom_icons, _ADDON_DATA_ROOT, THUMBNAIL_SIZE, BACKGROUND_WORKER_PY
    global THUMBNAIL_BATCH_SIZE_PER_WORKER, THUMBNAIL_MAX_RETRIES
    global g_thumbnail_process_ongoing, g_dispatch_lock, MAX_CONCURRENT_THUMBNAIL_WORKERS

    any_successful_load_this_cycle = False

    if not g_thumbnail_process_ongoing and thumbnail_task_queue.empty() and not thumbnail_worker_pool and not g_tasks_for_current_run :
        if thumbnail_monitor_timer_active:
            thumbnail_monitor_timer_active = False
            return None
    
    if g_thumbnail_process_ongoing and not thumbnail_monitor_timer_active:
        ensure_thumbnail_queue_processor_running()

    try:
        if not _verify_icon_template():
            print("[ThumbMan Timer] Icon template verification failed. Retrying check soon.", file=sys.stderr, flush=True)
            return 0.5

        completed_worker_indices_this_cycle = []

        for idx, worker_info in enumerate(list(thumbnail_worker_pool)):
            process = worker_info.get('process')
            original_batch_tasks = worker_info.get('batched_tasks_in_worker', [])
            batch_id_for_log = "UnknownBatch"
            if original_batch_tasks and len(original_batch_tasks) > 0 and original_batch_tasks[0].get('hash_value'):
                batch_id_for_log = original_batch_tasks[0]['hash_value'][:8]
            
            if not process:
                completed_worker_indices_this_cycle.append(idx)
                continue

            exit_code = process.poll()
            
            existing_thumbs = 0
            total_thumbs = len(original_batch_tasks)
            if total_thumbs > 0:
                for task in original_batch_tasks:
                    if isinstance(task, dict) and os.path.exists(task.get('thumb_path', '')):
                        try:
                            if os.path.getsize(task.get('thumb_path', '')) > 0 :
                                 existing_thumbs += 1
                        except OSError: pass

            if exit_code is not None:
                completed_worker_indices_this_cycle.append(idx)
            
                stdout_str, stderr_str = "", ""
                # ... (stdout/stderr communication - unchanged from your last full version) ...
                try:
                    stdout_bytes, stderr_bytes = process.communicate(timeout=10)
                    stdout_str = stdout_bytes.decode('utf-8', errors='replace').strip() if stdout_bytes else ""
                    stderr_str = stderr_bytes.decode('utf-8', errors='replace').strip() if stderr_bytes else ""
                except subprocess.TimeoutExpired: stderr_str += "\n[Communicate Timeout on COMPLETED process]"
                except Exception as e_comm: stderr_str += f"\n[Error communicating with COMPLETED process: {e_comm}]"

                if stderr_str: print(f"[WORKER STDERR] W{idx} (Batch:{batch_id_for_log}):\n{stderr_str}", file=sys.stderr, flush=True)


                parsed_worker_json_results = []
                # ... (JSON parsing - unchanged from your last full version) ...
                if exit_code == 0 and stdout_str: 
                    json_line_to_parse = None
                    try:
                        lines = stdout_str.strip().splitlines()
                        if lines:
                            for line in reversed(lines):
                                line_stripped = line.strip()
                                if (line_stripped.startswith('{') and line_stripped.endswith('}')) or \
                                   (line_stripped.startswith('[') and line_stripped.endswith(']')):
                                    json_line_to_parse = line_stripped; break
                        if json_line_to_parse:
                            json_data = json.loads(json_line_to_parse)
                            if isinstance(json_data, dict) and "results" in json_data and isinstance(json_data["results"], list):
                                parsed_worker_json_results = json_data["results"]
                    except json.JSONDecodeError: pass

                tasks_to_evaluate = []
                # ... (Construct tasks_to_evaluate - unchanged from your last full version) ...
                if parsed_worker_json_results:
                    for res_item in parsed_worker_json_results:
                        hash_val_from_res = res_item.get('hash_value')
                        original_task = next((t for t in original_batch_tasks if t.get('hash_value') == hash_val_from_res), None)
                        if original_task:
                            tasks_to_evaluate.append({
                                "task_data": original_task,
                                "worker_status": res_item.get("status"),
                                "worker_reason": res_item.get("reason", "no_reason_in_json")
                            })
                else: 
                    for task_in_batch in original_batch_tasks:
                        tasks_to_evaluate.append({
                            "task_data": task_in_batch,
                            "worker_status": "failure", 
                            "worker_reason": f"no_json_or_bad_exit_rc_{exit_code}"
                        })

                for eval_item in tasks_to_evaluate:
                    task_data = eval_item["task_data"]; hash_val = task_data['hash_value']; thumb_p = task_data['thumb_path']; retries_done = task_data.get('retries', 0)
                    
                    thumbnail_pending_on_disk_check.pop(hash_val, None)
                    g_current_run_task_hashes_being_processed.discard(hash_val)

                    file_ok_on_disk = False; file_size = 0
                    if os.path.exists(thumb_p):
                        try:
                            file_size = os.path.getsize(thumb_p)
                            if file_size > 0: file_ok_on_disk = True
                        except OSError as e_stat:
                            print(f"    [Task Eval - File Stat Error] Hash {hash_val[:8]} for '{thumb_p}': {e_stat}", flush=True)
                    
                    loaded_to_blender_properly = False
                    if file_ok_on_disk:
                        if custom_icons is not None:
                            try:
                                time.sleep(0.05)
                                if hash_val in custom_icons:
                                    del custom_icons[hash_val]
                                
                                custom_icons.load(hash_val, thumb_p, 'IMAGE')
                                final_entry = custom_icons.get(hash_val)

                                if final_entry and hasattr(final_entry, 'icon_id') and final_entry.icon_id > 0:
                                    actual_w, actual_h = final_entry.icon_size
                                    if actual_w <= 1 or actual_h <= 1: # Lenient check
                                        print(f"    [Task Eval - Cache Load VERY BAD SIZE] Hash {hash_val[:8]}: Loaded ID {final_entry.icon_id} but size {actual_w}x{actual_h} is practically zero. Invalidating and deleting file.", flush=True)
                                        if hash_val in custom_icons: del custom_icons[hash_val]
                                        if os.path.exists(thumb_p):
                                            try: os.remove(thumb_p);
                                            except Exception as e_del_suspect: print(f"        Error deleting zero-size source file {thumb_p}: {e_del_suspect}", flush=True)
                                    elif actual_w < THUMBNAIL_SIZE or actual_h < THUMBNAIL_SIZE: # Log if smaller, but accept
                                         # print(f"    [Task Eval - Cache Load SMALLER SIZE] Hash {hash_val[:8]}: Loaded ID {final_entry.icon_id}, size {actual_w}x{actual_h} (expected {THUMBNAIL_SIZE}x{THUMBNAIL_SIZE}). Accepting.", flush=True)
                                         loaded_to_blender_properly = True; any_successful_load_this_cycle = True; list_version +=1
                                    else: # Size is as expected
                                        loaded_to_blender_properly = True; any_successful_load_this_cycle = True; list_version +=1
                                else:
                                    if os.path.exists(thumb_p): os.remove(thumb_p)
                            except RuntimeError as e_runtime_load:
                                if os.path.exists(thumb_p): os.remove(thumb_p)
                            except Exception as e_load_exc:
                                if os.path.exists(thumb_p): os.remove(thumb_p)
                    
                    if not loaded_to_blender_properly:
                        thumbnail_generation_scheduled.pop(hash_val, None)
                        if retries_done < THUMBNAIL_MAX_RETRIES:
                            task_for_retry = task_data.copy(); task_for_retry['retries'] = retries_done + 1
                            with g_dispatch_lock: g_tasks_for_current_run.append(task_for_retry); thumbnail_generation_scheduled[hash_val] = True
                        else: # Max retries hit
                            if os.path.exists(thumb_p) and file_ok_on_disk :
                                try: os.remove(thumb_p)
                                except Exception: pass
                    else:
                        thumbnail_generation_scheduled.pop(hash_val, None)

            else: # exit_code is None (worker is still running) - Aggressive kill logic
                if existing_thumbs == total_thumbs and total_thumbs > 0:
                    print(f"  Worker {idx} (Batch {batch_id_for_log}, PID: {getattr(process, 'pid', 'N/A')}): WARNING - All thumbnails exist on disk but process still running! Forcing KILL.", flush=True)
                    try:
                        process.kill()
                        try: process.wait(timeout=1.0)
                        except subprocess.TimeoutExpired: pass # Ignore if it doesn't die fast
                    except Exception: pass
                    completed_worker_indices_this_cycle.append(idx)

        # --- Worker Pool Cleanup & Dispatching Logic ---
        # (This part is largely unchanged from your last full version, focusing on popping completed workers,
        #  dispatching from g_tasks_for_current_run if slots open, then dispatching from thumbnail_task_queue.
        #  The check for 'all_tasks_in_batch_already_valid_in_cache' will use the lenient icon_size check.)

        if completed_worker_indices_this_cycle:
            for i in sorted(completed_worker_indices_this_cycle, reverse=True):
                if 0 <= i < len(thumbnail_worker_pool): thumbnail_worker_pool.pop(i)
            if g_tasks_for_current_run and len(thumbnail_worker_pool) < MAX_CONCURRENT_THUMBNAIL_WORKERS:
                 _dispatch_collected_tasks()

        if g_tasks_for_current_run and thumbnail_task_queue.qsize() < MAX_CONCURRENT_THUMBNAIL_WORKERS :
             _dispatch_collected_tasks()

        workers_started_this_cycle = 0
        while len(thumbnail_worker_pool) < MAX_CONCURRENT_THUMBNAIL_WORKERS and not thumbnail_task_queue.empty():
            try:
                queued_item = thumbnail_task_queue.get_nowait()
            except Empty: break

            if not isinstance(queued_item, dict) or not all(k in queued_item for k in ["batch_id", "tasks", "blend_file"]):
                continue

            batch_id_from_queue = queued_item['batch_id']; tasks_for_worker = queued_item['tasks']; blend_file_for_worker = queued_item['blend_file']
            
            all_tasks_in_batch_already_valid_in_cache = True # Assume true initially
            if not tasks_for_worker: all_tasks_in_batch_already_valid_in_cache = False
            else:
                for task_chk in tasks_for_worker:
                    hash_val_chk = task_chk.get('hash_value'); thumb_path_chk = task_chk.get('thumb_path')
                    if not hash_val_chk or not thumb_path_chk:
                        all_tasks_in_batch_already_valid_in_cache = False; break
                    
                    is_task_valid_in_cache = False
                    if custom_icons and hash_val_chk in custom_icons:
                        preview_to_check = custom_icons[hash_val_chk]
                        if hasattr(preview_to_check, 'icon_id') and preview_to_check.icon_id > 0:
                            actual_w, actual_h = preview_to_check.icon_size
                            # Lenient check: only practically zero size is invalid for "already done"
                            if not (actual_w <= 1 or actual_h <= 1):
                                if os.path.exists(thumb_path_chk) and os.path.getsize(thumb_path_chk) > 0:
                                    is_task_valid_in_cache = True
                    
                    if not is_task_valid_in_cache:
                        all_tasks_in_batch_already_valid_in_cache = False; break
            
            if all_tasks_in_batch_already_valid_in_cache:
                for task_skipped in tasks_for_worker:
                    h = task_skipped['hash_value']
                    thumbnail_pending_on_disk_check.pop(h, None)
                    thumbnail_generation_scheduled.pop(h, None)
                    g_current_run_task_hashes_being_processed.discard(h)
                any_successful_load_this_cycle = True; continue

            if not BACKGROUND_WORKER_PY or not os.path.exists(BACKGROUND_WORKER_PY):
                with g_dispatch_lock: g_tasks_for_current_run.extend(tasks_for_worker); continue
            try:
                for task_md in tasks_for_worker: os.makedirs(os.path.dirname(task_md['thumb_path']), exist_ok=True)
            except Exception:
                with g_dispatch_lock: g_tasks_for_current_run.extend(tasks_for_worker); continue

            for task_l in tasks_for_worker: thumbnail_pending_on_disk_check[task_l['hash_value']] = task_l

            tasks_json_payload = json.dumps(tasks_for_worker)
            cmd_worker = [bpy.app.binary_path, "--background", "--factory-startup", blend_file_for_worker, "--python", BACKGROUND_WORKER_PY, "--", "--operation", "render_thumbnail", "--tasks-json", tasks_json_payload, "--addon-data-root", _ADDON_DATA_ROOT, "--thumbnail-size", str(THUMBNAIL_SIZE)]
            try:
                popen_obj = subprocess.Popen(cmd_worker, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                thumbnail_worker_pool.append({'process': popen_obj, 'batched_tasks_in_worker': list(tasks_for_worker)})
                workers_started_this_cycle += 1
            except Exception as e_popen:
                with g_dispatch_lock: g_tasks_for_current_run.extend(tasks_for_worker)
                for task_fl in tasks_for_worker: thumbnail_pending_on_disk_check.pop(task_fl['hash_value'], None)
        
        if any_successful_load_this_cycle: force_redraw()

        if not g_tasks_for_current_run and thumbnail_task_queue.empty() and not thumbnail_worker_pool:
            if g_thumbnail_process_ongoing:
                 finalize_thumbnail_run()
            if not g_thumbnail_process_ongoing:
                thumbnail_monitor_timer_active = False; return None
        
        if g_thumbnail_process_ongoing or not thumbnail_task_queue.empty() or thumbnail_worker_pool or g_tasks_for_current_run :
            thumbnail_monitor_timer_active = True; return 1.0
        else:
            thumbnail_monitor_timer_active = False; return None

    except Exception as e_timer_main_loop:
        print(f"[ThumbMan Timer] CRITICAL UNHANDLED ERROR: {e_timer_main_loop}", file=sys.stderr, flush=True)
        traceback.print_exc(file=sys.stderr)
        g_thumbnail_process_ongoing = False; thumbnail_monitor_timer_active = False
        return None

def update_material_thumbnails(specific_tasks_to_process=None):
    """
    Main initiator for a thumbnail generation "run".
    Collects tasks via get_custom_icon and dispatches them.
    If specific_tasks_to_process is provided, it uses those instead of scanning all materials.
    This function sets g_thumbnail_process_ongoing = True.
    """
    global custom_icons, list_version
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_tasks_for_current_run, g_dispatch_lock, g_current_run_task_hashes_being_processed

    # If a full run is already ongoing and this is another call for a full run, skip.
    # Allow if specific_tasks are provided (can be ad-hoc additions to an ongoing run).
    if g_thumbnail_process_ongoing and specific_tasks_to_process is None:
        print("[UpdateMaterialThumbnails] Process already ongoing. Skipping new full scan.")
        return
    
    # Lock to ensure atomic update of global run state variables, especially g_thumbnail_process_ongoing.
    with g_dispatch_lock: 
        # Double check inside lock for full run scenario
        if g_thumbnail_process_ongoing and specific_tasks_to_process is None:
            return

        print(f"[UpdateMaterialThumbnails] Starting new thumbnail generation run. Specific tasks provided: {specific_tasks_to_process is not None}")
        g_thumbnail_process_ongoing = True # Mark that a run is officially starting/active
        g_material_creation_timestamp_at_process_start = time.time()
        
        # If this is a *new full run* (no specific tasks), clear the main task list and processing set.
        # If specific_tasks_to_process are provided, we are potentially adding to an existing run's
        # g_tasks_for_current_run (if it was idle but ongoing) or starting a mini-run.
        # For clarity, if it's a new full scan, ensure these are reset.
        if specific_tasks_to_process is None:
            g_tasks_for_current_run.clear()
            g_current_run_task_hashes_being_processed.clear() # Clear this too for a fresh full scan


    collected_tasks_for_this_run_call = [] # Tasks collected *specifically in this call*
    processed_hashes_this_call = set() # To avoid duplicates *within this specific call's collection phase*

    if specific_tasks_to_process is not None:
        # print(f"[UpdateMaterialThumbnails] Using {len(specific_tasks_to_process)} provided specific tasks.")
        for task_data in specific_tasks_to_process:
            if task_data and isinstance(task_data, dict) and task_data.get('hash_value') and \
               task_data['hash_value'] not in processed_hashes_this_call:
                collected_tasks_for_this_run_call.append(task_data)
                processed_hashes_this_call.add(task_data['hash_value'])
    else:
        # This is a full scan
        # print("[UpdateMaterialThumbnails] Scanning all materials in current .blend file...")
        materials_in_current_blend = list(bpy.data.materials) # Create a copy for safe iteration
        num_mats_to_check_for_gen = len(materials_in_current_blend)
        # print(f"[UpdateMaterialThumbnails] Checking {num_mats_to_check_for_gen} materials in current .blend file for thumbnail generation via get_custom_icon...")

        for mat_idx, current_mat_obj in enumerate(materials_in_current_blend):
            # Optional: Provide console feedback for very large projects
            if mat_idx > 0 and mat_idx % 100 == 0:
                # print(f"  ...scanned {mat_idx}/{num_mats_to_check_for_gen} materials for task collection.")
                pass

            # Basic validation of the material object
            current_mat_name_for_debug = f"MaterialAtIndex_{mat_idx}"
            try:
                if not current_mat_obj or not hasattr(current_mat_obj, 'name'): continue # Skip invalid
                current_mat_name_for_debug = current_mat_obj.name
                # Ensure material has a UUID (get_material_uuid also creates if missing for non-library)
                if not get_material_uuid(current_mat_obj): continue
            except ReferenceError: continue # Material might have been removed during iteration
            except Exception as e_mat_validate_for_thumb_update:
                # print(f"  Error validating material {current_mat_name_for_debug} for task collection: {e_mat_validate_for_thumb_update}")
                continue

            # Call get_custom_icon in collect_mode. It returns task_dict if generation is needed,
            # or an icon_id (int) if already cached/exists. We only care about task_dicts here.
            result = get_custom_icon(current_mat_obj, collect_mode=True)
            if isinstance(result, dict): # It's a task_dict, meaning thumbnail is needed
                if result['hash_value'] not in processed_hashes_this_call:
                    collected_tasks_for_this_run_call.append(result)
                    processed_hashes_this_call.add(result['hash_value'])

    # print(f"[UpdateMaterialThumbnails] Collected {len(collected_tasks_for_this_run_call)} new tasks in this call.")

    if collected_tasks_for_this_run_call:
        with g_dispatch_lock:
            for task_to_add in collected_tasks_for_this_run_call:
                # Add to g_tasks_for_current_run if not already there by hash (e.g. from a previous ad-hoc call in the same run)
                # and not already actively being processed in a batch (g_current_run_task_hashes_being_processed).
                if task_to_add['hash_value'] not in g_current_run_task_hashes_being_processed and \
                   not any(t['hash_value'] == task_to_add['hash_value'] for t in g_tasks_for_current_run):
                    g_tasks_for_current_run.append(task_to_add)
                    thumbnail_generation_scheduled[task_to_add['hash_value']] = True # Mark as part of the broader schedule
                    # print(f"  Added task for HASH {task_to_add['hash_value'][:8]} to g_tasks_for_current_run.")
        
        # print(f"[UpdateMaterialThumbnails] Total tasks in g_tasks_for_current_run now: {len(g_tasks_for_current_run)}. Calling _dispatch_collected_tasks.")
        _dispatch_collected_tasks() # This will attempt to put them on thumbnail_task_queue and start timer
    elif not g_tasks_for_current_run and thumbnail_task_queue.empty() and not thumbnail_worker_pool:
        # No new tasks collected in this call, AND no tasks were pending from a previous part of this run,
        # AND queues/pools are empty. This means the run might be "empty" or has just completed.
        print("[UpdateMaterialThumbnails] No new tasks collected and no pending/active tasks from this run. Finalizing run.")
        finalize_thumbnail_run() # Check for new materials, etc. This will manage g_thumbnail_process_ongoing.
    else:
        # No new tasks collected in *this specific call*, but g_tasks_for_current_run might have items
        # from previous ad-hoc additions to this ongoing run, or workers might still be active.
        # print("[UpdateMaterialThumbnails] No new tasks collected in this call, but tasks might be pending from previous calls in this run or workers active.")
        ensure_thumbnail_queue_processor_running() # Ensure timer is active if there are tasks or workers

    # UI refresh is handled by process_thumbnail_tasks after successful loads, or by a final refresh trigger if needed.
    # No direct UI refresh here to avoid too frequent updates during the collection phase.
    print("[UpdateMaterialThumbnails] Task collection/initiation phase complete.")

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
        mat_for_icon_lookup = None 

        # 1. Try to get icon_id from _cached_items_for_draw (will be 0 due to filter_items change)
        if (hasattr(self, "_cached_items_for_draw") and
                0 <= index < len(self._cached_items_for_draw)):
            cache_entry = self._cached_items_for_draw[index]
            icon_val = cache_entry.get("icon_id", 0) 

        # 2. If cache did not yield a valid icon_id (>0), resolve material and get icon_id.
        # This block will now always be entered for icon resolution.
        if icon_val <= 0:
            # Always try to get the material object using the UUID stored in the list item.
            mat_for_icon_lookup = get_material_by_uuid(item.material_uuid)

            if mat_for_icon_lookup:
                # print(f"[DrawItem] For item '{item.material_name}' (UUID: {item.material_uuid}), found mat '{mat_for_icon_lookup.name}'. Calling get_custom_icon.")
                icon_val = get_custom_icon(mat_for_icon_lookup)
                # if icon_val <= 0:
                    # print(f"[DrawItem] For item '{item.material_name}' (UUID: {item.material_uuid}), get_custom_icon for mat '{mat_for_icon_lookup.name}' returned 0 or less.")
            # else:
                # print(f"[DrawItem] For item '{item.material_name}' (UUID: {item.material_uuid}), mat_for_icon_lookup is None (get_material_by_uuid failed). Cannot call get_custom_icon.")
                # icon_val remains 0 or negative

        # 3. Draw the row, starting with the icon.
        row = layout.row(align=True)
        if icon_val > 0: 
            row.label(icon_value=icon_val)
        else:
            # Fallback icon logic: Check if the material (still) exists.
            # Re-use mat_for_icon_lookup if it was determined above.
            # If mat_for_icon_lookup was None, then material_exists_for_fallback will be False.
            material_exists_for_fallback = False
            if mat_for_icon_lookup: # Check if it was found
                 # Verify it's still a valid material in bpy.data (could have been deleted)
                if hasattr(mat_for_icon_lookup, 'name') and mat_for_icon_lookup.name in bpy.data.materials:
                    if bpy.data.materials[mat_for_icon_lookup.name] == mat_for_icon_lookup: # Check identity
                        material_exists_for_fallback = True

            if material_exists_for_fallback:
                row.label(icon="MATERIAL") 
                # print(f"[DrawItem Fallback] Item '{item.material_name}' (UUID: {item.material_uuid}), mat found ('{mat_for_icon_lookup.name}'), using default MATERIAL icon because get_custom_icon returned <=0.")
            else:
                row.label(icon="ERROR")    
                # print(f"[DrawItem Fallback] Item '{item.material_name}' (UUID: {item.material_uuid}), mat NOT found by get_material_by_uuid OR became invalid, using ERROR icon.")

        # 4. Draw the label text (material display name) and lock icon.
        # Use mat_for_icon_lookup if available from earlier resolution for efficiency.
        # If it was None earlier, it will still be None here.
        if mat_for_icon_lookup: # Material was found (and assumed still valid for name display)
            row.label(text=item.material_name) 
            if item.is_protected: 
                row.label(icon="LOCKED")
        else:
            # The material datablock could not be found by get_material_by_uuid.
            row.label(text=f"{item.material_name} (Missing)", icon="ERROR")

    def filter_items(self, context, data, propname):
        global material_list_cache, list_version # Ensure these are accessible if they are true globals
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
                # MODIFICATION START:
                # We no longer attempt to resolve the material object or call get_custom_icon
                # within filter_items when rebuilding the cache.
                # Let draw_item handle all material resolution and icon fetching.
                # This avoids calling get_custom_icon during this cache rebuild phase,
                # which was hypothesized to cause issues with the save-to-library logic
                # by altering material state or hash caches prematurely.
                material_list_cache.append({
                    'name': item_prop.material_name,
                    'uuid': item_prop.material_uuid,
                    'icon_id': 0,  # Always pass 0; draw_item will resolve the actual icon
                    'original_index': item_idx
                })
                # MODIFICATION END

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

        # This cache is used by draw_item to get the icon_id.
        # Since we now always put 0, draw_item will always do the full lookup.
        self._cached_items_for_draw = filtered_cache_for_draw
        return flt_flags, flt_neworder

class MATERIALLIST_PT_panel(bpy.types.Panel): # Ensure bpy.types.Panel is inherited
    bl_idname = "MATERIALLIST_PT_panel"
    bl_label = "Material List" # Panel label is the same
    bl_space_type = 'VIEW_3D'
    bl_region_type = 'UI'
    bl_category = "Material List"
    bl_options = {'DEFAULT_CLOSED'}

    def draw(self, context):
        layout = self.layout
        scene = context.scene

        # --- Workspace Mode ---
        workspace_box = layout.box()
        row = workspace_box.row(align=True)
        row.label(text="Workspace Mode:", icon='FILE_BLEND')
        row.label(text=f"{scene.workspace_mode}") 
        workspace_box.operator("materiallist.toggle_workspace_mode", text=f"Switch to {'Editing' if scene.workspace_mode == 'REFERENCE' else 'Reference'}", icon='ARROW_LEFTRIGHT')

        # --- Material Options ---
        options_box = layout.box()
        options_box.label(text="Material Options", icon='TOOL_SETTINGS')

        row = options_box.row(align=True)
        row.operator("materiallist.rename_to_albedo", text="Rename All to Albedo", icon='FILE_REFRESH')
        row.operator("materiallist.duplicate_material", text="Duplicate Selected", icon='DUPLICATE')

        row = options_box.row(align=True)
        row.prop(scene, "hide_mat_materials", toggle=True, text="Hide mat_ Materials")
        row.prop(scene, "material_list_show_only_local", toggle=True)

        row = options_box.row(align=True)
        row.operator("materiallist.rename_material", icon='FONT_DATA', text="Rename Display Name")
        row.operator("materiallist.unassign_mat", icon='PANEL_CLOSE', text="Unassign 'mat_'")

        idx = scene.material_list_active_index
        if 0 <= idx < len(scene.material_list_items):
            item = scene.material_list_items[idx]
            # Assuming get_material_by_uuid is defined (e.g. in addon's __init__.py or a helpers module)
            # And it's properly imported or available in the scope of this panel.
            # For example: from .. import get_material_by_uuid (if in a sub-module)
            # For now, we'll assume it's globally available or part of the addon's structure.
            # mat_for_make_local_check = get_material_by_uuid(item.material_uuid) 
            # Due to not having the definition of get_material_by_uuid, I'll comment out dependent lines
            # to ensure this snippet is runnable standalone, focusing on the UI structure.
            # You'd uncomment and ensure get_material_by_uuid is correctly referenced in your full addon.
            pass # Placeholder for where mat_for_make_local_check would be used.
            # if mat_for_make_local_check and mat_for_make_local_check.library:
            #     options_box.operator("materiallist.make_local", icon='LINKED', text="Make Selected Local")

        # --- Reference Snapshot ---
        backup_box = layout.box()
        backup_box.label(text="Reference Snapshot", icon='INFO') 
        backup_box.operator("materiallist.backup_editing", icon='FILE_TICK', text="Backup Current as Reference")

        # --- Assign to Active Object ---
        assign_box = layout.box()
        assign_box.operator("materiallist.add_material_to_slot", icon='PLUS', text="Add Selected to Object Slots")
        assign_box.operator("materiallist.assign_selected_material", icon='BRUSH_DATA', text="Assign Selected to Faces/Object")
        assign_box.operator("materiallist.select_dominant", text="Select Dominant Material on Active Object", icon='RESTRICT_SELECT_OFF')

        # --- Material List Display & Info ---
        mat_list_box = layout.box()
        row = mat_list_box.row(align=True)
        row.label(text="Materials:", icon='MATERIAL')
        row.prop(scene, "material_list_sort_alpha", text="", toggle=True, icon='SORTALPHA')
        row.operator("materiallist.scroll_to_top", icon='TRIA_UP', text="")

        row = mat_list_box.row()
        row.template_list("MATERIALLIST_UL_materials", "", scene, "material_list_items", scene, "material_list_active_index", rows=10, sort_lock=True)

        sub_row = mat_list_box.row(align=True)
        sub_row.prop(scene, "material_search", text="", icon='VIEWZOOM')

        if 0 <= idx < len(scene.material_list_items):
            item = scene.material_list_items[idx]
            # mat_for_preview = get_material_by_uuid(item.material_uuid) 
            # if mat_for_preview:
            #     preview_box = mat_list_box.box()
            #     # Assuming ensure_safe_preview is defined
            #     # if ensure_safe_preview(mat_for_preview):
            #     #     preview_box.template_preview(mat_for_preview, show_buttons=False)
            #     # else:
            #     #     preview_box.label(text="Preview not available", icon='ERROR')

            #     info_box = preview_box.box() # Changed from preview_box.box() to mat_list_box.box() if preview is removed
            info_box = mat_list_box.box() # Assuming info is always shown even if preview logic is complex
            info_box.label(text=f"Name: {item.material_name}")
            info_box.label(text=f"Source: {'Local' if not item.is_library else 'Library'}")
            info_box.label(text=f"UUID: {item.material_uuid[:8]}...")

            name_to_check = item.original_name
            if not name_to_check.startswith("mat_") and name_to_check != "Material":
                count = sum(1 for li in scene.material_list_items if li.original_name == name_to_check)
                if count > 1:
                    warning_box = info_box.box(); warning_box.alert = True
                    warning_box.label(text=f"'{name_to_check}' used by {count} materials!", icon='ERROR')

        # --- Library Operations ---
        library_ops_box = layout.box()
        library_ops_box.label(text="Library Operations", icon='ASSET_MANAGER')
        library_ops_box.operator("materiallist.integrate_library", text="Integrate External Library", icon='IMPORT')
        #library_ops_box.operator("materiallist.pack_library_textures", text="Pack All Library Textures", icon='PACKAGE')

        # --- Batch Utilities ---
        project_util_box = layout.box()
        project_util_box.label(text="Batch Utilities", icon='TOOL_SETTINGS')
        
        # MODIFIED LINE: Changed the text label for the directory property.
        # This assumes scene.material_list_external_unpack_dir is defined with subtype='DIR_PATH'
        # in your addon's registration code to enable the directory explorer.
        project_util_box.prop(scene, "material_list_external_unpack_dir", text="External Output Folder")

        col = project_util_box.column(align=True)
        # These bl_idname strings should correspond to your Operator classes
        col.operator("materiallist.pack_textures_externally", text="Projects: Localise & Unpack Externally", icon='EXPORT') # Assuming bl_idname matches your operator
        col.separator(factor=0.5) 
        col.operator("materiallist.pack_textures_internally", text="Projects: Localise & Pack Internally", icon='IMPORT') # Assuming bl_idname matches your operator
        
        project_util_box.operator("materiallist.trim_library", icon='TRASH', text="Trim Library") # Assuming bl_idname matches

        # --- Global Refresh ---
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
    MATERIALLIST_OT_refresh_material_list,
    MATERIALLIST_OT_rename_material,
    MATERIALLIST_OT_prepare_material,
    MATERIALLIST_OT_assign_to_object,
    MATERIALLIST_OT_assign_to_faces,
    MATERIALLIST_OT_make_local,
    MATERIALLIST_OT_sort_alphabetically,
    MATERIALLIST_OT_PollMaterialChanges,
    MATERIALLIST_OT_integrate_library,
    MATERIALLIST_OT_trim_library,
    MATERIALLIST_OT_select_dominant,
    MATERIALLIST_OT_run_localisation_worker,
    MATERIALLIST_OT_duplicate_material, # New
    MATERIALLIST_OT_pack_library_textures, # New
    MATERIALLIST_OT_scroll_to_top, # New
    MATERIALLIST_OT_pack_textures_externally,   # New
    MATERIALLIST_OT_pack_textures_internally, # New
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
    ("material_list_external_unpack_dir", bpy.props.StringProperty(
        name="External Output Folder",  # This name is used as the label by default if text isn't specified in layout.prop
        description="Directory to save external textures. Use // for paths relative to the .blend file.",
        subtype='DIR_PATH',          # This makes it use the directory explorer
        default="//textures_external/" # A sensible default relative path
    )),
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
def deferred_safe_init():
    try:
        print("[DEBUG] Running deferred_safe_init")
        if 'load_material_names' in globals() and callable(load_material_names):
            load_material_names()

        # Ensure material library and DB are ready first
        # This also creates _ADDON_DATA_ROOT and THUMBNAIL_FOLDER if they don't exist.
        if not ensure_material_library():
            print("[DEBUG] ensure_material_library failed in deferred init. Critical paths might be missing.")
            # Depending on desired behavior, you might want to return or handle this.
            # For now, we proceed to try ensuring the icon template, but it might fail if paths aren't set.
        else:
            print("[Deferred Init] Material library and database ensured/initialized.")

        # MOVED ensure_icon_template CALL HERE:
        # This function relies on ICON_TEMPLATE_FILE which is derived from LIBRARY_FOLDER,
        # which in turn is _ADDON_DATA_ROOT, set up by get_material_manager_addon_data_dir
        # and ensured by ensure_material_library.
        if 'ensure_icon_template' in globals() and callable(ensure_icon_template):
            print("[Deferred Init] Ensuring icon generation template...")
            if not ensure_icon_template(): # This function attempts to create the .blend file
                print("[Deferred Init] WARNING: Failed to ensure icon generation template. Thumbnail generation may fail.")
            else:
                print("[Deferred Init] Icon generation template ensured successfully.")
        else:
            print("[Deferred Init] ensure_icon_template function not found. Cannot create/verify template file.")

        # debug_library_contents() # Optional, for checking material_library.blend

        update_material_library(force_update=True) # Queues library update if necessary

        scene = get_first_scene()
        if scene:
            populate_material_list(scene) # Populates UI list (now excludes "mat_" by default if toggle is on)

            # Backup initial state for workspace modes
            reference_backup.clear()
            backup_current_assignments(reference_backup, 'reference')
            load_backups() # Load any persisted backups for the current file

            # Start polling for material changes if the operator exists
            if hasattr(bpy.ops.materiallist, 'poll_material_changes'):
                try:
                    bpy.ops.materiallist.poll_material_changes('INVOKE_DEFAULT')
                except Exception as op_error:
                    print(f"Error invoking poll_material_changes: {op_error}")

        # Initialize material properties (UUIDs, datablock names for local non-"mat_" materials)
        # This is crucial after initial file load and potential linking of library materials.
        if 'initialize_material_properties' in globals() and callable(initialize_material_properties):
            initialize_material_properties()
        else:
            print("[Deferred Init] ERROR: initialize_material_properties function not found!")

        # Initial call to update thumbnails after everything is set up
        if 'update_material_thumbnails' in globals() and callable(update_material_thumbnails):
            print("[Deferred Init] Triggering initial thumbnail update cycle.")
            update_material_thumbnails()
        else:
            print("[Deferred Init] update_material_thumbnails function not found.")


    except Exception as e:
        print(f"[DEBUG] Exception in deferred_safe_init: {e}")
        traceback.print_exc()
    return None # Important for timer to stop itself if it's a one-off

def register():
    global _ADDON_DATA_ROOT, LIBRARY_FOLDER, LIBRARY_FILE, DATABASE_FILE, THUMBNAIL_FOLDER, ICON_TEMPLATE_FILE
    global custom_icons
    global BACKGROUND_WORKER_PY, MAX_CONCURRENT_THUMBNAIL_WORKERS, THUMBNAIL_BATCH_SIZE_PER_WORKER
    global material_names, material_hashes, global_hash_cache, list_version, _display_name_cache, _display_name_cache_version
    global thumbnail_task_queue, thumbnail_generation_scheduled, thumbnail_pending_on_disk_check
    global thumbnail_worker_pool, thumbnail_monitor_timer_active, persistent_icon_template_scene
    global is_update_processing, library_update_queue, material_list_cache
    global db_connections 
    # New batch globals
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_tasks_for_current_run, g_dispatch_lock, g_library_update_pending, g_current_run_task_hashes_being_processed


    print("[Register] MaterialList Addon Starting Registration...")
    # print("[Register] Step 1: Forcefully resetting internal state variables...")

    # --- Forceful Reset of Global State Variables ---
    thumbnail_task_queue = Queue() 
    thumbnail_generation_scheduled = {}
    thumbnail_pending_on_disk_check = {}
    thumbnail_worker_pool = []      
    thumbnail_monitor_timer_active = False
    persistent_icon_template_scene = None 

    list_version = 0
    material_names = {}             
    material_hashes = {}            
    global_hash_cache = {}          
    material_list_cache = []        
    _display_name_cache = {}
    _display_name_cache_version = 0

    is_update_processing = False
    library_update_queue = []

    if 'Queue' in globals() and callable(Queue): 
        db_connections = Queue(maxsize=5) 
    else: # Should not happen in normal Blender addon environment
        print("[Register] CRITICAL: queue.Queue not available for db_connections!")
        
    materials_modified = False 

    # Reset new batch globals
    g_thumbnail_process_ongoing = False
    g_material_creation_timestamp_at_process_start = 0.0
    g_tasks_for_current_run = []
    if 'Lock' in globals() and callable(Lock): # Reinitialize lock
        g_dispatch_lock = Lock()
    else:  # Should not happen
        print("[Register] CRITICAL: threading.Lock not available for g_dispatch_lock!")
    g_library_update_pending = False
    g_current_run_task_hashes_being_processed = set()


    # print("[Register] Internal state variables reset.")

    # print("[Register] Step 2: Setting up paths...")
    _ADDON_DATA_ROOT = get_material_manager_addon_data_dir()
    if not _ADDON_DATA_ROOT or not os.path.isdir(_ADDON_DATA_ROOT):
        print("[Register] CRITICAL: Failed to get or create a valid addon data directory. Addon may not function correctly.", file=sys.stderr)
    
    LIBRARY_FOLDER = _ADDON_DATA_ROOT
    LIBRARY_FILE = os.path.join(LIBRARY_FOLDER, "material_library.blend")
    DATABASE_FILE = os.path.join(LIBRARY_FOLDER, "material_list.db")
    THUMBNAIL_FOLDER = os.path.join(LIBRARY_FOLDER, "thumbnails")
    ICON_TEMPLATE_FILE = os.path.join(LIBRARY_FOLDER, "icon_generation_template.blend")

    try:
        BACKGROUND_WORKER_PY = os.path.join(os.path.dirname(os.path.realpath(__file__)), "background_writer.py")
    except NameError: 
        print("[Register] WARNING: __file__ not defined, attempting alternative path for worker script.", file=sys.stderr)
        BACKGROUND_WORKER_PY = "" 

    # print(f"[Register] Addon Data Root: {_ADDON_DATA_ROOT}")
    # print(f"[Register] Thumbnail Folder: {THUMBNAIL_FOLDER}")
    # print(f"[Register] Icon Template File: {ICON_TEMPLATE_FILE}")
    # print(f"[Register] Background worker script set to: {BACKGROUND_WORKER_PY}")
    if not BACKGROUND_WORKER_PY or not os.path.exists(BACKGROUND_WORKER_PY):
        print(f"[Register] CRITICAL WARNING: Worker script not found at '{BACKGROUND_WORKER_PY}'. Thumbnail and library merge operations will fail.", file=sys.stderr)

    # print("[Register] Step 3: Initializing database structure...")
    if 'initialize_database' in globals() and callable(initialize_database):
        try:
            initialize_database() 
        except Exception as e_db_init:
            print(f"[Register] CRITICAL ERROR initializing database: {e_db_init}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
    else:
        print("[Register] CRITICAL: initialize_database function not found. Database tables might not be created.", file=sys.stderr)

    # print("[Register] Step 4: Ensuring critical directories exist...")
    try:
        if _ADDON_DATA_ROOT and os.path.isdir(_ADDON_DATA_ROOT): 
            os.makedirs(THUMBNAIL_FOLDER, exist_ok=True)
            # print(f"[Register] Ensured thumbnail directory exists: {THUMBNAIL_FOLDER}")
        else:
            print(f"[Register] Cannot ensure thumbnail directory as _ADDON_DATA_ROOT ('{_ADDON_DATA_ROOT}') is invalid.", file=sys.stderr)
    except Exception as e_mkdir:
        print(f"[Register] Error creating thumbnail directory '{THUMBNAIL_FOLDER}': {e_mkdir}", file=sys.stderr)

    # print("[Register] Step 5: Initializing Blender preview collection...")
    if custom_icons is not None: 
        try:
            bpy.utils.previews.remove(custom_icons)
            # print("[Register] Removed existing custom_icons collection.")
        except Exception: pass 
    try:
        custom_icons = bpy.utils.previews.new()
        # print(f"[Register] New custom_icons preview collection created: {custom_icons}")
    except Exception as e_previews_new:
        print(f"[Register] CRITICAL ERROR creating bpy.utils.previews collection: {e_previews_new}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        custom_icons = None 

    # print(f"[Register] Step 6: Registering {len(classes)} classes...")
    for cls in classes: 
        try:
            try: bpy.utils.unregister_class(cls)
            except RuntimeError: pass 
            bpy.utils.register_class(cls)
        except Exception as e_cls_reg:
            print(f"[Register] Error registering class {cls.__name__}: {e_cls_reg}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)

    # print(f"[Register] Step 7: Registering {len(scene_props)} scene properties...")
    for prop_name, prop_value in scene_props: 
        try:
            if hasattr(bpy.types.Scene, prop_name): 
                delattr(bpy.types.Scene, prop_name)
            setattr(bpy.types.Scene, prop_name, prop_value)
        except Exception as e_prop_reg:
            print(f"[Register] Error setting scene property '{prop_name}': {e_prop_reg}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)

    if not hasattr(bpy.types.WindowManager, 'matlist_save_handler_processed'):
        bpy.types.WindowManager.matlist_save_handler_processed = bpy.props.BoolProperty(
            name="MaterialList Save Handler Processed",
            description="Internal flag for save_handler's process-once logic.",
            default=False
        )
    # For pending library update force state
    if not hasattr(bpy.types.WindowManager, 'matlist_pending_lib_update_is_forced'):
        bpy.types.WindowManager.matlist_pending_lib_update_is_forced = bpy.props.BoolProperty(
            name="MaterialList Pending Library Update is Forced",
            description="Internal flag if a deferred library update needs to be forced.",
            default=False
        )
    else: 
        try: 
            bpy.context.window_manager.matlist_save_handler_processed = False
            bpy.context.window_manager.matlist_pending_lib_update_is_forced = False
        except AttributeError: 
            pass


    # print("[Register] Step 8: Initializing database connection pool...")
    if 'initialize_db_connection_pool' in globals() and callable(initialize_db_connection_pool):
        try:
            initialize_db_connection_pool() 
        except Exception as e_db_pool:
            print(f"[Register] Error initializing DB connection pool: {e_db_pool}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
    else:
        print("[Register] initialize_db_connection_pool function not found.", file=sys.stderr)


    # print("[Register] Step 9: Preloading existing thumbnails...")
    if custom_icons is not None and 'preload_existing_thumbnails' in globals() and callable(preload_existing_thumbnails):
        try:
            preload_existing_thumbnails()
        except Exception as e_preload:
            print(f"[Register] Error during preload_existing_thumbnails: {e_preload}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
    elif custom_icons is None:
        print("[Register] Skipping thumbnail preload: custom_icons collection is not available.", file=sys.stderr)
    else: 
        print("[Register] preload_existing_thumbnails function not found.", file=sys.stderr)


    # print(f"[Register] Step 10: Registering {len(handler_pairs)} application handlers...")
    for handler_list, func in handler_pairs: 
        if func and callable(func):
            if func not in handler_list:
                try:
                    handler_list.append(func)
                except Exception as e_handler_reg:
                    print(f"[Register] Error appending handler {func.__name__}: {e_handler_reg}", file=sys.stderr)
                    traceback.print_exc(file=sys.stderr)
        else:
            print(f"[Register] Warning: Invalid function or handler list for handler registration (func: {str(func)})", file=sys.stderr)


    # print("[Register] Step 11: Scheduling deferred safe initialization...")
    if 'deferred_safe_init' in globals() and callable(deferred_safe_init):
        if not bpy.app.timers.is_registered(deferred_safe_init):
             bpy.app.timers.register(deferred_safe_init, first_interval=0.75) 
    else:
        print("[Register] deferred_safe_init function not found. Addon might not fully initialize.", file=sys.stderr)

    print("[Register] MaterialList Addon Registration Finished Successfully.")


def unregister():
    global custom_icons
    global thumbnail_monitor_timer_active, thumbnail_worker_pool, thumbnail_task_queue
    global thumbnail_pending_on_disk_check, thumbnail_generation_scheduled
    global db_connections 
    global material_names, material_hashes, global_hash_cache, material_list_cache, _display_name_cache
    # New batch globals
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_tasks_for_current_run, g_library_update_pending, g_current_run_task_hashes_being_processed
    global list_version

    print("[Unregister] MaterialList Addon Unregistering...")

    if thumbnail_monitor_timer_active:
        print("[Unregister] Attempting to stop thumbnail monitor timer...")
        if bpy.app.timers.is_registered(process_thumbnail_tasks): 
            try:
                bpy.app.timers.unregister(process_thumbnail_tasks)
                print("[Unregister] Thumbnail monitor timer successfully unregistered.")
            except Exception as e_tmr_unreg: 
                 print(f"[Unregister] Error unregistering thumbnail monitor timer: {e_tmr_unreg}")
        else:
            print("[Unregister] Thumbnail monitor timer was not registered.")
        thumbnail_monitor_timer_active = False

    print(f"[Unregister] Found {len(thumbnail_worker_pool)} thumbnail worker processes to terminate...")
    for worker_idx, worker_info in enumerate(list(thumbnail_worker_pool)): 
        process = worker_info.get('process')
        batch_info = worker_info.get('batched_tasks_in_worker', [])
        batch_id = "N/A"
        if batch_info and len(batch_info) > 0 and batch_info[0].get('hash_value'):
            batch_id = batch_info[0]['hash_value'][:8]
        
        print(f"[Unregister] Processing worker {worker_idx + 1}/{len(thumbnail_worker_pool)} (Batch ID: {batch_id})")
        
        if not process:
            print(f"  Worker {worker_idx + 1}: No process object found, skipping.")
            continue
            
        if not hasattr(process, 'poll'):
            print(f"  Worker {worker_idx + 1}: Process object has no poll method, skipping.")
            continue
            
        # Check if process is still running
        poll_result = process.poll()
        if poll_result is not None:
            print(f"  Worker {worker_idx + 1}: Process already terminated with exit code {poll_result}.")
            continue
            
        # Process is still running, attempt to terminate
        try:
            pid = getattr(process, 'pid', 'Unknown')
            print(f"  Worker {worker_idx + 1}: Attempting to terminate running process (PID: {pid})...")
            
            process.terminate()
            print(f"  Worker {worker_idx + 1}: Terminate signal sent, waiting up to 2 seconds...")
            
            try:
                process.wait(timeout=2.0)
                final_exit_code = process.poll()
                print(f"  Worker {worker_idx + 1}: Process terminated gracefully with exit code {final_exit_code}.")
            except subprocess.TimeoutExpired:
                print(f"  Worker {worker_idx + 1}: Process did not terminate within 2 seconds, attempting to kill...")
                try:
                    process.kill()
                    print(f"  Worker {worker_idx + 1}: Kill signal sent, waiting up to 1 second...")
                    process.wait(timeout=1.0)
                    final_exit_code = process.poll()
                    print(f"  Worker {worker_idx + 1}: Process killed with exit code {final_exit_code}.")
                except subprocess.TimeoutExpired:
                    print(f"  Worker {worker_idx + 1}: CRITICAL - Process did not respond to kill signal within 1 second!")
                except Exception as e_kill:
                    print(f"  Worker {worker_idx + 1}: Error during kill: {e_kill}")
            except Exception as e_wait:
                print(f"  Worker {worker_idx + 1}: Error during wait after terminate: {e_wait}")
                
        except AttributeError as e_attr: 
            print(f"  Worker {worker_idx + 1}: Process object missing expected attributes: {e_attr}")
        except Exception as e_term: 
            print(f"  Worker {worker_idx + 1}: Unexpected error during termination: {e_term}")

    thumbnail_worker_pool.clear()
    print(f"[Unregister] Worker pool cleared. Processing task queue...")

    queue_size = thumbnail_task_queue.qsize()
    print(f"[Unregister] Draining {queue_size} items from thumbnail task queue...")
    drained_count = 0
    while not thumbnail_task_queue.empty(): 
        try:
            thumbnail_task_queue.get_nowait()
            drained_count += 1
        except Empty:
            break
    print(f"[Unregister] Drained {drained_count} items from task queue.")
    
    thumbnail_pending_on_disk_check.clear()
    print(f"[Unregister] Cleared thumbnail_pending_on_disk_check dictionary.")

    for handler_list, func in handler_pairs: 
        if func and callable(func): 
            removed_count = 0
            while func in handler_list: 
                try:
                    handler_list.remove(func)
                    removed_count += 1
                except ValueError: 
                    break 
                except Exception as e_handler_unreg: 
                    print(f"[Unregister] Error removing handler {func.__name__}: {e_handler_unreg}")
                    break 
            if removed_count > 0:
                print(f"[Unregister] Removed handler {func.__name__} {removed_count} time(s).")

    for prop_name, _ in scene_props: 
        if hasattr(bpy.types.Scene, prop_name):
            try:
                delattr(bpy.types.Scene, prop_name)
                print(f"[Unregister] Removed scene property: {prop_name}")
            except Exception as e_prop_unreg: 
                 print(f"[Unregister] Error deleting scene property '{prop_name}': {e_prop_unreg}")

    if hasattr(bpy.types.WindowManager, 'matlist_save_handler_processed'):
        try:
            delattr(bpy.types.WindowManager, 'matlist_save_handler_processed')
            print(f"[Unregister] Removed WindowManager.matlist_save_handler_processed")
        except Exception as e_wm_prop_unreg: 
            print(f"[Unregister] Error deleting WindowManager.matlist_save_handler_processed: {e_wm_prop_unreg}")
    if hasattr(bpy.types.WindowManager, 'matlist_pending_lib_update_is_forced'):
        try:
            delattr(bpy.types.WindowManager, 'matlist_pending_lib_update_is_forced')
            print(f"[Unregister] Removed WindowManager.matlist_pending_lib_update_is_forced")
        except Exception as e_wm_prop_unreg_force:
            print(f"[Unregister] Error deleting WindowManager.matlist_pending_lib_update_is_forced: {e_wm_prop_unreg_force}")

    for cls in reversed(classes): 
        try:
            bpy.utils.unregister_class(cls)
            print(f"[Unregister] Unregistered class: {cls.__name__}")
        except RuntimeError: 
            print(f"[Unregister] Class {cls.__name__} was not registered, skipping.")
        except Exception as e_cls_unreg: 
            print(f"[Unregister] Error unregistering class {cls.__name__}: {e_cls_unreg}")

    if custom_icons is not None:
        try:
            bpy.utils.previews.remove(custom_icons)
            print(f"[Unregister] Removed custom_icons preview collection.")
        except Exception as e_preview_rem: 
            print(f"[Unregister] Error removing custom_icons preview collection: {e_preview_rem}")
        custom_icons = None

    if 'db_connections' in globals() and isinstance(db_connections, Queue): 
        closed_count = 0
        print(f"[Unregister] Closing database connections from pool...")
        while not db_connections.empty():
            try:
                conn = db_connections.get_nowait()
                conn.close()
                closed_count +=1
            except Empty: 
                break 
            except Exception as e_db_close: 
                print(f"[Unregister] Error closing a DB connection from pool: {e_db_close}")
                break 
        if closed_count > 0: 
            print(f"[Unregister] Closed {closed_count} DB connections from pool.")

    material_names.clear()
    material_hashes.clear()
    global_hash_cache.clear()
    material_list_cache.clear()
    _display_name_cache.clear()
    thumbnail_generation_scheduled.clear() 
    # Clear new batch globals
    g_tasks_for_current_run.clear()
    g_current_run_task_hashes_being_processed.clear()

    if 'reference_backup' in globals() and isinstance(reference_backup, dict): reference_backup.clear()
    if 'editing_backup' in globals() and isinstance(editing_backup, dict): editing_backup.clear()

    list_version = 0

    print("[Unregister] MaterialList Addon Unregistration Finished.")

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
