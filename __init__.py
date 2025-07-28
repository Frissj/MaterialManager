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
import threading  # <-- THE CRITICAL FIX IS HERE 
from threading import Thread, Event, Lock
from datetime import datetime
from collections import deque

try:
    import psutil
except ImportError:
    psutil = None # Define psutil as None if the import fails

# --------------------------
# Helper function to get user-specific data directory
# --------------------------

def get_material_manager_addon_data_dir():
    """
    Returns a directory path for the addon's persistent data.
    It attempts to create a subdirectory within C:\ProgramData.
    WARNING: Writing to C:\ProgramData typically requires administrator privileges.
             This addon may not function correctly without them if this path is used.
    """
    # --- MODIFICATION START ---
    # User-requested base path
    base_data_path = r"C:\ProgramData" 
    # --- MODIFICATION END ---

    addon_data_path = os.path.join(base_data_path, "MaterialManagerAddon_Data")

    try:
        os.makedirs(addon_data_path, exist_ok=True)
        print(f"[Path Setup] Addon data directory set to: {addon_data_path}", flush=True)
        
        # Add a check to see if the directory is actually writable
        # This is a simple test by trying to create a temporary file
        # A more robust check might be needed depending on specific OS interactions.
        test_file_path = os.path.join(addon_data_path, f"write_test_{uuid.uuid4().hex}.tmp")
        try:
            with open(test_file_path, 'w') as f_test:
                f_test.write("test")
            os.remove(test_file_path)
            print(f"[Path Setup] Write access to {addon_data_path} confirmed.", flush=True)
        except Exception as write_test_error:
            print(f"WARNING: Could not confirm write access to {addon_data_path}. Test failed: {write_test_error}", flush=True)
            print("The addon might not be able to save persistent data to this location without appropriate permissions.", flush=True)


    except PermissionError as pe:
        print(f"CRITICAL PERMISSION ERROR: Could not create or write to addon data directory: {addon_data_path}", flush=True)
        print(f"Error details: {pe}", flush=True)
        print("Please ensure Blender has write permissions to this location, or run Blender as an administrator (not generally recommended).", flush=True)
        temp_dir_fallback = tempfile.mkdtemp(prefix="MaterialManagerAddon_TEMP_")
        print(f"FALLBACK: Using temporary directory for data (DATA WILL NOT PERSIST): {temp_dir_fallback}", flush=True)
        return temp_dir_fallback
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
_SUFFIX_REGEX_MAT_PARSE = re.compile(r"^(.*?)(\.(\d+))?$")
_THUMBNAIL_PRELOAD_PATTERN = re.compile(r"^[a-f0-9]{32}\.png$", re.IGNORECASE)
_ICON_TEMPLATE_VALIDATED = False
_LEGACY_THUMBNAIL_PATTERN = re.compile(r"^[a-zA-Z0-9_-]+_([a-f0-9]{32})\.png$", re.IGNORECASE) # ADD THIS LINE
g_thumbnails_loaded_in_current_UMT_run = False # Add this new global
g_matlist_transient_tasks_for_post_save = []
g_used_uuids_cache = set()
g_used_uuids_dirty = True
g_save_handler_start_time = 0.0
g_hashing_scene_bundle = None
g_materials_are_dirty = False
g_material_processing_timer_active = False
materials_modified = False
g_thumbnails_generated_in_current_run = 0
g_worker_manager_pool = []
g_worker_results_queue = Queue()
g_outstanding_task_count = 0
thumbnail_task_queue = Queue()
thumbnail_monitor_timer_active = False
g_task_collection_iterator = None
COLLECTION_BATCH_SIZE = 100
RAM_USAGE_THRESHOLD_PERCENT = 85.0
CPU_USAGE_THRESHOLD_PERCENT = 90.0

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
MAX_CONCURRENT_THUMBNAIL_WORKERS = max(1, (os.cpu_count() or 4) // 2) # Default, more aggressive
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
_preview_type_cache = {}

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
    
    # --- ADD/ENSURE THIS TABLE ---
    c.execute('''CREATE TABLE IF NOT EXISTS material_order
                 (uuid TEXT PRIMARY KEY, sort_index INTEGER)''')
    # --- REMOVE THE OLD TIMESTAMP TABLE ---
    c.execute('''DROP TABLE IF EXISTS mat_time''')
    
    c.execute('''CREATE TABLE IF NOT EXISTS clear_list
                 (material_name TEXT PRIMARY KEY)''')
    c.execute('''CREATE TABLE IF NOT EXISTS cache_version
                 (version INTEGER)''')
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

    c.execute("SELECT COUNT(*) FROM cache_version")
    if c.fetchone()[0] == 0:
        c.execute("INSERT INTO cache_version (version) VALUES (0)")
    else:
        c.execute("INSERT OR IGNORE INTO cache_version (rowid, version) VALUES (1,0)")

    conn.commit()
    conn.close()
    print("[DB Init] Database initialized/verified (Timestamp table removed, Index table ensured).", flush=True)

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
def _get_all_nodes_recursive(node_tree):
    """
    Recursively yields all nodes from a node tree and any nested groups.
    This function fulfills Point 2 of the description.
    """
    if not node_tree:
        return
    for node in node_tree.nodes:
        yield node
        if node.type == 'GROUP' and node.node_tree:
            yield from _get_all_nodes_recursive(node.node_tree)

def _get_node_recipe_string(node, image_hash_cache):
    """
    Builds the detailed "recipe" string for a single node, including special
    handling for content nodes AND a robust loop for all input default values.
    """
    # Basic node identification
    node_parts = [f"NODE:{node.name}", f"TYPE:{node.bl_idname}"]

    # --- Generic Property Loop ---
    # This reads standard node settings (like dropdown menus, checkboxes, etc.)
    for prop in node.bl_rna.properties:
        if prop.is_readonly or prop.identifier in [
            'rna_type', 'name', 'label', 'inputs', 'outputs', 'parent', 'internal_links',
            'color_ramp', 'image', 'node_tree'
        ]:
            continue
        try:
            value = getattr(node, prop.identifier)
            node_parts.append(f"PROP:{prop.identifier}={_stable_repr(value)}")
        except AttributeError:
            continue

    # --- *** THE CRITICAL FIX IS HERE *** ---
    # This loop explicitly reads the default value of every input socket.
    # This is how we "see" the sliders on custom node groups.
    for inp in node.inputs:
        # We only care about the default_value if nothing is plugged into the socket.
        if not inp.is_linked and hasattr(inp, 'default_value'):
            # This captures the state of UI sliders, color fields, and value boxes.
            node_parts.append(f"INPUT_DEFAULT:{inp.identifier}={_stable_repr(inp.default_value)}")

    # --- Special Content Node Handlers (These remain the same) ---
    if node.type == 'TEX_IMAGE' and node.image:
        image_content_hash = _hash_image(node.image, image_hash_cache)
        node_parts.append(f"SPECIAL_CONTENT_HASH:{image_content_hash}")

    elif node.type == 'ShaderNodeValToRGB':  # ColorRamp
        cr = node.color_ramp
        if cr:
            elements_str = [f"STOP({_stable_repr(s.position)}, {_stable_repr(s.color)})" for s in cr.elements]
            node_parts.append(f"SPECIAL_CONTENT_STOPS:[{','.join(elements_str)}]")

    # Sort all parts for perfect repeatability
    return "||".join(sorted(node_parts))

# Helper function for consistent float formatting (Identical to background_writer.py)
def _get_all_image_nodes_recursive(node_tree):
    """
    A generator function that recursively yields all TEX_IMAGE nodes
    from a node tree and any nested groups.
    """
    if not node_tree: return
    for node in node_tree.nodes:
        if node.type == 'TEX_IMAGE':
            yield node
        elif node.type == 'GROUP' and node.node_tree:
            # Recurse into the group's node tree
            yield from _get_all_image_nodes_recursive(node.node_tree)

def _validate_and_recover_image_source_main(image_datablock, temp_dir_for_recovery):
    """
    Ensures an image datablock has a valid, on-disk source file.
    If the path is invalid but pixel data exists, it saves the data to a
    temporary directory and reloads it. This is crucial for the hashing
    process to render packed or generated textures.
    Returns True on success, False on critical failure.
    """
    if not image_datablock:
        return True

    filepath = ""
    try:
        # Use filepath_from_user() to respect user-set paths
        if image_datablock.filepath_from_user():
             filepath = bpy.path.abspath(image_datablock.filepath_from_user())
    except Exception:
        filepath = ""

    if filepath and os.path.exists(filepath):
        return True # Path is valid, nothing to do.

    if not os.path.exists(filepath) and image_datablock.has_data:
        try:
            safe_name = "".join(c for c in image_datablock.name if c.isalnum() or c in ('_', '.', '-')).strip()
            ext = ".png"
            base_name, _ = os.path.splitext(safe_name)
            recovery_path = os.path.join(temp_dir_for_recovery, f"{base_name}{ext}")

            image_copy = image_datablock.copy()
            image_copy.filepath_raw = recovery_path
            image_copy.file_format = 'PNG'
            image_copy.save()
            
            image_datablock.filepath = recovery_path
            image_datablock.source = 'FILE'
            image_datablock.reload()
            
            return True

        except Exception as e:
            print(f"[Hash Texture Recovery] Failed to recover source image data for '{image_datablock.name}': {e}", file=sys.stderr)
            return False
    
    return True

def _float_repr(f):
    """Consistent, standardized string representation for float values."""
    try:
        return f"{float(f):.8f}"
    except (ValueError, TypeError):
        return "CONV_ERROR"

def _stable_repr(value):
    """Creates a stable, repeatable string representation for various data types."""
    if isinstance(value, (int, str, bool)):
        return str(value)
    elif isinstance(value, float):
        return f"{value:.8f}"
    elif isinstance(value, (bpy.types.bpy_prop_array, tuple, list)):
        if not value: return '[]'
        try:
            if all(isinstance(x, (int, float)) for x in value):
                return '[' + ','.join([_float_repr(item) for item in value]) + ']'
        except TypeError:
            pass
        return repr(value)
    elif hasattr(value, 'to_list'):
        list_val = value.to_list()
        if not list_val: return '[]'
        return '[' + ','.join([_float_repr(item) for item in list_val]) + ']'
    elif value is None:
        return 'None'
    else:
        return repr(value)

# _hash_image (Version from background_writer.py, modified for image_hash_cache)
def _hash_image(img, image_hash_cache):
    """Calculates a hash based on the image's file content."""
    if not img:
        return "NO_IMAGE_DATABLOCK"

    cache_key = img.name_full if hasattr(img, 'name_full') else str(id(img))

    if image_hash_cache is not None and cache_key in image_hash_cache:
        return image_hash_cache[cache_key]

    calculated_digest = None
    if hasattr(img, 'packed_file') and img.packed_file and hasattr(img.packed_file, 'data') and img.packed_file.data:
        try:
            data_to_hash = bytes(img.packed_file.data[:131072])
            calculated_digest = hashlib.md5(data_to_hash).hexdigest()
        except Exception as e_pack:
            print(f"[_hash_image Warning] Hash failed on packed data for '{img.name}': {e_pack}", file=sys.stderr)

    if calculated_digest is None and hasattr(img, 'filepath_raw') and img.filepath_raw:
        try:
            resolved_abs_path = bpy.path.abspath(img.filepath_raw)
            if os.path.isfile(resolved_abs_path):
                with open(resolved_abs_path, "rb") as f:
                    data_from_file = f.read(131072)
                calculated_digest = hashlib.md5(data_from_file).hexdigest()
        except Exception as e_file:
            print(f"[_hash_image Warning] Hash failed on file '{img.filepath_raw}': {e_file}", file=sys.stderr)

    if calculated_digest is None:
        fallback_data = f"FALLBACK|{getattr(img, 'name_full', 'N/A')}|{getattr(img, 'source', 'N/A')}"
        calculated_digest = hashlib.md5(fallback_data.encode('utf-8')).hexdigest()

    if image_hash_cache is not None:
        image_hash_cache[cache_key] = calculated_digest

    return calculated_digest

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
        for _ in range(20): # Limit search depth
            if not current_node or current_node in visited_nodes: break
            visited_nodes.add(current_node)
            if current_node.bl_idname == 'ShaderNodeBsdfPrincipled': return current_node

            potential_shader_inputs = []
            if hasattr(current_node, 'inputs'):
                shader_input_names = ["Shader", "Shader1", "Shader2"]
                for name in shader_input_names:
                    if name in current_node.inputs:
                        potential_shader_inputs.append(current_node.inputs[name])
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
        return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)
    except Exception as e:
        print(f"[find_principled_bsdf BG Error] For {getattr(mat, 'name', 'N/A')}: {e}", file=sys.stderr)
        return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)

# get_material_hash (Structure from __init__.py, using updated helpers)
      
def get_material_hash(mat, force=True, image_hash_cache=None):
    """
    [PRODUCTION VERSION] Calculates a highly detailed, content-based structural hash for a material.
    This version uses a robust, queue-based traversal to correctly handle nested node
    groups and their exposed slider values, including a specific fix for uniform
    parameter nodes (ShaderNodeValue).
    """
    # Incrementing the version ensures that any materials hashed with older,
    # incorrect logic will be re-hashed and their thumbnails updated correctly.
    HASH_VERSION = "v_STRUCTURAL_ROBUST_TRAVERSAL_2"

    if not mat:
        return None

    mat_uuid = mat.get("uuid")
    if not force and mat_uuid and mat_uuid in global_hash_cache:
        return global_hash_cache[mat_uuid]

    mat_name_for_debug = getattr(mat, 'name_full', getattr(mat, 'name', 'UnknownMaterial'))

    try:
        recipe_parts = [f"VERSION:{HASH_VERSION}"]

        if not mat.use_nodes or not mat.node_tree:
            recipe_parts.append("NON_NODE_MATERIAL")
            recipe_parts.append(f"DiffuseColor:{_stable_repr(mat.diffuse_color)}")
            recipe_parts.append(f"Metallic:{_stable_repr(mat.metallic)}")
            recipe_parts.append(f"Roughness:{_stable_repr(mat.roughness)}")
        else:
            if image_hash_cache is None:
                image_hash_cache = {}

            all_node_recipes = []
            all_link_recipes = []

            trees_to_process = deque([mat.node_tree])
            processed_trees = {mat.node_tree}

            while trees_to_process:
                current_tree = trees_to_process.popleft()

                for node in current_tree.nodes:
                    node_parts = [f"NODE:{node.name}", f"TYPE:{node.bl_idname}"]

                    # Generic Properties
                    for prop in node.bl_rna.properties:
                        if prop.is_readonly or prop.identifier in [
                            'rna_type', 'name', 'label', 'inputs', 'outputs', 'parent', 'internal_links',
                            'color_ramp', 'image', 'node_tree', 'outputs'
                        ]:
                            continue
                        try:
                            value = getattr(node, prop.identifier)
                            node_parts.append(f"PROP:{prop.identifier}={_stable_repr(value)}")
                        except AttributeError:
                            continue

                    # Unconnected Input Values
                    for inp in node.inputs:
                        if not inp.is_linked and hasattr(inp, 'default_value'):
                            node_parts.append(f"INPUT_DEFAULT:{inp.identifier}={_stable_repr(inp.default_value)}")

                    # Specific fix for ShaderNodeValue output values
                    if node.type == 'VALUE' and hasattr(node.outputs[0], 'default_value'):
                        output_val = node.outputs[0].default_value
                        node_parts.append(f"VALUE_NODE_OUTPUT={_stable_repr(output_val)}")

                    # Special Content Nodes
                    if node.type == 'TEX_IMAGE' and node.image:
                        image_content_hash = _hash_image(node.image, image_hash_cache)
                        node_parts.append(f"SPECIAL_CONTENT_HASH:{image_content_hash}")
                    elif node.type == 'ShaderNodeValToRGB':  # ColorRamp
                        cr = node.color_ramp
                        if cr:
                            elements_str = [f"STOP({_stable_repr(s.position)}, {_stable_repr(s.color)})" for s in cr.elements]
                            node_parts.append(f"SPECIAL_CONTENT_STOPS:[{','.join(elements_str)}]")

                    # Queue up Node Groups
                    if node.type == 'GROUP' and node.node_tree:
                        if node.node_tree not in processed_trees:
                            trees_to_process.append(node.node_tree)
                            processed_trees.add(node.node_tree)

                    all_node_recipes.append("||".join(sorted(node_parts)))

                # Process links
                for link in current_tree.links:
                    link_repr = (f"LINK:"
                                 f"{link.from_node.name}.{link.from_socket.identifier}->"
                                 f"{link.to_node.name}.{link.to_socket.identifier}")
                    all_link_recipes.append(link_repr)

            recipe_parts.extend(sorted(all_node_recipes))
            recipe_parts.extend(sorted(all_link_recipes))

        # Final hash calculation
        final_recipe_string = "|||".join(recipe_parts)
        digest = hashlib.md5(final_recipe_string.encode('utf-8')).hexdigest()

        if mat_uuid:
            global_hash_cache[mat_uuid] = digest
            material_hashes[mat_uuid] = digest

        return digest

    except Exception as e:
        print(f"[get_material_hash - PRODUCTION] Error hashing mat '{mat_name_for_debug}': {type(e).__name__} - {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        return None
        
def get_hashing_scene_bundle():
    """
    Lazily creates and manages a persistent, isolated scene for hashing operations.
    Returns a dictionary containing the scene and its required objects, or None on failure.
    This version is robust against being called from restricted contexts.
    """
    global g_hashing_scene_bundle

    # --- Step 1: Rigorous Validation of Existing Bundle ---
    if g_hashing_scene_bundle:
        is_valid = True
        try:
            # Check each key and ensure its value is a valid Blender ID object
            if not (g_hashing_scene_bundle.get('scene') and g_hashing_scene_bundle['scene'].name in bpy.data.scenes): is_valid = False
            if not (g_hashing_scene_bundle.get('plane') and g_hashing_scene_bundle['plane'].name in bpy.data.objects): is_valid = False
            if not (g_hashing_scene_bundle.get('hijack_mat') and g_hashing_scene_bundle['hijack_mat'].name in bpy.data.materials): is_valid = False
            
            if is_valid:
                return g_hashing_scene_bundle
            else:
                print("[Hashing Scene] Bundle validation failed. Will try to rebuild.")
                cleanup_hashing_scene_bundle() # Clean up the invalid bundle
        except (ReferenceError, KeyError, AttributeError):
            print("[Hashing Scene] Bundle reference lost. Will try to rebuild.")
            cleanup_hashing_scene_bundle()

    # --- Step 2: Lazy Creation (if bundle doesn't exist or was invalid) ---
    print("[Hashing Scene] Attempting to create persistent hashing scene bundle...")
    try:
        # This is the block that was failing with '_RestrictData' error.
        # We wrap it to catch the error and handle it gracefully.
        scene = bpy.data.scenes.new(name=f"__hashing_scene_{uuid.uuid4().hex}")
        
        # This is safe because we are creating the scene from scratch.
        scene.render.engine = 'CYCLES'
        scene.cycles.device = 'CPU'
        scene.render.resolution_x = 1
        scene.render.resolution_y = 1

        # Use a temporary context override to create objects without affecting the UI
        with bpy.context.temp_override(scene=scene):
            bpy.ops.mesh.primitive_plane_add(size=2)
            plane = bpy.context.active_object
        
        plane.name = "__hashing_plane"
        
        cam_data = bpy.data.cameras.new(name="__hashing_cam_data")
        cam_obj = bpy.data.objects.new("__hashing_cam", cam_data)
        scene.collection.objects.link(cam_obj)
        scene.camera = cam_obj
        cam_obj.location = (0, 0, 2)
        cam_data.type = 'ORTHO'
        cam_data.ortho_scale = 2.0

        hijack_mat = bpy.data.materials.new(name="__hashing_material")
        hijack_mat.use_nodes = True
        nt = hijack_mat.node_tree
        for node in nt.nodes: nt.nodes.remove(node)
        hijack_emission = nt.nodes.new('ShaderNodeEmission')
        hijack_output = nt.nodes.new('ShaderNodeOutputMaterial')
        nt.links.new(hijack_emission.outputs['Emission'], hijack_output.inputs['Surface'])
        
        plane.data.materials.append(hijack_mat)

        g_hashing_scene_bundle = {
            "scene": scene, "plane": plane,
            "hijack_mat": hijack_mat, "hijack_emission": hijack_emission
        }
        print("[Hashing Scene] Bundle created successfully.")
        return g_hashing_scene_bundle

    except AttributeError as e:
        if "'_RestrictData' object has no attribute 'scenes'" in str(e):
            print("[Hashing Scene] ERROR: Cannot create hashing scene. Context is restricted. Hashing will fail until context is available.", file=sys.stderr)
        else:
            print(f"[Hashing Scene] CRITICAL AttributeError creating bundle: {e}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
        g_hashing_scene_bundle = None
        return None # Return None on failure
    except Exception as e:
        print(f"[Hashing Scene] CRITICAL general error creating bundle: {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        g_hashing_scene_bundle = None
        return None

def cleanup_hashing_scene_bundle():
    """Safely removes the hashing scene and all its contents."""
    global g_hashing_scene_bundle
    if not g_hashing_scene_bundle:
        return
        
    try:
        scene = g_hashing_scene_bundle.get("scene")
        if scene and scene.name in bpy.data.scenes:
            # Unlink from any windows to prevent context issues on removal
            # This is a safety measure; it shouldn't be linked to any window
            for window in bpy.data.window_managers[0].windows:
                if window.scene == scene:
                    # Find any other scene to switch to
                    other_scene = next((s for s in bpy.data.scenes if s != scene), None)
                    if other_scene:
                        window.scene = other_scene
            
            # Now it should be safe to remove. This also removes its objects, etc.
            bpy.data.scenes.remove(scene, do_unlink=True)
            
    except (ReferenceError, KeyError, Exception) as e:
        print(f"[Hash Cleanup] Error removing hashing scene: {e}")

    g_hashing_scene_bundle = None
     
      
def process_dirty_materials_timer():
    """
    This is the new "background" process that runs on a timer.
    It does the heavy lifting that the save_handler used to do,
    but without blocking the UI.
    """
    global g_materials_are_dirty, g_material_processing_timer_active, materials_modified

    if not g_materials_are_dirty:
        g_material_processing_timer_active = False
        return None

    print(f"\n[{datetime.now().strftime('%H:%M:%S.%f')[:-3]} TIMER] Dirty flag detected. Processing materials...")
    
    g_materials_are_dirty = False

    changed_materials_for_library_update = {}
    hashes_to_save_to_db = {}
    uuids_to_promote_for_recency = []
    _session_image_hash_cache = {}

    load_material_hashes()

    for mat in list(bpy.data.materials):
        if not mat or mat.name.startswith("__hashing_"):
            continue
            
        # --- THIS IS THE CRITICAL FIX YOU ASKED FOR ---
        # If the material is from a library, we do not process it.
        # Its hash is considered final and is already in the database.
        if mat.library:
            continue
        # --- END OF FIX ---
        
        actual_uuid = get_material_uuid(mat)
        if not actual_uuid:
            continue

        db_stored_hash = material_hashes.get(actual_uuid)
        current_hash = get_material_hash(mat, force=True, image_hash_cache=_session_image_hash_cache)
        
        if not current_hash:
            continue

        if db_stored_hash != current_hash:
            materials_modified = True
            changed_materials_for_library_update[actual_uuid] = mat
            hashes_to_save_to_db[actual_uuid] = current_hash
            uuids_to_promote_for_recency.append(actual_uuid)
    
    if hashes_to_save_to_db:
        material_hashes.update(hashes_to_save_to_db)
        save_material_hashes()
        print(f"  [TIMER] Updated {len(hashes_to_save_to_db)} hashes in the database.")

    if uuids_to_promote_for_recency:
        for uuid_str in set(uuids_to_promote_for_recency):
            promote_material_by_recency_counter(uuid_str)
        print(f"  [TIMER] Promoted {len(set(uuids_to_promote_for_recency))} materials for recency.")

    if changed_materials_for_library_update:
        print(f"  [TIMER] Queuing library update for {len(changed_materials_for_library_update)} materials.")
        update_material_library(force_update=True, changed_materials_map=changed_materials_for_library_update)
    
    print(f"[{datetime.now().strftime('%H:%M:%S.%f')[:-3]} TIMER] Material processing finished.")
    
    return 2.0

def preload_existing_thumbnails():
    global custom_icons, THUMBNAIL_FOLDER # Ensure THUMBNAIL_FOLDER is accessible
    # _THUMBNAIL_PRELOAD_PATTERN is now a global, no need to define 'pattern' locally

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

    # Local 'pattern' variable is removed as we use the global _THUMBNAIL_PRELOAD_PATTERN
    loaded_count = 0; skipped_count = 0; error_count = 0

    print(f"[Thumb Preload] Scanning directory: {THUMBNAIL_FOLDER}")
    try:
        for filename in os.listdir(THUMBNAIL_FOLDER):
            # Use the pre-compiled global pattern here
            if _THUMBNAIL_PRELOAD_PATTERN.match(filename): # MODIFIED LINE
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

      
def get_unique_display_name(base_name):
    """
    Finds a unique display name.
    
    SPECIAL RULE: If the base_name is exactly "Material", this function will
    always return "Material" without attempting to add a suffix. This allows
    multiple UUID-named materials to share the same default display name.
    
    For all other names, it ensures uniqueness by adding a .001 suffix if needed.
    """
    global material_names # Ensure access to the global dictionary of finalized display names
    
    # --- THIS IS THE FIX ---
    # If the requested name is "Material", just return it. Do not check for uniqueness.
    if base_name == "Material":
        return "Material"
    # --- END OF FIX ---

    # For all other names, perform the original uniqueness check.
    existing_display_names = set(material_names.values())

    if base_name not in existing_display_names:
        return base_name
    
    count = 1
    while True:
        new_name = f"{base_name}.{count:03d}"
        if new_name not in existing_display_names:
            return new_name
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
    Ensures UUIDs exist for ALL non-"mat_" materials and sets their initial display name in the database.
    
    LOGIC:
    - SKIPS any material whose name starts with "mat_".
    - If a local material's datablock name is a UUID, its display name defaults to "Material".
    - Otherwise, the display name is based on the material's original datablock name.
    - Uses get_unique_display_name to handle naming.
    """
    global _display_name_cache, material_names
    
    print("[InitProps] Running initialize_material_properties (v3 - with 'mat_' skip logic)")
    
    local_needs_name_db_save_init = False 
    
    if not material_names: 
        load_material_names()

    all_mats_in_data = list(bpy.data.materials)

    for mat in all_mats_in_data:
        if not mat or mat.name.startswith("__hashing_"):
            continue

        # --- THIS IS THE CRITICAL FIX FOR YOUR SPECIAL CASE ---
        # If the material name starts with "mat_", do not process it for UUIDs or display names.
        if mat.name.startswith("mat_"):
            continue
        # --- END OF FIX ---

        original_datablock_name = mat.name  
        final_uuid_for_mat = validate_material_uuid(mat, is_copy=False)

        if not final_uuid_for_mat:
            continue

        # If this UUID is new to us, we need to assign it a display name.
        if final_uuid_for_mat not in material_names:
            display_name_basis = ""
            
            # Get the base name, e.g., "Rock" from "Rock.001"
            name_match = _SUFFIX_REGEX_MAT_PARSE.fullmatch(original_datablock_name)
            base_of_original_name = name_match.group(1) if name_match and name_match.group(1) else original_datablock_name
            
            # If the material's base name is a valid UUID, its display name should be "Material".
            # Otherwise, use the base name as the starting point.
            if is_valid_uuid_format(base_of_original_name):
                display_name_basis = "Material"
            else:
                display_name_basis = base_of_original_name

            # get_unique_display_name will handle the "Material" special case correctly.
            unique_display_name_for_db = get_unique_display_name(display_name_basis)
            
            material_names[final_uuid_for_mat] = unique_display_name_for_db
            local_needs_name_db_save_init = True

        # Ensure local, non-"mat_" materials are named by their UUID and have fake user set.
        if not mat.library:
            if mat.name != final_uuid_for_mat:
                try:
                    existing_mat_with_target_name = bpy.data.materials.get(final_uuid_for_mat)
                    if not existing_mat_with_target_name or existing_mat_with_target_name == mat:
                        mat.name = final_uuid_for_mat
                except Exception:
                    pass
            if not mat.use_fake_user:
                try:
                    mat.use_fake_user = True
                except Exception:
                    pass

    if local_needs_name_db_save_init:
        print("[InitProps] Saving newly added/updated display names to database...")
        save_material_names()
        _display_name_cache.clear()

    print("[InitProps] initialize_material_properties finished.")

def is_valid_uuid_format(uuid_string):
    """
    Checks if the given string is a well-formatted UUID.
    A simple structural check is performed, then uuid.UUID() for full validation.
    """
    if not isinstance(uuid_string, str) or len(uuid_string) != 36:
        return False
    # Basic check for xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx format with 4 hyphens
    parts = uuid_string.split('-')
    if len(parts) != 5:
        return False
    if not (len(parts[0]) == 8 and len(parts[1]) == 4 and len(parts[2]) == 4 and \
            len(parts[3]) == 4 and len(parts[4]) == 12):
        return False
    # Try to convert to UUID object for full validation of hex characters etc.
    try:
        uuid.UUID(uuid_string) # This will raise ValueError if format is wrong (e.g. invalid chars)
        return True
    except ValueError:
        return False
     
def is_valid_uuid_format(uuid_string):
    """
    Checks if the given string is a well-formatted UUID.
    A simple structural check is performed, then uuid.UUID() for full validation.
    """
    if not isinstance(uuid_string, str) or len(uuid_string) != 36:
        return False
    # Basic check for xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx format with 4 hyphens
    parts = uuid_string.split('-')
    if len(parts) != 5:
        return False
    if not (len(parts[0]) == 8 and len(parts[1]) == 4 and len(parts[2]) == 4 and \
            len(parts[3]) == 4 and len(parts[4]) == 12):
        return False
    # Try to convert to UUID object for full validation of hex characters etc.
    try:
        uuid.UUID(uuid_string) # This will raise ValueError if format is wrong (e.g. invalid chars)
        return True
    except ValueError:
        return False

# --- MODIFIED FUNCTION ---
def validate_material_uuid(mat, is_copy=False):
    """
    Ensures a material has a valid UUID stored in its custom property "uuid".
    Priority:
    1. If is_copy, always generate a new UUID.
    2. Use existing "uuid" custom property if valid.
    3. If "uuid" custom prop is missing/invalid, check mat.name (and its base).
       If the base of mat.name is a valid UUID string, use it.
    4. Otherwise, generate a new UUID.
    Returns the determined UUID string.
    """
    if mat is None:
        return None

    if is_copy:
        new_uuid_for_copy = str(uuid.uuid4())
        try:
            mat["uuid"] = new_uuid_for_copy
        except Exception as e:
            print(f"[UUID Validate] Warning: Could not set new UUID on copied material {getattr(mat, 'name', 'N/A')}: {e}")
        return new_uuid_for_copy

    # 1. Check existing "uuid" custom property
    uuid_prop_val = mat.get("uuid", "")
    if is_valid_uuid_format(uuid_prop_val):
        return uuid_prop_val

    # 2. If custom property is missing or invalid, check if the base of mat.name is a valid UUID
    current_mat_name = getattr(mat, 'name', None)
    if current_mat_name:
        name_match = _SUFFIX_REGEX_MAT_PARSE.fullmatch(current_mat_name)
        base_name_from_datablock = current_mat_name # Default to full name if no suffix
        if name_match and name_match.group(1): # Ensure group(1) exists (base name part)
            base_name_from_datablock = name_match.group(1)

        if is_valid_uuid_format(base_name_from_datablock):
            # print(f"[UUID Validate] Mat '{current_mat_name}' base '{base_name_from_datablock}' is UUID. Using it and setting custom prop.")
            try:
                mat["uuid"] = base_name_from_datablock # Set the custom property
                return base_name_from_datablock
            except Exception as e:
                print(f"[UUID Validate] Warning: Could not set 'uuid' prop from mat's base name '{base_name_from_datablock}': {e}. Generating new UUID.")
                # Fall through to new UUID generation if setting the property fails

    # 3. If no valid UUID found via prop or name, generate a new one.
    # print(f"[UUID Validate] Mat '{getattr(mat, 'name', 'N/A')}' - No valid UUID from prop or name. Generating new UUID.")
    new_fallback_uuid = str(uuid.uuid4())
    try:
        mat["uuid"] = new_fallback_uuid
    except Exception as e:
        print(f"[UUID Validate] Warning: Could not set newly generated fallback UUID on {getattr(mat, 'name', 'N/A')}: {e}")
    return new_fallback_uuid

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
  
      
def _perform_library_update(force: bool = False, changed_map: dict | None = None):
    """
    [CORRECTED] Performs the background library update.
    - If `changed_map` is provided, only those materials are processed.
    - If `force=True` is used WITHOUT a `changed_map`, it is now treated as a no-op,
      preventing the expensive fallback of processing all local materials.
    """
    print(f"[DEBUG LibUpdate] Starting. Force: {force}, Changed Map Items: {len(changed_map) if changed_map else 0}")

    global g_thumbnail_process_ongoing, g_library_update_pending

    if g_thumbnail_process_ongoing:
        print("[DEBUG LibUpdate] Thumbnail generation is ongoing. Deferring library update.")
        g_library_update_pending = True
        if force and hasattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced'):
            bpy.context.window_manager.matlist_pending_lib_update_is_forced = True
        return False
    
    # --- THIS IS THE CRITICAL FIX ---
    # Only proceed if a specific map of changed materials is provided.
    # The 'force' flag is now only relevant for deferral logic, not for triggering a full scan.
    if not changed_map:
        print("[DEBUG LibUpdate] No explicit 'changed_map' provided. Nothing to transfer to library.")
        return True
    
    mats_to_transfer_map = changed_map
    # --- END OF FIX ---

    if not mats_to_transfer_map:
        print("[DEBUG LibUpdate] Material map was empty. Nothing to transfer.")
        return True

    final_mats_for_write = set()
    for uid, mat_to_write in mats_to_transfer_map.items():
        try:
            # Ensure the datablock is named by its UUID for writing
            if mat_to_write.name != uid:
                conflicting_mat = bpy.data.materials.get(uid)
                if conflicting_mat and conflicting_mat != mat_to_write:
                    # This is a safety check for a rare edge case
                    print(f"      CRITICAL WARNING: Cannot rename '{mat_to_write.name}' to '{uid}'. A DIFFERENT material already has that name. Skipping.")
                    continue
                else:
                    mat_to_write.name = uid
            
            mat_to_write.use_fake_user = True
            
            # Store origin metadata
            display_name = mat_get_display_name(mat_to_write)
            mat_to_write["ml_origin_blend_file"] = bpy.data.filepath if bpy.data.filepath else "UnsavedOrUnknown"
            mat_to_write["ml_origin_mat_name"] = display_name
            mat_to_write["ml_origin_mat_uuid"] = uid
            
            final_mats_for_write.add(mat_to_write)

        except Exception as prep_err:
            print(f"      CRITICAL WARNING: Failed to prepare datablock '{getattr(mat_to_write, 'name', 'N/A')}' for library write: {prep_err}. Skipping.")
            continue
            
    if not final_mats_for_write:
        print("[DEBUG LibUpdate] No materials were successfully prepared for writing.")
        return True

    tmp_dir_for_transfer = ""
    transfer_blend_file_path = ""
    try:
        tmp_dir_for_transfer = tempfile.mkdtemp(prefix="matlib_transfer_")
        transfer_blend_file_path = os.path.join(tmp_dir_for_transfer, f"transfer_data_{uuid.uuid4().hex[:8]}.blend")

        print(f"[DEBUG LibUpdate] Writing {len(final_mats_for_write)} materials to transfer file: {transfer_blend_file_path}")
        bpy.data.libraries.write(transfer_blend_file_path, final_mats_for_write, fake_user=True, compress=True)

        # Staging textures for the worker
        unique_images_to_stage = {}
        for mat in final_mats_for_write:
            if mat.use_nodes and mat.node_tree:
                for node in _get_all_nodes_recursive(mat.node_tree):
                    if node.bl_idname == 'ShaderNodeTexImage' and node.image and not node.image.packed_file and node.image.filepath_raw:
                        source_abs = bpy.path.abspath(node.image.filepath_raw)
                        if os.path.exists(source_abs):
                            target_abs = os.path.join(tmp_dir_for_transfer, os.path.basename(source_abs))
                            if source_abs not in unique_images_to_stage:
                                unique_images_to_stage[source_abs] = target_abs
        
        if unique_images_to_stage:
            print(f"[DEBUG LibUpdate] Staging {len(unique_images_to_stage)} unique image files for worker...")
            for src, dest in unique_images_to_stage.items():
                try:
                    shutil.copy2(src, dest)
                except Exception as e_stage:
                    print(f"    ERROR staging '{src}': {e_stage}")

        if not BACKGROUND_WORKER_PY or not os.path.exists(BACKGROUND_WORKER_PY):
            raise RuntimeError(f"Background worker script missing: {BACKGROUND_WORKER_PY}")

        # --- Background Thread Logic (remains the same) ---
        def _bg_merge_thread_target(transfer_file, target_library, db_path, temp_dir):
            try:
                cmd = [
                    bpy.app.binary_path, "--background", "--factory-startup",
                    "--python", BACKGROUND_WORKER_PY, "--",
                    "--operation", "merge_library", "--transfer", transfer_file,
                    "--target", target_library, "--db", db_path
                ]
                subprocess.run(cmd, check=False, capture_output=True, text=True, timeout=600)
            except Exception as e:
                print(f"[BG Merge Thread] Error: {e}")
            finally:
                if temp_dir and os.path.exists(temp_dir):
                    shutil.rmtree(temp_dir, ignore_errors=True)
        
        bg_thread = Thread(target=_bg_merge_thread_target, args=(
            transfer_blend_file_path, os.path.abspath(LIBRARY_FILE),
            os.path.abspath(DATABASE_FILE), tmp_dir_for_transfer
        ), daemon=True)
        bg_thread.start()
        print(f"[DEBUG LibUpdate] Background merge thread launched for {len(final_mats_for_write)} materials.")

    except Exception as e_write:
        print(f"[DEBUG LibUpdate] Failed during transfer file write: {e_write}")
        traceback.print_exc()
        if 'tmp_dir_for_transfer' in locals() and tmp_dir_for_transfer and os.path.exists(tmp_dir_for_transfer):
            shutil.rmtree(tmp_dir_for_transfer, ignore_errors=True)
        return False
        
    return True

# --------------------------------------------------------------
# Localisation-Worker helper (Unchanged)
# --------------------------------------------------------------
def run_localisation_worker(blend_path: str | None = None, wait: bool = False) -> subprocess.Popen | None: # Unchanged
    blend_path = blend_path or bpy.data.filepath
    if not blend_path or not os.path.exists(WORKER_SCRIPT): return None
    cmd = [bpy.app.binary_path, "-b", blend_path, "--python", WORKER_SCRIPT, "--", "--lib", LIBRARY_FILE, "--db", DATABASE_FILE]
    return subprocess.run(cmd) if wait else subprocess.Popen(cmd)

def promote_material_by_recency_counter(material_uuid: str):
    """
    Optimized method to promote a material to the top of the sort order.
    It retrieves the current highest recency number and assigns 'highest + 1'
    to the target material's sort_index. This is extremely fast as it only
    ever updates a single row.
    """
    if not material_uuid:
        return

    try:
        with get_db_connection() as conn:
            # Get the current maximum sort_index in the entire table.
            # COALESCE ensures that if the table is empty, we get 0 instead of NULL.
            c = conn.cursor()
            c.execute("SELECT COALESCE(MAX(sort_index), 0) FROM material_order")
            max_index = c.fetchone()[0]
            
            # The new "top" index is simply the next number in the sequence.
            new_top_index = max_index + 1
            
            # Use INSERT OR REPLACE to handle both new and existing materials in one query.
            # If the UUID exists, it updates its sort_index.
            # If the UUID is new, it inserts it with the new sort_index.
            c.execute("INSERT OR REPLACE INTO material_order (uuid, sort_index) VALUES (?, ?)", (material_uuid, new_top_index))
            conn.commit()

    except Exception as e:
        print(f"[PromoteMaterial] Database error for UUID {material_uuid}: {e}")
        traceback.print_exc()

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

def set_active_index_to_top(context):
    """
    Deferred function to set the active index to 0.
    This runs after the UI has had a chance to update and filter.
    """
    scene = context.scene
    if scene and hasattr(scene, 'material_list_items') and scene.material_list_items:
        # Check if the current index is still valid in the filtered view.
        # This is a bit tricky, but a simple reset to 0 is the main goal.
        scene.material_list_active_index = 0
    return None # Timer stops itself

def update_filter_and_select_top(self, context):
    """
    Update callback for filter toggles.
    It forces a redraw and schedules the active index to be set to 0.
    """
    force_redraw()
    
    # Schedule the selection to happen in the near future, after the UI has updated.
    # We check if a timer is already scheduled to avoid stacking them.
    if not bpy.app.timers.is_registered(lambda: set_active_index_to_top(context)):
        bpy.app.timers.register(lambda: set_active_index_to_top(context), first_interval=0.02)
        
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
def update_material_library(force_update=False, changed_materials_map=None):
    global is_update_processing
    if not is_update_processing:
        # Create the task dictionary for the queue, now including the explicit map of changes.
        task = {
            'type': 'UPDATE',
            'force': force_update,
            'changed_map': changed_materials_map or {} # Ensure it's always a dict
        }
        library_update_queue.append(task)
        is_update_processing = True
        bpy.app.timers.register(process_library_queue)

def _parse_material_suffix(name: str) -> tuple[str, int]:
    """
    Parses a material name into its base name and suffix number.
    Example: "mat_Plastic.001" -> ("mat_Plastic", 1)
             "mat_Plastic" -> ("mat_Plastic", -2) (no suffix is considered lowest)
             "mat_Plastic.000" -> ("mat_Plastic", 0)
    Returns (base_name, suffix_number)
    """
    match = _SUFFIX_REGEX_MAT_PARSE.fullmatch(name)
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
    Builds the complete, unfiltered master material list.
    All filtering is now handled by the much faster UIList.filter_items method.
    """
    global material_list_cache, list_version
    
    if not scene:
        print("[Populate List] Error: Scene object is None.")
        return

    print("[Populate List] Rebuilding master material list (unfiltered)...")

    try:
        if hasattr(scene, "material_list_items"):
            scene.material_list_items.clear()
        else:
            print("[Populate List] Error: Scene missing 'material_list_items'. Cannot populate.")
            return
        
        material_list_cache.clear()

        all_mats_data = []
        for mat in bpy.data.materials:
            if not mat or not hasattr(mat, 'name'):
                continue
                
            # <<< FIX: Skip our internal hashing materials from appearing in the UI list >>>
            if mat.name.startswith("__hashing_"):
                continue

            try:
                all_mats_data.append({
                    'mat_obj': mat,
                    'uuid': get_material_uuid(mat),
                    'display_name': mat_get_display_name(mat),
                    'is_library': bool(mat.library),
                    'is_protected': mat.get('is_protected', False),
                    'original_name': mat.get("orig_name", mat_get_display_name(mat)),
                })
            except (ReferenceError, Exception):
                continue

        # Step 3: De-duplicate the list to get a single, canonical entry per material concept
        material_info_map = {}
        mat_prefix_candidates = {}
        
        for item_info_dict in all_mats_data:
            display_name = item_info_dict['display_name']
            if display_name.startswith("mat_"):
                # Find the "base" material (e.g., mat_Plastic from mat_Plastic.001, .002)
                base_name, suffix_num = _parse_material_suffix(display_name)
                item_info_dict['suffix_num'] = suffix_num
                existing = mat_prefix_candidates.get(base_name)
                if not existing or suffix_num < existing['suffix_num']:
                    mat_prefix_candidates[base_name] = item_info_dict
            else:
                # Ensure only one entry per UUID (preferring local over library versions)
                uuid = item_info_dict['uuid']
                existing = material_info_map.get(uuid)
                if not existing or (not item_info_dict['is_library'] and existing['is_library']):
                    material_info_map[uuid] = item_info_dict
        
        # Add the de-duplicated mat_ items to the main map
        for base_name, chosen_info in mat_prefix_candidates.items():
            if chosen_info['uuid'] not in material_info_map:
                material_info_map[chosen_info['uuid']] = chosen_info
        
        items_to_process_for_ui = list(material_info_map.values())
        
        # Step 4: Sort the de-duplicated list based on the scene property
        if scene.material_list_sort_alpha:
            sorted_list = sorted(items_to_process_for_ui, key=lambda item: item['display_name'].lower())
        else:  # Default sort by recency from database
            material_sort_indices = {}
            try:
                with get_db_connection() as conn:
                    c = conn.cursor()
                    c.execute("SELECT uuid, sort_index FROM material_order")
                    material_sort_indices = {row[0]: row[1] for row in c.fetchall()}
            except Exception as e:
                print(f"[Populate List] Error loading sort indices: {e}")
            
            for info in items_to_process_for_ui:
                info['sort_key'] = material_sort_indices.get(info['uuid'], -1)
            sorted_list = sorted(items_to_process_for_ui, key=lambda item: -item['sort_key'])

        # Step 5: Populate Blender's list and our fast UI cache
        current_list_version_for_pop = list_version # Capture version before populating

        for item_data in sorted_list:
            list_item = scene.material_list_items.add()
            list_item.material_name = item_data['display_name']
            list_item.material_uuid = item_data['uuid']
            list_item.is_library = item_data['is_library']
            list_item.original_name = item_data['original_name']
            list_item.is_protected = item_data['is_protected']
            
            material_list_cache.append({
                'uuid': item_data['uuid'],
                'icon_id': 0, # Default to 0, signals "not loaded"
                'version': current_list_version_for_pop, # MODIFICATION: Store the current version
                'is_missing': not bool(item_data.get('mat_obj')),
                'display_name': item_data['display_name'],
                'is_protected': item_data.get('is_protected', False)
            })

        print(f"[Populate List] Master list rebuild complete with {len(scene.material_list_items)} items.")
        list_version += 1 # MODIFICATION: Increment AFTER population is done
        
        # Step 6: Trigger the asynchronous icon loading process
        if not called_from_finalize_run and 'update_material_thumbnails' in globals():
            print("[Populate List] Triggering background thumbnail update for the new list.")
            update_material_thumbnails()

    except Exception as e:
        print(f"[Populate List] CRITICAL error during list population: {e}")
        traceback.print_exc()

def get_material_by_unique_id(unique_id): # Unchanged
    for mat in bpy.data.materials:
        if str(id(mat)) == unique_id: return mat
    return None

def initialize_db_connection_pool():
    print("[DB Pool] Initializing database connection pool...", flush=True)
    try:
        if not LIBRARY_FOLDER or not os.path.isdir(LIBRARY_FOLDER):
            if _ADDON_DATA_ROOT and os.path.isdir(_ADDON_DATA_ROOT):
                os.makedirs(LIBRARY_FOLDER, exist_ok=True)
                print(f"[DB Pool] Created LIBRARY_FOLDER: {LIBRARY_FOLDER}")
            else:
                print(f"[DB Pool] CRITICAL: LIBRARY_FOLDER ('{LIBRARY_FOLDER}') is not a valid directory. Cannot initialize pool for '{DATABASE_FILE}'.")
                return

        temp_connections = []
        for i in range(5):
            db_dir = os.path.dirname(DATABASE_FILE)
            if not os.path.isdir(db_dir):
                print(f"[DB Pool] Database directory '{db_dir}' does not exist. Attempting to create.")
                os.makedirs(db_dir, exist_ok=True)

            # This tells SQLite to wait for 10 seconds if the DB is locked before erroring out.
            conn = sqlite3.connect(DATABASE_FILE, check_same_thread=False, timeout=10.0)
            
            temp_connections.append(conn)

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
def save_pre_handler(dummy):
    """
    ULTRA-LIGHTWEIGHT: Initializes new materials and syncs dirty ones before save.
    """
    global g_material_processing_timer_active, g_materials_are_dirty

    print(f"\n[{datetime.now().strftime('%H:%M:%S.%f')[:-3]} SAVE_PRE] Triggered.")

    # Synchronously initialize any new materials BEFORE processing them.
    # This now correctly skips "mat_" materials.
    initialize_material_properties()

    # If materials are dirty, run the processor once, right now.
    if g_materials_are_dirty:
        process_dirty_materials_timer()
    
    # This validation loop is now partially redundant but acts as a good safety net.
    # It also needs to skip "mat_" materials.
    mats_to_process = list(bpy.data.materials)
    for mat in mats_to_process:
        if not mat or mat.name.startswith("__hashing_") or mat.name.startswith("mat_"):
            continue
        
        current_uuid = validate_material_uuid(mat, is_copy=False)
        if not mat.library and mat.name != current_uuid:
            try:
                existing = bpy.data.materials.get(current_uuid)
                if not existing or existing == mat:
                    mat.name = current_uuid
            except Exception: pass
        if not mat.library and not mat.use_fake_user:
            try:
                mat.use_fake_user = True
            except Exception: pass
    
    # Ensure the timer is running for future background checks after the save completes.
    if not g_material_processing_timer_active:
        bpy.app.timers.register(process_dirty_materials_timer, first_interval=2.0)
        g_material_processing_timer_active = True
    
def non_blocking_task_collector():
    """
    [OPTIMIZED v2] This function is registered with a timer and acts as a
    "Producer". It scans a small batch of materials, and if it finds a task,
    it IMMEDIATELY queues it for the workers instead of waiting for the scan
    to finish. This provides instant feedback to the user.
    """
    global g_task_collection_iterator, g_thumbnail_process_ongoing

    # If the iterator hasn't been created, create it.
    if g_task_collection_iterator is None:
        # This generator yields one material at a time.
        g_task_collection_iterator = (mat for mat in bpy.data.materials)

    # Process a small chunk of materials in this timer tick
    for _ in range(COLLECTION_BATCH_SIZE):
        try:
            # Get the next material from our generator
            mat = next(g_task_collection_iterator)
            if not mat or mat.name.startswith("__hashing_"):
                continue

            # Check if this specific material needs a thumbnail
            task = get_custom_icon(mat, collect_mode=True)

            # If a task is returned, queue it IMMEDIATELY
            if isinstance(task, dict):
                print(f"[Collector] Found task for '{mat.name}'. Queuing immediately.")
                _queue_all_pending_tasks(single_task_list=[task])
                ensure_thumbnail_queue_processor_running()

        except StopIteration:
            # We have processed all materials. The collection is done.
            print("[Collector] Finished scanning all materials.")
            g_task_collection_iterator = None
            # We don't call finalize_thumbnail_run() here, because workers might still be busy.
            # The process_thumbnail_tasks loop will handle finalization when all work is done.
            return None # Stop this timer.
        except Exception as e:
            print(f"[Collector] Error: {e}")
            traceback.print_exc()
            g_task_collection_iterator = None
            return None # Stop this timer on error

    return 0.01 # Continue the timer to process the next chunk.

@persistent
def save_post_handler(dummy=None):
    """
    Post-save callback.
    CORRECTED: Intelligently calls the UI refresh function only when materials
    have actually been modified, fixing both the save-time lag for unchanged files
    and ensuring the UI updates for new materials.
    """
    global materials_modified, g_matlist_transient_tasks_for_post_save

    t0 = time.time()

    # --- CORE FIX ---
    # Only if materials were actually changed during the pre-save handler,
    # do we need to trigger a full UI refresh and thumbnail check.
    if materials_modified:
        print("[POST-SAVE] Material modifications detected. Refreshing UI and checking thumbnails.")
        
        # 1. Refresh the UI list and reset the selection.
        #    This is now correctly placed here, so it only runs when needed.
        if 'populate_and_reset_selection' in globals():
            populate_and_reset_selection(bpy.context)
        
        # 2. Trigger thumbnail generation for specifically changed materials.
        specific_tasks = list(g_matlist_transient_tasks_for_post_save)
        if 'update_material_thumbnails' in globals() and callable(update_material_thumbnails):
            if specific_tasks:
                update_material_thumbnails(specific_tasks_to_process=specific_tasks)
            else:
                update_material_thumbnails()
    
    # --- END CORE FIX ---

    # Cleanup and logging logic remains the same.
    g_matlist_transient_tasks_for_post_save.clear()

    try:
        _log_blend_material_usage()
    except Exception as e:
        print(f"[POST-SAVE] usage-log error: {e}")

    # Reset the flag for the next depsgraph update.
    materials_modified = False
    
    if hasattr(bpy.context.window_manager, 'matlist_save_handler_processed'):
        bpy.context.window_manager.matlist_save_handler_processed = False

    print(f"[POST-SAVE] handler Python time: {time.time() - t0:.4f}s")

def _log_blend_material_usage():
    """Write / refresh the blend_material_usage rows for this .blend."""
    if not bpy.data.filepath or not os.path.exists(LIBRARY_FILE):
        return

    library_norm = os.path.normcase(os.path.abspath(LIBRARY_FILE))
    used_lib_uuids = set()

    for obj in bpy.data.objects:
        if obj.type != 'MESH':
            continue
        for slot in obj.material_slots:
            mat = slot.material
            if mat and mat.library and \
               os.path.normcase(bpy.path.abspath(mat.library.filepath)) == library_norm:
                uid = get_material_uuid(mat)
                if uid:
                    used_lib_uuids.add(uid)

    with get_db_connection() as conn:
        cur = conn.cursor()
        cur.execute("DELETE FROM blend_material_usage WHERE blend_filepath=?",
                    (bpy.data.filepath,))
        if used_lib_uuids:
            rows = [(bpy.data.filepath, u, int(time.time())) for u in used_lib_uuids]
            cur.executemany("""INSERT OR IGNORE INTO blend_material_usage
                               (blend_filepath, material_uuid, timestamp)
                               VALUES (?, ?, ?)""", rows)
        conn.commit()

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
                    # <<< MODIFICATION: Replace terminate/kill logic >>>
                    time.sleep(0.1)
                    process.kill()
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

class MATERIALLIST_OT_duplicate_or_localise_material(Operator):
    """Duplicates a local material, or creates a local, editable copy of a library material"""
    bl_idname = "materiallist.duplicate_or_localise"
    bl_label = "Create Local Copy"
    bl_options = {'REGISTER', 'UNDO'}

    @classmethod
    def poll(cls, context):
        scene = context.scene
        if not (scene and hasattr(scene, 'material_list_items')):
            return False
        
        # Enable the button as long as there is a valid selection.
        # The execute method will handle the different behaviors.
        idx = scene.material_list_active_index
        return 0 <= idx < len(scene.material_list_items)

    def execute(self, context):
        global material_names, _display_name_cache
        scene = context.scene
        idx = scene.material_list_active_index
        original_item = scene.material_list_items[idx]
        original_mat = get_material_by_uuid(original_item.material_uuid)

        if not original_mat:
            self.report({'WARNING'}, "Selected material data not found.")
            return {'CANCELLED'}

        original_display_name = mat_get_display_name(original_mat)

        # --- BRANCH 1: The selected material is from the LIBRARY ---
        if original_mat.library:
            try:
                # This block contains the logic from the old "Make Local" operator
                local_mat = original_mat.copy()
                local_mat.library = None # Make it a local datablock
                
                new_local_uuid = str(uuid.uuid4())
                local_mat["uuid"] = new_local_uuid
                local_mat.name = new_local_uuid # Name the datablock by its new UUID
                
                # Keep the original display name for the new local copy
                material_names[new_local_uuid] = original_display_name
                save_material_names()
                
                local_mat["from_library_uuid"] = get_material_uuid(original_mat)
                local_mat.use_fake_user = True
                
                # Promote to the top of the recency list
                promote_material_by_recency_counter(new_local_uuid)
                
                # Replace all instances of the library material with the new local one
                for obj in bpy.data.objects:
                    if obj.material_slots:
                        for slot in obj.material_slots:
                            if slot.material == original_mat:
                                slot.material = local_mat
                                
                _display_name_cache.clear()
                populate_and_reset_selection(context)
                
                if hasattr(local_mat, "preview"):
                    force_update_preview(local_mat)
                    
                self.report({'INFO'}, f"Created local copy of library material '{original_display_name}'")

            except Exception as e:
                self.report({'ERROR'}, f"Failed to create local copy: {e}")
                traceback.print_exc()
                return {'CANCELLED'}

        # --- BRANCH 2: The selected material is already LOCAL ---
        else:
            try:
                # This block contains the logic from the old "Duplicate" operator
                new_mat = original_mat.copy()
                
                new_local_uuid = str(uuid.uuid4())
                new_mat["uuid"] = new_local_uuid
                new_mat.name = new_local_uuid
                
                # Create a new, unique display name for the duplicate
                base_name = original_display_name.rsplit('.', 1)[0] if '.' in original_display_name else original_display_name
                new_display_name = get_unique_display_name(f"{base_name}.copy")
                
                material_names[new_local_uuid] = new_display_name
                save_material_names()
                
                new_mat.use_fake_user = True
                
                # Promote the new duplicate to the top of the recency list
                promote_material_by_recency_counter(new_local_uuid)
                
                _display_name_cache.clear()
                populate_and_reset_selection(context)

                self.report({'INFO'}, f"Duplicated local material '{original_display_name}' as '{new_display_name}'")

            except Exception as e:
                self.report({'ERROR'}, f"Failed to duplicate material: {e}")
                traceback.print_exc()
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
                # <<< MODIFICATION: Replace terminate/kill logic >>>
                time.sleep(0.1)
                self._proc.kill()
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

def is_mat_prefixed(slot_mat):
    """True if the visible display name starts with 'mat_'."""
    return (
        slot_mat
        and mat_get_display_name(slot_mat).startswith("mat_")
    )

class MATERIALLIST_OT_unassign_mat(bpy.types.Operator):
    """Remove material slots containing materials that start with 'mat_' from all mesh objects"""
    bl_idname = "materiallist.unassign_mat"
    bl_label = "Remove 'mat_' Material Slots"
    bl_options = {'REGISTER', 'UNDO'}

    def execute(self, context):
        view_layer = context.view_layer
        initial_active = view_layer.objects.active
        initial_mode = context.mode

        # Ensure we're in Object Mode once
        if bpy.ops.object.mode_set.poll():
            bpy.ops.object.mode_set(mode='OBJECT')

        processed_objects = 0
        total_removed = 0

        # Loop through all mesh objects
        for obj in context.scene.objects:
            if obj.type != 'MESH':
                continue

            mats = obj.data.materials
            # Build a filtered list of slots to keep
            kept = [m for m in mats if not (m and m.name.startswith('mat_'))]
            removed = len(mats) - len(kept)
            if removed <= 0:
                continue

            processed_objects += 1
            total_removed += removed

            # Bulk‐remove & reassign
            mats.clear()
            for mat in kept:
                mats.append(mat)

        # Restore original active object
        if initial_active and initial_active.name in bpy.data.objects:
            view_layer.objects.active = initial_active

        # Restore original mode
        if bpy.ops.object.mode_set.poll():
            bpy.ops.object.mode_set(mode=initial_mode)

        self.report(
            {'INFO'},
            f"Processed {processed_objects} mesh objects, removed {total_removed} 'mat_' slots"
        )
        return {'FINISHED'}

class MATERIALLIST_OT_install_psutil(bpy.types.Operator):
    """Installs the 'psutil' library for system resource monitoring."""
    bl_idname = "materiallist.install_psutil"
    bl_label = "Install Resource Monitor (psutil)"
    bl_description = "Downloads and installs the 'psutil' Python library required for dynamic resource monitoring. Requires an internet connection."
    bl_options = {'REGISTER'}

    def execute(self, context):
        try:
            python_exe = sys.executable
            # Ensure pip is up to date
            subprocess.call([python_exe, "-m", "pip", "install", "--upgrade", "pip"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            # Install psutil
            # Using --user can help avoid permission errors in some cases
            result = subprocess.call([python_exe, "-m", "pip", "install", "psutil", "--user"])

            if result == 0:
                self.report({'INFO'}, "'psutil' installed successfully. Please restart Blender to enable the feature.")
            else:
                self.report({'ERROR'}, "Installation failed. Check Blender's System Console for errors.")
                print("[MaterialList] 'psutil' installation failed. Please try installing it manually from the command line.", file=sys.stderr)

        except Exception as e:
            self.report({'ERROR'}, f"An error occurred: {e}")
            print(f"[MaterialList] An error occurred while trying to install 'psutil': {e}", file=sys.stderr)
            traceback.print_exc()

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
            # --- The only change is this line ---
            promote_material_by_recency_counter(target_uuid)
            
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
    bl_options = {'REGISTER', 'UNDO'} # <--- ADD 'UNDO' HERE

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
            # --- The only change is this line ---
            promote_material_by_recency_counter(target_uuid)
            
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
        mat = get_material_by_uuid(item.material_uuid)
        return mat is not None and mat.library is not None

    def execute(self, context):
        global material_names, _display_name_cache
        scene = context.scene
        idx = scene.material_list_active_index
        item = scene.material_list_items[idx]
        lib_mat = get_material_by_uuid(item.material_uuid)
        if lib_mat is None or not lib_mat.library:
            self.report({'ERROR'}, "Selected material is not a library material."); return {'CANCELLED'}
        try:
            display_name_from_lib = mat_get_display_name(lib_mat)
            local_mat = lib_mat.copy(); local_mat.library = None
            new_local_uuid = str(uuid.uuid4()); local_mat["uuid"] = new_local_uuid
            local_mat.name = new_local_uuid
            material_names[new_local_uuid] = display_name_from_lib
            local_mat["from_library_uuid"] = get_material_uuid(lib_mat)
            local_mat.use_fake_user = True
            promote_material_by_recency_counter(new_local_uuid)
            for obj in bpy.data.objects:
                if obj.material_slots:
                    for slot in obj.material_slots:
                        if slot.material == lib_mat: slot.material = slot.material
            _display_name_cache.clear()
            
            populate_and_reset_selection(context)

            if hasattr(local_mat, "preview"): force_update_preview(local_mat)
            self.report({'INFO'}, f"Converted '{display_name_from_lib}' to a local material.")
        except Exception as e:
            self.report({'ERROR'}, f"Failed to create local copy: {e}"); traceback.print_exc(); return {'CANCELLED'}
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

class MATERIALLIST_OT_refresh_material_list(Operator):
    bl_idname = "materiallist.refresh_material_list"
    bl_label = "Refresh List & Check Thumbs"
    bl_description = "Refresh the material list UI, reset selection to the top, and initiate checks for missing thumbnails"

    def execute(self, context):
        try:
            populate_and_reset_selection(context)

            if 'update_material_thumbnails' in globals() and callable(update_material_thumbnails):
                update_material_thumbnails()

            self.report({'INFO'}, "Material list refreshed & selection reset.")
        except Exception as e:
            self.report({'ERROR'}, f"Error during refresh: {e}")
            traceback.print_exc()
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
                    
                    # --- The only change is this line ---
                    promote_material_by_recency_counter(new_uuid)
                    
                    new_local_mat["hash_dirty"] = True; new_local_mat.use_fake_user = True
                    print(f"[Integrate Lib DB] Copied '{display_name_from_source}' as local '{new_local_mat.name}', added name to DB, moved to top of list.")
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
    bl_description = (
        "On the active object: if in Edit Mode with faces selected, finds the material "
        "used by the largest number of selected faces. Otherwise, finds the material "
        "used by the largest number of total faces. Selects it in the list."
    )

    @classmethod
    def poll(cls, context):
        ob = context.active_object
        return ob and ob.type == 'MESH'

    def execute(self, context):
        ob = context.active_object
        me = ob.data
        scene = context.scene

        if not me.materials:
            self.report({'WARNING'}, "Object has no materials.")
            return {'CANCELLED'}

        counts = {}
        faces_to_consider = []
        is_edit_mode_with_selection = False

        if ob.mode == 'EDIT':
            bm = bmesh.from_edit_mesh(me)
            bm.faces.ensure_lookup_table() # Ensure indices are up to date
            selected_faces = [f for f in bm.faces if f.select]
            if selected_faces:
                is_edit_mode_with_selection = True
                faces_to_consider = selected_faces
                # print(f"[Select Dominant] Edit Mode: Found {len(selected_faces)} selected faces.")
            else:
                # No faces selected in Edit Mode, consider all faces
                faces_to_consider = list(bm.faces) # Make a copy
                # print(f"[Select Dominant] Edit Mode: No faces selected, considering all {len(faces_to_consider)} faces.")
            # We don't free bm here if selected_faces were used, as they are references.
            # If we made a copy for all faces, bm can be freed earlier if we are done with it.
            # However, for simplicity, let's free it after counts are gathered.
        else: # Object Mode
            # print(f"[Select Dominant] Object Mode: Will consider all faces.")
            # Create a temporary BMesh to access face data
            bm = bmesh.new()
            bm.from_mesh(me)
            bm.faces.ensure_lookup_table()
            faces_to_consider = list(bm.faces) # Make a copy
            # bm.free() # Free immediately if created just for this block

        if not faces_to_consider:
            if is_edit_mode_with_selection:
                self.report({'WARNING'}, "No faces are selected.")
            else:
                self.report({'WARNING'}, "Object has no faces to analyze.")
            if ob.mode == 'OBJECT' and 'bm' in locals() and bm.is_wrapped: # Check if bm exists and is valid from Object mode
                 bm.free()
            elif ob.mode == 'EDIT' and 'bm' in locals(): # For edit mode, bmesh.from_edit_mesh does not need explicit free
                pass
            return {'CANCELLED'}

        for f in faces_to_consider:
            counts[f.material_index] = counts.get(f.material_index, 0) + 1

        # Free BMesh if it was created (Object Mode) or if from_edit_mesh was used (Edit Mode)
        if 'bm' in locals():
            if bm.is_wrapped: # True if created by bmesh.new()
                bm.free()
            # else: bmesh.from_edit_mesh() doesn't need explicit free, changes are written back or discarded by Blender

        if not counts:
            if is_edit_mode_with_selection:
                self.report({'WARNING'}, "Selected faces have no material assignments, or materials are invalid.")
            else:
                self.report({'WARNING'}, "No material assignments found on object faces.")
            return {'CANCELLED'}

        try:
            dominant_idx = max(counts, key=counts.get)
        except ValueError: # Should not happen if counts is not empty
            self.report({'WARNING'}, "Could not determine dominant material index.")
            return {'CANCELLED'}

        if not (0 <= dominant_idx < len(me.materials)):
            self.report({'WARNING'}, f"Dominant material index {dominant_idx} is out of bounds for material slots.")
            return {'CANCELLED'}

        dominant_mat = me.materials[dominant_idx]
        if not dominant_mat:
            self.report({'WARNING'}, f"Dominant material slot {dominant_idx} has no material assigned.")
            return {'CANCELLED'}

        dominant_uuid = get_material_uuid(dominant_mat)
        if not dominant_uuid:
            self.report({'WARNING'}, f"Could not get UUID for dominant material '{dominant_mat.name}'.")
            return {'CANCELLED'}

        found_in_list = False
        for i, itm in enumerate(scene.material_list_items):
            if itm.material_uuid == dominant_uuid:
                scene.material_list_active_index = i
                found_in_list = True
                break
        
        if found_in_list:
            mode_info = "selected faces" if is_edit_mode_with_selection else "object"
            self.report({'INFO'}, f"Selected '{mat_get_display_name(dominant_mat)}' (dominant on {mode_info})")
        else:
            self.report({'WARNING'}, f"Dominant material '{mat_get_display_name(dominant_mat)}' not found in the UI list.")
            # Optionally, refresh the list here if this happens
            # populate_material_list(scene) 
            # force_redraw()

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
    scene_to_save_in_template = None # Will be defined by the inserted snippet
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
                break # Avoid infinite loop if removal fails

        # --- END CRITICAL PRE-CLEANUP ---

        temp_setup_scene = bpy.data.scenes.new(temp_setup_scene_name)
        if not temp_setup_scene:
            print("[IconTemplate Ensure] CRITICAL: Failed to create temporary setup scene for context.")
            return False

        # --- START OF USER'S PROVIDED SNIPPET ---
        # Create data blocks (mesh, camera, light) as before
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
        created_data_blocks_for_template_file.append(light_data)

        # --- MODIFICATION: Create the scene_to_save_in_template earlier ---
        print(f"[IconTemplate Ensure] Creating scene for template file with target name: '{template_scene_name_in_file}'")
        scene_to_save_in_template = bpy.data.scenes.new(template_scene_name_in_file)
        if not scene_to_save_in_template: # Your original check was later, this is a good place for it
            print(f"[IconTemplate Ensure] CRITICAL: Failed to create target template scene with name '{template_scene_name_in_file}'.")
            raise RuntimeError(f"Failed to create target template scene '{template_scene_name_in_file}'.")

        print(f"[IconTemplate Ensure] Scene created with actual name: '{scene_to_save_in_template.name}'. Intended: '{template_scene_name_in_file}'.")
        if scene_to_save_in_template.name != template_scene_name_in_file: # Your original check
            print(f"[IconTemplate Ensure] CRITICAL WARNING: Created scene name '{scene_to_save_in_template.name}' "
                  f"does not match target '{template_scene_name_in_file}'. This will likely cause worker failure. "
                  "Check pre-cleanup logs for scene removal issues.")
            raise RuntimeError(f"Template scene created with incorrect name: {scene_to_save_in_template.name} vs target {template_scene_name_in_file}")
        # --- End scene creation block, scene_to_save_in_template now exists ---
        # Add scene and its collection to the list of items to be written (as in your original code)
        created_data_blocks_for_template_file.append(scene_to_save_in_template)
        created_data_blocks_for_template_file.append(scene_to_save_in_template.collection)


        preview_obj = bpy.data.objects.new(preview_obj_name, mesh_data)
        # *** MODIFICATION: Link to scene's collection BEFORE modifying transform ***
        scene_to_save_in_template.collection.objects.link(preview_obj)
        # Now modify properties
        preview_obj.rotation_euler = (0, math.radians(-25), math.radians(-45))
        wn_mod = preview_obj.modifiers.new(name="WeightedNormal", type='WEIGHTED_NORMAL')
        created_data_blocks_for_template_file.append(preview_obj)

        cam_obj = bpy.data.objects.new(camera_obj_name, cam_data)
        # *** MODIFICATION: Link to scene's collection BEFORE modifying transform ***
        scene_to_save_in_template.collection.objects.link(cam_obj)
        # Now modify properties
        cam_obj.location = (1.7, -1.7, 1.4)
        cam_obj.rotation_euler = (math.radians(60), 0, math.radians(45))
        created_data_blocks_for_template_file.append(cam_obj)

        light_obj = bpy.data.objects.new(light_obj_name, light_data)
        # *** MODIFICATION: Link to scene's collection BEFORE modifying transform ***
        scene_to_save_in_template.collection.objects.link(light_obj)
        # Now modify properties
        light_obj.location = (0.15, -2.0, 1.3)
        created_data_blocks_for_template_file.append(light_obj)

        # Set active camera for the scene (this was after linking in your original, which is fine)
        scene_to_save_in_template.camera = cam_obj

        # Set light energy (this was after linking in your original try-catch, which is correct)
        try:
            light_data.energy = 240
            print(f"[IconTemplate Ensure] Set light_data.energy = {light_data.energy} after linking object.")
        except AttributeError as e_energy: # Your specific exception handling
            print(f"[IconTemplate Ensure] CRITICAL ERROR setting light energy even after linking: {e_energy}")
            traceback.print_exc()
            raise
        except Exception as e_generic_energy:
            print(f"[IconTemplate Ensure] CRITICAL GENERIC ERROR setting light energy: {e_generic_energy}")
            traceback.print_exc()
            raise
        # --- END OF USER'S PROVIDED SNIPPET ---

        # ... (The rest of your function: render settings, writing to file, verification, cleanup) proceeds from here
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

        # Note: The lines below were originally here, but are now handled within the user's snippet.
        # created_data_blocks_for_template_file.append(scene_to_save_in_template)
        # created_data_blocks_for_template_file.append(scene_to_save_in_template.collection)

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
def migrate_thumbnail_files(dummy): # Unchanged in core logic, just uses pre-compiled regex
    global THUMBNAIL_FOLDER # Ensure THUMBNAIL_FOLDER is accessible
    # _LEGACY_THUMBNAIL_PATTERN is now a global, no need to define 'legacy_pattern' locally

    if not os.path.exists(THUMBNAIL_FOLDER): return
    migrated_count = 0
    # Local 'legacy_pattern' variable is removed
    try:
        for filename in os.listdir(THUMBNAIL_FOLDER):
            src_path = os.path.join(THUMBNAIL_FOLDER, filename)
            # Use the pre-compiled global pattern here
            if not _LEGACY_THUMBNAIL_PATTERN.match(filename): continue # MODIFIED LINE
            hash_value = filename.split("_")[1].split(".")[0]
            dest_path = get_thumbnail_path(hash_value) # Assumes get_thumbnail_path is defined
            if not os.path.exists(dest_path): os.rename(src_path, dest_path); migrated_count += 1
            else: os.remove(src_path) # Remove duplicate legacy
    except Exception as e: print(f"Thumbnail Migration Error: {str(e)}"); traceback.print_exc()
    # print(f"Thumbnail Migration: {migrated_count} files migrated.") # Optional log

# --------------------------
# Thumbnail Generation Core Logic (get_custom_icon, generate_thumbnail_async, update_material_thumbnails)
# --------------------------
def get_custom_icon(mat, collect_mode=False):
    """
    [CORRECTED v4] Gets a custom icon, or prepares a task if one is needed.
    This version includes the critical check against the global "in-flight" task set
    to prevent the infinite re-queuing of tasks during a single run.
    """
    global custom_icons
    global g_current_run_task_hashes_being_processed, _ICON_TEMPLATE_VALIDATED

    if not mat:
        return 0

    # --- Hashing and Initial "In-Flight" Check ---
    current_material_hash = get_material_hash(mat)
    if not current_material_hash:
        return 0

    # -------------------------------------------------------------------
    # --- THIS IS THE CRITICAL FIX TO PREVENT THE INFINITE LOOP ---
    #
    # If we have already queued this exact hash for processing in this run,
    # then we must do nothing and exit immediately. This prevents the collector
    # from finding the same missing icon over and over again while the worker
    # is still busy processing the first request.
    #
    if current_material_hash in g_current_run_task_hashes_being_processed:
        return 0 # Task is already in the pipeline, do not create a duplicate.
    #
    # --- END OF CRITICAL FIX ---
    # -------------------------------------------------------------------

    # --- Check Caches (If not already in flight) ---
    # Check 1: Blender's internal preview cache (fastest)
    if current_material_hash in custom_icons:
        cached_preview_item = custom_icons[current_material_hash]
        if hasattr(cached_preview_item, 'icon_id') and cached_preview_item.icon_id > 0:
            if cached_preview_item.icon_size[0] > 1:
                return cached_preview_item.icon_id
            else:
                del custom_icons[current_material_hash] # Corrupt cache entry

    # Check 2: If a valid file already exists on disk
    thumbnail_file_path = get_thumbnail_path(current_material_hash)
    if os.path.isfile(thumbnail_file_path) and os.path.getsize(thumbnail_file_path) > 0:
        try:
            preview_item_from_disk = custom_icons.load(current_material_hash, thumbnail_file_path, 'IMAGE')
            if preview_item_from_disk.icon_size[0] > 1:
                return preview_item_from_disk.icon_id
            else: # Corrupt file on disk
                del custom_icons[current_material_hash]
                os.remove(thumbnail_file_path)
        except (RuntimeError, OSError, Exception):
            pass # Problem loading the file, fall through to regenerate

    # --- If we reach here, a thumbnail must be generated ---
    if not _ICON_TEMPLATE_VALIDATED:
        if not _verify_icon_template(): return 0
        _ICON_TEMPLATE_VALIDATED = True

    blend_file_path_for_worker = None
    if mat.library and mat.library.filepath:
        blend_file_path_for_worker = bpy.path.abspath(mat.library.filepath)
    elif not mat.library and bpy.data.filepath:
        blend_file_path_for_worker = bpy.path.abspath(bpy.data.filepath)
    else:
        return 0 # Cannot process local material in an unsaved file

    if not blend_file_path_for_worker or not os.path.exists(blend_file_path_for_worker):
        return 0

    mat_uuid_for_task = get_material_uuid(mat)
    if not mat_uuid_for_task: return 0

    # --- Add to "In-Flight" Set ---
    # Since we are about to create a task, add its hash to our "in-flight" set immediately
    # so that the next call to this function knows not to re-create it.
    g_current_run_task_hashes_being_processed.add(current_material_hash)

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

def _queue_all_pending_tasks(single_task_list=None):
    """
    [CORRECTED v4] Queues tasks. The responsibility for tracking "in-flight"
    tasks is now handled by get_custom_icon, simplifying this function.
    """
    global g_tasks_for_current_run, thumbnail_task_queue, g_dispatch_lock
    global g_outstanding_task_count, _ADDON_DATA_ROOT, THUMBNAIL_SIZE

    with g_dispatch_lock:
        tasks_to_process = single_task_list if single_task_list is not None else g_tasks_for_current_run
        if not tasks_to_process:
            return

        tasks_by_blend_file = {}
        for task in tasks_to_process:
            blend_file = task.get('blend_file')
            if blend_file and os.path.exists(blend_file):
                if blend_file not in tasks_by_blend_file:
                    tasks_by_blend_file[blend_file] = []
                tasks_by_blend_file[blend_file].append(task)
        
        if not tasks_by_blend_file:
            if single_task_list is None: g_tasks_for_current_run.clear()
            return

        blend_file_to_process_now = next(iter(tasks_by_blend_file))
        tasks_for_this_file = tasks_by_blend_file.pop(blend_file_to_process_now)
        
        remaining_tasks = []
        for remaining_list in tasks_by_blend_file.values():
            remaining_tasks.extend(remaining_list)
        g_tasks_for_current_run = remaining_tasks

        batches_created, tasks_queued = 0, 0
        
        for i in range(0, len(tasks_for_this_file), THUMBNAIL_BATCH_SIZE_PER_WORKER):
            batch = tasks_for_this_file[i:i + THUMBNAIL_BATCH_SIZE_PER_WORKER]
            thumbnail_task_queue.put({
                "tasks": batch, "blend_file": blend_file_to_process_now,
                "addon_data_root": _ADDON_DATA_ROOT, "size": THUMBNAIL_SIZE
            })
            batches_created += 1
            tasks_queued += len(batch)
        
        g_outstanding_task_count += tasks_queued

        if batches_created > 0:
            print(f"[_queue_all_pending_tasks] Queued {tasks_queued} tasks for '{os.path.basename(blend_file_to_process_now)}'.")
            if g_tasks_for_current_run:
                print(f"  {len(g_tasks_for_current_run)} tasks for other files are pending.")
                
def finalize_thumbnail_run():
    """
    [IMPROVED] Finalizes a thumbnail run cleanly.

    This is the SOLE authority for ending the thumbnail generation process.
    It's called by the worker manager (`process_thumbnail_tasks`) ONLY when
    the main task queue and all worker-internal queues are empty.
    """
    global g_thumbnail_process_ongoing, g_library_update_pending
    global g_thumbnails_loaded_in_current_UMT_run

    print("[Finalize Thumbnail Run] All thumbnail tasks complete. Finalizing run.")
    g_thumbnail_process_ongoing = False

    # If any new thumbnails were successfully loaded into Blender's preview cache
    # during this entire run, force a UI redraw to make them visible.
    if g_thumbnails_loaded_in_current_UMT_run:
        print("[Finalize Thumbnail Run] New thumbnails were loaded. Forcing UI redraw.")
        force_redraw()
        
        # Incrementing the list version also helps the UIList know its icons may be stale.
        global list_version
        list_version += 1
    else:
        print("[Finalize Thumbnail Run] No new thumbnails were loaded in this run.")

    # Reset the flag for the next run.
    g_thumbnails_loaded_in_current_UMT_run = False

    # If a library update was deferred because thumbnails were being generated,
    # run it now that the process is complete.
    if g_library_update_pending:
        print("[Finalize Thumbnail Run] Processing deferred library update.")
        g_library_update_pending = False
        force_pending_update = getattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced', False)
        _perform_library_update(force=force_pending_update)
        if hasattr(bpy.context.window_manager, 'matlist_pending_lib_update_is_forced'):
            bpy.context.window_manager.matlist_pending_lib_update_is_forced = False

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
      
def _handle_worker_result(result_data):
    """ Callback to put results from any worker into the central results queue. """
    g_worker_results_queue.put(result_data)

def _handle_worker_exit(manager_id):
    """ Callback to safely remove a finished/crashed worker manager from the pool. """
    print(f"[WorkerManager-{manager_id}] has exited. Removing from pool.")
    global g_worker_manager_pool
    # This list comprehension is a thread-safe way to rebuild the list
    g_worker_manager_pool = [m for m in g_worker_manager_pool if m.id != manager_id]

# --- REPLACEMENT for process_thumbnail_tasks ---
def process_thumbnail_tasks():
    """
    [COMPLETE AND FINAL VERSION] Manages the persistent worker pool.
    - Monitors system RAM and CPU usage before launching new workers.
    - Launches new PersistentWorkerManager instances when work is available and resources permit.
    - Distributes work to idle managers.
    - Processes results from the central queue and handles retries.
    - Handles the logic for queuing tasks for the next .blend file after one is complete.
    - Shuts down the entire system when the entire job (all files, all tasks) is complete.
    """
    global g_worker_manager_pool, thumbnail_task_queue, g_worker_results_queue
    global g_outstanding_task_count, thumbnail_monitor_timer_active, g_thumbnail_process_ongoing
    global list_version, g_thumbnails_loaded_in_current_UMT_run, g_tasks_for_current_run
    global g_current_run_task_hashes_being_processed, custom_icons, THUMBNAIL_MAX_RETRIES

    # --- Section 1: Cleanup and Global Shutdown Check ---
    # First, remove any workers that may have crashed or exited from the pool.
    g_worker_manager_pool = [m for m in g_worker_manager_pool if m.is_alive()]

    # If the global "job in progress" flag is false, the only goal is to shut down.
    if not g_thumbnail_process_ongoing:
        if g_worker_manager_pool:
            # If workers are still running, signal them to stop and check back soon.
            for manager in g_worker_manager_pool:
                manager.stop_async()
            return 0.1  # Continue timer to give workers time to shut down.
        else:
            # All workers are gone, so the timer can be safely stopped.
            thumbnail_monitor_timer_active = False
            return None  # Stop the timer.

    # --- Section 2: Dynamic Resource Throttling ---
    # Before launching new workers, check if system resources are already high.
    if psutil and not thumbnail_task_queue.empty() and len(g_worker_manager_pool) < MAX_CONCURRENT_THUMBNAIL_WORKERS:
        system_ram = psutil.virtual_memory()
        cpu_load = psutil.cpu_percent(interval=None)

        if system_ram.percent > RAM_USAGE_THRESHOLD_PERCENT:
            print(f"[Resource Throttle] RAM at {system_ram.percent:.1f}% > {RAM_USAGE_THRESHOLD_PERCENT}%. Pausing worker dispatch.", file=sys.stderr)
            return 0.5  # Wait longer before checking again.

        if cpu_load > CPU_USAGE_THRESHOLD_PERCENT:
            print(f"[Resource Throttle] CPU at {cpu_load:.1f}% > {CPU_USAGE_THRESHOLD_PERCENT}%. Pausing worker dispatch.", file=sys.stderr)
            return 0.5  # Wait longer before checking again.

    # --- Section 3: Worker Creation and Task Distribution ---
    # If the queue has work and we have capacity, launch new workers.
    if not thumbnail_task_queue.empty():
        while len(g_worker_manager_pool) < MAX_CONCURRENT_THUMBNAIL_WORKERS:
            if thumbnail_task_queue.empty():
                break
            
            manager = PersistentWorkerManager(_handle_worker_result, _handle_worker_exit)
            manager.start()
            if not manager.is_running:
                print("[Thumb Timer] Failed to start a new worker, will retry.", file=sys.stderr)
                break
            g_worker_manager_pool.append(manager)
            
            # Immediately try to give the new worker a task.
            try:
                manager.add_task(thumbnail_task_queue.get_nowait())
            except Empty:
                pass  # Another worker might have grabbed the task.
    
    # Distribute any remaining tasks to already-running workers that are now idle.
    if not thumbnail_task_queue.empty():
        for manager in g_worker_manager_pool:
            if manager.task_queue.qsize() == 0:  # Check if the worker's personal queue is empty.
                try:
                    manager.add_task(thumbnail_task_queue.get_nowait())
                except Empty:
                    break

    # --- Section 4: Process All Available Results from Workers ---
    try:
        while True:  # Process all results currently in the queue without blocking.
            result_batch = g_worker_results_queue.get_nowait()
            original_tasks = result_batch.get("original_tasks", [])
            results_map = {res.get('hash_value'): res for res in result_batch.get("results", []) if 'hash_value' in res}

            for task in original_tasks:
                g_outstanding_task_count -= 1
                h = task.get('hash_value')
                if not h:
                    continue

                is_successful = False
                result = results_map.get(h)
                if result and result.get('status') == 'success':
                    thumb_path = task['thumb_path']
                    if os.path.isfile(thumb_path) and os.path.getsize(thumb_path) > 0:
                        try:
                            if h in custom_icons:
                                del custom_icons[h]
                            custom_icons.load(h, thumb_path, 'IMAGE')
                            if custom_icons.get(h) and custom_icons[h].icon_size[0] > 1:
                                is_successful = True
                                g_thumbnails_loaded_in_current_UMT_run = True
                                list_version += 1
                        except Exception as e_load:
                            print(f"[Thumb Timer] Error loading generated thumbnail {h[:8]}: {e_load}", file=sys.stderr)
                
                # If the task was not successful, decide whether to retry.
                if not is_successful:
                    retries = task.get('retries', 0)
                    if retries < THUMBNAIL_MAX_RETRIES:
                        task['retries'] = retries + 1
                        with g_dispatch_lock:
                            g_tasks_for_current_run.append(task)
                    else:
                        print(f"[Thumb Timer] Max retries reached for {h[:8]}", file=sys.stderr)
                
                # Whether successful or failed, the task is no longer "in-flight".
                # This allows it to be re-queued for a retry pass if necessary.
                g_current_run_task_hashes_being_processed.discard(h)

    except Empty:
        pass  # No more results in the queue for now.

    # --- Section 5: Job Completion and Next Batch Logic ---
    # This logic runs after checking for results.
    if g_outstanding_task_count <= 0 and thumbnail_task_queue.empty():
        # If all tasks for the current file (and any retries) are done,
        # we check if there are more tasks waiting for other blend files or new retries.
        if g_tasks_for_current_run:
            print("[Thumb Manager] Batch complete. Queuing tasks for next file/retries...")
            # This will now queue the next file in the list.
            _queue_all_pending_tasks()
        # Otherwise, if no more tasks exist anywhere, the entire job is truly finished.
        elif g_thumbnail_process_ongoing:
            finalize_thumbnail_run()

    # Continue the timer to keep monitoring.
    return 0.2

def update_material_thumbnails(specific_tasks_to_process=None):
    """
    [OPTIMIZED v2] Main initiator for a thumbnail generation "run".
    For full scans, it now just starts the non-blocking collector timer.
    """
    global g_thumbnail_process_ongoing, g_dispatch_lock, g_task_collection_iterator

    if g_thumbnail_process_ongoing and specific_tasks_to_process is None: return

    with g_dispatch_lock:
        if g_thumbnail_process_ongoing and specific_tasks_to_process is None: return

        # Reset state for a new run
        g_thumbnail_process_ongoing = True
        g_tasks_for_current_run.clear()
        g_task_collection_iterator = None # Important: reset the iterator

        # Unregister any previous timer to ensure a clean start
        if bpy.app.timers.is_registered(non_blocking_task_collector):
            bpy.app.timers.unregister(non_blocking_task_collector)
        
        if specific_tasks_to_process:
            # Specific tasks are already fast, queue them directly.
            print(f"[Thumb Update] Processing {len(specific_tasks_to_process)} specific tasks directly.")
            _queue_all_pending_tasks(single_task_list=specific_tasks_to_process)
            ensure_thumbnail_queue_processor_running()
        else:
            # For a full scan, just start the collector. It will handle the rest.
            print("[Thumb Update] Starting streaming task collection...")
            bpy.app.timers.register(non_blocking_task_collector, first_interval=0.1)

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
def create_reference_snapshot(context: bpy.types.Context) -> bool:
    duplicates_refs = []
    original_duplicate_names = []
    joined_obj = None
    original_active = context.view_layer.objects.active

    try:
        # 1) Ensure “Reference” collection exists
        ref_coll_name = "Reference"
        if ref_coll_name not in bpy.data.collections:
            ref_coll = bpy.data.collections.new(ref_coll_name)
            if context.scene and context.scene.collection:
                context.scene.collection.children.link(ref_coll)
            else:
                context.report({'ERROR'}, "Scene context missing for collection linking.")
                return False
        else:
            ref_coll = bpy.data.collections[ref_coll_name]

        # 2) Gather visible mesh objects (skip UTIL_)
        visible_objs = [
            obj for obj in context.visible_objects
            if not obj.name.startswith('UTIL_') and obj.type == 'MESH'
        ]
        if not visible_objs:
            context.report({'WARNING'}, "No visible MESH objects to create reference")
            return False

        # 3) Rename all UV layers to the same name so join() will preserve them
        for obj in visible_objs:
            for uv in obj.data.uv_layers:
                uv.name = "UVMap"

        # 4) Duplicate each visible mesh
        for obj in visible_objs:
            try:
                dup = obj.copy()
                dup.data = obj.data.copy()
                dup.animation_data_clear()
                context.collection.objects.link(dup)
                duplicates_refs.append(dup)
                original_duplicate_names.append(dup.name)
            except Exception as e_dup:
                context.report({'ERROR'}, f"Error duplicating {obj.name}: {e_dup}")
                # cleanup any successful duplicates
                for name in original_duplicate_names:
                    obj_rm = bpy.data.objects.get(name)
                    if obj_rm:
                        bpy.data.objects.remove(obj_rm, do_unlink=True)
                return False

        if not duplicates_refs:
            context.report({'ERROR'}, "Failed to duplicate any valid objects")
            return False

        # 5) Join all duplicates into one mesh
        try:
            bpy.ops.object.select_all(action='DESELECT')
            valid_for_join = [
                dup for dup in duplicates_refs
                if dup and dup.name in context.view_layer.objects
            ]
            if not valid_for_join:
                context.report({'ERROR'}, "No valid duplicates for join.")
                for name in original_duplicate_names:
                    obj_rm = bpy.data.objects.get(name)
                    if obj_rm:
                        bpy.data.objects.remove(obj_rm, do_unlink=True)
                return False

            for dup in valid_for_join:
                dup.select_set(True)
            context.view_layer.objects.active = valid_for_join[0]
            bpy.ops.object.join()

            joined_obj = context.active_object
            joined_obj.name = f"REF_{datetime.now().strftime('%Y%m%d_%H%M%S')}"

        except Exception as e_join:
            context.report({'ERROR'}, f"Join failed: {e_join}")
            for name in original_duplicate_names:
                obj_rm = bpy.data.objects.get(name)
                if obj_rm:
                    bpy.data.objects.remove(obj_rm, do_unlink=True)
            return False

        finally:
            # restore original active object
            if original_active and original_active.name in context.view_layer.objects:
                context.view_layer.objects.active = original_active
            elif context.view_layer.objects:
                context.view_layer.objects.active = context.view_layer.objects[0]

        # 6) Validate join result
        if not joined_obj or joined_obj.name not in bpy.data.objects:
            context.report({'ERROR'}, "Joined object invalid.")
            for name in original_duplicate_names:
                obj_rm = bpy.data.objects.get(name)
                if obj_rm:
                    bpy.data.objects.remove(obj_rm, do_unlink=True)
            return False

        # 7) Move the joined object into the Reference collection
        try:
            for coll in list(joined_obj.users_collection):
                coll.objects.unlink(joined_obj)
            ref_coll.objects.link(joined_obj)
        except Exception as e_move:
            context.report({'ERROR'}, f"Collection move failed: {e_move}")
            if joined_obj.name in bpy.data.objects:
                bpy.data.objects.remove(joined_obj, do_unlink=True)
            for name in original_duplicate_names:
                obj_rm = bpy.data.objects.get(name)
                if obj_rm and obj_rm != joined_obj:
                    bpy.data.objects.remove(obj_rm, do_unlink=True)
            return False

        # 8) Clean up the original duplicates
        for name in original_duplicate_names:
            if name != joined_obj.name:
                obj_rm = bpy.data.objects.get(name)
                if obj_rm:
                    try:
                        bpy.data.objects.remove(obj_rm, do_unlink=True)
                    except Exception:
                        pass

        return True

    except Exception as e:
        print(f"CRITICAL ERROR in create_reference_snapshot: {e}")
        traceback.print_exc()
        try:
            context.report({'ERROR'}, f"Snapshot creation failed: {e}")
        except Exception:
            pass
        # final cleanup on catastrophic failure
        if 'original_duplicate_names' in locals():
            final_name = joined_obj.name if joined_obj else None
            for name in original_duplicate_names:
                obj_rm = bpy.data.objects.get(name)
                if obj_rm and name != final_name:
                    try:
                        bpy.data.objects.remove(obj_rm, do_unlink=True)
                    except Exception:
                        pass
        return False

# This global `start worker once` block is removed as the new thumbnail system
# in get_custom_icon uses bpy.app.timers.register directly.

# --------------------------
# Depsgraph Handler (Unchanged from your version)
# --------------------------    
@persistent
def depsgraph_update_handler(scene, depsgraph):
    """
    ULTRA-LIGHTWEIGHT: Only detects if a material has changed.
    It does NOT iterate or do any work. It just sets a single boolean flag.
    """
    global g_materials_are_dirty, g_used_uuids_dirty
    # If the dirty flag is already set, we don't need to check further.
    if g_materials_are_dirty:
        return

    for update in depsgraph.updates:
        if isinstance(update.id, bpy.types.Material):
            g_materials_are_dirty = True
            # No need to check for object updates here for this specific optimization
            break # Exit early once a material change is found

# --------------------------
# Property Update Callbacks and UI Redraw (from old addon)
# --------------------------
def update_material_list_active_index(self, context):
    print(f"[MaterialList] Active material index updated to: {context.scene.material_list_active_index}")

      
def update_list_and_reset_selection(self, context):
    """
    Update callback for UI properties that trigger a list rebuild.
    It calls populate_and_reset_selection to handle the logic.
    """
    populate_and_reset_selection(context)
    return None

def populate_and_reset_selection(context):
    """
    Populates the material list based on current filters and then resets the active index to 0.
    """
    scene = context.scene
    if not scene:
        return

    # 1. Repopulate the list based on the current filter settings.
    populate_material_list(scene)

    # 2. If the newly populated list has items, set the active index to the top.
    if scene.material_list_items:
        scene.material_list_active_index = 0

    # 3. Force a redraw to ensure the UI updates immediately.
    force_redraw()

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

def force_redraw(limit_timer: bool = False):
    """
    Lightweight redraw utility.

    • Tags every visible area so Blender repaints on the next UI tick.
    • If ‟limit_timer” is True you still get a single forced swap,
      but the old 3-swap cycle is gone.

    Removing the triple-swap takes the post-save stall from ~0.3 s to
    almost nothing—even on large scenes that only contain mat_ materials.
    """
    for win in bpy.context.window_manager.windows:
        for ar in win.screen.areas:
            ar.tag_redraw()

    if limit_timer:
        # one swap is plenty; comment out to disable completely
        bpy.ops.wm.redraw_timer(type='DRAW_WIN_SWAP', iterations=1)

def ensure_safe_preview(mat):
    if not mat:
        return False
    try:
        # get previous preview type from our external cache
        last = _preview_type_cache.get(mat.name, None)
        # read current type
        cur = getattr(mat, "preview_render_type", None)
        if cur is None:
            # force first render
            mat.preview_ensure()
            cur = mat.preview_render_type
        # only re-render if the type changed
        if last != cur:
            mat.preview_ensure()
            _preview_type_cache[mat.name] = cur
        return True
    except Exception as e:
        print(f"[Preview] ERROR on {mat.name}: {e}")
        return False

# --------------------------
# UIList and Panel Classes (from old addon, will use updated helpers)
# --------------------------
class PersistentWorkerManager:
    """ Manages a single, long-lived worker process with two-way communication. """
    def __init__(self, on_result_callback, on_exit_callback):
        self.worker_process = None
        self.task_queue = Queue()
        self.is_running = False
        self.main_thread = None
        self.on_result = on_result_callback
        self.on_exit = on_exit_callback
        self.id = str(uuid.uuid4())[:8]
        self.is_stopping = False

    def start(self):
        if self.is_running:
            return

        # Command to start a persistent worker that waits for JSON commands on stdin
        cmd = [
            bpy.app.binary_path, "--background", "--factory-startup",
            "--python", BACKGROUND_WORKER_PY,
            "--", "--operation", "render_thumbnail_persistent"
        ]

        try:
            self.worker_process = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, encoding='utf-8', errors='replace', bufsize=1
            )
            self.is_running = True
            self.main_thread = threading.Thread(target=self._io_manager, daemon=True)
            self.main_thread.start()
            print(f"[WorkerManager-{self.id}] Persistent worker started (PID: {self.worker_process.pid}).")
        except Exception as e:
            print(f"[WorkerManager-{self.id}] FAILED to start: {e}", file=sys.stderr)
            self.is_running = False

    def add_task(self, work_item):
        if self.is_running and not self.is_stopping:
            self.task_queue.put(work_item)

    def stop_async(self):
        if not self.is_running or self.is_stopping:
            return
        print(f"[WorkerManager-{self.id}] Signaling worker to stop asynchronously...")
        self.is_stopping = True
        self.task_queue.put(None) # Sentinel value to stop the IO loop

    def is_alive(self):
        return self.worker_process and self.worker_process.poll() is None

    def _io_manager(self):
        # Helper threads to read stdout/stderr without blocking
        def read_pipe(pipe, callback):
            for line in iter(pipe.readline, ''):
                callback(line)
            try:
                pipe.close()
            except Exception: pass

        stdout_thread = threading.Thread(target=read_pipe, args=(self.worker_process.stdout, self._handle_stdout), daemon=True)
        stderr_thread = threading.Thread(target=read_pipe, args=(self.worker_process.stderr, self._handle_stderr), daemon=True)
        stdout_thread.start()
        stderr_thread.start()

        # Main loop to send tasks from the queue to the worker's stdin
        while self.is_running:
            try:
                work_item = self.task_queue.get(timeout=0.1)
                if work_item is None: # Stop signal
                    break
                command = json.dumps(work_item) + '\n'
                self.worker_process.stdin.write(command)
                self.worker_process.stdin.flush()
            except Empty:
                if self.worker_process.poll() is not None:
                    break # Worker process died unexpectedly
            except (IOError, BrokenPipeError, ValueError):
                break # Worker process closed its stdin

        self.is_running = False
        try:
            self.worker_process.stdin.close()
        except Exception: pass
        
        self.worker_process.wait(timeout=10)
        stdout_thread.join(timeout=2)
        stderr_thread.join(timeout=2)
        self.on_exit(self.id) # Notify the main thread that this manager is done

    def _handle_stdout(self, line):
        line = line.strip()
        if line and line.startswith('{'):
            try:
                result_data = json.loads(line)
                self.on_result(result_data)
            except json.JSONDecodeError:
                print(f"[Worker-{self.id} STDOUT non-JSON]: {line}", file=sys.stderr)
        elif line:
             print(f"[Worker-{self.id} STDOUT]: {line}")

    def _handle_stderr(self, line):
        line = line.strip()
        if line:
            print(f"[Worker-{self.id} STDERR]: {line}", file=sys.stderr)

class MATERIALLIST_UL_materials(UIList):
    use_filter_show = False
    use_filter_menu = False
    use_filter_sort_alpha = False
    use_sort_alpha = False

    def draw_item(self, context, layout, data, item, icon, active_data, active_propname, index):
        # This function must remain extremely fast.
        global list_version, material_list_cache # Ensure globals are available
        
        if index < len(material_list_cache):
            cache_entry = material_list_cache[index]
            
            # --- START OF FIX ---
            # If the global list_version has been incremented (e.g., by a background thumbnail load),
            # the version stored in our cache entry will be outdated. This signals that
            # our cached icon_id might be stale and we need to re-fetch it.
            if cache_entry.get('version', -1) < list_version:
                cache_entry['icon_id'] = 0  # Force a re-fetch by resetting the cached ID
                cache_entry['version'] = list_version  # Update the entry's version to the current one
            # --- END OF FIX ---

            # If the icon_id in our fast cache is 0 (either initially or because it was just invalidated),
            # try to get the icon. get_custom_icon is optimized to be fast for already-loaded icons.
            if cache_entry.get('icon_id', 0) <= 0:
                mat_obj = get_material_by_uuid(item.material_uuid)
                if mat_obj:
                    # Update our cache with the result for the next redraw.
                    # This will return a valid ID if the icon is already in Blender's preview system,
                    # or it will return 0 and queue a generation if it's missing.
                    cache_entry['icon_id'] = get_custom_icon(mat_obj)

            icon_val = cache_entry.get("icon_id", 0)
            is_missing = cache_entry.get("is_missing", True)
            
            row = layout.row(align=True)
            if icon_val > 0:
                # The BKE_icon_get error happens here if icon_val is stale.
                # The invalidation logic above prevents a stale ID from being used.
                row.label(icon_value=icon_val)
            else:
                row.label(icon="ERROR" if is_missing else "MATERIAL")

            if is_missing:
                row.label(text=f"{item.material_name} (Missing)", icon="GHOST")
            else:
                row.label(text=item.material_name)
                if cache_entry.get("is_protected"):
                    row.label(icon="LOCKED")
        else:
            # Fallback for safety if cache and list go out of sync.
            layout.label(text=item.material_name, icon='QUESTION')

    def filter_items(self, context, data, propname):
        """
        UIList run-time filtering.
        OPTIMIZED: Caches the set of used UUIDs and only recalculates it
        when the g_used_uuids_dirty flag is set by the depsgraph handler.
        """
        global g_used_uuids_cache, g_used_uuids_dirty

        items            = getattr(data, propname)
        search_term      = context.scene.material_search.strip().lower()
        hide_mat_prefix  = context.scene.hide_mat_materials
        show_only_used   = context.scene.material_list_show_only_local

        if not (search_term or hide_mat_prefix or show_only_used):
            return [], []

        # --- OPTIMIZATION ---
        # Only recalculate the expensive 'used_uuids' set if the depsgraph
        # has told us that something has changed.
        if show_only_used and g_used_uuids_dirty:
            print("[Filter Items] Recalculating used materials cache...")
            g_used_uuids_cache.clear()
            for obj in bpy.data.objects:
                if obj.type == 'MESH':
                    for slot in obj.material_slots:
                        if slot.material:
                            uid = get_material_uuid(slot.material)
                            if uid:
                                g_used_uuids_cache.add(uid)
            g_used_uuids_dirty = False # Reset the flag until the next change

        filter_flags = []
        for item in items:
            visible = True
            if search_term and search_term not in item.material_name.lower():
                visible = False
            if visible and hide_mat_prefix and item.material_name.startswith("mat_"):
                visible = False
            if visible and show_only_used:
                # Filter using the (now up-to-date) cache
                if item.is_library and item.material_uuid not in g_used_uuids_cache:
                    visible = False
                
            filter_flags.append(self.bitflag_filter_item if visible else 0)

        return filter_flags, []

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

        # --- NEW SECTION: Check for psutil dependency ---
        if psutil is None:
            box = layout.box()
            box.label(text="Resource Monitoring is Disabled.", icon='ERROR')
            box.label(text="'psutil' library not found.")
            box.operator("materiallist.install_psutil", icon='CONSOLE')
            box.label(text="Blender must be restarted after installation.")
            layout.separator()

        # --- Workspace Mode ---
        workspace_box = layout.box()
        row = workspace_box.row(align=True)
        row.label(text="Workspace Mode:", icon='FILE_BLEND')
        row.label(text=f"{scene.workspace_mode}")
        workspace_box.operator(
            "materiallist.toggle_workspace_mode",
            text=f"Switch to {'Editing' if scene.workspace_mode == 'REFERENCE' else 'Reference'}",
            icon='ARROW_LEFTRIGHT'
        )

        # --- Material Options ---
        options_box = layout.box()
        options_box.label(text="Material Options", icon='TOOL_SETTINGS')

        row = options_box.row(align=True)
        row.operator("materiallist.rename_to_albedo", text="Rename All to Albedo", icon='FILE_REFRESH')
        row.operator("materiallist.duplicate_or_localise", text="Create Local Copy", icon='COPYDOWN')

        row = options_box.row(align=True)
        row.prop(scene, "hide_mat_materials",           toggle=True, text="Hide mat_ Materials")
        row.prop(scene, "material_list_show_only_local", toggle=True, text="Show Only Local/Used")

        row = options_box.row(align=True)
        row.operator("materiallist.rename_material", icon='FONT_DATA',   text="Rename Display Name")
        row.operator("materiallist.unassign_mat",     icon='PANEL_CLOSE', text="Unassign 'mat_'")

        # --- Reference Snapshot ---
        backup_box = layout.box()
        backup_box.label(text="Reference Snapshot", icon='INFO')
        backup_box.operator("materiallist.backup_editing", icon='FILE_TICK', text="Backup Current as Reference")

        # --- Assign to Active Object ---
        assign_box = layout.box()
        assign_box.operator("materiallist.select_dominant", text="Select Dominant Material on Active Object", icon='RESTRICT_SELECT_OFF')
        assign_box.operator("materiallist.add_material_to_slot", icon='PLUS', text="Add Selected to Object Slots")
        assign_box.operator("materiallist.assign_selected_material", icon='BRUSH_DATA', text="Assign Selected to Faces/Object")

        # --- Material List Display & Info ---
        mat_list_box = layout.box()
        row = mat_list_box.row(align=True)
        row.label(text="Materials:", icon='MATERIAL')
        row.prop(scene, "material_list_sort_alpha", text="", toggle=True, icon='SORTALPHA')
        row.operator("materiallist.scroll_to_top", icon='TRIA_UP', text="")

        row = mat_list_box.row()
        row.template_list(
            "MATERIALLIST_UL_materials", "",
            scene, "material_list_items",
            scene, "material_list_active_index",
            rows=10, sort_lock=True
        )

        sub_row = mat_list_box.row(align=True)
        sub_row.prop(scene, "material_search", text="", icon='VIEWZOOM')

        idx = scene.material_list_active_index
        if 0 <= idx < len(scene.material_list_items):
            item = scene.material_list_items[idx]
            mat_for_preview = get_material_by_uuid(item.material_uuid)
            info_parent = mat_list_box

            if mat_for_preview:
                preview_box = mat_list_box.box()
                if ensure_safe_preview(mat_for_preview):
                    preview_box.template_preview(mat_for_preview, show_buttons=True)
                else:
                    preview_box.label(text="Preview not available", icon='ERROR')
                info_parent = preview_box
            else:
                missing_box = mat_list_box.box()
                missing_box.label(text="Material data missing", icon='ERROR')

            # Duplicate‐name warning
            name_to_check = item.original_name
            if name_to_check and not name_to_check.startswith("mat_") and name_to_check != "Material":
                count = sum(1 for li in scene.material_list_items if li.original_name == name_to_check)
                if count > 1:
                    warn_box = info_parent.box(); warn_box.alert = True
                    warn_box.label(text=f"'{name_to_check}' used by {count} materials!", icon='ERROR')

        # --- Library Operations ---
        library_ops_box = layout.box()
        library_ops_box.label(text="Library Operations", icon='ASSET_MANAGER')
        library_ops_box.operator("materiallist.integrate_library", text="Integrate External Library", icon='IMPORT')

        # --- Batch Utilities ---
        project_util_box = layout.box()
        project_util_box.label(text="Batch Utilities", icon='TOOL_SETTINGS')
        project_util_box.prop(scene, "material_list_external_unpack_dir", text="External Output Folder")

        col = project_util_box.column(align=True)
        col.operator("materiallist.pack_textures_externally", text="Unpack Lib into Folder", icon='EXPORT')
        col.separator(factor=0.7)
        col.operator("materiallist.pack_textures_internally", text="Pack into Local Projects", icon='IMPORT')
        project_util_box.operator("materiallist.trim_library", icon='TRASH', text="Trim Library")

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
    MATERIALLIST_OT_rename_material,
    MATERIALLIST_OT_rename_to_albedo,
    MATERIALLIST_OT_duplicate_or_localise_material,
    MATERIALLIST_OT_make_local,
    MATERIALLIST_OT_assign_selected_material,
    MATERIALLIST_OT_add_material_to_slot,
    MATERIALLIST_OT_unassign_mat,
    MATERIALLIST_OT_select_dominant,
    MATERIALLIST_OT_backup_reference,
    MATERIALLIST_OT_backup_editing,
    MATERIALLIST_OT_refresh_material_list,
    MATERIALLIST_OT_sort_alphabetically,
    MATERIALLIST_OT_scroll_to_top,
    MATERIALLIST_OT_PollMaterialChanges,
    MATERIALLIST_OT_integrate_library,
    MATERIALLIST_OT_pack_library_textures,
    MATERIALLIST_OT_run_localisation_worker,
    MATERIALLIST_OT_pack_textures_internally,
    MATERIALLIST_OT_pack_textures_externally,
    MATERIALLIST_OT_trim_library,
    MATERIALLIST_OT_install_psutil,  
    MATERIALLIST_OT_prepare_material,
    MATERIALLIST_OT_assign_to_object,
    MATERIALLIST_OT_assign_to_faces,
)

scene_props = [
    ("material_list_items", bpy.props.CollectionProperty(type=MaterialListItem)),
    ("material_list_active_index", bpy.props.IntProperty(name="Active Index", default=-1, update=update_material_list_active_index)),
    ("material_search", bpy.props.StringProperty(
        name="Search Materials", 
        description="Filter material list by name", 
        default="", 
        update=update_filter_and_select_top # <--- CHANGED to the new smart function
    )),
    ("hide_mat_materials", bpy.props.BoolProperty(
        name="Hide Default Materials", 
        description="Hide materials starting with 'mat_'", 
        default=False, 
        update=update_filter_and_select_top # <--- CHANGED to the new smart function
    )),
    ("workspace_mode", bpy.props.EnumProperty(
        name="Workspace Mode", 
        items=[('REFERENCE', "Reference", "Reference configuration"), ('EDITING', "Editing", "Editing configuration")], 
        default='REFERENCE', 
        update=update_workspace_mode
    )),
    ("mat_materials_unassigned", bpy.props.BoolProperty(
        name="Unassign mat_ Materials", 
        description="Toggle backup/restore of mat_ assignments", 
        default=False
    )),
    ("material_list", bpy.props.PointerProperty(type=MaterialListProperties)),
    ("library_materials", bpy.props.CollectionProperty(type=LibraryMaterialEntry)),
    ("material_list_sort_alpha", bpy.props.BoolProperty(
        name="Sort Alphabetically", 
        description="Sort the material list alphabetically by display name instead of by recency", 
        default=False, 
        update=update_list_and_reset_selection # Correct: This one DOES need a full rebuild
    )),
    ("material_list_show_only_local", bpy.props.BoolProperty(
        name="Show Only Local/Used", 
        description="Show only local materials and linked materials currently assigned to objects in the scene", 
        default=False, 
        update=update_filter_and_select_top # <--- CHANGED to the new smart function
    )),
    ("material_list_external_unpack_dir", bpy.props.StringProperty(
        name="External Output Folder",
        description="Directory to save external textures. Use // for paths relative to the .blend file.",
        subtype='DIR_PATH',
        default="//textures_external/"
    )),
]

handler_pairs = [
    (bpy.app.handlers.load_post, load_post_handler),
    (bpy.app.handlers.save_pre, save_pre_handler), # <-- CHANGE THIS LINE
    (bpy.app.handlers.save_post, save_post_handler),
    (bpy.app.handlers.depsgraph_update_post, depsgraph_update_handler),
    (bpy.app.handlers.load_post, migrate_thumbnail_files)
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
    # New batch and async globals
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_tasks_for_current_run, g_dispatch_lock, g_library_update_pending, g_current_run_task_hashes_being_processed
    global g_materials_are_dirty, g_material_processing_timer_active


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
    g_materials_are_dirty = False
    g_material_processing_timer_active = False

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

    get_hashing_scene_bundle()
    print("[Register] Persistent hashing scene bundle created.")
    
    # --- Start the background processing timer ---
    if not bpy.app.timers.is_registered(process_dirty_materials_timer):
        # Start checking for dirty materials 5 seconds after addon registration.
        bpy.app.timers.register(process_dirty_materials_timer, first_interval=5.0)
        g_material_processing_timer_active = True
    
    print("[Register] MaterialList Addon Registration Finished Successfully.")


def unregister():
    global custom_icons
    global thumbnail_monitor_timer_active, thumbnail_worker_pool, thumbnail_task_queue
    global thumbnail_pending_on_disk_check, thumbnail_generation_scheduled
    global db_connections
    global material_names, material_hashes, global_hash_cache, material_list_cache, _display_name_cache
    # New batch and async globals
    global g_thumbnail_process_ongoing, g_material_creation_timestamp_at_process_start
    global g_tasks_for_current_run, g_library_update_pending, g_current_run_task_hashes_being_processed
    global list_version, g_material_processing_timer_active

    print("[Unregister] MaterialList Addon Unregistering...")

    # --- Stop Asynchronous Timers ---
    if bpy.app.timers.is_registered(process_dirty_materials_timer):
        bpy.app.timers.unregister(process_dirty_materials_timer)
    g_material_processing_timer_active = False
    print("[Unregister] Stopped material processing timer.")

    cleanup_hashing_scene_bundle()
    print("[Unregister] Hashing scene bundle cleaned up.")
    
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
        if not process:
            continue
        if hasattr(process, 'poll') and process.poll() is None:
            # Process is still running
            try:
                pid = getattr(process, 'pid', 'Unknown')
                print(f"  Worker {worker_idx + 1}: Pausing 0.1s before killing running process (PID: {pid})...")
                time.sleep(0.1)
                process.kill()
                print(f"  Worker {worker_idx + 1}: Kill signal sent for PID: {pid}.")
            except Exception as e_kill_general:
                print(f"  Worker {worker_idx + 1}: Unexpected error during kill attempt: {e_kill_general}")

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
            while func in handler_list:
                try:
                    handler_list.remove(func)
                except (ValueError, Exception):
                    break

    for prop_name, _ in scene_props:
        if hasattr(bpy.types.Scene, prop_name):
            try:
                delattr(bpy.types.Scene, prop_name)
            except Exception as e_prop_unreg:
                print(f"[Unregister] Error deleting scene property '{prop_name}': {e_prop_unreg}")

    if hasattr(bpy.types.WindowManager, 'matlist_save_handler_processed'):
        try:
            delattr(bpy.types.WindowManager, 'matlist_save_handler_processed')
        except Exception as e_wm_prop_unreg:
            print(f"[Unregister] Error deleting WindowManager.matlist_save_handler_processed: {e_wm_prop_unreg}")
    if hasattr(bpy.types.WindowManager, 'matlist_pending_lib_update_is_forced'):
        try:
            delattr(bpy.types.WindowManager, 'matlist_pending_lib_update_is_forced')
        except Exception as e_wm_prop_unreg_force:
            print(f"[Unregister] Error deleting WindowManager.matlist_pending_lib_update_is_forced: {e_wm_prop_unreg_force}")

    for cls in reversed(classes):
        try:
            bpy.utils.unregister_class(cls)
        except RuntimeError:
            pass

    if custom_icons is not None:
        try:
            bpy.utils.previews.remove(custom_icons)
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
