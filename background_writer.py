# <--- Start of background_writer.py (Corrected Hashing) --->
import bpy
import sys
import os
import argparse
import traceback
import hashlib
import json
import uuid # Make sure uuid is imported
import sqlite3
import time
import re # Needed for preload regex potentially
import shutil # <-- Add this import for file moving
import tempfile # <-- Add this import for temp file name
# --- Hashing Functions (Copied EXACTLY from latest working Main Addon version) ---

# Helper function for consistent float formatting
def _float_repr(f):
    """ Ensure consistent float representation for hashing. """
    try:
        return f"{float(f):.8f}" # Use consistent precision
    except (ValueError, TypeError):
        print(f"[_float_repr Warning] Could not convert {f} to float.")
        return "CONV_ERROR"

# Stable Representation - Make sure this matches your corrected main addon version
def _stable_repr(value):
    """ Create a stable string representation for common Blender property types. """
    if isinstance(value, (int, str, bool)):
        return str(value)
    elif isinstance(value, float):
        return f"{value:.8f}"
    elif isinstance(value, (bpy.types.bpy_prop_array, tuple, list)) and len(value) > 0 and isinstance(value[0], (float, int)):
         # Use _float_repr for consistent float formatting
         if '_float_repr' in globals() and callable(_float_repr):
              return '[' + ','.join([_float_repr(item) for item in value]) + ']'
         else:
              print("[_stable_repr CRITICAL] _float_repr helper not found!")
              return '[' + ','.join([f"{item:.8f}" if isinstance(item, float) else str(item) for item in value]) + ']'
    elif hasattr(value, 'to_list'): # Fallback for other sequence types
        if '_float_repr' in globals() and callable(_float_repr):
             return '[' + ','.join([_float_repr(item) for item in value.to_list()]) + ']'
        else:
             print("[_stable_repr CRITICAL] _float_repr helper not found for to_list()!")
             return str(value.to_list())
    elif value is None:
         return 'None'
    else:
        # Fallback to standard repr
        return repr(value)

# Hash Image - Make sure this matches your main addon version
def _hash_image(img):
    """
    Returns md5 digest of the *file* backing the image (fast ‑ first 128 kB),
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
                print(f"[_hash_image BG Warning] Could not read {abs_path}: {read_err}")
    except Exception as path_err:
         print(f"[_hash_image BG Warning] Error during abspath for '{raw_path}': {path_err}")
    fallback_data = f"RAW_PATH:{raw_path}|NAME:{img.name}"
    return hashlib.md5(fallback_data.encode()).hexdigest()

# Find Principled BSDF - Make sure this matches your main addon version
def find_principled_bsdf(mat):
    # --- PASTE YOUR LATEST WORKING find_principled_bsdf HERE ---
    # Example structure:
    if not mat or not mat.use_nodes or not mat.node_tree: return None
    # ... (rest of your find_principled_bsdf logic) ...
    # Find output node
    output_node = next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeOutputMaterial' and n.is_active_output), None)
    if not output_node: output_node = next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeOutputMaterial'), None)
    if not output_node: return None
    # Traverse inputs etc... find first principled or fallback...
    principled_fallback = next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)
    return principled_fallback # Return found node or None

# UUID Validation (Keep as is or copy from main addon if changed)
def validate_material_uuid(mat, is_copy=False):
    if mat is None: return None
    original_uuid = mat.get("uuid", "")
    if not original_uuid or len(original_uuid) != 36 or is_copy:
        new_uuid = str(uuid.uuid4())
        # Don't set property in background writer
        return new_uuid
    return original_uuid

# GET MATERIAL HASH - Replace old version with exact copy from main addon
def get_material_hash(mat, force=False):
    # Ensure helper functions exist (important!)
    if '_stable_repr' not in globals() or '_float_repr' not in globals() or '_hash_image' not in globals():
         print("[get_material_hash BG CRITICAL ERROR] Helper function missing!")
         return None

    # --- PASTE YOUR LATEST WORKING get_material_hash HERE ---
    # Make sure it's identical to the one that correctly calculates
    # the hash based on Base Color etc. using _stable_repr in the main addon.
    # Example structure (replace with your actual latest):
    HASH_VERSION = "v_DEBUG_SIMPLE_1" # Make sure this matches main addon
    if not mat: return None
    mat_name_for_debug = getattr(mat, 'name', 'UnknownMaterial')
    uid = validate_material_uuid(mat)
    if not uid: return None
    # --- NO CACHE IN BACKGROUND ---
    # print(f"[get_material_hash BG DEBUG] Calculating hash for: {mat_name_for_debug} (UUID: {uid})") # Optional Debug

    hash_inputs = []
    try:
        principled_node = None
        image_hashes = set()
        if mat.use_nodes and mat.node_tree:
            # Find relevant nodes and inputs (USE YOUR LATEST LOGIC)
            principled_node = find_principled_bsdf(mat) # Use helper if needed
            for node in mat.node_tree.nodes:
                 # Hash relevant nodes/textures (USE YOUR LATEST LOGIC)
                 if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                      img_hash = _hash_image(node.image)
                      if img_hash: image_hashes.add(img_hash)

            if principled_node:
                 hash_inputs.append("NODE:PrincipledBSDF")
                 inputs_to_check = ['Base Color', 'Metallic', 'Roughness'] # Use your list
                 for inp_id in inputs_to_check:
                      inp = principled_node.inputs.get(inp_id)
                      if inp:
                           if inp.is_linked:
                               # USE YOUR LATEST LINKED INPUT LOGIC
                               hash_inputs.append(f"INPUT:{inp_id}=LINKED_OTHER") # Placeholder
                           else:
                               # USE YOUR LATEST UNLINKED INPUT LOGIC (using _stable_repr)
                               val_repr = _stable_repr(inp.default_value)
                               hash_inputs.append(f"INPUT:{inp_id}=VALUE:{val_repr}")
            else:
                 hash_inputs.append("NODE:NoPrincipledBSDF")

        # USE YOUR LATEST IMAGE HASH AGGREGATION LOGIC
        sorted_image_hashes = sorted(list(image_hashes))
        image_hash_input_str = f"IMAGE_HASHES:{'|'.join(sorted_image_hashes)}"
        hash_inputs.append(image_hash_input_str)

        # USE YOUR LATEST FINAL STRING AND HASHING LOGIC
        final_hash_string = f"VERSION:{HASH_VERSION}|||" + "|||".join(hash_inputs)
        digest = hashlib.md5(final_hash_string.encode('utf-8')).hexdigest()
        # print(f"    [Hash Result BG] Calculated Hash: {digest}") # Optional Debug
        return digest

    except Exception as e:
        print(f"[get_material_hash BG ERROR] Failed hashing {mat_name_for_debug}: {e}")
        traceback.print_exc()
        return None

# --- END OF HASHING FUNCTIONS ---


# Timestamp update function (Keep the corrected version)
def update_material_timestamp_in_db(db_path, material_uuid):
    """Updates the timestamp for a given material UUID in the database."""
    if not db_path or not material_uuid:
        print(f"[BG Timestamp] Error: Missing db_path or material_uuid.")
        return
    conn = None
    try:
        if not os.path.exists(db_path):
             print(f"[BG Timestamp] Error: Database file not found: '{db_path}'.")
             return
        conn = sqlite3.connect(db_path, timeout=10)
        c = conn.cursor()
        c.execute("CREATE TABLE IF NOT EXISTS mat_time (uuid TEXT PRIMARY KEY, ts INTEGER)")
        current_time = int(time.time())
        c.execute("INSERT OR REPLACE INTO mat_time (uuid, ts) VALUES (?, ?)", (material_uuid, current_time))
        conn.commit()
        print(f"[BG Timestamp] Updated timestamp for UUID {material_uuid} in DB '{os.path.basename(db_path)}'.") # Keep log
    except sqlite3.Error as db_err:
        print(f"[BG Timestamp] Database Error updating timestamp for {material_uuid}: {db_err}")
    except Exception as e:
        print(f"[BG Timestamp] General Error updating timestamp for {material_uuid}: {e}")
    finally:
        if conn:
            try: conn.close()
            except Exception as close_err: print(f"[BG Timestamp] Error closing DB connection: {close_err}")


# --- Main Merge Logic (Largely Unchanged - Relies on Correct Hashes Now) ---
def main():
    parser = argparse.ArgumentParser(description="Background script merge")
    parser.add_argument("--transfer", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--db", required=True)

    loaded_target_mats = []
    loaded_transfer_mats = []
    target_materials = {}
    transfer_materials = {}
    final_set = set()

    try:
        args_list = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else sys.argv[1:]
        args = parser.parse_args(args_list)

        transfer_file_abs = os.path.abspath(args.transfer)
        target_file_abs = os.path.abspath(args.target)
        db_path_abs = os.path.abspath(args.db)

        print(f"[BG Writer] Starting merge. Transfer: {os.path.basename(transfer_file_abs)}, Target: {os.path.basename(target_file_abs)}, DB: {os.path.basename(db_path_abs)}")
        db_path = db_path_abs if os.path.exists(db_path_abs) else None
        if not db_path: print(f"[BG Writer] WARNING: DB not found at '{db_path_abs}'. Timestamps not updated.")

        target_hashes = {}
        transfer_hashes = {}

        # 1. Load Target Lib Materials and Hashes
        if os.path.exists(target_file_abs):
            print(f"[BG Writer] Loading existing from target: {os.path.basename(target_file_abs)}")
            try:
                with bpy.data.libraries.load(target_file_abs, link=False) as (data_from, data_to):
                    if hasattr(data_from, 'materials') and data_from.materials:
                        valid_names = [name for name in data_from.materials if isinstance(name, str)]
                        if valid_names: data_to.materials = valid_names
                loaded_target_mats = list(data_to.materials)
                processed_target_uuids = set()
                for mat in loaded_target_mats:
                    if not mat or not hasattr(mat, 'name'): continue
                    # <<< FIX: Rename variable >>>
                    mat_uuid = validate_material_uuid(mat)
                    if mat_uuid and mat_uuid not in processed_target_uuids:
                        processed_target_uuids.add(mat_uuid)
                        target_materials[mat_uuid] = mat # Use mat_uuid as key
                        calculated_hash = get_material_hash(mat)
                        if calculated_hash: target_hashes[mat_uuid] = calculated_hash # Use mat_uuid as key
                        else: print(f"[BG Writer] Warning: Failed hash target '{getattr(mat,'name','N/A')}' (UUID:{mat_uuid}).")
                print(f"[BG Writer] Loaded {len(target_materials)} unique materials from target.")
            except Exception as load_target_err:
                 print(f"[BG Writer] Warning: Could not load/process target library '{os.path.basename(target_file_abs)}': {load_target_err}.")
        else:
            print(f"[BG Writer] Target library '{os.path.basename(target_file_abs)}' not found. Will create.")
            target_dir = os.path.dirname(target_file_abs)
            if target_dir: os.makedirs(target_dir, exist_ok=True)


        # 2. Load Transfer Lib Materials and Hashes
        if os.path.exists(transfer_file_abs):
            print(f"[BG Writer] Loading new/updated from transfer: {os.path.basename(transfer_file_abs)}")
            try:
                with bpy.data.libraries.load(transfer_file_abs, link=False) as (data_from, data_to):
                     if hasattr(data_from, 'materials') and data_from.materials:
                        valid_names = [name for name in data_from.materials if isinstance(name, str)]
                        if valid_names: data_to.materials = valid_names
                loaded_transfer_mats = list(data_to.materials)
                processed_transfer_uuids = set()
                for mat in loaded_transfer_mats:
                    if not mat or not hasattr(mat, 'name'): continue
                    # <<< FIX: Rename variable >>>
                    mat_uuid = validate_material_uuid(mat)
                    if mat_uuid and mat_uuid not in processed_transfer_uuids:
                        processed_transfer_uuids.add(mat_uuid)
                        transfer_materials[mat_uuid] = mat # Use mat_uuid as key
                        calculated_hash = get_material_hash(mat)
                        if calculated_hash: transfer_hashes[mat_uuid] = calculated_hash # Use mat_uuid as key
                        else: print(f"[BG Writer] Warning: Failed hash transfer '{getattr(mat,'name','N/A')}' (UUID:{mat_uuid}).")
                    elif mat_uuid and mat_uuid in processed_transfer_uuids: print(f"[BG Writer] Warning: Duplicate UUID '{mat_uuid}' in transfer.")
                print(f"[BG Writer] Loaded {len(transfer_materials)} materials from transfer.")
            except Exception as load_transfer_err:
                print(f"[BG Writer] Error loading/processing transfer library '{os.path.basename(transfer_file_abs)}': {load_transfer_err}")
                print(traceback.format_exc())
                return 1 # Failure
        else:
            print(f"[BG Writer] Transfer file '{os.path.basename(transfer_file_abs)}' not found.")
            return 1 # Failure

        # 3. Merge Logic
        final_materials_to_write = {}
        materials_updated = 0; materials_added = 0; skipped_duplicate_hash = 0; skipped_failed_hash_transfer = 0
        final_materials_to_write.update(target_materials)
        existing_target_hashes_set = set(target_hashes.values())
        hash_to_target_uuid_map = {h: u for u, h in target_hashes.items()} # Renamed internal var

        # <<< FIX: Rename loop variable >>>
        for uuid_key, transfer_mat in transfer_materials.items():
            transfer_hash = transfer_hashes.get(uuid_key)
            mat_name_for_log = getattr(transfer_mat, 'name', uuid_key)
            # print(f"\n[BG Writer Process] Checking transfer: '{mat_name_for_log}' (UUID: {uuid_key}), Hash: {transfer_hash or 'FAILED'}") # Verbose

            if transfer_hash is None:
                skipped_failed_hash_transfer += 1; continue

            # <<< FIX: Use uuid_key for checks and updates >>>
            if uuid_key not in target_materials: # New UUID
                if transfer_hash in existing_target_hashes_set: skipped_duplicate_hash += 1; continue
                else:
                    try:
                        transfer_mat.name = uuid_key
                        final_materials_to_write[uuid_key] = transfer_mat
                        materials_added += 1
                        existing_target_hashes_set.add(transfer_hash)
                        hash_to_target_uuid_map[transfer_hash] = uuid_key
                        if db_path: update_material_timestamp_in_db(db_path, uuid_key)
                    except Exception as name_err: print(f"[BG Proc] ERROR setting name new {uuid_key}: {name_err}. Skip add.")
            else: # Existing UUID
                target_hash = target_hashes.get(uuid_key)
                if target_hash is None or target_hash != transfer_hash:
                    try:
                        transfer_mat.name = uuid_key
                        final_materials_to_write[uuid_key] = transfer_mat
                        materials_updated += 1
                        if target_hash and target_hash in existing_target_hashes_set:
                             try: existing_target_hashes_set.remove(target_hash)
                             except KeyError: pass
                        if target_hash and target_hash in hash_to_target_uuid_map and hash_to_target_uuid_map[target_hash] == uuid_key:
                             del hash_to_target_uuid_map[target_hash]
                        existing_target_hashes_set.add(transfer_hash)
                        hash_to_target_uuid_map[transfer_hash] = uuid_key
                        if db_path: update_material_timestamp_in_db(db_path, uuid_key)
                    except Exception as name_err: print(f"[BG Proc] ERROR setting name update {uuid_key}: {name_err}. Skip update.")
                else: # Ensure name correct even if kept
                    if uuid_key in final_materials_to_write:
                        try: final_materials_to_write[uuid_key].name = uuid_key
                        except Exception: pass


        # 4. Prepare Final Set
        final_set = {mat for mat in final_materials_to_write.values() if mat and isinstance(mat, bpy.types.Material)}

        if not final_set:
             print("[BG Writer] No materials collected to write.")
             return 0

        print(f"\n[BG Writer] Final Summary: Preparing to write {len(final_set)} total materials.")
        print(f"  ({materials_added} added, {materials_updated} updated, {skipped_duplicate_hash} skipped duplicate hash, {skipped_failed_hash_transfer} skipped failed hash)")

        # Set fake user and ensure name = UUID on final set
        for mat in final_set:
            if hasattr(mat, 'use_fake_user'): mat.use_fake_user = True
            # <<< FIX: Rename variable >>>
            mat_uuid_final = validate_material_uuid(mat)
            if mat_uuid_final and mat.name != mat_uuid_final:
                try: mat.name = mat_uuid_final
                except Exception as final_name_err: print(f"[BG Pre-Write] ERROR setting final name for {mat_uuid_final}: {final_name_err}")

        # 5. Write to Temporary File & Replace
        temp_lib_file = None
        write_success = False
        try:
            target_dir = os.path.dirname(target_file_abs)
            # <<< FIX: Use the imported MODULE uuid here >>>
            temp_suffix = f"_temp_{uuid.uuid4()}.blend"
            temp_name_base = os.path.basename(target_file_abs).replace(".blend", "")
            temp_lib_file = os.path.join(target_dir, f"{temp_name_base[:50]}{temp_suffix}")

            print(f"[BG Writer] Writing final set to temporary file: {os.path.basename(temp_lib_file)}")
            bpy.data.libraries.write(temp_lib_file, final_set, fake_user=True, compress=True)
            print(f"[BG Writer] Successfully wrote temporary library.")
            write_success = True
        except Exception as write_error:
            print(f"[BG Writer] CRITICAL ERROR writing temporary library: {write_error}")
            print(traceback.format_exc())
            if temp_lib_file and os.path.exists(temp_lib_file):
                try: os.remove(temp_lib_file)
                except Exception: pass
            return 1

        if write_success:
            print(f"[BG Writer] Replacing original library '{os.path.basename(target_file_abs)}' with temporary file.")
            try:
                shutil.move(temp_lib_file, target_file_abs)
                print(f"[BG Writer] Library replacement successful.")
            except Exception as move_error:
                print(f"[BG Writer] CRITICAL ERROR replacing library file: {move_error}")
                print(traceback.format_exc())
                if temp_lib_file and os.path.exists(temp_lib_file):
                    try: os.remove(temp_lib_file)
                    except Exception: pass
                return 1

        print("[BG Writer] Merge process finished.")
        return 0 # Success

    except Exception as e:
        print(f"[BG Writer] Critical error during merge process: {str(e)}")
        print(traceback.format_exc())
        if 'args' not in locals(): print("[BG Writer] Args parsing likely failed.")
        return 1

    finally:
        # 6. Cleanup loaded temporary materials (Keep existing logic)
        print("[BG Writer] Cleaning up temporary materials from memory...")
        cleaned_count = 0
        mats_loaded_temp_objs = loaded_target_mats + loaded_transfer_mats
        all_final_names = {mat.name for mat in final_set}
        processed_for_cleanup_names = set()
        for mat in mats_loaded_temp_objs:
             if not mat or not hasattr(mat, 'name') or mat.name in processed_for_cleanup_names: continue
             processed_for_cleanup_names.add(mat.name)
             if mat.name in bpy.data.materials and mat.name not in all_final_names:
                 if bpy.data.materials[mat.name].library is None:
                     try:
                         bpy.data.materials.remove(bpy.data.materials[mat.name])
                         cleaned_count += 1
                     except Exception as e_clean: print(f"[BG Writer] Error cleaning mat '{mat.name}': {e_clean}")
        print(f"[BG Writer] Cleaned up {cleaned_count} temporary materials by name.")

# --- Entry Point (Keep as is) ---
if __name__ == "__main__":
    exit_code = 1
    try:
        exit_code = main()
    except Exception as main_exc:
        print(f"[BG Writer] Unhandled exception in main execution: {main_exc}")
        print(traceback.format_exc())
    finally:
        print(f"[BG Writer] Exiting with code: {exit_code}")
        sys.exit(exit_code)
