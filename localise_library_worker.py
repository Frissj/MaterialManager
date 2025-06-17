#!/usr/bin/env python3
import bpy, sys, os, sqlite3, uuid, time, argparse, traceback

def validate_uuid(mat):
    """Gets or creates a UUID for the material with debug logging."""
    print(f"[WORKER-TRACE] validate_uuid called for: '{mat.name if mat else 'None'}'", flush=True)
    if mat and "uuid" in mat and isinstance(mat["uuid"], str) and len(mat["uuid"]) == 36:
        print(f"[WORKER-TRACE]   Found existing valid UUID: {mat['uuid']}", flush=True)
        return mat["uuid"]

    new_id = str(uuid.uuid4())
    print(f"[WORKER-TRACE]   No valid UUID found. Generated new one: {new_id}", flush=True)
    try:
        if mat:
            mat["uuid"] = new_id
            print(f"[WORKER-TRACE]   Successfully assigned new UUID to '{mat.name}'", flush=True)
    except Exception as e:
        print(f"[WORKER-ERROR] Setting UUID failed for '{mat.name if mat else 'None'}': {e}", flush=True)
    return new_id

def parse_args():
    """Parses command line arguments with enhanced validation."""
    print("[WORKER-TRACE] parse_args called.", flush=True)
    print(f"[WORKER-TRACE]   Raw sys.argv: {sys.argv}", flush=True)
    if "--" not in sys.argv:
        print("[WORKER-ERROR] Fatal: Missing '--' separator for worker arguments.", flush=True)
        raise RuntimeError("Missing '--' separator for worker arguments")

    idx = sys.argv.index("--")
    argv = sys.argv[idx+1:]
    print(f"[WORKER-TRACE]   Arguments for parser: {argv}", flush=True)

    parser = argparse.ArgumentParser()
    parser.add_argument("--lib", required=True,
                        help="Absolute path to central material library")
    parser.add_argument("--db", required=True,
                        help="Absolute path to database file")

    args = parser.parse_args(argv)
    print(f"[WORKER-TRACE]   Arguments parsed: LIB='{args.lib}', DB='{args.db}'", flush=True)
    return args

def log_conversion(db_path, blend_file, lib_mat_uuid, local_mat_uuid):
    """Logs the material conversion details to the SQLite database."""
    print(f"[WORKER-TRACE] log_conversion called.", flush=True)
    print(f"[WORKER-TRACE]   DB Path: '{db_path}'", flush=True)
    print(f"[WORKER-TRACE]   Blend File: '{blend_file}'", flush=True)
    print(f"[WORKER-TRACE]   Lib UUID: '{lib_mat_uuid}'", flush=True)
    print(f"[WORKER-TRACE]   Local UUID: '{local_mat_uuid}'", flush=True)
    conn = None
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()

        print("[WORKER-TRACE]   Executing CREATE TABLE IF NOT EXISTS...", flush=True)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS conversions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                blend_file TEXT NOT NULL,
                library_material_uuid TEXT NOT NULL,
                local_material_uuid TEXT NOT NULL
            )
        """)
        print("[WORKER-TRACE]   Executing INSERT...", flush=True)
        cursor.execute("""
            INSERT INTO conversions (blend_file, library_material_uuid, local_material_uuid)
            VALUES (?, ?, ?)
        """, (blend_file, lib_mat_uuid, local_mat_uuid))

        conn.commit()
        print(f"[WORKER-TRACE]   SUCCESS: Logged conversion to DB.", flush=True)

    except sqlite3.Error as e:
        print(f"[WORKER-ERROR] Database operation failed: {e}", flush=True)
        traceback.print_exc(file=sys.stdout)
        if conn:
            conn.rollback()
    except Exception as e:
        print(f"[WORKER-ERROR] An unexpected error occurred during database logging: {e}", flush=True)
        traceback.print_exc(file=sys.stdout)
    finally:
        if conn:
            conn.close()
            print("[WORKER-TRACE]   Database connection closed.", flush=True)


def main():
    """Main function with complete error handling and debug logging."""
    args = None
    try:
        print("\n[WORKER-TRACE] Starting localization process (main function)", flush=True)
        args = parse_args()

        LIBRARY_FILE = os.path.abspath(args.lib)
        print(f"[WORKER-TRACE]   Absolute Library Path: {LIBRARY_FILE}", flush=True)
        if not os.path.exists(LIBRARY_FILE):
            raise FileNotFoundError(f"Library file missing: {LIBRARY_FILE}")

        DATABASE_FILE = os.path.abspath(args.db)
        print(f"[WORKER-TRACE]   Absolute DB Path: {DATABASE_FILE}", flush=True)
        db_dir = os.path.dirname(DATABASE_FILE)
        if not os.path.isdir(db_dir):
            raise NotADirectoryError(f"Database directory does not exist: {db_dir}")

        blend_path = bpy.data.filepath
        if not blend_path:
            raise RuntimeError("Blend file is not saved. Please save the file before running the script.")
        print(f"[WORKER-TRACE] Processing blend file: {blend_path}", flush=True)

        converted_count = 0
        materials_to_check = list(bpy.data.materials)
        print(f"[WORKER-TRACE] Found {len(materials_to_check)} total materials in memory. Starting loop.", flush=True)

        for mat in materials_to_check:
            print(f"\n[WORKER-TRACE] --- Processing material: '{mat.name if mat else 'INVALID_MATERIAL'}' ---", flush=True)

            if not mat or not mat.library:
                print("[WORKER-TRACE]   SKIP: Not a linked material.", flush=True)
                continue

            try:
                mat_lib_path = bpy.path.abspath(mat.library.filepath)
                print(f"[WORKER-TRACE]   Material's raw library path: {mat_lib_path}", flush=True)

                norm_mat_path = os.path.normcase(os.path.normpath(mat_lib_path))
                norm_target_path = os.path.normcase(os.path.normpath(LIBRARY_FILE))
                print(f"[WORKER-TRACE]   Comparing normalized paths:", flush=True)
                print(f"[WORKER-TRACE]     Material: '{norm_mat_path}'", flush=True)
                print(f"[WORKER-TRACE]       Target: '{norm_target_path}'", flush=True)

                if norm_mat_path != norm_target_path:
                    print("[WORKER-TRACE]   SKIP: Belongs to a different library.", flush=True)
                    continue

            except AttributeError:
                print("[WORKER-TRACE]   SKIP: Material library path is invalid or inaccessible.", flush=True)
                continue
            except Exception as e:
                print(f"[WORKER-ERROR] Path validation failed: {str(e)}", flush=True)
                continue

            print("[WORKER-TRACE]   Path matches. Checking usage...", flush=True)
            is_used = False
            for obj in bpy.data.objects:
                if obj.type == 'MESH' and obj.material_slots and obj.name in bpy.context.view_layer.objects:
                    # print(f"[WORKER-TRACE]     Checking obj '{obj.name}'...") # Can be too verbose, uncomment if needed
                    for slot in obj.material_slots:
                        if slot.material == mat:
                            print(f"[WORKER-TRACE]     FOUND USAGE in '{obj.name}' (slot '{slot.name}').", flush=True)
                            is_used = True
                            break
                    if is_used: break
            
            if not is_used:
                print("[WORKER-TRACE]   SKIP: Material not used in the active view layer.", flush=True)
                continue

            print("[WORKER-TRACE]   Material is used. Starting localization...", flush=True)
            try:
                lib_mat_uuid = validate_uuid(mat)
                print(f"[WORKER-TRACE]   Original Lib Mat UUID: {lib_mat_uuid}", flush=True)

                local_mat = mat.make_local()
                print(f"[WORKER-TRACE]   '.make_local()' executed. New local material name: '{local_mat.name if local_mat else 'None'}'", flush=True)
                
                local_mat_uuid = validate_uuid(local_mat)
                print(f"[WORKER-TRACE]   New Local Mat UUID: {local_mat_uuid}", flush=True)
                
                print("[WORKER-TRACE]   Updating material assignments...", flush=True)
                update_count = 0
                for obj in bpy.data.objects:
                    if obj.type == 'MESH' and obj.name in bpy.context.view_layer.objects:
                        for slot in obj.material_slots:
                            if slot.material and slot.material.library and bpy.path.abspath(slot.material.library.filepath) == LIBRARY_FILE and slot.material.name == mat.name:
                                print(f"[WORKER-TRACE]     Re-assigning slot '{slot.name}' on '{obj.name}' to new local material '{local_mat.name}'", flush=True)
                                slot.material = local_mat
                                update_count += 1
                print(f"[WORKER-TRACE]   Updated {update_count} material slots.", flush=True)
                
                log_conversion(DATABASE_FILE, blend_path, lib_mat_uuid, local_mat_uuid)
                converted_count += 1

            except Exception as e:
                print(f"[WORKER-ERROR] Localization FAILED for material '{mat.name}': {str(e)}", flush=True)
                traceback.print_exc(file=sys.stdout)
                continue

        if converted_count > 0:
            print(f"\n[WORKER-TRACE] Loop finished. Successfully localized {converted_count} material(s).", flush=True)
            print("[WORKER-TRACE] Saving changes to the blend file...", flush=True)
            try:
                bpy.ops.wm.save_mainfile()
                print("[WORKER-TRACE]   Save successful.", flush=True)
            except Exception as e:
                print(f"[WORKER-ERROR] Failed to save the blend file: {str(e)}", flush=True)
                return 2
        else:
            print("\n[WORKER-TRACE] Loop finished. No materials required localization.", flush=True)

        return 0

    except FileNotFoundError as fnf_error:
        print(f"\n[WORKER-FATAL] Missing file/directory: {fnf_error}", flush=True)
        traceback.print_exc(file=sys.stdout)
        return 3
    except NotADirectoryError as nd_error:
        print(f"\n[WORKER-FATAL] Invalid directory: {nd_error}", flush=True)
        traceback.print_exc(file=sys.stdout)
        return 3
    except RuntimeError as rt_error:
        print(f"\n[WORKER-FATAL] Runtime issue: {rt_error}", flush=True)
        traceback.print_exc(file=sys.stdout)
        return 4
    except Exception as fatal_error:
        print(f"\n[WORKER-FATAL] An unexpected critical error occurred: {str(fatal_error)}", flush=True)
        traceback.print_exc(file=sys.stdout)
        return 1

if __name__ == "__main__":
    exit_code = 99 # Default error code if main() fails to return
    try:
        exit_code = main()
    except Exception as e:
        print(f"[WORKER-FATAL] Unhandled exception in __main__: {e}", flush=True)
        traceback.print_exc(file=sys.stdout)
        exit_code = 1
    finally:
        print(f"\n[WORKER-TRACE] Script is about to exit with code: {exit_code}", flush=True)
        os._exit(exit_code)
