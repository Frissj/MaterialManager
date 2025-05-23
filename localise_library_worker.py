#!/usr/bin/env python3
import bpy, sys, os, sqlite3, uuid, time, argparse, traceback

def validate_uuid(mat):
    """Gets or creates a UUID for the material with debug logging."""
    print(f"[UUID Debug] Validating UUID for: {mat.name if mat else 'None'}")
    if mat and "uuid" in mat and isinstance(mat["uuid"], str) and len(mat["uuid"]) == 36:
        print(f"[UUID Debug] Valid existing UUID: {mat['uuid']}")
        return mat["uuid"]

    new_id = str(uuid.uuid4())
    try:
        if mat:
            mat["uuid"] = new_id
            print(f"[UUID Debug] Generated new UUID: {new_id} for {mat.name}")
    except Exception as e:
        print(f"[UUID Error] Setting UUID failed: {e}")
    return new_id

def parse_args():
    """Parses command line arguments with enhanced validation."""
    print("[Args Debug] Raw sys.argv:", sys.argv)
    if "--" not in sys.argv:
        raise RuntimeError("Missing '--' separator for worker arguments")

    idx = sys.argv.index("--")
    argv = sys.argv[idx+1:]
    print(f"[Args Debug] Processing arguments: {argv}")

    parser = argparse.ArgumentParser()
    parser.add_argument("--lib", required=True,
                       help="Absolute path to central material library")
    parser.add_argument("--db", required=True,
                       help="Absolute path to database file")

    args = parser.parse_args(argv)
    print(f"[Args Debug] Parsed arguments: LIB={args.lib}, DB={args.db}")
    return args

def log_conversion(db_path, blend_file, lib_mat_uuid, local_mat_uuid):
    """Logs the material conversion details to the SQLite database."""
    print(f"[DB Log] Attempting to log conversion to {db_path}")
    conn = None
    try:
        conn = sqlite3.connect(db_path)
        cursor = conn.cursor()

        # Create table if it doesn't exist
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS conversions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
                blend_file TEXT NOT NULL,
                library_material_uuid TEXT NOT NULL,
                local_material_uuid TEXT NOT NULL
            )
        """)
        print("[DB Debug] Table 'conversions' checked/created.")

        # Insert conversion record
        cursor.execute("""
            INSERT INTO conversions (blend_file, library_material_uuid, local_material_uuid)
            VALUES (?, ?, ?)
        """, (blend_file, lib_mat_uuid, local_mat_uuid))

        conn.commit()
        print(f"[DB Log] Successfully logged conversion: Blend={blend_file}, LibUUID={lib_mat_uuid}, LocalUUID={local_mat_uuid}")

    except sqlite3.Error as e:
        print(f"[DB Error] Database operation failed: {e}")
        traceback.print_exc()
        if conn:
            conn.rollback() # Rollback on error
    except Exception as e:
        print(f"[DB Error] An unexpected error occurred during database logging: {e}")
        traceback.print_exc()
    finally:
        if conn:
            conn.close()
            print("[DB Debug] Database connection closed.")


def main():
    """Main function with complete error handling and debug logging."""
    args = None
    try:
        print("\n[Worker] Starting localization process")
        args = parse_args()

        # Enhanced path validation
        LIBRARY_FILE = os.path.abspath(args.lib)
        if not os.path.exists(LIBRARY_FILE):
            raise FileNotFoundError(f"Library file missing: {LIBRARY_FILE}")

        DATABASE_FILE = os.path.abspath(args.db)
        # DB file doesn't need to exist beforehand, log_conversion will create it.
        db_dir = os.path.dirname(DATABASE_FILE)
        if not os.path.isdir(db_dir):
             raise NotADirectoryError(f"Database directory does not exist: {db_dir}")


        blend_path = bpy.data.filepath
        if not blend_path:
            raise RuntimeError("Blend file is not saved. Please save the file before running the script.")
        print(f"[Worker Debug] Processing blend file: {blend_path}")

        converted_count = 0
        materials_to_check = list(bpy.data.materials)
        print(f"[Worker Debug] Found {len(materials_to_check)} materials to check")

        for mat in materials_to_check:
            print(f"\n[Material Debug] Processing: {mat.name}")

            # Skip non-linked materials
            if not mat or not mat.library:
                print("[Material Debug] Skipping - not a linked material")
                continue

            try:
                # Enhanced path comparison
                mat_lib_path = bpy.path.abspath(mat.library.filepath)
                print(f"[Path Debug] Material library path: {mat_lib_path}")

                # Normalize paths for comparison
                norm_mat_path = os.path.normcase(os.path.normpath(mat_lib_path))
                norm_target_path = os.path.normcase(os.path.normpath(LIBRARY_FILE))
                print(f"[Path Compare] Material: {norm_mat_path}\nTarget: {norm_target_path}")

                if norm_mat_path != norm_target_path:
                    print("[Path Debug] Skipping - different library")
                    continue

            except AttributeError:
                 print("[Path Debug] Skipping - Material library path is invalid or inaccessible.")
                 continue # Skip if path is somehow invalid
            except Exception as e:
                print(f"[Path Error] Validation failed: {str(e)}")
                continue

            # Material usage check with detailed logging
            print("[Usage Debug] Checking material usage...")
            is_used = False
            for obj in bpy.data.objects:
                # Check only mesh objects in the current scene's view layer
                # This avoids checking objects in other scenes or libraries if file has multiple scenes
                # Check if object is visible and part of the active view layer for relevance
                if obj.type == 'MESH' and obj.material_slots and obj.name in bpy.context.view_layer.objects:
                    print(f"[Object Debug] Checking {obj.name} (Mesh in active view layer)")
                    for slot in obj.material_slots:
                        if slot.material == mat:
                            print(f"[Usage Found] Used in {obj.name} slot {slot.name}")
                            is_used = True
                            break
                    if is_used: break
            if not is_used:
                print("[Usage Debug] Material not in use in active view layer - skipping")
                continue

            # Localization process with transaction logging
            print("[Localization] Starting localization process")
            try:
                lib_mat_uuid = validate_uuid(mat) # Get UUID before copy might clear it
                local_mat = mat.make_local() # Use make_local for cleaner separation
                # No need to copy, make_local creates a new local datablock

                local_mat_uuid = validate_uuid(local_mat) # Assign/get UUID for the new local mat

                print(f"[Localization Debug] Original Lib Mat: {mat.name} (UUID: {lib_mat_uuid}) -> New Local Mat: {local_mat.name} (UUID: {local_mat_uuid})")

                # Update material assignments (re-iterate as make_local might have changed things)
                update_count = 0
                for obj in bpy.data.objects:
                    if obj.type == 'MESH' and obj.name in bpy.context.view_layer.objects:
                        for slot in obj.material_slots:
                             # Need to check by name now, as the original 'mat' reference might be invalid
                             # or point to the now-local material depending on Blender version/context.
                             # Safest is to compare by the original library material name and library source.
                             if slot.material and slot.material.library and bpy.path.abspath(slot.material.library.filepath) == LIBRARY_FILE and slot.material.name == mat.name:
                                print(f"[Assignment Debug] Updating slot {slot.name} on object {obj.name} from {slot.material.name} to {local_mat.name}")
                                slot.material = local_mat
                                update_count += 1

                print(f"[Assignment Debug] Updated {update_count} material slots.")

                # Database logging
                log_conversion(DATABASE_FILE, blend_path, lib_mat_uuid, local_mat_uuid)
                converted_count += 1

            except Exception as e:
                print(f"[Localization Error] Failed for material {mat.name}: {str(e)}")
                traceback.print_exc()
                # Decide if we should continue with the next material or stop
                # continue # Uncomment to try next material even if one fails

        # Finalization with save validation
        if converted_count > 0:
            print(f"\n[Worker] Successfully localized {converted_count} materials.")
            print("[Worker] Saving changes to the blend file...")
            try:
                bpy.ops.wm.save_mainfile()
                print("[Save Debug] Save successful")
            except Exception as e:
                print(f"[Save Error] Failed to save the blend file: {str(e)}")
                # Potentially return a different error code for save failure vs. processing failure
                return 2 # Indicate save failure
        else:
            print("[Worker] No materials required localization.")

        return 0 # Success

    except FileNotFoundError as fnf_error:
        print(f"\n[FATAL ERROR] Missing file/directory: {fnf_error}")
        traceback.print_exc()
        return 3 # Indicate configuration/file error
    except NotADirectoryError as nd_error:
        print(f"\n[FATAL ERROR] Invalid directory: {nd_error}")
        traceback.print_exc()
        return 3 # Indicate configuration/file error
    except RuntimeError as rt_error:
         print(f"\n[FATAL ERROR] Runtime issue: {rt_error}")
         traceback.print_exc()
         return 4 # Indicate runtime setup error
    except Exception as fatal_error:
        print(f"\n[FATAL ERROR] An unexpected critical error occurred: {str(fatal_error)}")
        traceback.print_exc()
        # General fatal error
        return 1 # General failure code

if __name__ == "__main__":
    exit_code = main()
    print(f"\n[Worker] Exiting with code: {exit_code}")
    # Ensure Blender exits cleanly with the determined code
    # Use os._exit for immediate exit if Blender hangs on sys.exit in background mode
    # sys.exit(exit_code)
    os._exit(exit_code) # Force exit in background mode
