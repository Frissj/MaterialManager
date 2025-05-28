import bpy
import sys
import os
import argparse
import traceback
import hashlib
import json
import uuid
import sqlite3
import time
import re # Not strictly used in this version but often useful in Blender scripts
import shutil # Make sure shutil is imported
import tempfile # Used by merge_library
import math
# sys is already imported

# --- Globals for Thumbnail Rendering Part (initialized by functions) ---
ICON_TEMPLATE_FILE_WORKER = None
THUMBNAIL_SIZE_WORKER = 256 # Default, overridden by arg
persistent_icon_template_scene_worker = None # Cache for loaded template scene within this worker instance
HASH_VERSION_FOR_WORKER = "v_RTX_REMIX_PBR_COMPREHENSIVE_2_CONTENT_ONLY"

# --- Hashing Functions (Ensure these match your main addon's implementation) ---
def _float_repr(f):
    try:
        return f"{float(f):.8f}"
    except (ValueError, TypeError):
        return "CONV_ERROR"

def _stable_repr(value):
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
        if not list_val: return '[]'
        return '[' + ','.join([_float_repr(item) for item in list_val]) + ']'
    elif value is None:
        return 'None'
    else:
        return repr(value)

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

def find_principled_bsdf(mat): # Keep your version
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

def validate_material_uuid(mat, is_copy=False): # From background_writer.py
    if mat is None: return None
    original_uuid = mat.get("uuid", "")
    if not original_uuid or len(original_uuid) != 36 or is_copy:
        # If it's a copy or has no valid UUID, generate a new one.
        # The actual setting of this UUID on the material is handled by the caller if needed.
        return str(uuid.uuid4())
    return original_uuid

def get_material_hash(mat, current_blend_filepath_for_worker_context=None):
    """
    Calculates a content-based hash for a material.
    This version is for background_writer.py and does NOT use main addon caches.
    `current_blend_filepath_for_worker_context` is the path to the .blend file
    currently being processed by the worker (e.g., the transfer file), crucial for
    resolving '//' style image paths within that file's context if bpy.data.filepath
    is not reliable in the worker for this purpose.
    """
    if not mat: 
        return None
    
    mat_name_for_debug = getattr(mat, 'name_full', getattr(mat, 'name', 'UnknownMaterial_BG_Worker'))
    # mat_uuid = mat.get("uuid") # Not used for caching in this worker version

    # NO CACHING LOGIC using main addon's material_hashes or global_hash_cache here.
    # This function in the worker always calculates or relies on its own context.

    # print(f"[GetHash BG_WORKER - CALCULATING] Mat: {mat_name_for_debug}, UUID: {mat_uuid}")

    hash_inputs = []
    pbr_image_hashes = set() 

    try:
        principled_node = None
        material_output_node = None

        if mat.use_nodes and mat.node_tree:
            principled_node = find_principled_bsdf(mat) 
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
            hash_inputs.append("NON_NODE_MATERIAL_BG_WORKER") # Suffix for clarity
            hash_inputs.append(f"DiffuseColor:{_stable_repr(mat.diffuse_color)}")
            hash_inputs.append(f"Metallic:{_stable_repr(mat.metallic)}")
            hash_inputs.append(f"Roughness:{_stable_repr(mat.roughness)}")

        if principled_node:
            hash_inputs.append(f"SHADER_TYPE:{principled_node.bl_idname}")
            inputs_to_process = [
                ("Base Color", "color_texture"), ("Metallic", "value_texture"), ("Roughness", "value_texture"),
                ("IOR", "value_only"), ("Alpha", "value_texture"), ("Normal", "normal_texture_special"),
                ("Emission Color", "color_texture"), ("Emission Strength", "value_only"),
                ("Subsurface Weight", "value_texture"), ("Subsurface Color", "color_texture"),
                ("Subsurface Radius", "vector_value_only"), ("Subsurface Scale", "value_only"),
                ("Subsurface IOR", "value_only"), ("Subsurface Anisotropy", "value_only"),
                ("Clearcoat Weight", "value_texture"), ("Clearcoat Tint", "color_texture"), 
                ("Clearcoat Roughness", "value_texture"),
                ("Clearcoat Normal", "normal_texture_special"),
                ("Specular IOR Level", "value_texture"), ("Specular Tint", "color_texture"),
                ("Sheen Weight", "value_texture"), ("Sheen Tint", "color_texture"),
                ("Sheen Roughness", "value_texture"),
                ("Transmission Weight", "value_texture"), ("Transmission Roughness", "value_texture"),
                ("Anisotropic", "value_texture"),("Anisotropic Rotation", "value_texture"),
            ]
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
                if not inp: continue

                input_key_str = f"INPUT:{input_name}"
                if inp.is_linked:
                    link = inp.links[0]; source_node = link.from_node; source_socket_name = link.from_socket.name
                    if processing_type == "normal_texture_special":
                        if source_node.bl_idname == 'ShaderNodeNormalMap':
                            nm_strength_input = source_node.inputs.get("Strength")
                            nm_strength = nm_strength_input.default_value if nm_strength_input and hasattr(nm_strength_input, 'default_value') else 1.0
                            nm_color_input = source_node.inputs.get("Color")
                            tex_hash = "NO_TEX_IN_NORMALMAP_BG_WORKER"
                            if nm_color_input and nm_color_input.is_linked and nm_color_input.links[0].from_node.bl_idname == 'ShaderNodeTexImage':
                                tex_node = nm_color_input.links[0].from_node
                                if tex_node.image:
                                    img_hash = _hash_image(tex_node.image, current_blend_filepath_for_worker_context)
                                    if img_hash: pbr_image_hashes.add(img_hash)
                                    tex_hash = img_hash if img_hash else f"TEX_NORMALMAP_IMG_NO_HASH_BGW_{getattr(tex_node.image, 'name', 'Unnamed')}"
                            hash_inputs.append(f"{input_key_str}=NORMALMAP(Strength:{_stable_repr(nm_strength)},Tex:{tex_hash})")
                        elif source_node.bl_idname == 'ShaderNodeBump':
                            bump_strength_input = source_node.inputs.get("Strength")
                            bump_distance_input = source_node.inputs.get("Distance")
                            bump_strength = bump_strength_input.default_value if bump_strength_input and hasattr(bump_strength_input, 'default_value') else 1.0
                            bump_distance = bump_distance_input.default_value if bump_distance_input and hasattr(bump_distance_input, 'default_value') else 0.1
                            bump_height_input = source_node.inputs.get("Height")
                            tex_hash = "NO_TEX_IN_BUMPMAP_BG_WORKER"
                            if bump_height_input and bump_height_input.is_linked and bump_height_input.links[0].from_node.bl_idname == 'ShaderNodeTexImage':
                                tex_node = bump_height_input.links[0].from_node
                                if tex_node.image:
                                    img_hash = _hash_image(tex_node.image, current_blend_filepath_for_worker_context)
                                    if img_hash: pbr_image_hashes.add(img_hash)
                                    tex_hash = img_hash if img_hash else f"TEX_BUMP_IMG_NO_HASH_BGW_{getattr(tex_node.image, 'name', 'Unnamed')}"
                            hash_inputs.append(f"{input_key_str}=BUMPMAP(Strength:{_stable_repr(bump_strength)},Distance:{_stable_repr(bump_distance)},Tex:{tex_hash})")
                        elif source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image:
                            img_hash = _hash_image(source_node.image, current_blend_filepath_for_worker_context)
                            if img_hash: pbr_image_hashes.add(img_hash)
                            tex_hash = img_hash if img_hash else f"TEX_NORMAL_IMG_NO_HASH_BGW_{getattr(source_node.image, 'name', 'Unnamed')}"
                            hash_inputs.append(f"{input_key_str}=TEX:{tex_hash}")
                        else:
                            hash_inputs.append(f"{input_key_str}=LINKED_NODE:{source_node.bl_idname}_SOCKET:{source_socket_name}")
                    elif source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image:
                        img_hash = _hash_image(source_node.image, current_blend_filepath_for_worker_context)
                        if img_hash: pbr_image_hashes.add(img_hash)
                        tex_hash = img_hash if img_hash else f"TEX_{input_name.replace(' ','')}_IMG_NO_HASH_BGW_{getattr(source_node.image, 'name', 'Unnamed')}"
                        hash_inputs.append(f"{input_key_str}=TEX:{tex_hash}")
                    else:
                        hash_inputs.append(f"{input_key_str}=LINKED_NODE:{source_node.bl_idname}_SOCKET:{source_socket_name}")
                else: # Input not linked
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
                    tex_hash = "NO_TEX_IN_DISPLACEMENT_NODE_BG_WORKER"
                    if disp_height_input and disp_height_input.is_linked and disp_height_input.links[0].from_node.bl_idname == 'ShaderNodeTexImage':
                        tex_node = disp_height_input.links[0].from_node
                        if tex_node.image:
                            img_hash = _hash_image(tex_node.image, current_blend_filepath_for_worker_context)
                            if img_hash: pbr_image_hashes.add(img_hash)
                            tex_hash = img_hash if img_hash else f"TEX_DISP_IMG_NO_HASH_BGW_{getattr(tex_node.image, 'name', 'Unnamed')}"
                    hash_inputs.append(f"MAT_OUTPUT_DISPLACEMENT=DISP_NODE(Mid:{_stable_repr(disp_midlevel)},Scale:{_stable_repr(disp_scale)},Tex:{tex_hash})")
                elif source_node.bl_idname == 'ShaderNodeTexImage' and source_node.image: 
                    img_hash = _hash_image(source_node.image, current_blend_filepath_for_worker_context)
                    if img_hash: pbr_image_hashes.add(img_hash)
                    tex_hash = img_hash if img_hash else f"TEX_DISP_DIRECT_IMG_NO_HASH_BGW_{getattr(source_node.image, 'name', 'Unnamed')}"
                    hash_inputs.append(f"MAT_OUTPUT_DISPLACEMENT=TEX:{tex_hash}")
                else: 
                    hash_inputs.append(f"MAT_OUTPUT_DISPLACEMENT=LINKED_NODE:{source_node.bl_idname}_SOCKET:{source_socket_name}")

        if mat.use_nodes and mat.node_tree:
            for node in mat.node_tree.nodes:
                if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                    img_hash_general = _hash_image(node.image, current_blend_filepath_for_worker_context) 
                    if img_hash_general:
                        pbr_image_hashes.add(img_hash_general)

        if pbr_image_hashes:
            sorted_pbr_image_hashes = sorted(list(pbr_image_hashes)) 
            hash_inputs.append(f"ALL_UNIQUE_IMAGE_HASHES_COMBINED:{'|'.join(sorted_pbr_image_hashes)}")
        
        final_hash_string = f"VERSION:{HASH_VERSION_FOR_WORKER}|||" + "|||".join(sorted(hash_inputs))
        digest = hashlib.md5(final_hash_string.encode('utf-8')).hexdigest()
        
        # No attempt to update main addon's global_hash_cache or material_hashes from the worker
        return digest

    except Exception as e:
        print(f"[BG_WORKER get_material_hash] Error hashing mat '{mat_name_for_debug}': {type(e).__name__} - {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr) 
        return None

# --- Database Timestamp Function (Used by Merge Library) ---
def update_material_timestamp_in_db(db_path, material_uuid):
    if not db_path or not material_uuid: return
    conn = None
    try:
        if not os.path.exists(db_path): return
        conn = sqlite3.connect(db_path, timeout=10)
        c = conn.cursor()
        c.execute("CREATE TABLE IF NOT EXISTS mat_time (uuid TEXT PRIMARY KEY, ts INTEGER)")
        current_time = int(time.time())
        c.execute("INSERT OR REPLACE INTO mat_time (uuid, ts) VALUES (?, ?)", (material_uuid, current_time))
        conn.commit()
    except sqlite3.Error as db_err: print(f"[BG Timestamp WORKER] Database Error for {material_uuid}: {db_err}", file=sys.stderr)
    except Exception as e: print(f"[BG Timestamp WORKER] General Error for {material_uuid}: {e}", file=sys.stderr)
    finally:
        if conn:
            try: conn.close()
            except Exception: pass
# --- End Database Timestamp ---

# --- Thumbnail Rendering Functions ---
def load_icon_template_scene_bg_worker():
    global persistent_icon_template_scene_worker, ICON_TEMPLATE_FILE_WORKER, THUMBNAIL_SIZE_WORKER
    preview_obj_name = "IconPreviewObject"
    camera_obj_name = "IconTemplateCam"
    expected_template_scene_name = "IconTemplateScene"

    if persistent_icon_template_scene_worker:
        try:
            if persistent_icon_template_scene_worker.name in bpy.data.scenes and \
               bpy.data.scenes[persistent_icon_template_scene_worker.name] == persistent_icon_template_scene_worker and \
               persistent_icon_template_scene_worker.objects.get(preview_obj_name) and \
               persistent_icon_template_scene_worker.camera and \
               persistent_icon_template_scene_worker.camera.name == camera_obj_name:
                return persistent_icon_template_scene_worker
            if persistent_icon_template_scene_worker.name in bpy.data.scenes:
                 if len(bpy.data.scenes) > 1 or (bpy.context.window and bpy.context.window.scene != persistent_icon_template_scene_worker): # Basic safety
                    try: bpy.data.scenes.remove(persistent_icon_template_scene_worker, do_unlink=True)
                    except: pass
            persistent_icon_template_scene_worker = None
        except (ReferenceError, AttributeError, Exception):
            persistent_icon_template_scene_worker = None

    if not ICON_TEMPLATE_FILE_WORKER or not os.path.exists(ICON_TEMPLATE_FILE_WORKER):
        print(f"[BG Worker - Template] FATAL: Icon template file missing or path not set: '{ICON_TEMPLATE_FILE_WORKER}'", file=sys.stderr)
        return None

    loaded_scene_from_blend_file = None
    worker_instance_scene_name = f"_BG_WORKER_TPL_SCENE_{str(uuid.uuid4())[:8]}"

    try:
        scene_name_to_load = expected_template_scene_name
        with bpy.data.libraries.load(ICON_TEMPLATE_FILE_WORKER, link=False, assets_only=False) as (data_from_lib_check, _):
            available_scenes_in_template = list(getattr(data_from_lib_check, "scenes", []))
            if not available_scenes_in_template:
                print(f"[BG Worker - Template] FATAL: No scenes found in template file '{ICON_TEMPLATE_FILE_WORKER}'.", file=sys.stderr)
                return None
            if expected_template_scene_name not in available_scenes_in_template:
                print(f"[BG Worker - Template] WARNING: Expected scene '{expected_template_scene_name}' not in template. Using first: '{available_scenes_in_template[0]}'.", file=sys.stderr)
                scene_name_to_load = available_scenes_in_template[0]

        with bpy.data.libraries.load(ICON_TEMPLATE_FILE_WORKER, link=False) as (data_from, data_to):
            if scene_name_to_load in data_from.scenes:
                data_to.scenes = [scene_name_to_load]
            else:
                print(f"[BG Worker - Template] FATAL: Scene '{scene_name_to_load}' not found for load.", file=sys.stderr)
                return None

        loaded_scene_from_blend_file = bpy.data.scenes.get(scene_name_to_load)
        if not loaded_scene_from_blend_file:
            print(f"[BG Worker - Template] FATAL: Failed to get scene '{scene_name_to_load}' after load.", file=sys.stderr)
            return None

        loaded_scene_from_blend_file.name = worker_instance_scene_name

        if not loaded_scene_from_blend_file.objects.get(preview_obj_name) or \
           not loaded_scene_from_blend_file.objects.get(camera_obj_name) or \
           not loaded_scene_from_blend_file.camera or \
           loaded_scene_from_blend_file.camera.name != camera_obj_name:
            print(f"[BG Worker - Template] FATAL: Template scene '{loaded_scene_from_blend_file.name}' invalid.", file=sys.stderr)
            if loaded_scene_from_blend_file.name in bpy.data.scenes:
                bpy.data.scenes.remove(loaded_scene_from_blend_file, do_unlink=True)
            return None

        render_settings = loaded_scene_from_blend_file.render
        render_settings.resolution_x = THUMBNAIL_SIZE_WORKER
        render_settings.resolution_y = THUMBNAIL_SIZE_WORKER
        render_settings.film_transparent = True
        try:
            engine_options = render_settings.bl_rna.properties['engine'].enum_items.keys()
            render_settings.engine = 'BLENDER_EEVEE_NEXT' if 'BLENDER_EEVEE_NEXT' in engine_options else 'BLENDER_EEVEE'
        except Exception: render_settings.engine = 'BLENDER_EEVEE'
        
        eevee_settings_obj = getattr(loaded_scene_from_blend_file, render_settings.engine.lower(), getattr(render_settings, 'eevee', None))
        if eevee_settings_obj:
            if hasattr(eevee_settings_obj, 'taa_render_samples'): eevee_settings_obj.taa_render_samples = 16
            elif hasattr(eevee_settings_obj, 'samples'): eevee_settings_obj.samples = 16
        
        persistent_icon_template_scene_worker = loaded_scene_from_blend_file
        return persistent_icon_template_scene_worker
    except Exception as e:
        print(f"[BG Worker - Template] CRITICAL ERROR loading/configuring template: {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        if loaded_scene_from_blend_file and loaded_scene_from_blend_file.name in bpy.data.scenes:
            try: bpy.data.scenes.remove(loaded_scene_from_blend_file, do_unlink=True)
            except Exception: pass
        persistent_icon_template_scene_worker = None
        return None

def create_sphere_preview_thumbnail_bg_worker(mat_to_render, output_thumb_path, render_scene_for_item):
    if not render_scene_for_item:
        print(f"[BG Worker - ItemRender] Error for '{getattr(mat_to_render, 'name', 'N/A')}': No render_scene provided.", file=sys.stderr)
        return False

    preview_obj_name = "IconPreviewObject"
    preview_obj = render_scene_for_item.objects.get(preview_obj_name)

    if not preview_obj or not preview_obj.data or not hasattr(preview_obj.data, 'materials'):
        print(f"[BG Worker - ItemRender] Preview object invalid in render scene '{render_scene_for_item.name}'.", file=sys.stderr)
        return False

    temp_mat_copy = None
    try:
        temp_mat_name = f"_TEMP_RENDER_COPY_{mat_to_render.name[:30]}_{str(uuid.uuid4())[:6]}"
        temp_mat_copy = mat_to_render.copy()
        temp_mat_copy.name = temp_mat_name
        temp_mat_copy.use_fake_user = False # Important for temp copies
    except Exception as e_copy:
        print(f"[BG Worker - ItemRender] Error copying material '{mat_to_render.name}': {e_copy}", file=sys.stderr)
        return False

    final_output_path = output_thumb_path
    output_dir = os.path.dirname(final_output_path)
    if not os.path.exists(output_dir):
        try: os.makedirs(output_dir, exist_ok=True)
        except Exception as e_mkdir:
            print(f"[BG Worker - ItemRender] ERROR: Could not create output dir '{output_dir}': {e_mkdir}", file=sys.stderr)
            if temp_mat_copy and temp_mat_copy.name in bpy.data.materials:
                try: bpy.data.materials.remove(temp_mat_copy, do_unlink=True)
                except Exception: pass
            return False

    temp_filename = f"render_temp_{uuid.uuid4().hex}.png"
    temp_render_output_path = os.path.join(output_dir, temp_filename)

    try:
        if not preview_obj.material_slots:
            preview_obj.data.materials.append(temp_mat_copy)
        else:
            preview_obj.material_slots[0].material = temp_mat_copy

        # UV Map linking (same as before)
        if temp_mat_copy.use_nodes and temp_mat_copy.node_tree:
            active_uv_map = preview_obj.data.uv_layers.active or (preview_obj.data.uv_layers[0] if preview_obj.data.uv_layers else None)
            if active_uv_map:
                uv_map_node = next((n for n in temp_mat_copy.node_tree.nodes if n.bl_idname == 'ShaderNodeUVMap'), None)
                if not uv_map_node: uv_map_node = temp_mat_copy.node_tree.nodes.new('ShaderNodeUVMap')
                uv_map_node.uv_map = active_uv_map.name
                for tex_node in temp_mat_copy.node_tree.nodes:
                    if tex_node.bl_idname == 'ShaderNodeTexImage':
                        vector_input = tex_node.inputs.get("Vector")
                        if vector_input and not vector_input.is_linked:
                            try: temp_mat_copy.node_tree.links.new(uv_map_node.outputs['UV'], vector_input)
                            except Exception: pass # Minor error

        render_scene_for_item.render.filepath = temp_render_output_path
        bpy.ops.render.render(scene=render_scene_for_item.name, write_still=True)
        time.sleep(0.1) # Pause

        if not os.path.exists(temp_render_output_path) or os.path.getsize(temp_render_output_path) == 0:
            print(f"[BG Worker - ItemRender] ERROR: Temp render output missing or empty: {temp_render_output_path}", file=sys.stderr)
            if os.path.exists(temp_render_output_path): 
                try: os.remove(temp_render_output_path) 
                except Exception: pass
            return False
        
        try:
            shutil.move(temp_render_output_path, final_output_path)
        except Exception as e_move:
            print(f"[BG Worker - ItemRender] ERROR: Failed to move temp render to final: {e_move}", file=sys.stderr)
            if os.path.exists(temp_render_output_path): 
                try: os.remove(temp_render_output_path) 
                except Exception: pass
            return False

        if not os.path.exists(final_output_path) or os.path.getsize(final_output_path) == 0:
            print(f"[BG Worker - ItemRender] ERROR: Final output file missing/empty after move: {final_output_path}", file=sys.stderr)
            return False
        return True
    except Exception as e_render_process:
        print(f"[BG Worker - ItemRender] Critical error rendering '{temp_mat_copy.name if temp_mat_copy else mat_to_render.name}': {e_render_process}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        if os.path.exists(temp_render_output_path): 
            try: os.remove(temp_render_output_path) 
            except Exception: pass
        return False
    finally:
        if temp_mat_copy and temp_mat_copy.name in bpy.data.materials:
            try: bpy.data.materials.remove(temp_mat_copy, do_unlink=True)
            except Exception: pass

def main_render_thumbnail_batch(args_batch_render): # Mostly same as before
    print(f"[BG Worker - Thumb Batch Op] STARTING Batch. AddonData: {args_batch_render.addon_data_root}", file=sys.stderr)
    global ICON_TEMPLATE_FILE_WORKER, THUMBNAIL_SIZE_WORKER
    ICON_TEMPLATE_FILE_WORKER = os.path.join(args_batch_render.addon_data_root, "icon_generation_template.blend")
    THUMBNAIL_SIZE_WORKER = args_batch_render.thumbnail_size
    json_output_payload = {"results": []}

    if not os.path.exists(ICON_TEMPLATE_FILE_WORKER):
        print(f"[BG Worker - Thumb Batch Op] FATAL: Icon template missing: '{ICON_TEMPLATE_FILE_WORKER}'.", file=sys.stderr)
        # Populate errors for all tasks if template is missing
        try: tasks_for_early_failure = json.loads(args_batch_render.tasks_json)
        except: tasks_for_early_failure = []
        for task_info in tasks_for_early_failure:
            json_output_payload["results"].append({
                "hash_value": task_info.get('hash_value', f"NO_HASH_TPL_MISSING_{str(uuid.uuid4())[:4]}"),
                "thumb_path": task_info.get('thumb_path', "NO_PATH_TPL_MISSING"),
                "status": "failure", "reason": "worker_icon_template_file_missing"
            })
        print(json.dumps(json_output_payload))
        sys.stdout.flush()
        return 1

    try: tasks_to_process_in_batch = json.loads(args_batch_render.tasks_json)
    except json.JSONDecodeError as e_json:
        print(f"[BG Worker - Thumb Batch Op] FATAL: Could not decode tasks_json: {e_json}", file=sys.stderr)
        json_output_payload["error"] = "tasks_json_decode_error"; json_output_payload["message"] = str(e_json)
        print(json.dumps(json_output_payload)); sys.stdout.flush()
        return 1
    
    if not tasks_to_process_in_batch:
        print("[BG Worker - Thumb Batch Op] No tasks in JSON. Exiting gracefully.", file=sys.stderr)
        print(json.dumps(json_output_payload)); sys.stdout.flush()
        return 0

    render_scene_instance_for_batch = load_icon_template_scene_bg_worker()
    if not render_scene_instance_for_batch:
        print(f"[BG Worker - Thumb Batch Op] FATAL: Failed to load icon template scene. Batch fails.", file=sys.stderr)
        for task_info in tasks_to_process_in_batch:
            json_output_payload["results"].append({
                "hash_value": task_info.get('hash_value', f"NO_HASH_SCENE_FAIL_{str(uuid.uuid4())[:4]}"),
                "thumb_path": task_info.get('thumb_path', "NO_PATH_SCENE_FAIL"),
                "status": "failure", "reason": "worker_template_scene_load_failed"
            })
        print(json.dumps(json_output_payload)); sys.stdout.flush()
        return 1
    
    # Pre-fill results with failure status
    for task_info in tasks_to_process_in_batch:
         json_output_payload["results"].append({
            "hash_value": task_info.get('hash_value'), "thumb_path": task_info.get('thumb_path'),
            "status": "failure", "reason": "processing_not_attempted_or_early_exit"
        })

    for task_index, current_task_info in enumerate(tasks_to_process_in_batch):
        current_task_result_dict = json_output_payload["results"][task_index] # Get the pre-filled dict
        task_hash = current_task_info.get('hash_value')
        task_thumb_path = current_task_info.get('thumb_path')
        task_mat_uuid = current_task_info.get('mat_uuid')
        task_mat_name_debug = current_task_info.get('mat_name_debug', 'N/A_DEBUG_NAME')

        if not all([task_hash, task_thumb_path, task_mat_uuid]):
            current_task_result_dict["reason"] = "Task data incomplete"; continue

        material_object_to_render = bpy.data.materials.get(task_mat_uuid) # Primary lookup by UUID (datablock name)
        if not material_object_to_render: # Fallback by custom prop "uuid"
            material_object_to_render = next((m for m in bpy.data.materials if m.get("uuid") == task_mat_uuid), None)
        if not material_object_to_render and task_mat_name_debug: # Fallback by debug name if UUID fails (less reliable)
             material_object_to_render = bpy.data.materials.get(task_mat_name_debug)
        
        if not material_object_to_render:
            current_task_result_dict["reason"] = f"Material UUID '{task_mat_uuid}' not found"; continue
        
        try:
            render_success = create_sphere_preview_thumbnail_bg_worker(
                material_object_to_render, task_thumb_path, render_scene_instance_for_batch
            )
            if render_success and os.path.exists(task_thumb_path) and os.path.getsize(task_thumb_path) > 0:
                current_task_result_dict["status"] = "success"
                current_task_result_dict["reason"] = "thumbnail_rendered_successfully"
            else:
                current_task_result_dict["reason"] = "render_call_ok_but_file_invalid_or_missing" if render_success else "render_function_returned_false"
        except Exception as e_render_item:
            current_task_result_dict["reason"] = f"exception_in_render_call:_{type(e_render_item).__name__}"
            print(f"  EXCEPTION rendering task for {task_mat_name_debug}: {e_render_item}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
    
    # Cleanup the scene used for this batch
    global persistent_icon_template_scene_worker # Ensure it's the global being cleared
    if persistent_icon_template_scene_worker and persistent_icon_template_scene_worker.name in bpy.data.scenes:
        try: bpy.data.scenes.remove(persistent_icon_template_scene_worker, do_unlink=True)
        except Exception as e_clean: print(f"[BG Worker - Thumb Batch Op] Error cleaning template scene: {e_clean}", file=sys.stderr)
    persistent_icon_template_scene_worker = None

    print(json.dumps(json_output_payload)); sys.stdout.flush()
    return 0
# --- End Thumbnail Rendering ---

# --- Library Merging Functions ---
def _load_and_process_blend_file(filepath, is_target_file): # Same as before
    mats_loaded_this_call = []
    processed_data = {}
    if not os.path.exists(filepath):
        print(f"[BG Merge - WORKER LoadFunc] File not found: {filepath}", file=sys.stderr)
        return mats_loaded_this_call, processed_data
    
    mats_before_load = {m.name: m for m in bpy.data.materials}
    try:
        with bpy.data.libraries.load(filepath, link=False, relative=False) as (data_from, data_to):
            if hasattr(data_from, 'materials') and data_from.materials:
                material_names_to_request = [name for name in data_from.materials if isinstance(name, str)]
                data_to.materials = material_names_to_request if material_names_to_request else []
            else:
                data_to.materials = []

        newly_loaded_or_updated_mats = []
        for mat_obj in bpy.data.materials:
            if not mat_obj.library: 
                if mat_obj.name not in mats_before_load or bpy.data.materials[mat_obj.name] != mats_before_load.get(mat_obj.name):
                    newly_loaded_or_updated_mats.append(mat_obj)
        
        if not newly_loaded_or_updated_mats: return mats_loaded_this_call, processed_data

        for mat_obj in newly_loaded_or_updated_mats:
            mats_loaded_this_call.append(mat_obj)
            uid = mat_obj.name # In library/transfer files, name should be UUID
            if not (uid and len(uid) == 36 and '-' in uid):
                uid_prop = mat_obj.get("uuid")
                uid_gen = validate_material_uuid(mat_obj)
                uid = uid_gen 
            h = get_material_hash(mat_obj)
            if uid and h:
                if uid not in processed_data: 
                    processed_data[uid] = {'mat_obj': mat_obj, 'hash': h}
    except Exception as e_load_actual:
        print(f"[BG Merge - WORKER LoadFunc] CRITICAL Error load/process {os.path.basename(filepath)}: {e_load_actual}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        # Basic cleanup of newly added non-library materials on error
        for mat_cleanup in list(bpy.data.materials):
            if not mat_cleanup.library and mat_cleanup.name not in mats_before_load:
                try: bpy.data.materials.remove(mat_cleanup)
                except: pass
        mats_loaded_this_call.clear()
    return mats_loaded_this_call, processed_data

def _worker_record_library_material_origin(db_path, lib_uuid, origin_file, origin_name_in_src, origin_uuid_in_src, check_existing=False): # Same as before
    if not db_path or not os.path.exists(db_path): return
    conn = None
    try:
        conn = sqlite3.connect(db_path, timeout=10)
        c = conn.cursor()
        c.execute('''CREATE TABLE IF NOT EXISTS library_material_origins
                     (library_material_uuid TEXT PRIMARY KEY, source_blend_filepath TEXT,
                      source_material_name_in_file TEXT, source_material_uuid_in_file TEXT,
                      timestamp_added_to_library INTEGER)''')
        if check_existing:
            c.execute("SELECT 1 FROM library_material_origins WHERE library_material_uuid = ? AND source_blend_filepath = ? AND source_material_uuid_in_file = ? AND source_material_name_in_file = ?", 
                      (lib_uuid, origin_file, origin_uuid_in_src, origin_name_in_src))
            if c.fetchone(): return # Already matches

        current_time = int(time.time())
        c.execute("INSERT OR REPLACE INTO library_material_origins VALUES (?, ?, ?, ?, ?)",
                  (lib_uuid, origin_file, origin_name_in_src, origin_uuid_in_src, current_time))
        conn.commit()
    except sqlite3.Error as e_db_origin: print(f"DB ERROR origin for {lib_uuid[:8]}: {e_db_origin}", file=sys.stderr)
    except Exception as e_gen: print(f"General ERROR origin for {lib_uuid[:8]}: {e_gen}", file=sys.stderr)
    finally:
        if conn: 
            try: conn.close() 
            except Exception: pass

def main_merge_library(args): # Same as before, with packing enhancement
    print(f"[BG Worker - Merge Op] Start. Transfer='{os.path.basename(args.transfer)}', Target='{os.path.basename(args.target)}', DB='{args.db}'", file=sys.stderr)
    target_materials_data = {}
    transfer_materials_data = {}
    transfer_file_abs = os.path.abspath(args.transfer)
    target_file_abs = os.path.abspath(args.target)
    db_path = os.path.abspath(args.db) if args.db and os.path.exists(args.db) else None

    if os.path.exists(target_file_abs):
        _, target_materials_data = _load_and_process_blend_file(target_file_abs, is_target_file=True)
    else: # Create dir for new library if it doesn't exist
        try: os.makedirs(os.path.dirname(target_file_abs), exist_ok=True)
        except Exception as e_mkdir: print(f"[BG Merge - WORKER] Warning: Could not create dir for new target library: {e_mkdir}", file=sys.stderr)

    if os.path.exists(transfer_file_abs):
        _, transfer_materials_data = _load_and_process_blend_file(transfer_file_abs, is_target_file=False)
        if not transfer_materials_data:
            print(f"[BG Merge - WORKER] No materials from transfer file '{transfer_file_abs}'.", file=sys.stderr)
            if not target_materials_data: return 0 # Nothing to do
    else:
        print(f"[BG Merge - WORKER] Transfer file '{transfer_file_abs}' not found.", file=sys.stderr)
        return 1

    final_materials_to_write_map = {u: data['mat_obj'] for u, data in target_materials_data.items()}
    mats_added, mats_updated, mats_skipped = 0, 0, 0

    for t_uuid, t_data in transfer_materials_data.items():
        t_mat, t_hash = t_data['mat_obj'], t_data['hash']
        if not t_hash: mats_skipped += 1; continue
        origin_file = t_mat.get("ml_origin_blend_file", "Unknown")
        origin_name = t_mat.get("ml_origin_mat_name", "Unknown")
        origin_uuid = t_mat.get("ml_origin_mat_uuid", "Unknown")
        
        existing_target = target_materials_data.get(t_uuid)
        if not existing_target:
            final_materials_to_write_map[t_uuid] = t_mat; mats_added += 1
            if db_path: update_material_timestamp_in_db(db_path, t_uuid); _worker_record_library_material_origin(db_path, t_uuid, origin_file, origin_name, origin_uuid)
        elif t_hash != existing_target['hash']:
            final_materials_to_write_map[t_uuid] = t_mat; mats_updated += 1
            if db_path: update_material_timestamp_in_db(db_path, t_uuid); _worker_record_library_material_origin(db_path, t_uuid, origin_file, origin_name, origin_uuid)
        else: # Hash is same, only update origin if necessary
             if db_path: _worker_record_library_material_origin(db_path, t_uuid, origin_file, origin_name, origin_uuid, check_existing=True)

    final_set_for_bpy_write = set()
    for lib_uuid, mat_obj in final_materials_to_write_map.items():
        if mat_obj and mat_obj.name in bpy.data.materials and bpy.data.materials[mat_obj.name] == mat_obj:
            try:
                if mat_obj.name != lib_uuid: mat_obj.name = lib_uuid # Ensure datablock name is UUID
                mat_obj.use_fake_user = True
                final_set_for_bpy_write.add(mat_obj)
            except Exception as e_prep: print(f"Error prepping final mat {lib_uuid[:8]}: {e_prep}", file=sys.stderr)
    
    # --- Image Packing Step for Merged Library (as per original __init__ logic) ---
    # This makes the library self-contained by packing any external images FROM THE TRANSFER FILE
    # that are now part of the materials being written to the library.
    packed_in_merge = 0
    for mat_final in final_set_for_bpy_write:
        if mat_final.use_nodes and mat_final.node_tree:
            for node in mat_final.node_tree.nodes:
                if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                    img = node.image
                    if img.packed_file is None and img.source == 'FILE' and img.filepath_raw:
                        try:
                            abs_path = bpy.path.abspath(img.filepath_raw) # Resolve relative to transfer context
                            if os.path.exists(abs_path):
                                img.pack()
                                packed_in_merge +=1
                                print(f"  Packed image '{img.name}' for material '{mat_final.name}' during merge.", file=sys.stderr)
                        except Exception as e_pack_merge:
                            print(f"  Failed to pack image '{img.name}' for '{mat_final.name}' during merge: {e_pack_merge}", file=sys.stderr)
    if packed_in_merge > 0: print(f"[BG Merge - WORKER] Packed {packed_in_merge} images into library materials.", file=sys.stderr)
    # --- End Image Packing Step ---

    temp_lib_output_path = None
    try:
        write_dir = os.path.dirname(target_file_abs); os.makedirs(write_dir, exist_ok=True)
        fd, temp_lib_output_path = tempfile.mkstemp(suffix='.blend', prefix=f"{os.path.splitext(os.path.basename(target_file_abs))[0]}_MERGETEMP_", dir=write_dir)
        os.close(fd)
        
        bpy.data.libraries.write(temp_lib_output_path, final_set_for_bpy_write, fake_user=True, compress=True)
        shutil.move(temp_lib_output_path, target_file_abs)
        temp_lib_output_path = None # Prevent deletion in finally if move succeeded
        print(f"[BG Merge - WORKER Summary] Added: {mats_added}, Updated: {mats_updated}, Skipped: {mats_skipped}", file=sys.stderr)
        return 0
    except Exception as write_err:
        print(f"[BG Merge - WORKER] CRITICAL ERROR writing library: {write_err}", file=sys.stderr); traceback.print_exc(file=sys.stderr)
        return 1
    finally:
        if temp_lib_output_path and os.path.exists(temp_lib_output_path):
            try: os.remove(temp_lib_output_path)
            except Exception as e_clean: print(f"Error cleaning temp merge file: {e_clean}", file=sys.stderr)
# --- End Library Merging ---

# --- NEW Texture Packing Operation Helper Functions (Implementations from Second Script) ---
def _make_material_local_if_from_library(material_name_in_current_blend, central_library_filepath_abs):
    """
    If material_name_in_current_blend is linked from central_library_filepath_abs,
    it makes the material local directly using .make_local(), assigns it a new UUID,
    and returns (the_now_local_material, True).
    Returns (original_material, False) if already local or linked from a different library.
    Returns (None, False) on error or if material not found.
    """
    mat_to_process = bpy.data.materials.get(material_name_in_current_blend)
    was_localized_in_this_call = False

    if not mat_to_process:
        print(f"    [Worker _make_local_v4] Material '{material_name_in_current_blend}' not found.", file=sys.stderr)
        return None, was_localized_in_this_call

    if mat_to_process.library:
        try:
            linked_lib_path_abs = ""
            if mat_to_process.library.filepath:
                linked_lib_path_abs = os.path.normpath(bpy.path.abspath(mat_to_process.library.filepath))
            else:
                print(f"    [Worker _make_local_v4] Mat '{mat_to_process.name}' is linked but lib filepath empty. Treating as non-central.", file=sys.stderr)
                return mat_to_process, was_localized_in_this_call

            central_lib_norm = os.path.normpath(central_library_filepath_abs)

            if linked_lib_path_abs == central_lib_norm:
                print(f"    [Worker _make_local_v4] Mat '{mat_to_process.name}' (UUID prop: {mat_to_process.get('uuid', 'N/A')}) is from target central library. Making local.", file=sys.stderr)
                
                original_library_material_uuid = mat_to_process.get("uuid", None)
                original_name_for_log = mat_to_process.name_full

                if hasattr(mat_to_process, 'make_local'):
                    mat_to_process.make_local() # Modifies mat_to_process in-place.
                    was_localized_in_this_call = True 
                    
                    print(f"    [Worker _make_local_v4] Mat '{original_name_for_log}' made local. Current name: '{mat_to_process.name_full}'.", file=sys.stderr)

                    new_local_material_uuid = str(uuid.uuid4())
                    try:
                        mat_to_process["uuid"] = new_local_material_uuid
                    except Exception as e_set_uuid:
                         print(f"    [Worker _make_local_v4] WARNING: Could not set new UUID on '{mat_to_process.name}': {e_set_uuid}", file=sys.stderr)
                    
                    if original_library_material_uuid:
                        try:
                            mat_to_process["source_library_uuid"] = original_library_material_uuid
                        except Exception as e_set_src_uuid:
                            print(f"    [Worker _make_local_v4] WARNING: Could not set source_library_uuid on '{mat_to_process.name}': {e_set_src_uuid}", file=sys.stderr)

                    print(f"    [Worker _make_local_v4] Assigned new UUID '{new_local_material_uuid}' to now-local mat '{mat_to_process.name}'. Original lib UUID: '{original_library_material_uuid}'.", file=sys.stderr)
                    return mat_to_process, was_localized_in_this_call
                else:
                    print(f"    [Worker _make_local_v4] ERROR: Mat '{mat_to_process.name}' no .make_local() method.", file=sys.stderr)
                    return mat_to_process, was_localized_in_this_call
            else:
                return mat_to_process, was_localized_in_this_call
        except AttributeError as ae:
            print(f"    [Worker _make_local_v4] AttributeError for '{mat_to_process.name}': {ae}. Passing through.", file=sys.stderr)
            return mat_to_process, was_localized_in_this_call
        except Exception as e:
            print(f"    [Worker _make_local_v4] Error for '{mat_to_process.name}': {e}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
            return mat_to_process, was_localized_in_this_call
    
    return mat_to_process, was_localized_in_this_call

def _handle_texture_packing_external(material, base_blend_filepath, external_dir_name_rel):
    if not material or not material.use_nodes or not material.node_tree: return 0, 0
    unpacked_c, error_c = 0,0
    proj_dir_abs = os.path.dirname(base_blend_filepath)
    ext_dir_name_clean = os.path.basename(external_dir_name_rel) # Ensure it's just a name
    tex_subfolder_abs = os.path.join(proj_dir_abs, ext_dir_name_clean, "textures")
    base_rel_path_blend = f"//{ext_dir_name_clean}/textures/" # Blender relative path base
    
    processed_imgs_mat = set()
    for node in material.node_tree.nodes:
        if node.bl_idname == 'ShaderNodeTexImage' and node.image:
            img = node.image
            if img.name_full in processed_imgs_mat: continue # Use name_full for datablock instance uniqueness
            processed_imgs_mat.add(img.name_full)

            if img.packed_file:
                orig_img_name = img.name_full # Usually includes extension if from file
                base, ext = os.path.splitext(orig_img_name)
                if not ext or ext.lower() not in ['.png','.jpg','.jpeg','.tga','.tiff','.exr','.hdr']:
                    ext = f".{img.file_format.lower() if img.file_format else 'png'}" # Default if no ext
                
                clean_base = "".join(c if c.isalnum() or c in '_-' else '_' for c in base)
                disk_fname = f"{clean_base}{ext}"
                try: os.makedirs(tex_subfolder_abs, exist_ok=True)
                except Exception as e: print(f"Error mkdir {tex_subfolder_abs}: {e}", file=sys.stderr); error_c+=1; continue
                
                abs_disk_path = os.path.join(tex_subfolder_abs, disk_fname)
                count = 0
                while os.path.exists(abs_disk_path): # Ensure unique filename on disk
                    count+=1; disk_fname = f"{clean_base}.{count:03d}{ext}"; abs_disk_path = os.path.join(tex_subfolder_abs, disk_fname)
                
                rel_blend_path = f"{base_rel_path_blend}{disk_fname}"
                print(f"    Unpacking '{img.name}' to '{abs_disk_path}'. New Blender path: '{rel_blend_path}'", file=sys.stderr)
                try:
                    # Crucial: image.unpack needs a filepath set if using WRITE_ORIGINAL without 'id' param.
                    # Or, save manually. Using unpack with specific ID is often tricky.
                    # Let's save manually for full control.
                    with open(abs_disk_path, 'wb') as f: f.write(img.packed_file.data)
                    img.filepath = rel_blend_path
                    img.source = 'FILE'
                    # img.packed_file = None # This should happen implicitly when source is FILE and filepath is set
                    img.reload() # Important to reflect change
                    unpacked_c+=1
                except Exception as e:
                    print(f"Error unpacking/repathing '{img.name}': {e}", file=sys.stderr); traceback.print_exc(file=sys.stderr)
                    if os.path.exists(abs_disk_path): 
                        try: os.remove(abs_disk_path) 
                        except Exception: pass # Clean up failed write
                    error_c+=1
    return unpacked_c, error_c

def _handle_texture_packing_internal(material):
    if not material or not material.use_nodes or not material.node_tree: return 0,0
    packed_c, error_c = 0,0
    processed_imgs_mat = set()
    for node in material.node_tree.nodes:
        if node.bl_idname == 'ShaderNodeTexImage' and node.image:
            img = node.image
            if img.name_full in processed_imgs_mat: continue
            processed_imgs_mat.add(img.name_full)

            if img.source == 'FILE' and img.packed_file is None:
                abs_path = ""
                if img.filepath_raw:
                    try: abs_path = bpy.path.abspath(img.filepath_raw) # Resolve relative to current .blend
                    except Exception as e: print(f"Error abspath for '{img.name}': {e}", file=sys.stderr); error_c+=1; continue
                
                if not abs_path or not os.path.isfile(abs_path): # Check isfile too
                    print(f"External tex for '{img.name}' not found at '{abs_path}'. Cannot pack.", file=sys.stderr); error_c+=1; continue
                
                print(f"    Packing '{img.name}' from '{abs_path}'", file=sys.stderr)
                try:
                    # Ensure filepath is correct before packing if it relied on filepath_raw
                    if img.filepath != abs_path : img.filepath = abs_path
                    img.pack()
                    packed_c+=1
                except RuntimeError as e: print(f"Error packing '{img.name}': {e}", file=sys.stderr); error_c+=1
                except Exception as e_other: print(f"Unexpected error packing '{img.name}': {e_other}", file=sys.stderr); traceback.print_exc(file=sys.stderr); error_c+=1
    return packed_c, error_c
# --- End NEW Texture Packing Helpers ---

def calculate_image_pixel_hash(blender_image_object):
    """
    Calculates a hash for a Blender image's pixel data by saving it temporarily to PNG format.
    Returns MD5 hex digest or a string indicating error/no data.
    """
    if not blender_image_object:
        print(f"    [PackExternal - HashCalc] Received None image object.", file=sys.stderr)
        return "ERROR_NONE_IMAGE_OBJECT"

    if blender_image_object.size[0] == 0 or blender_image_object.size[1] == 0 or not blender_image_object.has_data:
        no_data_hash_val = f"NO_DATA_FOR_IMAGE_{''.join(filter(str.isalnum, blender_image_object.name_full[:30]))}"
        print(f"    [PackExternal - HashCalc] Image '{blender_image_object.name_full}' has no data or zero dimensions. Hash: {no_data_hash_val}", file=sys.stderr)
        return no_data_hash_val

    temp_img_copy = None
    temp_dir_for_hash = tempfile.mkdtemp(prefix="bml_hash_temp_")
    sanitized_img_name_part = "".join(c if c.isalnum() else '_' for c in blender_image_object.name_full[:40])
    temp_filepath_for_hash = os.path.join(temp_dir_for_hash, f"temp_hash_{sanitized_img_name_part}.png")

    try:
        temp_img_copy = blender_image_object.copy()
        if not temp_img_copy:
            raise RuntimeError(f"Image.copy() failed for '{blender_image_object.name_full}'.")
        
        temp_img_copy.name = f"__{blender_image_object.name_full[:50]}_temp_hash_copy"
        temp_img_copy.filepath_raw = temp_filepath_for_hash 
        temp_img_copy.file_format = 'PNG'
        
        temp_img_copy.save_render(filepath=temp_filepath_for_hash)

        hasher = hashlib.md5()
        with open(temp_filepath_for_hash, 'rb') as f_hash:
            while True:
                data_chunk = f_hash.read(65536)
                if not data_chunk:
                    break
                hasher.update(data_chunk)
        hex_digest = hasher.hexdigest()
        return hex_digest

    except Exception as e_hash_calc:
        print(f"    [PackExternal - HashCalc] ERROR calculating pixel hash for '{blender_image_object.name_full}': {type(e_hash_calc).__name__} - {e_hash_calc}", file=sys.stderr)
        return f"ERROR_HASH_CALC_{''.join(filter(str.isalnum, blender_image_object.name_full[:30]))}"
    finally:
        if temp_img_copy and temp_img_copy.name in bpy.data.images: # Check if it exists before removal
            try:
                temp_img_copy.user_clear()
                bpy.data.images.remove(temp_img_copy, do_unlink=True)
            except Exception: # Ignore errors during cleanup of temp object
                pass 
        if os.path.exists(temp_dir_for_hash): # Check existence before rmtree
            shutil.rmtree(temp_dir_for_hash, ignore_errors=True)

def hash_file_on_disk(filepath_on_disk):
    """Calculates MD5 hash of a file already on disk."""
    hasher = hashlib.md5()
    try:
        with open(filepath_on_disk, 'rb') as f_disk_hash:
            while True:
                data_chunk = f_disk_hash.read(65536) 
                if not data_chunk:
                    break
                hasher.update(data_chunk)
        return hasher.hexdigest()
    except IOError as e_io_hash:
        print(f"    [PackExternal - DiskHash] ERROR reading file for hashing '{filepath_on_disk}': {e_io_hash}", file=sys.stderr)
        return None

def derive_sensible_filename_elements(blender_image_object):
    """
    Derives a sanitized base filename and an extension string (e.g., '.png') for saving a Blender image.
    """
    base_name_candidate = ""
    file_extension_candidate = ""

    if blender_image_object.filepath_raw: # Don't check source, filepath_raw might have original name even if packed/generated
        try:
            path_basename = os.path.basename(blender_image_object.filepath_raw)
            name_part, ext_part = os.path.splitext(path_basename)
            if name_part:
                base_name_candidate = name_part
            if ext_part and len(ext_part) > 1 and ext_part.startswith('.'):
                file_extension_candidate = ext_part.lower()
        except Exception:
            pass

    if not base_name_candidate:
        base_name_candidate = blender_image_object.name
    
    img_format = blender_image_object.file_format # Check current format first
    if not file_extension_candidate: # If extension couldn't be derived from filepath_raw
        if img_format == 'JPEG': file_extension_candidate = '.jpg'
        elif img_format == 'TARGA': file_extension_candidate = '.tga'
        elif img_format == 'BMP': file_extension_candidate = '.bmp'
        elif img_format == 'OPEN_EXR': file_extension_candidate = '.exr'
        elif img_format == 'PNG': file_extension_candidate = '.png'
        # Add other common Blender formats if needed: TIFF, IRIS, JP2, HDR, CINEON, DPX
        elif img_format == 'TIFF': file_extension_candidate = '.tif'
        elif img_format == 'IRIS': file_extension_candidate = '.sgi' # or .rgb
        elif img_format == 'JPEG2000': file_extension_candidate = '.jp2'
        elif img_format == 'HDR': file_extension_candidate = '.hdr'
        # Default to .png if still no extension or unknown format string
        else: file_extension_candidate = '.png'
    
    # Ensure common extensions are used
    if file_extension_candidate == '.jpeg': file_extension_candidate = '.jpg'
    if file_extension_candidate == '.tiff': file_extension_candidate = '.tif'


    sanitized_base = re.sub(r'[^\w\d_-]+', '_', base_name_candidate)
    sanitized_base = sanitized_base.strip('_')
    if not sanitized_base:
        sanitized_base = f"image_export_{str(uuid.uuid4())[:8]}"

    return sanitized_base, file_extension_candidate

def main_process_pack_external(args):
    print(f"[BG Worker - PackExternal V2.3] START Processing file: {bpy.data.filepath}", file=sys.stderr) # Version updated
    sys.stderr.flush()
    if not args.library_file or not args.external_dir_name:
        print(f"[BG Worker - PackExternal V2.3] ERROR: --library-file and --external-dir_name arguments are required.", file=sys.stderr)
        return 1
        
    print(f"  Central Library File Path (for ID): {args.library_file}", file=sys.stderr)
    print(f"  Raw External Directory Arg Received: '{args.external_dir_name}'", file=sys.stderr)

    if not bpy.data.filepath:
        print(f"[BG Worker - PackExternal V2.3] ERROR: No .blend file seems to be loaded.", file=sys.stderr)
        return 1

    # --- Path Setup ---
    # This logic assumes args.external_dir_name is either a valid absolute path
    # or a path starting with '//' (relative to the .blend file being processed).
    raw_user_path_input = args.external_dir_name 
    current_blend_file_abs_dir = os.path.dirname(bpy.data.filepath)

    texture_output_dir_absolute = "" # This will be the absolute disk path for saving files
    blender_path_prefix_for_images = ""  # This will be the root path stored in image.filepath

    if raw_user_path_input.startswith('//'):
        # User provided a path relative to the current blend file (e.g., //my_textures/)
        # bpy.path.abspath() correctly resolves this relative to bpy.data.filepath
        texture_output_dir_absolute = bpy.path.abspath(raw_user_path_input) 
        blender_path_prefix_for_images = raw_user_path_input.replace(os.sep, '/')
        if not blender_path_prefix_for_images.endswith('/'):
            blender_path_prefix_for_images += '/'
    else:
        # Assumes raw_user_path_input is a valid absolute path string from the UI
        # (after the fix in __init__.py to stop mangling it).
        texture_output_dir_absolute = os.path.normpath(raw_user_path_input)

        # Determine the path to store in Blender for images based on the resolved absolute disk path.
        # Prefer a relative path (//) if the output directory is within the project structure.
        try:
            rel_path_from_blend = os.path.relpath(texture_output_dir_absolute, current_blend_file_abs_dir)
            # Check if it's a simple relative path (not going up with '..' or just '.')
            if not rel_path_from_blend.startswith('..') and rel_path_from_blend != '.':
                blender_path_prefix_for_images = f"//{rel_path_from_blend.replace(os.sep, '/')}"
            else: # Not easily relative (e.g., different drive, or parent directory) -> store absolute path
                blender_path_prefix_for_images = texture_output_dir_absolute.replace(os.sep, '/')
        except ValueError: # Handles cases like different drives on Windows where relpath fails
            blender_path_prefix_for_images = texture_output_dir_absolute.replace(os.sep, '/')
    
    # Ensure the Blender path prefix ends with a slash for easy concatenation later
    if not blender_path_prefix_for_images.endswith('/'):
        blender_path_prefix_for_images += '/'
    
    # Ensure the absolute disk directory for saving textures exists
    try:
        os.makedirs(texture_output_dir_absolute, exist_ok=True)
        print(f"  Actual disk save directory for textures: {texture_output_dir_absolute}", file=sys.stderr)
        print(f"  Blender image filepath prefix will be: {blender_path_prefix_for_images}", file=sys.stderr)
    except Exception as e_mkdir:
        print(f"[BG Worker - PackExternal V2.3] CRITICAL ERROR: Could not create texture output directory '{texture_output_dir_absolute}': {e_mkdir}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        return 1
    # --- End Path Setup ---
        
    all_material_names_in_file_at_start = [m.name for m in bpy.data.materials]
    any_modifications_made_to_file = False
    saved_texture_hashes_map = {} 

    for mat_name_from_initial_list in all_material_names_in_file_at_start:
        material_to_evaluate = bpy.data.materials.get(mat_name_from_initial_list)
        if not material_to_evaluate: continue

        name_as_linked_in_current_file = material_to_evaluate.name
        is_from_central_library = False
        if material_to_evaluate.library and material_to_evaluate.library.filepath:
            try:
                lib_fp_abs = os.path.normpath(bpy.path.abspath(material_to_evaluate.library.filepath))
                central_lib_fp_abs = os.path.normpath(bpy.path.abspath(args.library_file))
                if lib_fp_abs == central_lib_fp_abs:
                    is_from_central_library = True
            except Exception: pass
        
        if is_from_central_library:
            print(f"  Processing library material '{material_to_evaluate.name_full}' (orig: '{name_as_linked_in_current_file}') for external export.", file=sys.stderr)
            try:
                material_to_evaluate.make_local()
                any_modifications_made_to_file = True
                print(f"    Made material local. Now named: '{material_to_evaluate.name}'.", file=sys.stderr)
                
                if material_to_evaluate.use_nodes and material_to_evaluate.node_tree:
                    print(f"    DEBUG: Material '{material_to_evaluate.name}' uses nodes and has a node tree. Node count: {len(material_to_evaluate.node_tree.nodes)}", file=sys.stderr)
                else:
                    print(f"    DEBUG WARNING: Material '{material_to_evaluate.name}' either does not use nodes (use_nodes: {material_to_evaluate.use_nodes}) or has no node tree (node_tree is None: {material_to_evaluate.node_tree is None}) after make_local. Texture processing will be SKIPPED for this material.", file=sys.stderr)

            except RuntimeError as e_mlm:
                print(f"    FAILED to make material '{name_as_linked_in_current_file}' local: {e_mlm}. Skipping.", file=sys.stderr)
                continue

            if not material_to_evaluate.use_fake_user:
                material_to_evaluate.use_fake_user = True; any_modifications_made_to_file = True
            
            if material_to_evaluate.use_nodes and material_to_evaluate.node_tree:
                for node in material_to_evaluate.node_tree.nodes:
                    if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                        img_datablock = node.image
                        
                        if img_datablock.library:
                            try:
                                img_datablock.make_local(); any_modifications_made_to_file = True
                            except RuntimeError as e_mil:
                                print(f"      FAILED to make image datablock '{img_datablock.name}' local: {e_mil}. Skipping this image.", file=sys.stderr)
                                continue
                        
                        if not img_datablock.use_fake_user:
                            img_datablock.use_fake_user = True; any_modifications_made_to_file = True
                        
                        current_pixel_hash = calculate_image_pixel_hash(img_datablock)
                        if current_pixel_hash is None or "ERROR" in current_pixel_hash or "NO_DATA" in current_pixel_hash :
                            print(f"      SKIPPING image '{img_datablock.name_full}' due to hash error/no data: {current_pixel_hash}.", file=sys.stderr)
                            continue

                        if current_pixel_hash in saved_texture_hashes_map:
                            existing_blender_path = saved_texture_hashes_map[current_pixel_hash]
                            if img_datablock.filepath != existing_blender_path or img_datablock.source != 'FILE' or img_datablock.packed_file is not None:
                                img_datablock.filepath = existing_blender_path
                                img_datablock.source = 'FILE'
                                if img_datablock.packed_file: 
                                    try: img_datablock.unpack(method='REMOVE')
                                    except RuntimeError: pass 
                                img_datablock.reload(); any_modifications_made_to_file = True
                            continue

                        base_name_for_disk, ext_for_disk = derive_sensible_filename_elements(img_datablock)
                        original_img_file_format = img_datablock.file_format 
                        
                        if ext_for_disk == '.png': img_datablock.file_format = 'PNG'
                        elif ext_for_disk in ['.jpg', '.jpeg']: img_datablock.file_format = 'JPEG'
                        elif ext_for_disk == '.tga': img_datablock.file_format = 'TARGA'
                        elif ext_for_disk == '.bmp': img_datablock.file_format = 'BMP'
                        elif ext_for_disk == '.exr': img_datablock.file_format = 'OPEN_EXR'
                        elif ext_for_disk == '.tif': img_datablock.file_format = 'TIFF'
                        else: img_datablock.file_format = 'PNG'; ext_for_disk = '.png'

                        suffix_count = 0
                        while True:
                            disk_filename_to_try = f"{base_name_for_disk}{f'.{suffix_count:03d}' if suffix_count > 0 else ''}{ext_for_disk}"
                            absolute_save_path_on_disk = os.path.join(texture_output_dir_absolute, disk_filename_to_try)
                            blender_filepath_to_store = blender_path_prefix_for_images + disk_filename_to_try 
                            
                            if not os.path.exists(absolute_save_path_on_disk):
                                try:
                                    print(f"      Saving '{img_datablock.name_full}' (hash: {current_pixel_hash}) to disk: '{absolute_save_path_on_disk}'. Blender path: '{blender_filepath_to_store}'", file=sys.stderr)
                                    img_datablock.save_render(filepath=absolute_save_path_on_disk)
                                    
                                    img_datablock.source = 'FILE'
                                    img_datablock.filepath = blender_filepath_to_store
                                    if img_datablock.packed_file: img_datablock.unpack(method='REMOVE')
                                    img_datablock.reload()
                                    saved_texture_hashes_map[current_pixel_hash] = blender_filepath_to_store
                                    any_modifications_made_to_file = True
                                    break 
                                except Exception as e_sr:
                                    print(f"      ERROR saving image '{img_datablock.name_full}' to '{absolute_save_path_on_disk}': {e_sr}", file=sys.stderr)
                                    img_datablock.file_format = original_img_file_format 
                                    break 
                            else: 
                                hash_of_disk_file = hash_file_on_disk(absolute_save_path_on_disk)
                                if hash_of_disk_file == current_pixel_hash:
                                    if img_datablock.filepath != blender_filepath_to_store or img_datablock.source != 'FILE' or img_datablock.packed_file:
                                        img_datablock.source = 'FILE'
                                        img_datablock.filepath = blender_filepath_to_store
                                        if img_datablock.packed_file: img_datablock.unpack(method='REMOVE')
                                        img_datablock.reload(); any_modifications_made_to_file = True
                                    saved_texture_hashes_map[current_pixel_hash] = blender_filepath_to_store
                                    break
                                else:
                                    suffix_count += 1
                                    if suffix_count > 999:
                                        print(f"      ERROR: Exceeded 999 suffixes for '{base_name_for_disk}'. Skipping save for '{img_datablock.name_full}'.", file=sys.stderr)
                                        img_datablock.file_format = original_img_file_format 
                                        break
            # No renaming of material

    if any_modifications_made_to_file:
        print(f"[BG Worker - PackExternal V2.3] Modifications detected. Saving .blend file: {bpy.data.filepath}", file=sys.stderr)
        try:
            bpy.ops.wm.save_mainfile()
            print(f"  .blend file save successful.", file=sys.stderr)
        except Exception as e_save_b:
            print(f"  CRITICAL ERROR saving .blend file {bpy.data.filepath}: {e_save_b}", file=sys.stderr); traceback.print_exc(file=sys.stderr)
            return 1
    else:
        print(f"[BG Worker - PackExternal V2.3] No modifications requiring .blend file save.", file=sys.stderr)
    
    sys.stderr.flush()
    print(f"[BG Worker - PackExternal V2.3] FINISHED processing file '{bpy.data.filepath}'.", file=sys.stderr)
    return 0

def main_process_pack_internal(args):
    print(f"[BG Worker - PackInternal] START Processing file: {bpy.data.filepath}", file=sys.stderr)
    sys.stderr.flush()
    print(f"  Central Library File Path (for identifying materials to make local): {args.library_file}", file=sys.stderr)
    sys.stderr.flush()

    if not bpy.data.filepath:
        print(f"[BG Worker - PackInternal] ERROR: No .blend file seems to be loaded by Blender's -b argument.", file=sys.stderr)
        sys.stderr.flush()
        return 1

    all_material_names_in_file_at_start = [m.name for m in bpy.data.materials]
    
    any_modifications_made_to_file = False

    for mat_name_from_initial_list in all_material_names_in_file_at_start:
        material_to_evaluate = bpy.data.materials.get(mat_name_from_initial_list)

        if not material_to_evaluate:
            print(f"  [PackInternal] Material '{mat_name_from_initial_list}' not found by this name at this stage. It might have been processed and renamed. Skipping.", file=sys.stderr)
            continue

        name_as_linked_in_current_file = material_to_evaluate.name 
        
        is_from_central_library = False
        if material_to_evaluate.library and material_to_evaluate.library.filepath:
            try:
                linked_lib_path_abs = os.path.normpath(bpy.path.abspath(material_to_evaluate.library.filepath))
                central_lib_path_abs_norm = os.path.normpath(bpy.path.abspath(args.library_file))
                if linked_lib_path_abs == central_lib_path_abs_norm:
                    is_from_central_library = True
            except Exception as e_lib_check:
                print(f"    [PackInternal] Error during library path check for material '{material_to_evaluate.name}': {e_lib_check}", file=sys.stderr)
        
        if is_from_central_library:
            print(f"  [PackInternal] Processing library material '{material_to_evaluate.name_full}' (original linked name: '{name_as_linked_in_current_file}').", file=sys.stderr)

            try:
                material_to_evaluate.make_local() 
                any_modifications_made_to_file = True
                name_after_make_local = material_to_evaluate.name 
                print(f"    Step 1: Made material '{name_as_linked_in_current_file}' local. It is now named '{name_after_make_local}'.", file=sys.stderr)
            except RuntimeError as e_make_local_mat:
                print(f"    Step 1 FAILED: Could not make material '{name_as_linked_in_current_file}' local: {e_make_local_mat}. Skipping this material.", file=sys.stderr)
                continue 

            try:
                if not material_to_evaluate.use_fake_user:
                    material_to_evaluate.use_fake_user = True
                    any_modifications_made_to_file = True 
                print(f"    Step 2: Ensured fake_user is set for material '{material_to_evaluate.name}'.", file=sys.stderr)
            except Exception as e_fake_user_mat:
                print(f"    Step 2 FAILED: Could not set fake_user for material '{material_to_evaluate.name}': {e_fake_user_mat}.", file=sys.stderr)

            print(f"    Step 3: Processing textures for material '{material_to_evaluate.name}'.", file=sys.stderr)
            if material_to_evaluate.use_nodes and material_to_evaluate.node_tree:
                for node in material_to_evaluate.node_tree.nodes:
                    if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                        image_datablock = node.image
                        image_name_for_log = image_datablock.name_full 

                        image_was_made_local_in_this_step = False
                        if image_datablock.library: 
                            original_image_name_before_local = image_datablock.name
                            print(f"      Found linked image data-block: '{image_name_for_log}' from library: '{image_datablock.library.filepath}'.", file=sys.stderr)
                            try:
                                image_datablock.make_local() 
                                image_was_made_local_in_this_step = True
                                any_modifications_made_to_file = True
                                print(f"        Made image data-block '{original_image_name_before_local}' (now '{image_datablock.name}') local.", file=sys.stderr)
                            except RuntimeError as e_make_local_img:
                                print(f"        FAILED to make image data-block '{original_image_name_before_local}' local: {e_make_local_img}.", file=sys.stderr)
                        
                        if not image_datablock.library: 
                            try:
                                if not image_datablock.use_fake_user:
                                    image_datablock.use_fake_user = True
                                    any_modifications_made_to_file = True
                                    print(f"        Ensured fake_user is set for image data-block '{image_datablock.name}'.", file=sys.stderr)
                                elif image_was_made_local_in_this_step: 
                                     print(f"        Image data-block '{image_datablock.name}' (just made local) already had fake_user set.", file=sys.stderr)
                            except Exception as e_fake_user_img:
                                print(f"        FAILED to set fake_user for image data-block '{image_datablock.name}': {e_fake_user_img}.", file=sys.stderr)
            
            # Step 4 (Renaming) has been removed as per user request.
            # The material will keep the name it has after being made local (e.g., 'MaterialName.001').
            print(f"    Step 4 (Renaming) skipped. Material will keep its current name: '{material_to_evaluate.name}'.", file=sys.stderr)
        
    if any_modifications_made_to_file:
        print(f"[BG Worker - PackInternal] Modifications detected. Saving file: {bpy.data.filepath}", file=sys.stderr)
        sys.stderr.flush()
        try:
            bpy.ops.wm.save_mainfile()
            print(f"  Save successful. File '{bpy.data.filepath}' updated for self-sufficiency.", file=sys.stderr)
        except Exception as e_save:
            print(f"  CRITICAL ERROR saving file {bpy.data.filepath}: {e_save}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
            return 1 
    else:
        print(f"[BG Worker - PackInternal] No library materials processed or no modifications made that required saving in '{bpy.data.filepath}'. No save performed by worker.", file=sys.stderr)
    
    sys.stderr.flush()
    print(f"[BG Worker - PackInternal] FINISHED processing file '{bpy.data.filepath}'.", file=sys.stderr)
    sys.stderr.flush()
    return 0

# --- Main Entry Point for the Worker Script ---
def main_worker_entry():
    print(f"[BG Worker - Entry] Worker started. Full argv: {sys.argv}", file=sys.stderr)
    time.sleep(0.2) # Brief pause
    print(f"[BG Worker - Entry] Current .blend file context (loaded by -b): {bpy.data.filepath if bpy.data.filepath else 'Unsaved/None'}", file=sys.stderr)
    sys.stderr.flush()

    parser = argparse.ArgumentParser(description="Background worker for MaterialList Addon.")
    parser.add_argument("--operation", 
                        choices=['merge_library', 'render_thumbnail', 
                                 'pack_to_external', 'pack_to_internal'], # Added new choices
                        required=True,
                        help="The operation to perform.")

    # Args for 'merge_library'
    parser.add_argument("--transfer", help="Path to the transfer .blend file (for merge_library).")
    parser.add_argument("--target", help="Path to the target (main) library .blend file (for merge_library).")
    parser.add_argument("--db", help="Path to the addon's SQLite database file (for merge_library timestamps).")

    # Args for 'render_thumbnail'
    parser.add_argument("--tasks-json", help="JSON string detailing a batch of thumbnail tasks.")
    parser.add_argument("--addon-data-root", help="Path to the addon's main data directory (for icon_template.blend).")
    parser.add_argument("--thumbnail-size", type=int, help="Target size for thumbnails.")

    # Args for 'pack_to_external' and 'pack_to_internal'
    # Note: --target-blend-file is implicitly handled by Blender's -b <file> argument
    # We still add it for clarity in arg parsing if needed, but it's the one bpy.data.filepath refers to.
    # parser.add_argument("--target-blend-file", help="Path to the .blend file to be processed (for packing ops).") # Redundant if -b is used
    parser.add_argument("--library-file", help="Path to the central material_library.blend (for identifying lib materials).")
    parser.add_argument("--external-dir-name", help="Directory name for unpacking external textures (for pack_to_external).")
    
    try:
        # Get arguments after '--'
        app_args = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else sys.argv[1:]
    except ValueError:
        app_args = sys.argv[1:] # Fallback if '--' is missing
        print(f"[BG Worker - Entry] Warning: '--' separator not found in sys.argv. Parsing from sys.argv[1:].", file=sys.stderr)

    if not app_args:
        print(f"[BG Worker - Entry] No arguments provided to worker after '--' (or at all). Exiting.", file=sys.stderr)
        parser.print_help(sys.stderr)
        return 1 # Error: No arguments

    args = parser.parse_args(app_args)

    if args.operation == 'merge_library':
        if not all([args.transfer, args.target]): # --db is optional for the operation itself
            parser.error("--transfer and --target arguments are required for 'merge_library' operation.")
            # parser.error exits with code 2
        return main_merge_library(args)
    elif args.operation == 'render_thumbnail':
        if not args.tasks_json:
            parser.error("--tasks-json argument is required for 'render_thumbnail' operation.")
        if not all([args.addon_data_root, args.thumbnail_size is not None]):
             parser.error("--addon-data-root and --thumbnail-size are required with --tasks-json for 'render_thumbnail'.")
        return main_render_thumbnail_batch(args)
    elif args.operation == 'pack_to_external': # New operation
        if not args.external_dir_name or not args.library_file:
            # Note: target_blend_file is assumed to be loaded by Blender via `-b`
            parser.error("--external-dir-name and --library-file are required for 'pack_to_external'.")
        return main_process_pack_external(args)
    elif args.operation == 'pack_to_internal': # New operation
        if not args.library_file:
            # Note: target_blend_file is assumed to be loaded by Blender via `-b`
            parser.error("--library-file is required for 'pack_to_internal'.")
        return main_process_pack_internal(args)
    else:
        # This case should ideally not be reached due to 'choices' in parser
        print(f"[BG Worker - Entry] Unknown operation specified: {args.operation}", file=sys.stderr)
        return 1 # General error

if __name__ == "__main__":
    final_exit_code = 1 # Default to error
    try:
        final_exit_code = main_worker_entry()
    except SystemExit as e_sysexit: # Catches parser.error() which raises SystemExit
        final_exit_code = e_sysexit.code if isinstance(e_sysexit.code, int) else 1 # Use exit code from SystemExit
        if final_exit_code != 0: # Argparse usually prints its own error message to stderr
            print(f"[BG Worker - __main__] Argparse SystemExit with code: {final_exit_code}.", file=sys.stderr)
    except Exception as e_global_worker:
        print(f"[BG Worker - __main__] === Unhandled Global Exception in Worker === ", file=sys.stderr)
        print(f"Error Type: {type(e_global_worker).__name__}", file=sys.stderr)
        print(f"Error Message: {e_global_worker}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        final_exit_code = 3 # Different code for unhandled exceptions in worker's main
    finally:
        print(f"[BG Worker - __main__] Worker process exiting with code: {final_exit_code}", file=sys.stderr)
        sys.stderr.flush() # Ensure all error logs are written
        sys.stdout.flush() # Ensure any JSON payload is written
        bpy.ops.wm.quit_blender() # Ensure Blender quits cleanly after script execution
        sys.exit(final_exit_code)
