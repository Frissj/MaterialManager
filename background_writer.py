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
import sys

# --- Globals for Thumbnail Rendering Part (initialized by functions) ---
ICON_TEMPLATE_FILE_WORKER = None
THUMBNAIL_SIZE_WORKER = 128 # Default, overridden by arg
persistent_icon_template_scene_worker = None # Cache for loaded template scene within this worker instance

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
    if not img: return "NO_IMAGE_DATA"
    raw_path = img.filepath_raw if img.filepath_raw else ""
    try:
        abs_path = bpy.path.abspath(raw_path) if raw_path else ""
        if abs_path and os.path.exists(abs_path):
            try:
                with open(abs_path, "rb") as f: data = f.read(131072) 
                return hashlib.md5(data).hexdigest()
            except Exception as read_err:
                print(f"[_hash_image BG Warning] Could not read {abs_path}: {read_err}", file=sys.stderr)
    except Exception as path_err:
        print(f"[_hash_image BG Warning] Error during abspath for '{raw_path}': {path_err}", file=sys.stderr)
    fallback_data = f"IMAGE_NAME:{img.name}|RAW_PATH:{raw_path}|HAS_PIXELS:{img.has_data}"
    return hashlib.md5(fallback_data.encode('utf-8')).hexdigest()

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
        for _ in range(20): 
            if not current_node or current_node in visited_nodes: break
            visited_nodes.add(current_node)
            if current_node.bl_idname == 'ShaderNodeBsdfPrincipled':
                return current_node
            potential_shader_inputs = []
            if hasattr(current_node, 'inputs'):
                # Check common specific names first for efficiency
                shader_input_names = ["Shader", "Shader1", "Shader2"] # Common names for shader inputs
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
        # If traversal fails, fall back to a direct search
        return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)
    except Exception as e:
        print(f"[find_principled_bsdf BG Error] For {getattr(mat, 'name', 'N/A')}: {e}", file=sys.stderr)
        # Fallback to direct search on any error during traversal
        return next((n for n in mat.node_tree.nodes if n.bl_idname == 'ShaderNodeBsdfPrincipled'), None)

def validate_material_uuid(mat, is_copy=False): # From background_writer.py
    if mat is None: return None
    original_uuid = mat.get("uuid", "") 
    if not original_uuid or len(original_uuid) != 36 or is_copy:
        return str(uuid.uuid4())
    return original_uuid

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

def update_material_timestamp_in_db(db_path, material_uuid): # From background_writer.py
    if not db_path or not material_uuid:
        return
    conn = None
    try:
        if not os.path.exists(db_path):
            return
        conn = sqlite3.connect(db_path, timeout=10)
        c = conn.cursor()
        c.execute("CREATE TABLE IF NOT EXISTS mat_time (uuid TEXT PRIMARY KEY, ts INTEGER)")
        current_time = int(time.time())
        c.execute("INSERT OR REPLACE INTO mat_time (uuid, ts) VALUES (?, ?)", (material_uuid, current_time))
        conn.commit()
    except sqlite3.Error as db_err:
        print(f"[BG Timestamp WORKER] Database Error updating for {material_uuid}: {db_err}", file=sys.stderr)
    except Exception as e:
        print(f"[BG Timestamp WORKER] General Error updating for {material_uuid}: {e}", file=sys.stderr)
    finally:
        if conn:
            try: conn.close()
            except Exception: pass

def load_icon_template_scene_bg_worker():
    global persistent_icon_template_scene_worker, ICON_TEMPLATE_FILE_WORKER, THUMBNAIL_SIZE_WORKER
    preview_obj_name = "IconPreviewObject"
    camera_obj_name = "IconTemplateCam"
    expected_template_scene_name = "IconTemplateScene" # As created by main addon

    # Check cache first
    if persistent_icon_template_scene_worker:
        try:
            if persistent_icon_template_scene_worker.name in bpy.data.scenes and \
               bpy.data.scenes[persistent_icon_template_scene_worker.name] == persistent_icon_template_scene_worker and \
               persistent_icon_template_scene_worker.objects.get(preview_obj_name) and \
               persistent_icon_template_scene_worker.camera and \
               persistent_icon_template_scene_worker.camera.name == camera_obj_name:
                # print(f"[BG Worker - Template] Using cached template scene: {persistent_icon_template_scene_worker.name}", file=sys.stderr)
                return persistent_icon_template_scene_worker
            # Cache is invalid if checks fail
            if persistent_icon_template_scene_worker.name in bpy.data.scenes: # Try to remove stale scene from cache if it's there
                 if len(bpy.data.scenes) > 1 or bpy.context.screen.scene != persistent_icon_template_scene_worker: # Basic safety
                    try: bpy.data.scenes.remove(persistent_icon_template_scene_worker, do_unlink=True)
                    except: pass
            persistent_icon_template_scene_worker = None
        except (ReferenceError, AttributeError, Exception): # Catch more errors if scene became invalid
            persistent_icon_template_scene_worker = None

    if not ICON_TEMPLATE_FILE_WORKER or not os.path.exists(ICON_TEMPLATE_FILE_WORKER):
        print(f"[BG Worker - Template] FATAL: Icon template file not found or path not set: '{ICON_TEMPLATE_FILE_WORKER}'", file=sys.stderr)
        return None

    loaded_scene_from_blend_file = None
    # Ensure a unique name for the scene loaded in this worker instance, even if it's temporary
    worker_instance_scene_name = f"_BG_WORKER_TPL_SCENE_{str(uuid.uuid4())[:8]}"

    try:
        scene_name_to_load = expected_template_scene_name
        # Verify the scene exists in the template .blend file
        with bpy.data.libraries.load(ICON_TEMPLATE_FILE_WORKER, link=False, assets_only=False) as (data_from_lib_check, _):
            available_scenes_in_template = list(getattr(data_from_lib_check, "scenes", []))
            if not available_scenes_in_template:
                print(f"[BG Worker - Template] FATAL: No scenes found in template file '{ICON_TEMPLATE_FILE_WORKER}'.", file=sys.stderr)
                return None
            if expected_template_scene_name not in available_scenes_in_template:
                print(f"[BG Worker - Template] WARNING: Expected scene '{expected_template_scene_name}' not in template. Using first available: '{available_scenes_in_template[0]}'.", file=sys.stderr)
                scene_name_to_load = available_scenes_in_template[0]
        
        # Load the chosen scene
        with bpy.data.libraries.load(ICON_TEMPLATE_FILE_WORKER, link=False) as (data_from, data_to):
            if scene_name_to_load in data_from.scenes:
                data_to.scenes = [scene_name_to_load]
            else: # Should not happen if previous check was done
                print(f"[BG Worker - Template] FATAL: Scene '{scene_name_to_load}' was listed but could not be targeted for load.", file=sys.stderr)
                return None
        
        loaded_scene_from_blend_file = bpy.data.scenes.get(scene_name_to_load)
        if not loaded_scene_from_blend_file:
            print(f"[BG Worker - Template] FATAL: Failed to retrieve scene '{scene_name_to_load}' from bpy.data after load attempt.", file=sys.stderr)
            return None

        # Rename the loaded scene to avoid any potential name clashes if this function were called multiple times
        # in a way that the old scene wasn't cleaned up (though current design is one scene per worker instance).
        loaded_scene_from_blend_file.name = worker_instance_scene_name

        # Validate essential components are present
        if not loaded_scene_from_blend_file.objects.get(preview_obj_name) or \
           not loaded_scene_from_blend_file.objects.get(camera_obj_name) or \
           not loaded_scene_from_blend_file.camera or \
           loaded_scene_from_blend_file.camera.name != camera_obj_name:
            print(f"[BG Worker - Template] FATAL: Template scene '{loaded_scene_from_blend_file.name}' (loaded from '{scene_name_to_load}') is missing key objects or camera setup.", file=sys.stderr)
            if loaded_scene_from_blend_file.name in bpy.data.scenes: # Cleanup this invalid scene
                bpy.data.scenes.remove(loaded_scene_from_blend_file, do_unlink=True)
            return None

        # Apply necessary render settings
        render_settings = loaded_scene_from_blend_file.render
        render_settings.resolution_x = THUMBNAIL_SIZE_WORKER
        render_settings.resolution_y = THUMBNAIL_SIZE_WORKER
        render_settings.film_transparent = True
        try:
            engine_options = render_settings.bl_rna.properties['engine'].enum_items.keys()
            render_settings.engine = 'BLENDER_EEVEE_NEXT' if 'BLENDER_EEVEE_NEXT' in engine_options else 'BLENDER_EEVEE'
        except Exception: render_settings.engine = 'BLENDER_EEVEE' # Fallback
        
        # Eevee specific settings
        eevee_attr_name = render_settings.engine.lower() # e.g., 'blender_eevee_next' or 'eevee'
        eevee_settings_obj = getattr(loaded_scene_from_blend_file, eevee_attr_name, getattr(render_settings, 'eevee', None))
        if eevee_settings_obj:
            if hasattr(eevee_settings_obj, 'taa_render_samples'): eevee_settings_obj.taa_render_samples = 16
            elif hasattr(eevee_settings_obj, 'samples'): eevee_settings_obj.samples = 16
        
        persistent_icon_template_scene_worker = loaded_scene_from_blend_file
        # print(f"[BG Worker - Template] Template scene '{loaded_scene_from_blend_file.name}' (loaded from '{scene_name_to_load}') successfully configured for rendering.", file=sys.stderr)
        return persistent_icon_template_scene_worker

    except Exception as e:
        print(f"[BG Worker - Template] CRITICAL ERROR loading/configuring icon template scene: {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        # Cleanup attempt if a scene was loaded but failed during configuration
        if loaded_scene_from_blend_file and loaded_scene_from_blend_file.name in bpy.data.scenes:
            try: bpy.data.scenes.remove(loaded_scene_from_blend_file, do_unlink=True)
            except Exception: pass
        persistent_icon_template_scene_worker = None
        return None


def create_sphere_preview_thumbnail_bg_worker(mat_to_render, output_thumb_path, render_scene_for_item):
    # render_scene_for_item is the pre-loaded and configured template scene instance
    if not render_scene_for_item:
        print(f"[BG Worker - ItemRender] Error for '{getattr(mat_to_render, 'name', 'N/A')}': No render_scene_for_item provided by caller.", file=sys.stderr)
        return False

    preview_obj_name = "IconPreviewObject" # Must match the name in your icon_generation_template.blend
    preview_obj = render_scene_for_item.objects.get(preview_obj_name)

    if not preview_obj or not preview_obj.data or not hasattr(preview_obj.data, 'materials'):
        print(f"[BG Worker - ItemRender] Preview object '{preview_obj_name}' is invalid or missing mesh data in the provided render scene ('{render_scene_for_item.name}').", file=sys.stderr)
        return False

    temp_mat_copy = None
    try:
        temp_mat_name = f"_TEMP_RENDER_COPY_{mat_to_render.name[:30]}_{str(uuid.uuid4())[:6]}"
        temp_mat_copy = mat_to_render.copy()
        temp_mat_copy.name = temp_mat_name
        temp_mat_copy.use_fake_user = False
    except Exception as e_copy:
        print(f"[BG Worker - ItemRender] Error copying material '{mat_to_render.name}': {e_copy}", file=sys.stderr)
        return False

    # --- Solution: Render to private path and move atomically ---
    # output_thumb_path is the FINAL destination.
    # We'll render to a temporary path in the same directory first.
    final_output_path = output_thumb_path
    output_dir = os.path.dirname(final_output_path)
    # Ensure the output directory exists (though typically the main addon should handle thumbnail folder creation)
    if not os.path.exists(output_dir):
        try:
            os.makedirs(output_dir, exist_ok=True)
        except Exception as e_mkdir:
            print(f"[BG Worker - ItemRender] ERROR: Could not create output directory '{output_dir}': {e_mkdir}", file=sys.stderr)
            # Cleanup temp material and return
            if temp_mat_copy and temp_mat_copy.name in bpy.data.materials:
                try: bpy.data.materials.remove(temp_mat_copy, do_unlink=True)
                except Exception: pass
            return False

    # Create a unique temporary file name in the same directory as the final output
    temp_filename = f"render_temp_{uuid.uuid4().hex}.png"
    temp_render_output_path = os.path.join(output_dir, temp_filename)
    # --- End of modification for private path setup ---

    try:
        if not preview_obj.material_slots:
            preview_obj.data.materials.append(temp_mat_copy)
        else:
            preview_obj.material_slots[0].material = temp_mat_copy

        if temp_mat_copy.use_nodes and temp_mat_copy.node_tree:
            active_uv_map_on_preview_obj = preview_obj.data.uv_layers.active
            if not active_uv_map_on_preview_obj and len(preview_obj.data.uv_layers) > 0:
                active_uv_map_on_preview_obj = preview_obj.data.uv_layers[0]

            if active_uv_map_on_preview_obj:
                uv_map_node = None
                for node in temp_mat_copy.node_tree.nodes:
                    if node.bl_idname == 'ShaderNodeUVMap':
                        uv_map_node = node
                        break
                if not uv_map_node:
                    uv_map_node = temp_mat_copy.node_tree.nodes.new('ShaderNodeUVMap')
                
                uv_map_node.uv_map = active_uv_map_on_preview_obj.name

                for tex_node in temp_mat_copy.node_tree.nodes:
                    if tex_node.bl_idname == 'ShaderNodeTexImage':
                        vector_input = tex_node.inputs.get("Vector")
                        if vector_input and not vector_input.is_linked:
                            try:
                                temp_mat_copy.node_tree.links.new(uv_map_node.outputs['UV'], vector_input)
                            except Exception as e_link_uv:
                                print(f"[BG Worker - ItemRender] Minor error linking UV for {tex_node.name}: {e_link_uv}", file=sys.stderr)
            # else: print(f"[BG Worker - ItemRender] Preview object has no UV map to link for material '{temp_mat_copy.name}'.", file=sys.stderr)

        # --- MODIFICATION: Render to the temporary path ---
        render_scene_for_item.render.filepath = temp_render_output_path
        # --- End Modification ---
        
        # print(f"[BG Worker - ItemRender] Rendering '{temp_mat_copy.name}' (original: '{mat_to_render.name}') to TEMP '{temp_render_output_path}' using scene '{render_scene_for_item.name}'.", file=sys.stderr)
        bpy.ops.render.render(scene=render_scene_for_item.name, write_still=True)
        
        time.sleep(0.1) # Short pause to help ensure file is written before os.path checks

        # --- MODIFICATION: Check the temporary file first ---
        if not os.path.exists(temp_render_output_path) or os.path.getsize(temp_render_output_path) == 0:
            print(f"[BG Worker - ItemRender] ERROR: Temporary render output file missing or empty. Temp Path: {temp_render_output_path}", file=sys.stderr)
            if os.path.exists(temp_render_output_path): # Attempt to clean up failed temp file
                 try: os.remove(temp_render_output_path)
                 except Exception as e_del_failed_temp: print(f"[BG Worker - ItemRender] Could not delete failed temp render {temp_render_output_path}: {e_del_failed_temp}", file=sys.stderr)
            return False
        # --- End Modification ---

        # --- MODIFICATION: Atomically move the temporary file to the final path ---
        try:
            # print(f"[BG Worker - ItemRender] Moving temp render '{temp_render_output_path}' to final '{final_output_path}'.", file=sys.stderr)
            shutil.move(temp_render_output_path, final_output_path) # This is the atomic operation if on same filesystem
        except Exception as e_move:
            print(f"[BG Worker - ItemRender] ERROR: Failed to move temp render '{temp_render_output_path}' to final path '{final_output_path}': {e_move}", file=sys.stderr)
            if os.path.exists(temp_render_output_path): # Attempt to clean up temp file if move failed
                 try: os.remove(temp_render_output_path)
                 except Exception as e_del_unmoved_temp: print(f"[BG Worker - ItemRender] Could not delete unmoved temp render {temp_render_output_path}: {e_del_unmoved_temp}", file=sys.stderr)
            return False
        # --- End Modification ---

        # Final check on the actual destination path
        if not os.path.exists(final_output_path) or os.path.getsize(final_output_path) == 0:
            print(f"[BG Worker - ItemRender] ERROR: Final output file missing or empty AFTER MOVE. Path: {final_output_path}", file=sys.stderr)
            return False
            
        # print(f"[BG Worker - ItemRender] Thumbnail successfully rendered and moved to: {final_output_path}", file=sys.stderr)
        return True

    except Exception as e_render_process:
        print(f"[BG Worker - ItemRender] Critical error during rendering process for '{temp_mat_copy.name if temp_mat_copy else mat_to_render.name}': {e_render_process}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        # Attempt to clean up the temporary render file if an error occurred mid-process
        if os.path.exists(temp_render_output_path):
            try: os.remove(temp_render_output_path)
            except Exception as e_del_error_temp: print(f"[BG Worker - ItemRender] Could not delete temp render {temp_render_output_path} during exception: {e_del_error_temp}", file=sys.stderr)
        return False
    finally:
        if temp_mat_copy and temp_mat_copy.name in bpy.data.materials:
            try:
                bpy.data.materials.remove(temp_mat_copy, do_unlink=True)
            except Exception: pass

def main_render_thumbnail_batch(args_batch_render):
    print(f"[BG Worker - Thumb Batch Op] STARTING Batch. AddonData: {args_batch_render.addon_data_root}", file=sys.stderr)
    sys.stderr.flush()

    global ICON_TEMPLATE_FILE_WORKER, THUMBNAIL_SIZE_WORKER, persistent_icon_template_scene_worker
    ICON_TEMPLATE_FILE_WORKER = os.path.join(args_batch_render.addon_data_root, "icon_generation_template.blend")
    THUMBNAIL_SIZE_WORKER = args_batch_render.thumbnail_size

    json_output_payload = {"results": []} # Initialize with empty results

    if not os.path.exists(ICON_TEMPLATE_FILE_WORKER):
        print(f"[BG Worker - Thumb Batch Op] FATAL: Icon template missing: '{ICON_TEMPLATE_FILE_WORKER}'. Batch aborted.", file=sys.stderr)
        # Try to parse tasks to report failure for each, even if template is missing
        tasks_for_early_failure = []
        try: tasks_for_early_failure = json.loads(args_batch_render.tasks_json)
        except: pass
        for task_info in tasks_for_early_failure:
            json_output_payload["results"].append({
                "hash_value": task_info.get('hash_value', 'UNKNOWN_HASH_NO_TPL'),
                "thumb_path": task_info.get('thumb_path', 'UNKNOWN_PATH_NO_TPL'),
                "status": "failure", "reason": "worker_icon_template_file_missing"
            })
        print(json.dumps(json_output_payload)) # To STDOUT
        sys.stdout.flush()
        return 1

    try:
        tasks_to_process_in_batch = json.loads(args_batch_render.tasks_json)
    except json.JSONDecodeError as e_json:
        print(f"[BG Worker - Thumb Batch Op] FATAL: Could not decode tasks_json: {e_json}", file=sys.stderr)
        json_output_payload["error"] = "tasks_json_decode_error"
        json_output_payload["message"] = str(e_json)
        print(json.dumps(json_output_payload)) # To STDOUT
        sys.stdout.flush()
        return 1

    if not tasks_to_process_in_batch:
        print("[BG Worker - Thumb Batch Op] No tasks in JSON. Exiting batch gracefully.", file=sys.stderr)
        print(json.dumps(json_output_payload)) # To STDOUT (empty results)
        sys.stdout.flush()
        return 0

    print(f"[BG Worker - Thumb Batch Op] Received {len(tasks_to_process_in_batch)} tasks.", file=sys.stderr)

    # Load the icon template scene ONCE for the entire batch
    # This instance will be passed to create_sphere_preview_thumbnail_bg_worker
    render_scene_instance_for_batch = load_icon_template_scene_bg_worker() # This sets persistent_icon_template_scene_worker

    if not render_scene_instance_for_batch:
        print(f"[BG Worker - Thumb Batch Op] FATAL: Failed to load/prepare icon template scene. All tasks in batch will fail.", file=sys.stderr)
        for task_info in tasks_to_process_in_batch:
            json_output_payload["results"].append({
                "hash_value": task_info.get('hash_value', 'UNKNOWN_HASH_TPL_FAIL'),
                "thumb_path": task_info.get('thumb_path', 'UNKNOWN_PATH_TPL_FAIL'),
                "status": "failure", "reason": "worker_template_scene_load_failed"
            })
        print(json.dumps(json_output_payload)) # To STDOUT
        sys.stdout.flush()
        return 1

    # Ensure a result entry is created for EVERY task, even if processing fails mid-way for some reason
    # Initialize all result entries first to guarantee structure
    for task_info in tasks_to_process_in_batch:
        json_output_payload["results"].append({
            "hash_value": task_info.get('hash_value'),
            "thumb_path": task_info.get('thumb_path'),
            "status": "failure", # Default to failure
            "reason": "processing_not_attempted_or_early_exit_in_worker"
        })

    # Now, attempt to process each task and update its corresponding result entry
    for task_index, current_task_info in enumerate(tasks_to_process_in_batch):
        # Get the pre-initialized result dict for this task
        current_task_result_dict = json_output_payload["results"][task_index]
        
        task_hash = current_task_info.get('hash_value') # Already in current_task_result_dict
        task_thumb_path = current_task_info.get('thumb_path') # Already in current_task_result_dict
        task_mat_uuid = current_task_info.get('mat_uuid')
        task_mat_name_debug = current_task_info.get('mat_name_debug', 'N/A_DEBUG_NAME')

        print(f"  [Batch Worker Task {task_index + 1}/{len(tasks_to_process_in_batch)}] Processing: UUID '{task_mat_uuid}', Name '{task_mat_name_debug}', Hash '{task_hash[:8] if task_hash else 'None'}'", file=sys.stderr)
        sys.stderr.flush()

        if not all([task_hash, task_thumb_path, task_mat_uuid]):
            msg = "Task data incomplete (missing hash, path, or uuid)."
            print(f"    [Batch Worker Task {task_index + 1}] ERROR: {msg}", file=sys.stderr)
            current_task_result_dict["reason"] = msg
            # status remains "failure"
            continue # Move to the next task in the batch

        material_object_to_render = bpy.data.materials.get(task_mat_uuid)
        if not material_object_to_render:
            for mat_iter in bpy.data.materials:
                if mat_iter.get("uuid") == task_mat_uuid:
                    material_object_to_render = mat_iter; break
        if not material_object_to_render and task_mat_name_debug:
             material_object_to_render = bpy.data.materials.get(task_mat_name_debug)

        if not material_object_to_render:
            msg = f"Material for UUID '{task_mat_uuid}' (Name: '{task_mat_name_debug}') not found in source .blend."
            print(f"    [Batch Worker Task {task_index + 1}] ERROR: {msg}", file=sys.stderr)
            current_task_result_dict["reason"] = msg
            continue

        try:
            # Pass the single loaded render_scene_instance_for_batch
            individual_render_success = create_sphere_preview_thumbnail_bg_worker(
                material_object_to_render, task_thumb_path, render_scene_instance_for_batch
            )

            if individual_render_success:
                if os.path.exists(task_thumb_path) and os.path.getsize(task_thumb_path) > 0:
                    current_task_result_dict["status"] = "success"
                    current_task_result_dict["reason"] = "thumbnail_rendered_successfully_by_worker"
                    print(f"    [Batch Worker Task {task_index + 1}] SUCCESS for '{material_object_to_render.name}'.", file=sys.stderr)
                else:
                    current_task_result_dict["reason"] = "render_call_true_but_output_file_invalid"
                    print(f"    [Batch Worker Task {task_index + 1}] ERROR: Render call success, but output file invalid for '{material_object_to_render.name}'.", file=sys.stderr)
            else:
                current_task_result_dict["reason"] = "create_sphere_preview_function_returned_false"
                print(f"    [Batch Worker Task {task_index + 1}] FAILURE reported by render function for '{material_object_to_render.name}'.", file=sys.stderr)
        except Exception as e_render_task_item:
            current_task_result_dict["reason"] = f"exception_in_item_render_call:_{type(e_render_task_item).__name__}"
            print(f"    [Batch Worker Task {task_index + 1}] EXCEPTION during render call for '{material_object_to_render.name}': {e_render_task_item}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
        
        sys.stderr.flush() # Ensure per-task log is out

    # Clean up the specific template scene instance used by this worker batch
    if persistent_icon_template_scene_worker and \
       persistent_icon_template_scene_worker.name in bpy.data.scenes and \
       persistent_icon_template_scene_worker == render_scene_instance_for_batch :
        try:
            # print(f"[BG Worker - Thumb Batch Op] Cleaning up worker's template scene instance: {persistent_icon_template_scene_worker.name}", file=sys.stderr)
            bpy.data.scenes.remove(persistent_icon_template_scene_worker, do_unlink=True)
        except Exception as e_cleanup_scene:
             print(f"[BG Worker - Thumb Batch Op] Error cleaning up template scene '{persistent_icon_template_scene_worker.name}': {e_cleanup_scene}", file=sys.stderr)
        persistent_icon_template_scene_worker = None

    print(f"[BG Worker - Thumb Batch Op] Batch processing loop finished. Final JSON results ({len(json_output_payload['results'])} items) will be printed to stdout.", file=sys.stderr)
    sys.stderr.flush()
    
    print(json.dumps(json_output_payload)) # This is the critical output to STDOUT
    sys.stdout.flush()
    
    return 0 # Worker process itself completed its task of iterating through the batch.

def _load_and_process_blend_file(filepath, is_target_file): # For background_writer.py
    mats_loaded_this_call = []
    processed_data = {} # {uuid: {'mat_obj':mat, 'hash':h}}
    
    if not os.path.exists(filepath):
        print(f"[BG Merge - WORKER LoadFunc] File not found: {filepath}", file=sys.stderr)
        return mats_loaded_this_call, processed_data

    print(f"[BG Merge - WORKER LoadFunc] Attempting to load all materials from: {os.path.basename(filepath)}", file=sys.stderr)
    
    # Store materials present *before* loading this specific file
    # (Relies on --factory-startup making bpy.data.materials mostly empty initially for the worker)
    mats_before_load = {m.name: m for m in bpy.data.materials}
    print(f"[BG Merge - WORKER LoadFunc] Materials in bpy.data BEFORE loading {os.path.basename(filepath)}: {list(mats_before_load.keys())}", file=sys.stderr)

    try:
        with bpy.data.libraries.load(filepath, link=False, relative=False) as (data_from, data_to):
            # Request to load all materials found in the file by name
            # data_from.materials should be a list of names (strings)
            if hasattr(data_from, 'materials') and data_from.materials:
                material_names_to_request = [name for name in data_from.materials if isinstance(name, str)]
                if material_names_to_request:
                    print(f"[BG Merge - WORKER LoadFunc] Requesting load of names: {material_names_to_request} from {os.path.basename(filepath)}", file=sys.stderr)
                    data_to.materials = material_names_to_request
                else:
                    print(f"[BG Merge - WORKER LoadFunc] No material names (strings) found in data_from.materials for {os.path.basename(filepath)}.", file=sys.stderr)
                    data_to.materials = [] # Explicitly set to empty if no valid names
            else:
                print(f"[BG Merge - WORKER LoadFunc] No 'materials' attribute or empty in data_from for {os.path.basename(filepath)}.", file=sys.stderr)
                data_to.materials = []


        # Now, iterate through bpy.data.materials and identify those that were newly loaded
        # and are not linked (i.e., they are local copies from the file)
        print(f"[BG Merge - WORKER LoadFunc] Materials in bpy.data AFTER loading {os.path.basename(filepath)}: {[m.name for m in bpy.data.materials]}", file=sys.stderr)
        
        newly_loaded_or_updated_mats = []
        for mat_obj in bpy.data.materials:
            # Check if it's a new material not present before, or if it was present but has now been overwritten (updated)
            # A simple check is if its library attribute is None (meaning it's a local copy from the load)
            # and it wasn't in mats_before_load OR if it was, that this is a fresh instance.
            # For simplicity with factory startup, any non-library material that isn't a default startup material
            # is likely from our load.
            if not mat_obj.library: # It's a local datablock
                # A more robust check might be needed if factory startup still creates some default materials.
                # For now, assume all non-library are from our load operation in this worker.
                if mat_obj.name not in mats_before_load or bpy.data.materials[mat_obj.name] != mats_before_load.get(mat_obj.name):
                     newly_loaded_or_updated_mats.append(mat_obj)


        if not newly_loaded_or_updated_mats:
            print(f"[BG Merge - WORKER LoadFunc] No new non-library materials identified in bpy.data after loading {os.path.basename(filepath)}.", file=sys.stderr)
            # This could also happen if data_to.materials was empty
            if not data_to.materials: # Check if we even requested anything
                 print(f"[BG Merge - WORKER LoadFunc] This is expected as no materials were requested for load from {os.path.basename(filepath)}.", file=sys.stderr)

            return mats_loaded_this_call, processed_data # processed_data will be empty

        print(f"[BG Merge - WORKER LoadFunc] Identified {len(newly_loaded_or_updated_mats)} new/updated local materials after load.", file=sys.stderr)

        for mat_obj in newly_loaded_or_updated_mats:
            mats_loaded_this_call.append(mat_obj)
            
            uid = mat_obj.name # In library/transfer files, name IS the UUID
            if not (uid and len(uid) == 36 and '-' in uid): # Basic UUID format check
                uid_prop = mat_obj.get("uuid")
                uid_gen = validate_material_uuid(mat_obj) # Generates if prop bad/missing
                print(f"[BG Merge - WORKER LoadFunc] Mat '{mat_obj.name}' name not UUID. Prop: '{uid_prop}', Validated/Generated: '{uid_gen}'. Using '{uid_gen}' for processing.", file=sys.stderr)
                uid = uid_gen # Use the validated/generated UUID
            
            h = get_material_hash(mat_obj)

            if uid and h:
                if uid not in processed_data: 
                    processed_data[uid] = {'mat_obj': mat_obj, 'hash': h}
                # else: print(f"[BG Merge - WORKER LoadFunc] Warning: Duplicate UUID '{uid}' processed from {os.path.basename(filepath)}.", file=sys.stderr)
            # else: print(f"[BG Merge - WORKER LoadFunc] Warning: Failed UID/Hash for mat '{mat_obj.name}' from {os.path.basename(filepath)}.", file=sys.stderr)
        
        print(f"[BG Merge - WORKER LoadFunc] Successfully processed {len(processed_data)} materials from {os.path.basename(filepath)}.", file=sys.stderr)

    except Exception as e_load_actual:
        print(f"[BG Merge - WORKER LoadFunc] CRITICAL Error during load/process from {os.path.basename(filepath)}: {e_load_actual}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        for mat_cleanup in list(bpy.data.materials): # More aggressive cleanup on error
            if not mat_cleanup.library and mat_cleanup.name not in mats_before_load:
                try: bpy.data.materials.remove(mat_cleanup)
                except: pass
        mats_loaded_this_call.clear()
    
    return mats_loaded_this_call, processed_data

def _worker_record_library_material_origin(db_path, lib_uuid, origin_file, origin_name_in_src, origin_uuid_in_src, check_existing=False):
    """Helper to record or update material origin in the database by the worker."""
    if not db_path or not os.path.exists(db_path):
        # print(f"    Origin DB not found at '{db_path}' for {lib_uuid[:8]}. Skipping origin record.", file=sys.stderr)
        return
    conn = None
    try:
        conn = sqlite3.connect(db_path, timeout=10)
        c = conn.cursor()
        # Ensure table exists (though main addon should create it)
        c.execute('''CREATE TABLE IF NOT EXISTS library_material_origins
                     (library_material_uuid TEXT PRIMARY KEY,
                      source_blend_filepath TEXT,
                      source_material_name_in_file TEXT, 
                      source_material_uuid_in_file TEXT,
                      timestamp_added_to_library INTEGER)''')

        if check_existing: # Used when only updating origin for an existing unchanged material
            c.execute("SELECT source_blend_filepath, source_material_uuid_in_file, source_material_name_in_file FROM library_material_origins WHERE library_material_uuid = ?", (lib_uuid,))
            row = c.fetchone()
            if row and row[0] == origin_file and row[1] == origin_uuid_in_src and row[2] == origin_name_in_src:
                # print(f"    Origin for {lib_uuid[:8]} (File: {os.path.basename(origin_file)}, SourceUUID: {origin_uuid_in_src}) already up-to-date. No DB change.", file=sys.stderr)
                return

        current_time = int(time.time())
        # print(f"    Recording/Updating origin in DB for lib UUID {lib_uuid[:8]}: File='{os.path.basename(origin_file)}', SourceName='{origin_name_in_src}', SourceUUID='{origin_uuid_in_src}', Time={current_time}", file=sys.stderr)
        c.execute("INSERT OR REPLACE INTO library_material_origins VALUES (?, ?, ?, ?, ?)",
                  (lib_uuid, origin_file, origin_name_in_src, origin_uuid_in_src, current_time))
        conn.commit()
    except sqlite3.Error as e_db_origin:
        print(f"    DB ERROR recording/updating origin for {lib_uuid[:8]}: {e_db_origin}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
    except Exception as e_gen:
        print(f"    General ERROR recording/updating origin for {lib_uuid[:8]}: {e_gen}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
    finally:
        if conn:
            try: conn.close()
            except Exception: pass

def main_merge_library(args):
    print(f"[BG Worker - Merge Op] Start. Transfer='{os.path.basename(args.transfer)}', Target='{os.path.basename(args.target)}', DB='{args.db}'", file=sys.stderr)
    sys.stderr.flush()

    loaded_target_mats_objs = []
    loaded_transfer_mats_objs = []
    target_materials_data = {}    # {uuid: {'mat_obj': obj, 'hash': hash_string}}
    transfer_materials_data = {}  # {uuid: {'mat_obj': obj, 'hash': hash_string, 'origin_props': {}}}

    transfer_file_abs = os.path.abspath(args.transfer)
    target_file_abs = os.path.abspath(args.target)
    db_path = os.path.abspath(args.db) if args.db and os.path.exists(args.db) else None

    if not db_path:
        print(f"[BG Merge - WORKER] WARNING: DB not found at '{args.db}'. Timestamps and origins won't be updated by worker.", file=sys.stderr)

    # 1. Load Target Library (if exists)
    if os.path.exists(target_file_abs):
        print(f"[BG Merge - WORKER] Loading existing target library: {os.path.basename(target_file_abs)}", file=sys.stderr)
        loaded_target_mats_objs, target_materials_data = _load_and_process_blend_file(target_file_abs, is_target_file=True)
    else:
        print(f"[BG Merge - WORKER] Target library '{os.path.basename(target_file_abs)}' not found. Will create new.", file=sys.stderr)
        try:
            target_dir = os.path.dirname(target_file_abs)
            if target_dir:
                os.makedirs(target_dir, exist_ok=True)
        except Exception as e_mkdir:
            print(f"[BG Merge - WORKER] Warning: Could not create directory for new target library: {e_mkdir}", file=sys.stderr)

    # 2. Load Transfer Library
    if os.path.exists(transfer_file_abs):
        print(f"[BG Merge - WORKER] Loading transfer file: {os.path.basename(transfer_file_abs)}", file=sys.stderr)
        loaded_transfer_mats_objs, transfer_materials_data = _load_and_process_blend_file(transfer_file_abs, is_target_file=False)
        if not transfer_materials_data and not loaded_transfer_mats_objs :
            print(f"[BG Merge - WORKER] No materials loaded or processed from transfer file '{transfer_file_abs}'. Nothing to merge.", file=sys.stderr)
            if not target_materials_data:
                 print(f"[BG Merge - WORKER] Both transfer and target are empty. No operation needed.", file=sys.stderr)
                 return 0 # Success, nothing to do.
    else:
        print(f"[BG Merge - WORKER] Transfer file '{os.path.basename(transfer_file_abs)}' not found. Cannot merge.", file=sys.stderr)
        return 1 # Error condition

    # --- Merge Logic ---
    final_materials_to_write_map = {} # {uuid_in_library: material_object_to_write}
    for u, data in target_materials_data.items():
        final_materials_to_write_map[u] = data['mat_obj']

    mats_added_count = 0
    mats_updated_count = 0
    mats_skipped_failed_hash_transfer_count = 0

    print(f"[BG Merge - WORKER] Starting merge. Target materials initially in map: {len(final_materials_to_write_map)}, Transfer materials to process: {len(transfer_materials_data)}", file=sys.stderr)

    for t_uuid, t_data_dict in transfer_materials_data.items():
        t_mat_obj = t_data_dict['mat_obj']
        t_hash = t_data_dict['hash']
        if not t_hash:
            mats_skipped_failed_hash_transfer_count += 1
            print(f"  Skipping transfer mat with lib UUID {t_uuid[:8]} ('{getattr(t_mat_obj, 'name', 'N/A')}') due to missing hash.", file=sys.stderr)
            continue

        origin_blend_file = t_mat_obj.get("ml_origin_blend_file", "UnknownSourceFile")
        origin_mat_name_in_source = t_mat_obj.get("ml_origin_mat_name", "UnknownSourceName")
        origin_mat_uuid_in_source = t_mat_obj.get("ml_origin_mat_uuid", "UnknownSourceUUID")
        existing_target_data = target_materials_data.get(t_uuid)

        if not existing_target_data:
            print(f"  ADDING new material to library: UUID {t_uuid[:8]} (ContentHash {t_hash[:8]}). Origin: '{os.path.basename(origin_blend_file)}' ({origin_mat_uuid_in_source[:8]})", file=sys.stderr)
            final_materials_to_write_map[t_uuid] = t_mat_obj
            mats_added_count += 1
            if db_path:
                update_material_timestamp_in_db(db_path, t_uuid)
                _worker_record_library_material_origin(db_path, t_uuid, origin_blend_file, origin_mat_name_in_source, origin_mat_uuid_in_source)
        else:
            target_hash_for_this_uuid = existing_target_data['hash']
            if t_hash != target_hash_for_this_uuid:
                print(f"  UPDATING existing library material: UUID {t_uuid[:8]}. OldHash: {target_hash_for_this_uuid[:8] if target_hash_for_this_uuid else 'None'}, NewHash: {t_hash[:8]}. Origin: '{os.path.basename(origin_blend_file)}' ({origin_mat_uuid_in_source[:8]})", file=sys.stderr)
                final_materials_to_write_map[t_uuid] = t_mat_obj
                mats_updated_count += 1
                if db_path:
                    update_material_timestamp_in_db(db_path, t_uuid)
                    _worker_record_library_material_origin(db_path, t_uuid, origin_blend_file, origin_mat_name_in_source, origin_mat_uuid_in_source)
            else:
                print(f"  Content for library material UUID {t_uuid[:8]} is IDENTICAL (Hash {t_hash[:8]}). Updating origin record. Origin: '{os.path.basename(origin_blend_file)}' ({origin_mat_uuid_in_source[:8]})", file=sys.stderr)
                if db_path:
                    _worker_record_library_material_origin(db_path, t_uuid, origin_blend_file, origin_mat_name_in_source, origin_mat_uuid_in_source, check_existing=True)

    # --- Prepare final set of bpy.types.Material objects for writing ---
    final_set_for_bpy_write = set()
    mats_prepared_for_write = 0
    for lib_uuid, mat_object_to_write in final_materials_to_write_map.items():
        if mat_object_to_write and hasattr(mat_object_to_write, 'name') and mat_object_to_write.name in bpy.data.materials:
            if bpy.data.materials[mat_object_to_write.name] == mat_object_to_write:
                try:
                    if mat_object_to_write.name != lib_uuid:
                        mat_object_to_write.name = lib_uuid
                    mat_object_to_write.use_fake_user = True
                    final_set_for_bpy_write.add(mat_object_to_write)
                    mats_prepared_for_write +=1
                except Exception as e_final_prep:
                    print(f"  ERROR preparing final material for lib UUID '{lib_uuid[:8]}' (Name: '{mat_object_to_write.name}'): {e_final_prep}", file=sys.stderr)
            else:
                print(f"  WARNING: Stale reference for material object intended for lib UUID '{lib_uuid[:8]}' (Name: '{mat_object_to_write.name}'). Skipping.", file=sys.stderr)
        else:
            print(f"  WARNING: Invalid or missing material object for lib UUID '{lib_uuid[:8]}'. Skipping.", file=sys.stderr)
    
    print(f"[BG Merge - WORKER] Total materials prepared for writing to library: {mats_prepared_for_write}", file=sys.stderr)

    # --- NEW: Pack Images directly for materials in final_set_for_bpy_write ---
    # This replaces the call to _ensure_texture_local_to_library
    print(f"[BG Merge - WORKER] Starting image packing for {len(final_set_for_bpy_write)} materials...", file=sys.stderr)
    packed_image_count = 0
    failed_pack_count = 0
    # Keep track of image datablocks already processed to avoid redundant packing attempts or messages
    images_already_processed_for_packing = set()

    for mat_obj_for_packing in final_set_for_bpy_write:
        if not mat_obj_for_packing.use_nodes or not mat_obj_for_packing.node_tree:
            continue
        for node in mat_obj_for_packing.node_tree.nodes:
            if node.bl_idname == 'ShaderNodeTexImage' and node.image:
                img_datablock = node.image
                
                # Skip if this image datablock instance has already been processed
                if img_datablock.name in images_already_processed_for_packing: # Using name as a proxy for the datablock instance
                    continue

                if img_datablock.packed_file is not None:
                    print(f"  Image '{img_datablock.name}' is already packed. Skipping.", file=sys.stderr)
                    images_already_processed_for_packing.add(img_datablock.name)
                    continue

                if img_datablock.source != 'FILE':
                    print(f"  Image '{img_datablock.name}' source is '{img_datablock.source}' (not FILE). Skipping packing.", file=sys.stderr)
                    images_already_processed_for_packing.add(img_datablock.name)
                    continue
                
                if not img_datablock.filepath_raw: # Check filepath_raw specifically
                    print(f"  Image '{img_datablock.name}' has no raw filepath. Cannot determine source for packing. Skipping.", file=sys.stderr)
                    images_already_processed_for_packing.add(img_datablock.name)
                    failed_pack_count +=1 # Count as a failure if it should have been packed but couldn't
                    continue

                # At this point, image.source == 'FILE', image.packed_file is None, and filepath_raw exists.
                # Attempt to resolve the absolute path for disk check
                abs_image_path = ""
                try:
                    # bpy.path.abspath() resolves relative to the current .blend file context.
                    # When textures are loaded from the transfer file, their paths are relative to it.
                    abs_image_path = bpy.path.abspath(img_datablock.filepath_raw)
                except Exception as e_abs:
                    print(f"  Error resolving absolute path for image '{img_datablock.name}' (raw: '{img_datablock.filepath_raw}'): {e_abs}. Skipping packing.", file=sys.stderr)
                    failed_pack_count += 1
                    images_already_processed_for_packing.add(img_datablock.name)
                    continue

                if not os.path.exists(abs_image_path):
                    print(f"  Source file for image '{img_datablock.name}' not found at resolved path '{abs_image_path}' (from raw '{img_datablock.filepath_raw}'). Skipping packing.", file=sys.stderr)
                    failed_pack_count += 1
                    images_already_processed_for_packing.add(img_datablock.name)
                    continue
                
                # Now attempt to pack
                try:
                    print(f"  Attempting to pack image: '{img_datablock.name}' from current filepath: '{img_datablock.filepath}' (raw: '{img_datablock.filepath_raw}', resolved abs: '{abs_image_path}')", file=sys.stderr)
                    # Crucially, ensure the image.filepath is what image.pack() expects.
                    # If image.filepath is not already abs_image_path, it might be safer to set it if pack fails.
                    # However, Blender's internal loading via bpy.data.libraries.load should handle this.
                    # If image.filepath is, for example, `//textures/foo.png` from the temp transfer file,
                    # and that file exists at `abs_image_path`, pack() should work.
                    img_datablock.pack()
                    packed_image_count += 1
                    print(f"    Successfully packed image '{img_datablock.name}'. New source: {img_datablock.source}, Filepath: '{img_datablock.filepath}'", file=sys.stderr)
                except RuntimeError as e_pack:
                    print(f"  Failed to pack image '{img_datablock.name}' (resolved from '{abs_image_path}'): {e_pack}", file=sys.stderr)
                    failed_pack_count += 1
                except Exception as e_pack_other:
                    print(f"  Unexpected error while packing image '{img_datablock.name}': {e_pack_other}", file=sys.stderr)
                    traceback.print_exc(file=sys.stderr)
                    failed_pack_count += 1
                
                images_already_processed_for_packing.add(img_datablock.name) # Mark as processed regardless of outcome for this instance
    
    print(f"[BG Merge - WORKER] Image packing finished. Successfully packed: {packed_image_count}, Failed/Skipped: {failed_pack_count}.", file=sys.stderr)
    sys.stderr.flush()
    # --- End NEW Image Packing Section ---

    # --- Write the final library file ---
    temp_lib_output_path = None
    try:
        write_dir = os.path.dirname(target_file_abs)
        if not write_dir: write_dir = "." 
        os.makedirs(write_dir, exist_ok=True)
        
        fd, temp_lib_output_path = tempfile.mkstemp(suffix='.blend', prefix=f"{os.path.splitext(os.path.basename(target_file_abs))[0]}_MERGETEMP_", dir=write_dir)
        os.close(fd) 

        if not final_set_for_bpy_write:
            print(f"[BG Merge - WORKER] No valid materials to write to library. Writing empty library to temp: {os.path.basename(temp_lib_output_path)}", file=sys.stderr)
            bpy.data.libraries.write(temp_lib_output_path, set(), fake_user=True, compress=True)
        else:
            print(f"[BG Merge - WORKER] Writing final set of {len(final_set_for_bpy_write)} materials (with packed images) to temporary file: {os.path.basename(temp_lib_output_path)}", file=sys.stderr)
            bpy.data.libraries.write(temp_lib_output_path, final_set_for_bpy_write, fake_user=True, compress=True)
        
        print(f"[BG Merge - WORKER] Moving temporary library to final target: {os.path.basename(target_file_abs)}", file=sys.stderr)
        shutil.move(temp_lib_output_path, target_file_abs) 
        temp_lib_output_path = None 
        print(f"[BG Merge - WORKER] Library merge and replacement successful: {os.path.basename(target_file_abs)}", file=sys.stderr)
        print(f"[BG Merge - WORKER Summary] Added: {mats_added_count}, Updated: {mats_updated_count}, Skipped (No Hash): {mats_skipped_failed_hash_transfer_count}", file=sys.stderr)
        sys.stderr.flush()
        return 0 # Success
    except Exception as write_replace_err:
        print(f"[BG Merge - WORKER] CRITICAL ERROR during final write/replace of library: {write_replace_err}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        return 1 # Error
    finally:
        if temp_lib_output_path and os.path.exists(temp_lib_output_path):
            try:
                os.remove(temp_lib_output_path)
                print(f"[BG Merge - WORKER] Cleaned up stray temporary library file: {temp_lib_output_path}", file=sys.stderr)
            except Exception as e_clean_temp:
                print(f"[BG Merge - WORKER] Error cleaning up stray temporary library file '{temp_lib_output_path}': {e_clean_temp}", file=sys.stderr)
        # bpy.data.materials are implicitly cleaned up when the worker Blender instance exits.

# --- Main Entry Point for the Worker Script ---
def main_worker_entry():
    # All diagnostic prints from this function should go to sys.stderr
    print(f"[BG Worker - Entry] Worker started. Full argv: {sys.argv}", file=sys.stderr)
    # Blender loads the .blend file passed to it before --python is executed.
    # A small delay might ensure everything is settled in some edge cases.
    time.sleep(0.2) # Short delay
    print(f"[BG Worker - Entry] Current .blend file context: {bpy.data.filepath if bpy.data.filepath else 'Unsaved/None'}", file=sys.stderr)
    sys.stderr.flush()

    parser = argparse.ArgumentParser(description="Background worker for MaterialList Addon.")
    parser.add_argument("--operation", choices=['merge_library', 'render_thumbnail'], required=True,
                        help="The operation to perform: 'merge_library' or 'render_thumbnail'.")

    # Arguments for 'merge_library'
    parser.add_argument("--transfer", help="Path to the transfer .blend file (for merge_library).")
    parser.add_argument("--target", help="Path to the target (main) library .blend file (for merge_library).")
    parser.add_argument("--db", help="Path to the addon's SQLite database file (for merge_library timestamps).")

    # Arguments for 'render_thumbnail' (expects batch mode)
    parser.add_argument("--tasks-json", help="JSON string detailing a batch of thumbnail tasks (for render_thumbnail).")
    parser.add_argument("--addon-data-root", help="Path to the addon's main data directory (used to find icon_template.blend).")
    parser.add_argument("--thumbnail-size", type=int, help="Target size (width/height) for the thumbnails.")
    
    # Filter out Blender's own arguments before passing to argparse
    try:
        app_args = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else []
    except ValueError: # "--" not in sys.argv, which might happen if script called directly without it
        app_args = sys.argv[1:] # Assume all args after script name are for this script
        print(f"[BG Worker - Entry] Warning: '--' separator not found in sys.argv. Parsing from sys.argv[1:].", file=sys.stderr)


    if not app_args: # If no arguments after '--' or no arguments at all
        print(f"[BG Worker - Entry] No arguments provided to worker after '--'. Exiting.", file=sys.stderr)
        parser.print_help(sys.stderr) # Print help to stderr
        return 1

    args = parser.parse_args(app_args)

    if args.operation == 'merge_library':
        if not all([args.transfer, args.target]): # --db is optional for merge operation itself but good for timestamps
            parser.error("--transfer and --target arguments are required for 'merge_library' operation.")
            # Argparse error automatically exits with code 2
        return main_merge_library(args)
    elif args.operation == 'render_thumbnail':
        if not args.tasks_json:
            parser.error("--tasks-json argument is required for 'render_thumbnail' operation.")
        if not all([args.addon_data_root, args.thumbnail_size is not None]):
            parser.error("--addon-data-root and --thumbnail-size are required with --tasks-json.")
        return main_render_thumbnail_batch(args)
    else:
        # This case should not be reached due to 'choices' in parser, but as a safeguard:
        print(f"[BG Worker - Entry] Unknown operation specified: {args.operation}", file=sys.stderr)
        return 1 # General error

if __name__ == "__main__":
    final_exit_code = 1 # Default to error
    try:
        # print(f"[BG Worker - __main__] Starting worker process.", file=sys.stderr)
        # sys.stderr.flush()
        final_exit_code = main_worker_entry()
    except SystemExit as e_sysexit: # Catches parser.error() which raises SystemExit
        final_exit_code = e_sysexit.code if isinstance(e_sysexit.code, int) else 1
        if final_exit_code != 0: # Argparse usually prints its own error message
            print(f"[BG Worker - __main__] SystemExit with code: {final_exit_code}.", file=sys.stderr)
    except Exception as e_global_worker:
        print(f"[BG Worker - __main__] === Unhandled Global Exception in Worker === ", file=sys.stderr)
        print(f"Error: {e_global_worker}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        final_exit_code = 3 # Different code for unhandled exceptions in worker's main
    finally:
        print(f"[BG Worker - __main__] Worker process exiting with code: {final_exit_code}", file=sys.stderr)
        sys.stderr.flush() # Ensure all error logs are written
        sys.exit(final_exit_code)
