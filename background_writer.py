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
import bmesh
from contextlib import contextmanager
from collections import deque
# sys is already imported

# --- Globals for Thumbnail Rendering Part (initialized by functions) ---
ICON_TEMPLATE_FILE_WORKER = None
THUMBNAIL_SIZE_WORKER = 256 # Default, overridden by arg
persistent_icon_template_scene_worker = None # Cache for loaded template scene within this worker instance
HASH_VERSION_FOR_WORKER = "v_RTX_REMIX_PBR_COMPREHENSIVE_2_CONTENT_ONLY"
global_hash_cache = {}
material_hashes = {}
g_hashing_scene_bundle = None

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

def _get_all_image_nodes_recursive(node_tree):
    if not node_tree: return
    for node in node_tree.nodes:
        if node.type == 'TEX_IMAGE':
            yield node
        elif node.type == 'GROUP' and node.node_tree:
            yield from _get_all_image_nodes_recursive(node.node_tree)

def _validate_and_recover_image_source_main(image_datablock, temp_dir_for_recovery):
    if not image_datablock:
        return True
    filepath = ""
    try:
        if image_datablock.filepath_from_user():
             filepath = bpy.path.abspath(image_datablock.filepath_from_user())
    except Exception:
        filepath = ""
    if filepath and os.path.exists(filepath):
        return True
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
            print(f"[Hash Texture Recovery - BG] Failed to recover source image for '{image_datablock.name}': {e}", file=sys.stderr)
            return False
    return True

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

@contextmanager
def temp_hashing_scene():
    """
    Provides a temporary, isolated scene for hashing in a background script.
    This is the robust method for a non-interactive process.
    """
    temp_scene = None
    original_window = bpy.context.window
    original_scene = original_window.scene if original_window else None
    created_object_names = set()
    created_data_names = {'meshes': set(), 'cameras': set()}
    
    try:
        # Create a new temporary scene for hashing operations
        temp_scene = bpy.data.scenes.new(name=f"__hashing_scene_{uuid.uuid4().hex}")
        if original_window:
            original_window.scene = temp_scene
        
        # This is SAFE to do in a background script
        temp_scene.render.engine = 'CYCLES'
        temp_scene.cycles.device = 'CPU'
        temp_scene.render.resolution_x = 1
        temp_scene.render.resolution_y = 1
        
        # Create plane and camera
        bpy.ops.mesh.primitive_plane_add(size=2, enter_editmode=False, align='WORLD', location=(0, 0, 0))
        plane = bpy.context.active_object
        plane.name = "__hashing_plane"
        created_object_names.add(plane.name)
        if plane.data: created_data_names['meshes'].add(plane.data.name)
        
        cam_data = bpy.data.cameras.new(name="__hashing_cam_data")
        created_data_names['cameras'].add(cam_data.name)
        cam_obj = bpy.data.objects.new("__hashing_cam", cam_data)
        created_object_names.add(cam_obj.name)
        temp_scene.collection.objects.link(cam_obj)
        temp_scene.camera = cam_obj
        cam_obj.location = (0, 0, 2)
        cam_data.type = 'ORTHO'
        cam_data.ortho_scale = 2.0

        yield temp_scene, plane

    finally:
        # Restore original context first
        if original_window and original_scene and original_scene.name in bpy.data.scenes:
            original_window.scene = original_scene
            
        # Safe cleanup of all temporary datablocks
        if temp_scene and temp_scene.name in bpy.data.scenes:
            bpy.data.scenes.remove(temp_scene)
        for obj_name in created_object_names:
            if obj_name in bpy.data.objects: bpy.data.objects.remove(bpy.data.objects[obj_name])
        for mesh_name in created_data_names['meshes']:
            if mesh_name in bpy.data.meshes: bpy.data.meshes.remove(bpy.data.meshes[mesh_name])
        for cam_name in created_data_names['cameras']:
            if cam_name in bpy.data.cameras: bpy.data.cameras.remove(bpy.data.cameras[cam_name])

def validate_material_uuid(mat, is_copy=False): # From background_writer.py
    if mat is None: return None
    original_uuid = mat.get("uuid", "")
    if not original_uuid or len(original_uuid) != 36 or is_copy:
        # If it's a copy or has no valid UUID, generate a new one.
        # The actual setting of this UUID on the material is handled by the caller if needed.
        return str(uuid.uuid4())
    return original_uuid

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

def _validate_and_recover_image_source_bg_worker(image_datablock, temp_dir_for_recovery):
    """
    Ensures an image datablock has a valid, on-disk source file.
    If the path is invalid but pixel data exists, it saves the data to a
    temporary directory and reloads it. This is crucial for the background
    worker to render packed or generated textures.
    Returns (True, path_to_temp_file) on recovery, or (True, None) if no recovery was needed.
    Returns (False, None) on critical failure.
    """
    if not image_datablock:
        return True, None

    filepath = ""
    try:
        # Use filepath_from_user() to respect user-set paths
        if image_datablock.filepath_from_user():
             filepath = bpy.path.abspath(image_datablock.filepath_from_user())
    except Exception:
        filepath = ""

    # If the file path is valid and exists, we're good.
    if filepath and os.path.exists(filepath):
        return True, None

    # If the file doesn't exist on disk, but Blender has the pixel data in memory...
    if not os.path.exists(filepath) and image_datablock.has_data:
        # print(f"    [Thumb BG Worker] Source image '{image_datablock.name}' has no valid file path. Recovering from memory.")
        try:
            safe_name = "".join(c for c in image_datablock.name if c.isalnum() or c in ('_', '.', '-')).strip()
            ext = ".png" # Default to PNG for recovery
            base_name, _ = os.path.splitext(safe_name)
            recovery_path = os.path.join(temp_dir_for_recovery, f"{base_name}{ext}")

            # Save a copy of the image data to the new path
            image_copy = image_datablock.copy()
            image_copy.filepath_raw = recovery_path
            image_copy.file_format = 'PNG'
            image_copy.save()
            
            # CRITICAL: Point the original image datablock to the newly saved file and reload
            image_datablock.filepath = recovery_path
            image_datablock.source = 'FILE'
            image_datablock.reload()
            
            # print(f"    [Thumb BG Worker] Successfully recovered source image '{image_datablock.name}' to '{recovery_path}'")
            return True, recovery_path

        except Exception as e:
            print(f"[Thumb BG Worker] Failed to recover source image data for '{image_datablock.name}': {e}", file=sys.stderr)
            return False, None
    
    # If path is invalid and there's no data, we can't do anything.
    return True, None

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
    temp_texture_dir = None
    try:
        temp_mat_name = f"_TEMP_RENDER_COPY_{mat_to_render.name[:30]}_{str(uuid.uuid4())[:6]}"
        temp_mat_copy = mat_to_render.copy()
        temp_mat_copy.name = temp_mat_name
        temp_mat_copy.use_fake_user = False
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

        # --- ROBUST TEXTURE VALIDATION (Logic from Remix Ingestor Addon) ---
        if temp_mat_copy.use_nodes and temp_mat_copy.node_tree:
            temp_texture_dir = tempfile.mkdtemp(prefix="bml_thumb_tex_recovery_")
            
            # Recursively find all image texture nodes
            all_image_nodes = _get_all_image_nodes_recursive(temp_mat_copy.node_tree)

            for node in all_image_nodes:
                if node.image:
                    # Validate and recover the source if necessary
                    success, recovered_path = _validate_and_recover_image_source_bg_worker(node.image, temp_texture_dir)
                    if not success:
                        print(f"[BG Worker - ItemRender] Critical failure validating/recovering texture '{node.image.name}' for material '{temp_mat_copy.name}'. Aborting render.", file=sys.stderr)
                        # The function will proceed to the finally block for cleanup
                        return False
        # --- END OF ROBUST TEXTURE VALIDATION ---

        # UV Map linking (existing logic, still necessary)
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
                            except Exception: pass 

        render_scene_for_item.render.filepath = temp_render_output_path
        bpy.ops.render.render(scene=render_scene_for_item.name, write_still=True)
        time.sleep(0.1) 

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
        # Cleanup the temporary material copy
        if temp_mat_copy and temp_mat_copy.name in bpy.data.materials:
            try: bpy.data.materials.remove(temp_mat_copy, do_unlink=True)
            except Exception: pass
        
        # Cleanup the temporary directory used for texture recovery
        if temp_texture_dir and os.path.exists(temp_texture_dir):
            try:
                shutil.rmtree(temp_texture_dir, ignore_errors=True)
            except Exception as e_clean:
                print(f"[BG Worker - ItemRender] Error cleaning up temp texture dir '{temp_texture_dir}': {e_clean}", file=sys.stderr)
      
def get_hashing_scene_bundle():
    """
    Creates and manages a persistent, isolated scene for hashing operations.
    Returns a dictionary containing the scene, plane, and hijack nodes.
    This avoids creating/destroying scenes repeatedly and handles context correctly.
    """
    global g_hashing_scene_bundle

    # --- START OF FIX: Rigorous Validation ---
    if g_hashing_scene_bundle:
        is_valid = True
        try:
            # Check each key and ensure its value is a valid Blender ID object
            if not (g_hashing_scene_bundle.get('scene') and g_hashing_scene_bundle['scene'].name in bpy.data.scenes): is_valid = False
            if not (g_hashing_scene_bundle.get('plane') and g_hashing_scene_bundle['plane'].name in bpy.data.objects): is_valid = False
            if not (g_hashing_scene_bundle.get('hijack_mat') and g_hashing_scene_bundle['hijack_mat'].name in bpy.data.materials): is_valid = False
            if not (g_hashing_scene_bundle.get('hijack_emission') and g_hashing_scene_bundle['hijack_emission'].name in g_hashing_scene_bundle['hijack_mat'].node_tree.nodes): is_valid = False
            
            if is_valid:
                return g_hashing_scene_bundle
            else:
                # If any part is invalid, the whole bundle is corrupt. Clean up and rebuild.
                print("[Hashing Scene] Bundle validation failed. Rebuilding.")
                cleanup_hashing_scene_bundle()

        except (ReferenceError, KeyError, AttributeError):
            print("[Hashing Scene] Bundle reference lost. Rebuilding.")
            cleanup_hashing_scene_bundle()
    # --- END OF FIX ---

    # Create the scene and its contents
    scene = bpy.data.scenes.new(name=f"__hashing_scene_{uuid.uuid4().hex}")
    
    window = bpy.context.window
    if not window:
        window = bpy.data.window_managers[0].windows[0]

    original_scene = window.scene
    window.scene = scene

    try:
        scene.render.engine = 'CYCLES'
        scene.cycles.device = 'CPU'
        scene.render.resolution_x = 1
        scene.render.resolution_y = 1
        scene.render.film_transparent = True
        scene.render.threads_mode = 'FIXED'
        scene.render.threads = 1

        bpy.ops.mesh.primitive_plane_add(size=2, enter_editmode=False, align='WORLD', location=(0, 0, 0))
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
    finally:
        if original_scene and original_scene.name in bpy.data.scenes:
            window.scene = original_scene
        
    return g_hashing_scene_bundle

def cleanup_hashing_scene_bundle():
    """Safely removes the hashing scene and all its contents."""
    global g_hashing_scene_bundle
    if not g_hashing_scene_bundle:
        return
        
    try:
        scene = g_hashing_scene_bundle.get("scene")
        if scene and scene.name in bpy.data.scenes:
            # Unlink from any windows to prevent context issues on removal
            for window in bpy.data.window_managers[0].windows:
                if window.scene == scene:
                    # Find any other scene to switch to
                    other_scene = next((s for s in bpy.data.scenes if s != scene), None)
                    if other_scene:
                        window.scene = other_scene
            
            # Now it should be safe to remove
            bpy.data.scenes.remove(scene, do_unlink=True)
    except (ReferenceError, KeyError, Exception) as e:
        print(f"[Hash Cleanup] Error removing hashing scene: {e}")

    g_hashing_scene_bundle = None
    
def main_render_thumbnail_batch(args_batch_render):
    """
    [DEFINITIVE FIX] Processes a batch of thumbnail tasks without re-calculating hashes.

    This version TRUSTS the hash value provided by the main addon. It no longer
    performs its own hashing, which eliminates any possible inconsistencies between
    the main session and the worker environment. This is the key to solving the
    missing thumbnail problem for local materials that have been modified but not yet saved.
    """
    global ICON_TEMPLATE_FILE_WORKER, THUMBNAIL_SIZE_WORKER, persistent_icon_template_scene_worker

    # --- Setup ---
    # Initialize paths and load the task list from the command-line arguments.
    ICON_TEMPLATE_FILE_WORKER = os.path.join(args_batch_render.addon_data_root, "icon_generation_template.blend")
    THUMBNAIL_SIZE_WORKER = args_batch_render.thumbnail_size
    json_output_payload = {"results": []}

    try:
        tasks_to_process_in_batch = json.loads(args_batch_render.tasks_json)
    except json.JSONDecodeError as e_json:
        print(f"[BG Worker] FATAL: Could not decode tasks_json: {e_json}", file=sys.stderr)
        # Attempt to create error results for all tasks if possible
        json_output_payload["error"] = "tasks_json_decode_error"
        json_output_payload["message"] = str(e_json)
        print(json.dumps(json_output_payload))
        sys.stdout.flush()
        return 1

    # --- Template Loading ---
    # Load the dedicated scene for rendering thumbnails.
    render_scene_instance_for_batch = load_icon_template_scene_bg_worker()
    if not render_scene_instance_for_batch:
        print(f"[BG Worker] FATAL: Failed to load icon template scene. Batch fails.", file=sys.stderr)
        for task_info in tasks_to_process_in_batch:
            json_output_payload["results"].append({
                "hash_value": task_info.get('hash_value', 'unknown'),
                "status": "failure", "reason": "worker_template_scene_load_failed"
            })
        print(json.dumps(json_output_payload))
        sys.stdout.flush()
        return 1

    # --- CORE FIX: Process tasks without re-hashing ---
    for task_info in tasks_to_process_in_batch:
        # Get all necessary info directly from the task dictionary sent by the main addon.
        task_hash = task_info.get('hash_value')
        task_mat_uuid = task_info.get('mat_uuid')
        task_thumb_path = task_info.get('thumb_path') # The worker will save to this exact path.

        # Basic validation of the task data.
        if not all([task_hash, task_mat_uuid, task_thumb_path]):
            json_output_payload["results"].append({
                "hash_value": task_hash or 'unknown_task',
                "status": "failure", "reason": "incomplete_task_data"
            })
            continue

        # Find the material in the blend file using its UUID.
        material_object_to_render = get_material_by_uuid_worker(task_mat_uuid)

        if not material_object_to_render:
            json_output_payload["results"].append({
                "hash_value": task_hash,
                "status": "failure", "reason": f"material_uuid_not_found_{task_mat_uuid}"
            })
            continue

        # ** NO HASHING IS PERFORMED HERE. **
        # The worker proceeds directly to rendering the found material and saves it
        # using the path/hash provided by the main addon, solving the stale file problem.
        render_success = create_sphere_preview_thumbnail_bg_worker(
            material_object_to_render, task_thumb_path, render_scene_instance_for_batch
        )

        # Report the outcome for this specific task.
        if render_success:
            json_output_payload["results"].append({
                "hash_value": task_hash,
                "status": "success", "reason": "thumbnail_rendered_successfully"
            })
        else:
            json_output_payload["results"].append({
                "hash_value": task_hash,
                "status": "failure", "reason": "render_function_returned_false"
            })

    # --- Cleanup ---
    # Clean up the template scene that was loaded for this batch.
    if persistent_icon_template_scene_worker and persistent_icon_template_scene_worker.name in bpy.data.scenes:
        try:
            bpy.data.scenes.remove(persistent_icon_template_scene_worker, do_unlink=True)
        except Exception:
            pass
    persistent_icon_template_scene_worker = None

    # Print the final JSON results to stdout for the main addon to read.
    print(json.dumps(json_output_payload))
    sys.stdout.flush()
    return 0

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
    """
    [COMPLETE & CORRECTED] Main entry point for the worker script.

    This function parses the command-line arguments to determine the requested
    operation. It dispatches to the `persistent_worker_loop` for the new,
    long-lived worker model, while retaining the ability to call other
    single-shot operations like 'merge_library'.
    """
    # This sleep can be helpful to ensure Blender is fully initialized in background mode.
    time.sleep(0.2)
    print(f"[BG Worker - Entry] Worker started. Full argv: {sys.argv}", file=sys.stderr)
    print(f"[BG Worker - Entry] Current .blend file context (if any loaded by -b): {bpy.data.filepath if bpy.data.filepath else 'Unsaved/None'}", file=sys.stderr)
    sys.stderr.flush()

    parser = argparse.ArgumentParser(description="Background worker for MaterialList Addon.")
    parser.add_argument(
        "--operation",
        choices=['merge_library', 'render_thumbnail', 'pack_to_external', 'pack_to_internal', 'render_thumbnail_persistent'],
        required=True,
        help="The operation to perform."
    )

    # Args for 'merge_library'
    parser.add_argument("--transfer", help="Path to the transfer .blend file (for merge_library).")
    parser.add_argument("--target", help="Path to the target (main) library .blend file (for merge_library).")
    parser.add_argument("--db", help="Path to the addon's SQLite database file (for merge_library timestamps).")

    # Args for 'render_thumbnail' (single-shot batch)
    parser.add_argument("--tasks-json", help="JSON string detailing a batch of thumbnail tasks.")
    parser.add_argument("--addon-data-root", help="Path to the addon's main data directory (for icon_template.blend).")
    parser.add_argument("--thumbnail-size", type=int, help="Target size for thumbnails.")

    # Args for 'pack_to_external' and 'pack_to_internal'
    parser.add_argument("--library-file", help="Path to the central material_library.blend (for identifying lib materials).")
    parser.add_argument("--external-dir-name", help="Directory name for unpacking external textures (for pack_to_external).")

    try:
        # Get arguments after '--'
        app_args = sys.argv[sys.argv.index("--") + 1:] if "--" in sys.argv else sys.argv[1:]
    except ValueError:
        app_args = sys.argv[1:]
        print(f"[BG Worker - Entry] Warning: '--' separator not found in sys.argv. Parsing from sys.argv[1:].", file=sys.stderr)

    if not app_args:
        print(f"[BG Worker - Entry] No arguments provided to worker. Exiting.", file=sys.stderr)
        parser.print_help(sys.stderr)
        return 1 # Error: No arguments

    args = parser.parse_args(app_args)

    # --- Operation Dispatcher ---

    if args.operation == 'render_thumbnail_persistent':
        # Enter the new, long-lived worker loop. This function will not return.
        persistent_worker_loop()
        return 0 # Should not be reached, as the loop is infinite until stdin closes.

    elif args.operation == 'render_thumbnail':
        # This is the original, single-shot batch operation.
        if not all([args.tasks_json, args.addon_data_root, args.thumbnail_size is not None]):
            parser.error("--tasks-json, --addon-data-root, and --thumbnail-size are required for 'render_thumbnail'.")
        return main_render_thumbnail_batch(args)

    elif args.operation == 'merge_library':
        if not all([args.transfer, args.target]):
            parser.error("--transfer and --target are required for 'merge_library'.")
        return main_merge_library(args)

    elif args.operation == 'pack_to_external':
        if not all([args.library_file, args.external_dir_name]):
            parser.error("--library-file and --external-dir-name are required for 'pack_to_external'.")
        return main_process_pack_external(args)

    elif args.operation == 'pack_to_internal':
        if not args.library_file:
            parser.error("--library-file is required for 'pack_to_internal'.")
        return main_process_pack_internal(args)

    else:
        # This case should not be reached due to 'choices' in the parser.
        print(f"[BG Worker - Entry] Unknown operation specified: {args.operation}", file=sys.stderr)
        return 1
      
def persistent_worker_loop():
    """ [CORRECTED & COMPLETE] Main loop for a persistent worker. Includes original tasks in output. """
    global ICON_TEMPLATE_FILE_WORKER, THUMBNAIL_SIZE_WORKER, persistent_icon_template_scene_worker

    current_blend_file = None
    render_scene_for_batch = None

    for line in sys.stdin:
        try:
            command = json.loads(line)
            
            # Command format: {"blend_file": "path", "tasks": [...], "addon_data_root": "path", "size": 128}
            blend_file_path = command.get("blend_file")
            tasks = command.get("tasks", [])
            addon_data = command.get("addon_data_root")
            thumb_size = command.get("size")
            
            if not all([blend_file_path, tasks, addon_data, thumb_size]):
                continue

            # Load new .blend file and template ONLY if they have changed
            if blend_file_path != current_blend_file:
                # A new file is being processed, we must clear the old state.
                bpy.ops.wm.open_mainfile(filepath=blend_file_path)
                current_blend_file = blend_file_path
                
                # Force template scene to reload for the new context
                if persistent_icon_template_scene_worker and persistent_icon_template_scene_worker.name in bpy.data.scenes:
                    try: bpy.data.scenes.remove(persistent_icon_template_scene_worker)
                    except Exception: pass
                persistent_icon_template_scene_worker = None
                render_scene_for_batch = None # Mark scene as invalid
            
            if not render_scene_for_batch:
                ICON_TEMPLATE_FILE_WORKER = os.path.join(addon_data, "icon_generation_template.blend")
                THUMBNAIL_SIZE_WORKER = thumb_size
                render_scene_for_batch = load_icon_template_scene_bg_worker()
            
            # --- THE CORE CHANGE IS HERE ---
            # The output payload must include the original task list for the main addon to process retries.
            json_output_payload = {
                "original_tasks": tasks,
                "results": []
            }

            if not render_scene_for_batch:
                for task in tasks:
                    json_output_payload["results"].append({"hash_value": task.get('hash_value'), "status": "failure", "reason": "template_load_failed"})
            else:
                for task in tasks:
                    # Use a helper that is safe to call within the worker script
                    material_to_render = get_material_by_uuid_worker(task.get('mat_uuid'))
                    
                    if not material_to_render:
                        json_output_payload["results"].append({"hash_value": task.get('hash_value'), "status": "failure", "reason": "material_not_found"})
                        continue
                    
                    success = create_sphere_preview_thumbnail_bg_worker(
                        material_to_render, task.get('thumb_path'), render_scene_for_batch
                    )
                    
                    if success and os.path.isfile(task.get('thumb_path')) and os.path.getsize(task.get('thumb_path')) > 0:
                        json_output_payload["results"].append({"hash_value": task.get('hash_value'), "status": "success"})
                    else:
                        json_output_payload["results"].append({"hash_value": task.get('hash_value'), "status": "failure", "reason": "render_call_or_file_invalid"})

            # Write the result of this entire batch to stdout
            print(json.dumps(json_output_payload))
            sys.stdout.flush()

        except json.JSONDecodeError:
            continue
        except Exception as e:
            print(f"[Persistent Worker ERROR]: {e}", file=sys.stderr)
            traceback.print_exc(file=sys.stderr)
            sys.stderr.flush()

# This is a local helper for the worker script, to avoid dependency on the main addon's cache.
def get_material_by_uuid_worker(uuid_str: str):
    if not uuid_str: return None
    mat_by_name = bpy.data.materials.get(uuid_str)
    if mat_by_name: return mat_by_name
    for m in bpy.data.materials:
        if m.get("uuid") == uuid_str:
            return m
    return None

def get_material_by_uuid_worker(uuid_str: str):
    """
    A helper function for the worker script to find a material by its UUID.
    It first checks the material's datablock name and then falls back to checking
    the 'uuid' custom property.
    """
    if not uuid_str:
        return None
    # Primary lookup by datablock name, which should be the UUID for managed materials.
    mat_by_name = bpy.data.materials.get(uuid_str)
    if mat_by_name:
        return mat_by_name
    # Fallback to iterating and checking the custom property.
    for m in bpy.data.materials:
        if m.get("uuid") == uuid_str:
            return m
    return None

if __name__ == "__main__":
    # The __main__ block remains the same, it just needs to call the new entry point.
    final_exit_code = 1
    try:
        final_exit_code = main_worker_entry() or 0
    except Exception as e:
        print(f"[BG Worker __main__] Unhandled Exception: {e}", file=sys.stderr)
        traceback.print_exc(file=sys.stderr)
        final_exit_code = 3
    finally:
        bpy.ops.wm.quit_blender()
        sys.exit(final_exit_code)
