pub mod access;
pub mod objects;

use crate::json::*;
use crate::model::*;
use crate::read::access::*;
use crate::read::objects::*;

fn strings_of(d: &Vec<JsonNode>, a: &Vec<usize>) -> Result<Vec<Vec<u8>>, ()> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match node_at(d, a[i]) {
            Some(JsonNode::String(s)) => out.push(copy_key(s)),
            _ => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

fn read_string_array(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8]) -> Result<Vec<Vec<u8>>, ()> {
    match get_array(d, o, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => strings_of(d, a),
    }
}

fn read_scenes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Scene>, GltfError> {
    let mut out: Vec<Scene> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_scene(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_scenes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Scene>, GltfError> {
    match get_array(d, o, &[b's', b'c', b'e', b'n', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_scenes_items(d, a, ext),
    }
}

fn read_nodes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Node>, GltfError> {
    let mut out: Vec<Node> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_node(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_nodes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Node>, GltfError> {
    match get_array(d, o, &[b'n', b'o', b'd', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_nodes_items(d, a, ext),
    }
}

fn read_meshes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Mesh>, GltfError> {
    let mut out: Vec<Mesh> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_mesh(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_meshes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Mesh>, GltfError> {
    match get_array(d, o, &[b'm', b'e', b's', b'h', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_meshes_items(d, a, ext),
    }
}

fn read_accessors_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Accessor>, GltfError> {
    let mut out: Vec<Accessor> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_accessor(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(out)
}

fn read_accessors(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Accessor>, GltfError> {
    match get_array(d, o, &[b'a', b'c', b'c', b'e', b's', b's', b'o', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_accessors_items(d, a, ext),
    }
}

fn read_buffer_views_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<BufferView>, GltfError> {
    let mut out: Vec<BufferView> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_buffer_view(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_buffer_views(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<BufferView>, GltfError> {
    match get_array(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_buffer_views_items(d, a, ext),
    }
}

fn read_buffers_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Buffer>, GltfError> {
    let mut out: Vec<Buffer> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_buffer(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_buffers(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Buffer>, GltfError> {
    match get_array(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_buffers_items(d, a, ext),
    }
}

fn read_materials_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Material>, GltfError> {
    let mut out: Vec<Material> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_material(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_materials(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Material>, GltfError> {
    match get_array(d, o, &[b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_materials_items(d, a, ext),
    }
}

fn read_textures_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Texture>, GltfError> {
    let mut out: Vec<Texture> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_texture(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_textures(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Texture>, GltfError> {
    match get_array(d, o, &[b't', b'e', b'x', b't', b'u', b'r', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_textures_items(d, a, ext),
    }
}

fn read_images_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Image>, GltfError> {
    let mut out: Vec<Image> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_image(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_images(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Image>, GltfError> {
    match get_array(d, o, &[b'i', b'm', b'a', b'g', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_images_items(d, a, ext),
    }
}

fn read_cameras_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Camera>, GltfError> {
    let mut out: Vec<Camera> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_camera(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_cameras(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Camera>, GltfError> {
    match get_array(d, o, &[b'c', b'a', b'm', b'e', b'r', b'a', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_cameras_items(d, a, ext),
    }
}

fn read_skins_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Skin>, GltfError> {
    let mut out: Vec<Skin> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_skin(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

fn read_skins(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Skin>, GltfError> {
    match get_array(d, o, &[b's', b'k', b'i', b'n', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_skins_items(d, a, ext),
    }
}

fn read_animations_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Animation>, GltfError> {
    let mut out: Vec<Animation> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_animation(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(out)
}

fn read_animations(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Animation>, GltfError> {
    match get_array(d, o, &[b'a', b'n', b'i', b'm', b'a', b't', b'i', b'o', b'n', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_animations_items(d, a, ext),
    }
}

fn check_sampler_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<(), GltfError> {
    let mut i = 0;
    while i < a.len() {
        match read_sampler(d, a[i], ext) {
            Ok(()) => {}
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(())
}

fn read_samplers(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<u64, GltfError> {
    match get_array(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(0),
        Ok(Some(a)) => match check_sampler_items(d, a, ext) {
            Err(e) => Err(e),
            Ok(()) => Ok(a.len() as u64),
        },
    }
}

pub fn read_gltf(doc: &JsonDoc, is_glb: bool, glb_bin_len: Option<u64>) -> Result<Gltf, GltfError> {
    let mut extensions_present: Vec<Vec<u8>> = Vec::new();
    let ext = &mut extensions_present;
    let d = &doc.nodes;
    let o = match as_object(d, doc.root) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_extensions(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let asset = match get_object(d, o, &[b'a', b's', b's', b'e', b't']) { Ok(Some(a)) => a, _ => return Err(GltfError::Invalid) };
    match check_extensions(d, asset, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    match get_string(d, asset, &[b'c', b'o', b'p', b'y', b'r', b'i', b'g', b'h', b't']) { Err(()) => return Err(GltfError::Invalid), Ok(_) => {} }
    match get_string(d, asset, &[b'g', b'e', b'n', b'e', b'r', b'a', b't', b'o', b'r']) { Err(()) => return Err(GltfError::Invalid), Ok(_) => {} }
    let (version_major, version_minor) = match get_string(d, asset, &[b'v', b'e', b'r', b's', b'i', b'o', b'n']) {
        Ok(Some(v)) => match parse_version(&v) { Some(p) => p, None => return Err(GltfError::Invalid) },
        _ => return Err(GltfError::Invalid),
    };
    let min_version = match get_string(d, asset, &[b'm', b'i', b'n', b'V', b'e', b'r', b's', b'i', b'o', b'n']) {
        Err(()) => return Err(GltfError::Invalid),
        Ok(None) => None,
        Ok(Some(v)) => match parse_version(&v) { Some(p) => Some(p), None => return Err(GltfError::Invalid) },
    };
    let extensions_used = match read_string_array(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'U', b's', b'e', b'd']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let extensions_required = match read_string_array(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'R', b'e', b'q', b'u', b'i', b'r', b'e', b'd']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let scene = match get_uint(d, o, &[b's', b'c', b'e', b'n', b'e']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };

    let scenes = match read_scenes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let nodes = match read_nodes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let meshes = match read_meshes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let accessors = match read_accessors(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let buffer_views = match read_buffer_views(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let buffers = match read_buffers(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let materials = match read_materials(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let textures = match read_textures(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let images = match read_images(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let samplers_len = match read_samplers(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let cameras = match read_cameras(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let skins = match read_skins(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let animations = match read_animations(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    Ok(Gltf {
        version_major, version_minor, min_version, extensions_used, extensions_required, scene, scenes, nodes, meshes,
        accessors, buffer_views, buffers, materials, textures, images, samplers_len, cameras, skins, animations, extensions_present, is_glb, glb_bin_len,
    })
}
