use crate::json::*;
use crate::json::number::*;
use crate::model::*;
use crate::read::access::*;

fn read_texture_info(d: &Vec<JsonNode>, id: usize, extra: u64, ext: &mut Vec<Vec<u8>>) -> Result<TextureInfo, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let index = match req_uint(d, o, &[b'i', b'n', b'd', b'e', b'x']) { Ok(v) => v, Err(()) => return Err(()) };
    let tex_coord = match get_uint(d, o, &[b't', b'e', b'x', b'C', b'o', b'o', b'r', b'd']) {
        Ok(Some(v)) => v,
        Ok(None) => 0,
        Err(()) => return Err(()),
    };
    if extra == 1 {
        match check_number(d, o, &[b's', b'c', b'a', b'l', b'e']) { Err(()) => return Err(()), Ok(_) => {} }
    } else if extra == 2 {
        match check_number(d, o, &[b's', b't', b'r', b'e', b'n', b'g', b't', b'h']) { Err(()) => return Err(()), Ok(_) => {} }
    }
    Ok(TextureInfo { index, tex_coord })
}

fn opt_texture_info(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8], extra: u64, ext: &mut Vec<Vec<u8>>) -> Result<Option<TextureInfo>, ()> {
    match find_member(o, key) {
        None => Ok(None),
        Some(i) => match read_texture_info(d, o[i].value, extra, ext) {
            Ok(t) => Ok(Some(t)),
            Err(()) => Err(()),
        },
    }
}

pub(crate) fn read_material(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Material, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let mut base_color_texture: Option<TextureInfo> = None;
    let mut metallic_roughness_texture: Option<TextureInfo> = None;
    match get_object(d, o, &[b'p', b'b', b'r', b'M', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'R', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's']) {
        Err(()) => return Err(()),
        Ok(None) => {}
        Ok(Some(p)) => {
            match check_extensions(d, p, ext) { Err(()) => return Err(()), Ok(()) => {} }
            match check_number_array(d, p, &[b'b', b'a', b's', b'e', b'C', b'o', b'l', b'o', b'r', b'F', b'a', b'c', b't', b'o', b'r'], 4) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'm', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'F', b'a', b'c', b't', b'o', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'r', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's', b'F', b'a', b'c', b't', b'o', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
            base_color_texture = match opt_texture_info(d, p, &[b'b', b'a', b's', b'e', b'C', b'o', b'l', b'o', b'r', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
            metallic_roughness_texture = match opt_texture_info(d, p, &[b'm', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'R', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
        }
    }
    let normal_texture = match opt_texture_info(d, o, &[b'n', b'o', b'r', b'm', b'a', b'l', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 1, ext) { Ok(t) => t, Err(()) => return Err(()) };
    let occlusion_texture = match opt_texture_info(d, o, &[b'o', b'c', b'c', b'l', b'u', b's', b'i', b'o', b'n', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 2, ext) { Ok(t) => t, Err(()) => return Err(()) };
    let emissive_texture = match opt_texture_info(d, o, &[b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
    match check_number_array(d, o, &[b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'F', b'a', b'c', b't', b'o', b'r'], 3) { Err(()) => return Err(()), Ok(_) => {} }
    match get_string(d, o, &[b'a', b'l', b'p', b'h', b'a', b'M', b'o', b'd', b'e']) { Err(()) => return Err(()), Ok(_) => {} }
    match check_number(d, o, &[b'a', b'l', b'p', b'h', b'a', b'C', b'u', b't', b'o', b'f', b'f']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_bool(d, o, &[b'd', b'o', b'u', b'b', b'l', b'e', b'S', b'i', b'd', b'e', b'd']) { Err(()) => return Err(()), Ok(_) => {} }
    Ok(Material { base_color_texture, metallic_roughness_texture, normal_texture, occlusion_texture, emissive_texture })
}

fn attribute_entries(d: &Vec<JsonNode>, o: &Vec<Member>) -> Result<Vec<Attribute>, ()> {
    let mut out: Vec<Attribute> = Vec::new();
    let mut i = 0;
    while i < o.len() {
        if is_last_member(o, i) {
            match node_at(d, o[i].value) {
                Some(JsonNode::Number(n)) => match number_to_u64(n) {
                    Some(v) => out.push(Attribute { name: copy_key(&o[i].key), accessor: v }),
                    None => return Err(()),
                },
                _ => return Err(()),
            }
        }
        i += 1;
    }
    Ok(out)
}

fn read_attribute_map(d: &Vec<JsonNode>, id: usize, allow_empty: bool) -> Result<Vec<Attribute>, ()> {
    match as_object(d, id) {
        Err(()) => Err(()),
        Ok(o) => {
            if o.len() == 0 && !allow_empty {
                Err(())
            } else {
                attribute_entries(d, o)
            }
        }
    }
}

fn read_primitive(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Primitive, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let attributes = match find_member(o, &[b'a', b't', b't', b'r', b'i', b'b', b'u', b't', b'e', b's']) {
        None => return Err(()),
        Some(i) => match read_attribute_map(d, o[i].value, false) { Ok(a) => a, Err(()) => return Err(()) },
    };
    let indices = match get_uint(d, o, &[b'i', b'n', b'd', b'i', b'c', b'e', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    let material = match get_uint(d, o, &[b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l']) { Ok(v) => v, Err(()) => return Err(()) };
    let mode = match get_uint(d, o, &[b'm', b'o', b'd', b'e']) { Ok(Some(v)) => v, Ok(None) => 4, Err(()) => return Err(()) };
    let targets = match get_array(d, o, &[b't', b'a', b'r', b'g', b'e', b't', b's']) {
        Err(()) => return Err(()),
        Ok(None) => Vec::new(),
        Ok(Some(a)) => match read_target_items(d, a) {
            Ok(t) => t,
            Err(()) => return Err(()),
        },
    };
    Ok(Primitive { attributes, indices, material, mode, targets })
}

fn read_target_items(d: &Vec<JsonNode>, a: &Vec<usize>) -> Result<Vec<Vec<Attribute>>, ()> {
    let mut out: Vec<Vec<Attribute>> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_attribute_map(d, a[i], true) {
            Ok(t) => out.push(t),
            Err(()) => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

fn read_primitive_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Primitive>, ()> {
    let mut out: Vec<Primitive> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_primitive(d, a[i], ext) {
            Ok(p) => out.push(p),
            Err(()) => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

pub(crate) fn read_mesh(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Mesh, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let primitives = match get_array(d, o, &[b'p', b'r', b'i', b'm', b'i', b't', b'i', b'v', b'e', b's']) {
        Ok(Some(a)) => match read_primitive_items(d, a, ext) {
            Ok(p) => p,
            Err(()) => return Err(()),
        },
        _ => return Err(()),
    };
    let weights_len = match get_number_array_len(d, o, &[b'w', b'e', b'i', b'g', b'h', b't', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Mesh { primitives, weights_len })
}

pub(crate) fn read_node(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Node, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let children = match get_uint_array(d, o, &[b'c', b'h', b'i', b'l', b'd', b'r', b'e', b'n']) {
        Ok(Some(c)) => c,
        Ok(None) => Vec::new(),
        Err(()) => return Err(()),
    };
    let mesh = match get_uint(d, o, &[b'm', b'e', b's', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let camera = match get_uint(d, o, &[b'c', b'a', b'm', b'e', b'r', b'a']) { Ok(v) => v, Err(()) => return Err(()) };
    let skin = match get_uint(d, o, &[b's', b'k', b'i', b'n']) { Ok(v) => v, Err(()) => return Err(()) };
    let has_matrix = match check_number_array(d, o, &[b'm', b'a', b't', b'r', b'i', b'x'], 16) { Ok(b) => b, Err(()) => return Err(()) };
    let has_t = match check_number_array(d, o, &[b't', b'r', b'a', b'n', b's', b'l', b'a', b't', b'i', b'o', b'n'], 3) { Ok(b) => b, Err(()) => return Err(()) };
    let has_r = match check_number_array(d, o, &[b'r', b'o', b't', b'a', b't', b'i', b'o', b'n'], 4) { Ok(b) => b, Err(()) => return Err(()) };
    let has_s = match check_number_array(d, o, &[b's', b'c', b'a', b'l', b'e'], 3) { Ok(b) => b, Err(()) => return Err(()) };
    let weights_len = match get_number_array_len(d, o, &[b'w', b'e', b'i', b'g', b'h', b't', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Node { children, mesh, camera, skin, has_matrix, has_trs: has_t || has_r || has_s, weights_len })
}

pub(crate) fn read_scene(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Scene, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let nodes = match get_uint_array(d, o, &[b'n', b'o', b'd', b'e', b's']) {
        Ok(Some(c)) => c,
        Ok(None) => Vec::new(),
        Err(()) => return Err(()),
    };
    Ok(Scene { nodes })
}

fn type_components(t: &Vec<u8>) -> Option<(u64, bool)> {
    if bytes_eq(t, &[b'S', b'C', b'A', b'L', b'A', b'R']) {
        Some((1, false))
    } else if bytes_eq(t, &[b'V', b'E', b'C', b'2']) {
        Some((2, false))
    } else if bytes_eq(t, &[b'V', b'E', b'C', b'3']) {
        Some((3, false))
    } else if bytes_eq(t, &[b'V', b'E', b'C', b'4']) {
        Some((4, false))
    } else if bytes_eq(t, &[b'M', b'A', b'T', b'2']) {
        Some((4, true))
    } else if bytes_eq(t, &[b'M', b'A', b'T', b'3']) {
        Some((9, true))
    } else if bytes_eq(t, &[b'M', b'A', b'T', b'4']) {
        Some((16, true))
    } else {
        None
    }
}

fn read_sparse(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Sparse, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let count = match req_uint(d, o, &[b'c', b'o', b'u', b'n', b't']) { Ok(v) => v, Err(()) => return Err(()) };
    let ind = match get_object(d, o, &[b'i', b'n', b'd', b'i', b'c', b'e', b's']) { Ok(Some(x)) => x, _ => return Err(()) };
    match check_extensions(d, ind, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let indices_buffer_view = match req_uint(d, ind, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let indices_byte_offset = match get_uint(d, ind, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    let indices_component_type = match req_uint(d, ind, &[b'c', b'o', b'm', b'p', b'o', b'n', b'e', b'n', b't', b'T', b'y', b'p', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let val = match get_object(d, o, &[b'v', b'a', b'l', b'u', b'e', b's']) { Ok(Some(x)) => x, _ => return Err(()) };
    match check_extensions(d, val, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let values_buffer_view = match req_uint(d, val, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let values_byte_offset = match get_uint(d, val, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    Ok(Sparse { count, indices_buffer_view, indices_byte_offset, indices_component_type, values_buffer_view, values_byte_offset })
}

pub(crate) fn read_accessor(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Accessor, GltfError> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let buffer_view = match get_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let byte_offset = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let component_type = match req_uint(d, o, &[b'c', b'o', b'm', b'p', b'o', b'n', b'e', b'n', b't', b'T', b'y', b'p', b'e']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let normalized = match get_bool(d, o, &[b'n', b'o', b'r', b'm', b'a', b'l', b'i', b'z', b'e', b'd']) { Ok(Some(b)) => b, Ok(None) => false, Err(()) => return Err(GltfError::Invalid) };
    let count = match req_uint(d, o, &[b'c', b'o', b'u', b'n', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let t = match get_string(d, o, &[b't', b'y', b'p', b'e']) { Ok(Some(t)) => t, _ => return Err(GltfError::Invalid) };
    let (components, is_matrix) = match type_components(&t) { Some(c) => c, None => return Err(GltfError::Unsupported) };
    let min_len = match get_number_array_len(d, o, &[b'm', b'i', b'n']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let max_len = match get_number_array_len(d, o, &[b'm', b'a', b'x']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let sparse = match find_member(o, &[b's', b'p', b'a', b'r', b's', b'e']) {
        None => None,
        Some(i) => match read_sparse(d, o[i].value, ext) { Ok(s) => Some(s), Err(()) => return Err(GltfError::Invalid) },
    };
    Ok(Accessor { buffer_view, byte_offset, component_type, normalized, count, components, is_matrix, min_len, max_len, sparse })
}

pub(crate) fn read_buffer_view(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<BufferView, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let buffer = match req_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let byte_offset = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    let byte_length = match req_uint(d, o, &[b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let byte_stride = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'S', b't', b'r', b'i', b'd', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let target = match get_uint(d, o, &[b't', b'a', b'r', b'g', b'e', b't']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(BufferView { buffer, byte_offset, byte_length, byte_stride, target })
}

pub(crate) fn read_buffer(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Buffer, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let byte_length = match req_uint(d, o, &[b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let uri = match get_string(d, o, &[b'u', b'r', b'i']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Buffer { byte_length, uri })
}

pub(crate) fn read_image(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Image, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let uri = match get_string(d, o, &[b'u', b'r', b'i']) { Ok(v) => v, Err(()) => return Err(()) };
    let buffer_view = match get_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let has_mime_type = match get_string(d, o, &[b'm', b'i', b'm', b'e', b'T', b'y', b'p', b'e']) { Ok(v) => v.is_some(), Err(()) => return Err(()) };
    Ok(Image { uri, buffer_view, has_mime_type })
}

pub(crate) fn read_texture(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Texture, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let sampler = match get_uint(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let source = match get_uint(d, o, &[b's', b'o', b'u', b'r', b'c', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Texture { sampler, source })
}

pub(crate) fn read_sampler(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    match get_uint(d, o, &[b'm', b'a', b'g', b'F', b'i', b'l', b't', b'e', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'm', b'i', b'n', b'F', b'i', b'l', b't', b'e', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'w', b'r', b'a', b'p', b'S']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'w', b'r', b'a', b'p', b'T']) { Err(()) => return Err(()), Ok(_) => {} }
    Ok(())
}

fn check_perspective(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<bool, ()> {
    match get_object(d, o, &[b'p', b'e', b'r', b's', b'p', b'e', b'c', b't', b'i', b'v', b'e']) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(p)) => {
            match check_extensions(d, p, ext) { Err(()) => return Err(()), Ok(()) => {} }
            match check_number(d, p, &[b'a', b's', b'p', b'e', b'c', b't', b'R', b'a', b't', b'i', b'o']) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'y', b'f', b'o', b'v']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'z', b'f', b'a', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'z', b'n', b'e', b'a', b'r']) { Ok(true) => {} _ => return Err(()) }
            Ok(true)
        }
    }
}

fn check_orthographic(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<bool, ()> {
    match get_object(d, o, &[b'o', b'r', b't', b'h', b'o', b'g', b'r', b'a', b'p', b'h', b'i', b'c']) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(p)) => {
            match check_extensions(d, p, ext) { Err(()) => return Err(()), Ok(()) => {} }
            match check_number(d, p, &[b'x', b'm', b'a', b'g']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'y', b'm', b'a', b'g']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'z', b'f', b'a', b'r']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'z', b'n', b'e', b'a', b'r']) { Ok(true) => {} _ => return Err(()) }
            Ok(true)
        }
    }
}

pub(crate) fn read_camera(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Camera, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let t = match get_string(d, o, &[b't', b'y', b'p', b'e']) { Ok(Some(t)) => t, _ => return Err(()) };
    let kind = if bytes_eq(&t, &[b'p', b'e', b'r', b's', b'p', b'e', b'c', b't', b'i', b'v', b'e']) {
        CAMERA_PERSPECTIVE
    } else if bytes_eq(&t, &[b'o', b'r', b't', b'h', b'o', b'g', b'r', b'a', b'p', b'h', b'i', b'c']) {
        CAMERA_ORTHOGRAPHIC
    } else {
        KIND_OTHER
    };
    let has_perspective = match check_perspective(d, o, ext) { Ok(b) => b, Err(()) => return Err(()) };
    let has_orthographic = match check_orthographic(d, o, ext) { Ok(b) => b, Err(()) => return Err(()) };
    Ok(Camera { kind, has_perspective, has_orthographic })
}

pub(crate) fn read_skin(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Skin, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let joints = match get_uint_array(d, o, &[b'j', b'o', b'i', b'n', b't', b's']) { Ok(Some(c)) => c, _ => return Err(()) };
    let skeleton = match get_uint(d, o, &[b's', b'k', b'e', b'l', b'e', b't', b'o', b'n']) { Ok(v) => v, Err(()) => return Err(()) };
    let inverse_bind_matrices = match get_uint(d, o, &[b'i', b'n', b'v', b'e', b'r', b's', b'e', b'B', b'i', b'n', b'd', b'M', b'a', b't', b'r', b'i', b'c', b'e', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Skin { joints, skeleton, inverse_bind_matrices })
}

fn read_channel(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Channel, ()> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let sampler = match req_uint(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let t = match get_object(d, o, &[b't', b'a', b'r', b'g', b'e', b't']) { Ok(Some(t)) => t, _ => return Err(()) };
    match check_extensions(d, t, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let node = match get_uint(d, t, &[b'n', b'o', b'd', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let p = match get_string(d, t, &[b'p', b'a', b't', b'h']) { Ok(Some(p)) => p, _ => return Err(()) };
    let path = if bytes_eq(&p, &[b't', b'r', b'a', b'n', b's', b'l', b'a', b't', b'i', b'o', b'n']) {
        PATH_TRANSLATION
    } else if bytes_eq(&p, &[b'r', b'o', b't', b'a', b't', b'i', b'o', b'n']) {
        PATH_ROTATION
    } else if bytes_eq(&p, &[b's', b'c', b'a', b'l', b'e']) {
        PATH_SCALE
    } else if bytes_eq(&p, &[b'w', b'e', b'i', b'g', b'h', b't', b's']) {
        PATH_WEIGHTS
    } else {
        KIND_OTHER
    };
    Ok(Channel { sampler, node, path })
}

fn read_animation_sampler(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<AnimationSampler, GltfError> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_extensions(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let input = match req_uint(d, o, &[b'i', b'n', b'p', b'u', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let output = match req_uint(d, o, &[b'o', b'u', b't', b'p', b'u', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let interpolation = match get_string(d, o, &[b'i', b'n', b't', b'e', b'r', b'p', b'o', b'l', b'a', b't', b'i', b'o', b'n']) {
        Err(()) => return Err(GltfError::Invalid),
        Ok(None) => INTERP_LINEAR,
        Ok(Some(s)) => {
            if bytes_eq(&s, &[b'L', b'I', b'N', b'E', b'A', b'R']) {
                INTERP_LINEAR
            } else if bytes_eq(&s, &[b'S', b'T', b'E', b'P']) {
                INTERP_STEP
            } else if bytes_eq(&s, &[b'C', b'U', b'B', b'I', b'C', b'S', b'P', b'L', b'I', b'N', b'E']) {
                INTERP_CUBICSPLINE
            } else {
                return Err(GltfError::Unsupported);
            }
        }
    };
    Ok(AnimationSampler { input, output, interpolation })
}

fn read_channel_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Channel>, ()> {
    let mut out: Vec<Channel> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_channel(d, a[i], ext) {
            Ok(c) => out.push(c),
            Err(()) => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

fn read_animation_sampler_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<AnimationSampler>, GltfError> {
    let mut out: Vec<AnimationSampler> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match read_animation_sampler(d, a[i], ext) {
            Ok(s) => out.push(s),
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(out)
}

pub(crate) fn read_animation(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Animation, GltfError> {
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let channels = match get_array(d, o, &[b'c', b'h', b'a', b'n', b'n', b'e', b'l', b's']) {
        Ok(Some(a)) => match read_channel_items(d, a, ext) {
            Ok(c) => c,
            Err(()) => return Err(GltfError::Invalid),
        },
        _ => return Err(GltfError::Invalid),
    };
    let samplers = match get_array(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']) {
        Ok(Some(a)) => match read_animation_sampler_items(d, a, ext) {
            Ok(s) => s,
            Err(e) => return Err(e),
        },
        _ => return Err(GltfError::Invalid),
    };
    Ok(Animation { channels, samplers })
}

fn parse_version_part(s: &Vec<u8>, start: usize, end: usize) -> Option<u64> {
    if start >= end || end - start > 9 {
        return None;
    }
    if s[start] == b'0' && end - start > 1 {
        return None;
    }
    let mut v: u64 = 0;
    let mut i = start;
    while i < end {
        if s[i] < b'0' || s[i] > b'9' {
            return None;
        }
        v = v * 10 + (s[i] - b'0') as u64;
        i += 1;
    }
    Some(v)
}

pub(crate) fn parse_version(s: &Vec<u8>) -> Option<(u64, u64)> {
    let mut dot = 0;
    while dot < s.len() && s[dot] != b'.' {
        dot += 1;
    }
    if dot >= s.len() {
        return None;
    }
    match parse_version_part(s, 0, dot) {
        None => None,
        Some(a) => match parse_version_part(s, dot + 1, s.len()) {
            None => None,
            Some(b) => Some((a, b)),
        },
    }
}
