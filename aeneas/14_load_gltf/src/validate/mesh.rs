use crate::model::*;
use crate::validate::util::*;

pub const SEM_OTHER: u64 = 0;

pub const SEM_POSITION: u64 = 1;

pub const SEM_NORMAL: u64 = 2;

pub const SEM_TANGENT: u64 = 3;

pub const SEM_TEXCOORD: u64 = 4;

pub const SEM_COLOR: u64 = 5;

pub const SEM_JOINTS: u64 = 6;

pub const SEM_WEIGHTS: u64 = 7;

pub const SEM_INVALID: u64 = 8;

pub(crate) fn starts_with(s: &Vec<u8>, p: &[u8]) -> bool {
    if s.len() < p.len() {
        return false;
    }
    let mut i = 0;
    while i < p.len() {
        if s[i] != p[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn decimal_digits(s: &Vec<u8>, start: usize) -> Option<u64> {
    let mut v: u64 = 0;
    let mut i = start;
    while i < s.len() {
        if s[i] < b'0' || s[i] > b'9' {
            return None;
        }
        v = v * 10 + (s[i] - b'0') as u64;
        i += 1;
    }
    Some(v)
}

fn parse_set_index(s: &Vec<u8>, start: usize) -> Option<u64> {
    let n = s.len() - start;
    if n == 0 || n > 9 || (s[start] == b'0' && n > 1) {
        None
    } else {
        decimal_digits(s, start)
    }
}

pub fn semantic(name: &Vec<u8>) -> (u64, u64) {
    if bytes_eq(name, &[b'P', b'O', b'S', b'I', b'T', b'I', b'O', b'N']) {
        return (SEM_POSITION, 0);
    }
    if bytes_eq(name, &[b'N', b'O', b'R', b'M', b'A', b'L']) {
        return (SEM_NORMAL, 0);
    }
    if bytes_eq(name, &[b'T', b'A', b'N', b'G', b'E', b'N', b'T']) {
        return (SEM_TANGENT, 0);
    }
    let (kind, plen) = if starts_with(name, &[b'T', b'E', b'X', b'C', b'O', b'O', b'R', b'D', b'_']) {
        (SEM_TEXCOORD, 9)
    } else if starts_with(name, &[b'C', b'O', b'L', b'O', b'R', b'_']) {
        (SEM_COLOR, 6)
    } else if starts_with(name, &[b'J', b'O', b'I', b'N', b'T', b'S', b'_']) {
        (SEM_JOINTS, 7)
    } else if starts_with(name, &[b'W', b'E', b'I', b'G', b'H', b'T', b'S', b'_']) {
        (SEM_WEIGHTS, 8)
    } else {
        return (SEM_OTHER, 0);
    };
    match parse_set_index(name, plen) {
        Some(n) => (kind, n),
        None => (SEM_INVALID, 0),
    }
}

fn attribute_type_ok(kind: u64, a: &Accessor, morph: bool) -> bool {
    if kind == SEM_OTHER {
        true
    } else if a.is_matrix {
        false
    } else if kind == SEM_POSITION || kind == SEM_NORMAL {
        a.components == 3 && float32(a)
    } else if kind == SEM_TANGENT {
        a.components == (if morph { 3 } else { 4 }) && float32(a)
    } else if kind == SEM_TEXCOORD {
        a.components == 2 && (float32(a) || unorm8_16(a) || (morph && snorm8_16(a)))
    } else if kind == SEM_COLOR {
        (a.components == 3 || a.components == 4) && (float32(a) || unorm8_16(a) || (morph && snorm8_16(a)))
    } else if kind == SEM_JOINTS {
        !morph && a.components == 4 && !a.normalized && (a.component_type == 5121 || a.component_type == 5123)
    } else if kind == SEM_WEIGHTS {
        !morph && a.components == 4 && (float32(a) || unorm8_16(a))
    } else {
        false
    }
}

pub(crate) fn has_semantic(attrs: &Vec<Attribute>, kind: u64, set: u64) -> bool {
    let mut i = 0;
    while i < attrs.len() {
        let (k, n) = semantic(&attrs[i].name);
        if k == kind && n == set {
            return true;
        }
        i += 1;
    }
    false
}

fn has_name(attrs: &Vec<Attribute>, name: &Vec<u8>) -> bool {
    let mut i = 0;
    while i < attrs.len() {
        if bytes_eq(&attrs[i].name, name) {
            return true;
        }
        i += 1;
    }
    false
}

fn attribute_ok(g: &Gltf, attrs: &Vec<Attribute>, i: usize, morph: bool, base: &Vec<Attribute>, count: u64) -> bool {
    let acc = &g.accessors[attrs[i].accessor as usize];
    let (kind, set) = semantic(&attrs[i].name);
    kind != SEM_INVALID
        && attribute_type_ok(kind, acc, morph)
        && acc.count == count
        && (!morph || has_name(base, &attrs[i].name))
        && (kind != SEM_POSITION || (acc.min_len.is_some() && acc.max_len.is_some()))
        && (kind < SEM_TEXCOORD || kind > SEM_WEIGHTS || set == 0 || has_semantic(attrs, kind, set - 1))
        && (kind != SEM_JOINTS || has_semantic(attrs, SEM_WEIGHTS, set))
        && (kind != SEM_WEIGHTS || has_semantic(attrs, SEM_JOINTS, set))
}

fn attributes_ok(g: &Gltf, attrs: &Vec<Attribute>, morph: bool, base: &Vec<Attribute>, count: u64) -> bool {
    let mut i = 0;
    while i < attrs.len() {
        if !attribute_ok(g, attrs, i, morph, base, count) {
            return false;
        }
        i += 1;
    }
    true
}

fn targets_ok(g: &Gltf, p: &Primitive, count: u64) -> bool {
    let mut t = 0;
    while t < p.targets.len() {
        if !attributes_ok(g, &p.targets[t], true, &p.attributes, count) {
            return false;
        }
        t += 1;
    }
    true
}

pub(crate) fn morph_target_count(m: &Mesh) -> u64 {
    let mut i = 0;
    while i < m.primitives.len() {
        if m.primitives[i].targets.len() > 0 {
            return m.primitives[i].targets.len() as u64;
        }
        i += 1;
    }
    0
}

fn vertex_count_ok(mode: u64, n: u64) -> bool {
    if n == 0 {
        false
    } else if mode == 0 {
        true
    } else if mode == 1 {
        n % 2 == 0
    } else if mode == 2 || mode == 3 {
        n >= 2
    } else if mode == 4 {
        n % 3 == 0
    } else {
        n >= 3
    }
}

fn texcoord_ok(t: &Option<TextureInfo>, attrs: &Vec<Attribute>) -> bool {
    match t {
        None => true,
        Some(ti) => has_semantic(attrs, SEM_TEXCOORD, ti.tex_coord),
    }
}

fn material_texcoords_ok(mat: &Material, attrs: &Vec<Attribute>) -> bool {
    texcoord_ok(&mat.base_color_texture, attrs) && texcoord_ok(&mat.metallic_roughness_texture, attrs) && texcoord_ok(&mat.normal_texture, attrs) && texcoord_ok(&mat.occlusion_texture, attrs) && texcoord_ok(&mat.emissive_texture, attrs)
}

fn index_accessor_ok(a: &Accessor) -> bool {
    a.components == 1 && !a.is_matrix && !a.normalized && (a.component_type == 5121 || a.component_type == 5123 || a.component_type == 5125)
}

fn primitive_ok(g: &Gltf, p: &Primitive, targets: u64) -> bool {
    if p.attributes.len() == 0 || (p.targets.len() > 0 && p.targets.len() as u64 != targets) {
        return false;
    }
    let count = g.accessors[p.attributes[0].accessor as usize].count;
    if !attributes_ok(g, &p.attributes, false, &p.attributes, count) || !targets_ok(g, p, count) {
        return false;
    }
    let vertices = match p.indices {
        None => count,
        Some(ix) => g.accessors[ix as usize].count,
    };
    let indices_ok = match p.indices {
        None => true,
        Some(ix) => index_accessor_ok(&g.accessors[ix as usize]),
    };
    let material_ok = match p.material {
        None => true,
        Some(m) => material_texcoords_ok(&g.materials[m as usize], &p.attributes),
    };
    indices_ok && vertex_count_ok(p.mode, vertices) && material_ok
}

fn primitives_ok(g: &Gltf, mesh: &Mesh, targets: u64) -> bool {
    let mut j = 0;
    while j < mesh.primitives.len() {
        if !primitive_ok(g, &mesh.primitives[j], targets) {
            return false;
        }
        j += 1;
    }
    true
}

fn mesh_ok(g: &Gltf, mesh: &Mesh) -> bool {
    let targets = morph_target_count(mesh);
    let weights_ok = match mesh.weights_len {
        None => true,
        Some(w) => w == targets,
    };
    weights_ok && primitives_ok(g, mesh, targets)
}

pub(crate) fn meshes_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.meshes.len() {
        if !mesh_ok(g, &g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}
