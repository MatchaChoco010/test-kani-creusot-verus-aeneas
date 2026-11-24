use crate::model::*;

pub fn component_size(ct: u64) -> u64 {
    if ct == 5120 || ct == 5121 {
        1
    } else if ct == 5122 || ct == 5123 {
        2
    } else {
        4
    }
}

pub fn element_size(a: &Accessor) -> u64 {
    let cs = component_size(a.component_type);
    if a.is_matrix {
        let rows = if a.components == 4 { 2 } else if a.components == 9 { 3 } else { 4 };
        (cs * rows + 3) / 4 * 4 * rows
    } else {
        a.components * cs
    }
}

fn fits(offset: u64, count: u64, stride: u64, size: u64, limit: u64) -> bool {
    match (count - 1).checked_mul(stride) {
        None => false,
        Some(x) => match offset.checked_add(x) {
            None => false,
            Some(y) => match y.checked_add(size) {
                None => false,
                Some(z) => z <= limit,
            },
        },
    }
}

pub struct Roles {
    pub attribute: Vec<bool>,
    pub index: Vec<bool>,
    pub ibm: Vec<bool>,
}

fn false_vec(n: usize) -> Vec<bool> {
    let mut v: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(false);
        i += 1;
    }
    v
}

fn zero_vec(n: usize) -> Vec<u64> {
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

fn mark_attributes(roles: &mut Vec<bool>, attrs: &Vec<Attribute>) {
    let mut i = 0;
    while i < attrs.len() {
        roles[attrs[i].accessor as usize] = true;
        i += 1;
    }
}

fn mark_primitive(r: &mut Roles, p: &Primitive) {
    mark_attributes(&mut r.attribute, &p.attributes);
    let mut t = 0;
    while t < p.targets.len() {
        mark_attributes(&mut r.attribute, &p.targets[t]);
        t += 1;
    }
    match p.indices {
        None => {}
        Some(ix) => r.index[ix as usize] = true,
    }
}

fn mark_mesh(r: &mut Roles, m: &Mesh) {
    let mut j = 0;
    while j < m.primitives.len() {
        mark_primitive(r, &m.primitives[j]);
        j += 1;
    }
}

fn mark_meshes(r: &mut Roles, g: &Gltf) {
    let mut i = 0;
    while i < g.meshes.len() {
        mark_mesh(r, &g.meshes[i]);
        i += 1;
    }
}

fn mark_skins(r: &mut Roles, g: &Gltf) {
    let mut i = 0;
    while i < g.skins.len() {
        match g.skins[i].inverse_bind_matrices {
            None => {}
            Some(m) => r.ibm[m as usize] = true,
        }
        i += 1;
    }
}

pub fn accessor_roles(g: &Gltf) -> Roles {
    let n = g.accessors.len();
    let mut r = Roles { attribute: false_vec(n), index: false_vec(n), ibm: false_vec(n) };
    mark_meshes(&mut r, g);
    mark_skins(&mut r, g);
    r
}

pub struct ViewUse {
    pub attribute: Vec<bool>,
    pub attribute_count: Vec<u64>,
    pub index: Vec<bool>,
    pub ibm: Vec<bool>,
    pub sparse: Vec<bool>,
    pub image: Vec<bool>,
    pub animation: Vec<bool>,
    pub accessor: Vec<bool>,
    pub non_attribute: Vec<bool>,
}

fn mark_accessor_views(u: &mut ViewUse, g: &Gltf, roles: &Roles) {
    let mut i = 0;
    while i < g.accessors.len() {
        let a = &g.accessors[i];
        match a.buffer_view {
            None => {}
            Some(bv) => {
                let b = bv as usize;
                u.accessor[b] = true;
                if !roles.attribute[i] {
                    u.non_attribute[b] = true;
                }
                if roles.attribute[i] {
                    u.attribute[b] = true;
                    u.attribute_count[b] = u.attribute_count[b].saturating_add(1);
                }
                if roles.index[i] {
                    u.index[b] = true;
                }
                if roles.ibm[i] {
                    u.ibm[b] = true;
                }
            }
        }
        match &a.sparse {
            None => {}
            Some(s) => {
                u.sparse[s.indices_buffer_view as usize] = true;
                u.sparse[s.values_buffer_view as usize] = true;
            }
        }
        i += 1;
    }
}

fn mark_image_views(u: &mut ViewUse, g: &Gltf) {
    let mut i = 0;
    while i < g.images.len() {
        match g.images[i].buffer_view {
            None => {}
            Some(bv) => u.image[bv as usize] = true,
        }
        i += 1;
    }
}

fn mark_accessor_view(v: &mut Vec<bool>, g: &Gltf, accessor: u64) {
    match g.accessors[accessor as usize].buffer_view {
        None => {}
        Some(bv) => v[bv as usize] = true,
    }
}

fn mark_animation_views(u: &mut ViewUse, g: &Gltf, an: &Animation) {
    let mut s = 0;
    while s < an.samplers.len() {
        mark_accessor_view(&mut u.animation, g, an.samplers[s].input);
        mark_accessor_view(&mut u.animation, g, an.samplers[s].output);
        s += 1;
    }
}

fn mark_animations_views(u: &mut ViewUse, g: &Gltf) {
    let mut i = 0;
    while i < g.animations.len() {
        mark_animation_views(u, g, &g.animations[i]);
        i += 1;
    }
}

pub fn view_use(g: &Gltf, roles: &Roles) -> ViewUse {
    let n = g.buffer_views.len();
    let mut u = ViewUse {
        attribute: false_vec(n),
        attribute_count: zero_vec(n),
        index: false_vec(n),
        ibm: false_vec(n),
        sparse: false_vec(n),
        image: false_vec(n),
        animation: false_vec(n),
        accessor: false_vec(n),
        non_attribute: false_vec(n),
    };
    mark_accessor_views(&mut u, g, roles);
    mark_image_views(&mut u, g);
    mark_animations_views(&mut u, g);
    u
}

fn buffer_view_ok(g: &Gltf, u: &ViewUse, b: usize) -> bool {
    let bv = &g.buffer_views[b];
    let in_buffer = match bv.byte_offset.checked_add(bv.byte_length) {
        None => false,
        Some(end) => end <= g.buffers[bv.buffer as usize].byte_length,
    };
    let attr = u.attribute[b];
    let idx = u.index[b];
    let ibm = u.ibm[b];
    let other = u.animation[b] || u.sparse[b];
    let image = u.image[b];
    let kinds = (attr as u64) + (idx as u64) + (ibm as u64) + (other as u64) + (image as u64);
    let one_kind = !(attr || idx || ibm || image) || kinds <= 1;
    let image_alone = !image || (!u.accessor[b] && !u.sparse[b]);
    let non_vertex = idx || ibm || other || image || u.non_attribute[b];
    bv.byte_length > 0
        && in_buffer
        && one_kind
        && image_alone
        && stride_ok(bv, u.attribute_count[b], non_vertex)
        && target_ok(bv.target, attr, idx, ibm || other || image)
}

fn stride_ok(bv: &BufferView, attribute_count: u64, non_vertex: bool) -> bool {
    match bv.byte_stride {
        None => attribute_count <= 1,
        Some(st) => st >= 4 && st <= 252 && st % 4 == 0 && st <= bv.byte_length && !non_vertex && !opt_eq(bv.target, Some(34963)),
    }
}

fn target_ok(target: Option<u64>, attr: bool, idx: bool, other: bool) -> bool {
    match target {
        None => true,
        Some(t) => !(attr && t != 34962) && !(idx && t != 34963) && !other,
    }
}

fn buffer_views_ok(g: &Gltf, u: &ViewUse) -> bool {
    let mut b = 0;
    while b < g.buffer_views.len() {
        if !buffer_view_ok(g, u, b) {
            return false;
        }
        b += 1;
    }
    true
}

fn accessor_view_ok(g: &Gltf, a: &Accessor, is_attribute: bool) -> bool {
    let cs = component_size(a.component_type);
    let size = element_size(a);
    match a.buffer_view {
        None => a.byte_offset.is_none(),
        Some(b) => {
            let bv = &g.buffer_views[b as usize];
            let offset = match a.byte_offset {
                Some(o) => o,
                None => 0,
            };
            let stride = match bv.byte_stride {
                None => size,
                Some(st) => st,
            };
            let stride_ok = match bv.byte_stride {
                None => true,
                Some(st) => st >= size && st % cs == 0,
            };
            offset % cs == 0
                && bv.byte_offset % cs == 0
                && stride_ok
                && (!is_attribute || (offset % 4 == 0 && (cs % 4 == 0 || bv.byte_stride.is_some())))
                && fits(offset, a.count, stride, size, bv.byte_length)
        }
    }
}

fn sparse_ok(g: &Gltf, a: &Accessor) -> bool {
    match &a.sparse {
        None => true,
        Some(s) => {
            let cs = component_size(a.component_type);
            let size = element_size(a);
            let ict = s.indices_component_type;
            if s.count == 0 || s.count > a.count || !(ict == 5121 || ict == 5123 || ict == 5125) {
                return false;
            }
            let isz = component_size(ict);
            let ib = &g.buffer_views[s.indices_buffer_view as usize];
            let vb = &g.buffer_views[s.values_buffer_view as usize];
            s.indices_byte_offset % isz == 0
                && ib.byte_offset % isz == 0
                && s.values_byte_offset % cs == 0
                && vb.byte_offset % cs == 0
                && fits(s.indices_byte_offset, s.count, isz, isz, ib.byte_length)
                && fits(s.values_byte_offset, s.count, size, size, vb.byte_length)
        }
    }
}

fn bounds_len_ok(l: Option<u64>, components: u64) -> bool {
    match l {
        None => true,
        Some(n) => n == components,
    }
}

fn accessor_ok(g: &Gltf, roles: &Roles, i: usize) -> bool {
    let a = &g.accessors[i];
    a.count > 0
        && !(a.normalized && (a.component_type == 5125 || a.component_type == 5126))
        && bounds_len_ok(a.min_len, a.components)
        && bounds_len_ok(a.max_len, a.components)
        && accessor_view_ok(g, a, roles.attribute[i])
        && sparse_ok(g, a)
}

fn accessors_ok(g: &Gltf, roles: &Roles) -> bool {
    let mut i = 0;
    while i < g.accessors.len() {
        if !accessor_ok(g, roles, i) {
            return false;
        }
        i += 1;
    }
    true
}

pub(crate) fn data_ok(g: &Gltf) -> bool {
    let roles = accessor_roles(g);
    let u = view_use(g, &roles);
    buffer_views_ok(g, &u) && accessors_ok(g, &roles)
}
