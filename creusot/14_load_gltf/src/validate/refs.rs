use creusot_std::prelude::*;
use crate::model::*;
use crate::validate::util::*;

#[logic(open)]
pub fn tex_lt(t: Option<TextureInfo>, n: Int) -> bool {
    pearlite! {
        match t {
            None => true,
            Some(ti) => ti.index@ < n,
        }
    }
}

#[ensures(result == tex_lt(*t, n@))]
#[check(terminates)]
fn texture_info_less(t: &Option<TextureInfo>, n: usize) -> bool {
    match t {
        None => true,
        Some(ti) => ti.index < n as u64,
    }
}

#[logic(open)]
pub fn attrs_lt(attrs: Seq<Attribute>, n: Int) -> bool {
    pearlite! { forall<k> 0 <= k && k < attrs.len() ==> attrs[k].accessor@ < n }
}

#[ensures(result == attrs_lt(attrs@, n@))]
#[check(terminates)]
fn attributes_less(attrs: &Vec<Attribute>, n: usize) -> bool {
    let mut i = 0;
    #[invariant(i@ <= attrs@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> attrs@[k].accessor@ < n@)]
    #[variant(attrs@.len() - i@)]
    while i < attrs.len() {
        if attrs[i].accessor >= n as u64 {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<t> 0 <= t && t < targets@.len() ==> attrs_lt(targets@[t]@, n@))]
#[check(terminates)]
fn targets_less(targets: &Vec<Vec<Attribute>>, n: usize) -> bool {
    let mut i = 0;
    #[invariant(i@ <= targets@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> attrs_lt(targets@[k]@, n@))]
    #[variant(targets@.len() - i@)]
    while i < targets.len() {
        if !attributes_less(&targets[i], n) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<i> 0 <= i && i < g.scenes@.len() ==> all_lt(g.scenes@[i].nodes@, g.nodes@.len()))]
#[check(terminates)]
fn scene_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.scenes@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> all_lt(g.scenes@[k].nodes@, g.nodes@.len()))]
    #[variant(g.scenes@.len() - i@)]
    while i < g.scenes.len() {
        if !all_less(&g.scenes[i].nodes, g.nodes.len()) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<i> 0 <= i && i < g.nodes@.len() ==> all_lt(g.nodes@[i].children@, g.nodes@.len()) && opt_lt(g.nodes@[i].mesh, g.meshes@.len()) && opt_lt(g.nodes@[i].camera, g.cameras@.len()) && opt_lt(g.nodes@[i].skin, g.skins@.len()))]
#[check(terminates)]
fn node_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.nodes@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> all_lt(g.nodes@[k].children@, g.nodes@.len()) && opt_lt(g.nodes@[k].mesh, g.meshes@.len()) && opt_lt(g.nodes@[k].camera, g.cameras@.len()) && opt_lt(g.nodes@[k].skin, g.skins@.len()))]
    #[variant(g.nodes@.len() - i@)]
    while i < g.nodes.len() {
        let n = &g.nodes[i];
        if !all_less(&n.children, g.nodes.len()) || !opt_less(n.mesh, g.meshes.len()) || !opt_less(n.camera, g.cameras.len()) || !opt_less(n.skin, g.skins.len()) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(open)]
pub fn primitive_refs(g: Gltf, p: Primitive) -> bool {
    pearlite! {
        attrs_lt(p.attributes@, g.accessors@.len())
            && (forall<t> 0 <= t && t < p.targets@.len() ==> attrs_lt(p.targets@[t]@, g.accessors@.len()))
            && opt_lt(p.indices, g.accessors@.len())
            && opt_lt(p.material, g.materials@.len())
    }
}

#[ensures(result == forall<j> 0 <= j && j < m.primitives@.len() ==> primitive_refs(*g, m.primitives@[j]))]
#[check(terminates)]
fn primitive_refs_ok(g: &Gltf, m: &Mesh) -> bool {
    let mut j = 0;
    #[invariant(j@ <= m.primitives@.len())]
    #[invariant(forall<k> 0 <= k && k < j@ ==> primitive_refs(*g, m.primitives@[k]))]
    #[variant(m.primitives@.len() - j@)]
    while j < m.primitives.len() {
        let p = &m.primitives[j];
        if !attributes_less(&p.attributes, g.accessors.len()) || !targets_less(&p.targets, g.accessors.len()) || !opt_less(p.indices, g.accessors.len()) || !opt_less(p.material, g.materials.len()) {
            return false;
        }
        j += 1;
    }
    true
}

#[ensures(result == forall<i, j> 0 <= i && i < g.meshes@.len() && 0 <= j && j < g.meshes@[i].primitives@.len() ==> primitive_refs(*g, g.meshes@[i].primitives@[j]))]
#[check(terminates)]
fn mesh_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.meshes@.len())]
    #[invariant(forall<k, j> 0 <= k && k < i@ && 0 <= j && j < g.meshes@[k].primitives@.len() ==> primitive_refs(*g, g.meshes@[k].primitives@[j]))]
    #[variant(g.meshes@.len() - i@)]
    while i < g.meshes.len() {
        if !primitive_refs_ok(g, &g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(open)]
pub fn sparse_refs(s: Option<Sparse>, n: Int) -> bool {
    pearlite! {
        match s {
            None => true,
            Some(s) => s.indices_buffer_view@ < n && s.values_buffer_view@ < n,
        }
    }
}

#[ensures(result == sparse_refs(*s, n@))]
#[check(terminates)]
fn sparse_refs_ok(s: &Option<Sparse>, n: usize) -> bool {
    match s {
        None => true,
        Some(s) => s.indices_buffer_view < n as u64 && s.values_buffer_view < n as u64,
    }
}

#[logic(open)]
pub fn shape_ok(a: Accessor) -> bool {
    pearlite! {
        if a.is_matrix { a.components@ == 4 || a.components@ == 9 || a.components@ == 16 }
        else { 1 <= a.components@ && a.components@ <= 4 }
    }
}

#[ensures(result == shape_ok(*a))]
#[check(terminates)]
fn accessor_shape_ok(a: &Accessor) -> bool {
    if a.is_matrix {
        a.components == 4 || a.components == 9 || a.components == 16
    } else {
        a.components >= 1 && a.components <= 4
    }
}

#[ensures(result == forall<i> 0 <= i && i < g.accessors@.len() ==> shape_ok(g.accessors@[i]) && opt_lt(g.accessors@[i].buffer_view, g.buffer_views@.len()) && sparse_refs(g.accessors@[i].sparse, g.buffer_views@.len()))]
#[check(terminates)]
fn accessor_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.accessors@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> shape_ok(g.accessors@[k]) && opt_lt(g.accessors@[k].buffer_view, g.buffer_views@.len()) && sparse_refs(g.accessors@[k].sparse, g.buffer_views@.len()))]
    #[variant(g.accessors@.len() - i@)]
    while i < g.accessors.len() {
        if !accessor_shape_ok(&g.accessors[i]) || !opt_less(g.accessors[i].buffer_view, g.buffer_views.len()) || !sparse_refs_ok(&g.accessors[i].sparse, g.buffer_views.len()) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<i> 0 <= i && i < g.buffer_views@.len() ==> g.buffer_views@[i].buffer@ < g.buffers@.len())]
#[check(terminates)]
fn buffer_view_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.buffer_views@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> g.buffer_views@[k].buffer@ < g.buffers@.len())]
    #[variant(g.buffer_views@.len() - i@)]
    while i < g.buffer_views.len() {
        if g.buffer_views[i].buffer >= g.buffers.len() as u64 {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<i> 0 <= i && i < g.textures@.len() ==> opt_lt(g.textures@[i].sampler, g.samplers_len@) && opt_lt(g.textures@[i].source, g.images@.len()))]
#[check(terminates)]
fn texture_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.textures@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> opt_lt(g.textures@[k].sampler, g.samplers_len@) && opt_lt(g.textures@[k].source, g.images@.len()))]
    #[variant(g.textures@.len() - i@)]
    while i < g.textures.len() {
        if !opt_less_u64(g.textures[i].sampler, g.samplers_len) || !opt_less(g.textures[i].source, g.images.len()) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<i> 0 <= i && i < g.images@.len() ==> opt_lt(g.images@[i].buffer_view, g.buffer_views@.len()))]
#[check(terminates)]
fn image_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.images@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> opt_lt(g.images@[k].buffer_view, g.buffer_views@.len()))]
    #[variant(g.images@.len() - i@)]
    while i < g.images.len() {
        if !opt_less(g.images[i].buffer_view, g.buffer_views.len()) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(open)]
pub fn material_refs(m: Material, n: Int) -> bool {
    pearlite! {
        tex_lt(m.base_color_texture, n) && tex_lt(m.metallic_roughness_texture, n) && tex_lt(m.normal_texture, n)
            && tex_lt(m.occlusion_texture, n) && tex_lt(m.emissive_texture, n)
    }
}

#[ensures(result == forall<i> 0 <= i && i < g.materials@.len() ==> material_refs(g.materials@[i], g.textures@.len()))]
#[check(terminates)]
fn material_refs_ok(g: &Gltf) -> bool {
    let nt = g.textures.len();
    let mut i = 0;
    #[invariant(i@ <= g.materials@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> material_refs(g.materials@[k], g.textures@.len()))]
    #[variant(g.materials@.len() - i@)]
    while i < g.materials.len() {
        let m = &g.materials[i];
        if !texture_info_less(&m.base_color_texture, nt) || !texture_info_less(&m.metallic_roughness_texture, nt) || !texture_info_less(&m.normal_texture, nt) || !texture_info_less(&m.occlusion_texture, nt) || !texture_info_less(&m.emissive_texture, nt) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<i> 0 <= i && i < g.skins@.len() ==> all_lt(g.skins@[i].joints@, g.nodes@.len()) && opt_lt(g.skins@[i].skeleton, g.nodes@.len()) && opt_lt(g.skins@[i].inverse_bind_matrices, g.accessors@.len()))]
#[check(terminates)]
fn skin_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.skins@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> all_lt(g.skins@[k].joints@, g.nodes@.len()) && opt_lt(g.skins@[k].skeleton, g.nodes@.len()) && opt_lt(g.skins@[k].inverse_bind_matrices, g.accessors@.len()))]
    #[variant(g.skins@.len() - i@)]
    while i < g.skins.len() {
        let s = &g.skins[i];
        if !all_less(&s.joints, g.nodes.len()) || !opt_less(s.skeleton, g.nodes.len()) || !opt_less(s.inverse_bind_matrices, g.accessors.len()) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<c> 0 <= c && c < an.channels@.len() ==> an.channels@[c].sampler@ < an.samplers@.len() && opt_lt(an.channels@[c].node, g.nodes@.len()))]
#[check(terminates)]
fn channel_refs_ok(g: &Gltf, an: &Animation) -> bool {
    let mut c = 0;
    #[invariant(c@ <= an.channels@.len())]
    #[invariant(forall<k> 0 <= k && k < c@ ==> an.channels@[k].sampler@ < an.samplers@.len() && opt_lt(an.channels@[k].node, g.nodes@.len()))]
    #[variant(an.channels@.len() - c@)]
    while c < an.channels.len() {
        if an.channels[c].sampler >= an.samplers.len() as u64 || !opt_less(an.channels[c].node, g.nodes.len()) {
            return false;
        }
        c += 1;
    }
    true
}

#[ensures(result == forall<s> 0 <= s && s < an.samplers@.len() ==> an.samplers@[s].input@ < g.accessors@.len() && an.samplers@[s].output@ < g.accessors@.len())]
#[check(terminates)]
fn animation_sampler_refs_ok(g: &Gltf, an: &Animation) -> bool {
    let mut s = 0;
    #[invariant(s@ <= an.samplers@.len())]
    #[invariant(forall<k> 0 <= k && k < s@ ==> an.samplers@[k].input@ < g.accessors@.len() && an.samplers@[k].output@ < g.accessors@.len())]
    #[variant(an.samplers@.len() - s@)]
    while s < an.samplers.len() {
        if an.samplers[s].input >= g.accessors.len() as u64 || an.samplers[s].output >= g.accessors.len() as u64 {
            return false;
        }
        s += 1;
    }
    true
}

#[logic(open)]
pub fn animation_refs(g: Gltf, an: Animation) -> bool {
    pearlite! {
        (forall<c> 0 <= c && c < an.channels@.len() ==>
            an.channels@[c].sampler@ < an.samplers@.len() && opt_lt(an.channels@[c].node, g.nodes@.len()))
        && (forall<s> 0 <= s && s < an.samplers@.len() ==>
            an.samplers@[s].input@ < g.accessors@.len() && an.samplers@[s].output@ < g.accessors@.len())
    }
}

#[ensures(result == forall<i> 0 <= i && i < g.animations@.len() ==> animation_refs(*g, g.animations@[i]))]
#[check(terminates)]
fn animation_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.animations@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> animation_refs(*g, g.animations@[k]))]
    #[variant(g.animations@.len() - i@)]
    while i < g.animations.len() {
        if !channel_refs_ok(g, &g.animations[i]) || !animation_sampler_refs_ok(g, &g.animations[i]) {
            return false;
        }
        i += 1;
    }
    true
}

// V.0: すべての参照が範囲内で、モデルの形が正しい
// MUST-014: インデックスは範囲内
#[logic(open)]
pub fn refs_ok(g: Gltf) -> bool {
    pearlite! {
        (forall<i> 0 <= i && i < g.accessors@.len() ==> shape_ok(g.accessors@[i]))
        && opt_lt(g.scene, g.scenes@.len())
        && (forall<i> 0 <= i && i < g.scenes@.len() ==> all_lt(g.scenes@[i].nodes@, g.nodes@.len()))
        && (forall<i> 0 <= i && i < g.nodes@.len() ==>
            all_lt(g.nodes@[i].children@, g.nodes@.len())
            && opt_lt(g.nodes@[i].mesh, g.meshes@.len())
            && opt_lt(g.nodes@[i].camera, g.cameras@.len())
            && opt_lt(g.nodes@[i].skin, g.skins@.len()))
        && (forall<i, j> 0 <= i && i < g.meshes@.len() && 0 <= j && j < g.meshes@[i].primitives@.len() ==>
            primitive_refs(g, g.meshes@[i].primitives@[j]))
        && (forall<i> 0 <= i && i < g.accessors@.len() ==>
            opt_lt(g.accessors@[i].buffer_view, g.buffer_views@.len())
            && sparse_refs(g.accessors@[i].sparse, g.buffer_views@.len()))
        && (forall<i> 0 <= i && i < g.buffer_views@.len() ==> g.buffer_views@[i].buffer@ < g.buffers@.len())
        && (forall<i> 0 <= i && i < g.textures@.len() ==>
            opt_lt(g.textures@[i].sampler, g.samplers_len@) && opt_lt(g.textures@[i].source, g.images@.len()))
        && (forall<i> 0 <= i && i < g.images@.len() ==> opt_lt(g.images@[i].buffer_view, g.buffer_views@.len()))
        && (forall<i> 0 <= i && i < g.materials@.len() ==> material_refs(g.materials@[i], g.textures@.len()))
        && (forall<i> 0 <= i && i < g.skins@.len() ==>
            all_lt(g.skins@[i].joints@, g.nodes@.len())
            && opt_lt(g.skins@[i].skeleton, g.nodes@.len())
            && opt_lt(g.skins@[i].inverse_bind_matrices, g.accessors@.len()))
        && (forall<i> 0 <= i && i < g.animations@.len() ==> animation_refs(g, g.animations@[i]))
    }
}

// MUST-014: インデックスは範囲内
#[ensures(result == refs_ok(*g))]
#[check(terminates)]
pub fn refs_in_range(g: &Gltf) -> bool {
    opt_less(g.scene, g.scenes.len())
        && scene_refs_ok(g)
        && node_refs_ok(g)
        && mesh_refs_ok(g)
        && accessor_refs_ok(g)
        && buffer_view_refs_ok(g)
        && texture_refs_ok(g)
        && image_refs_ok(g)
        && material_refs_ok(g)
        && skin_refs_ok(g)
        && animation_refs_ok(g)
}
