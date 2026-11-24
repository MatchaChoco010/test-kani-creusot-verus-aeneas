use crate::model::*;
use crate::validate::util::*;

fn texture_info_less(t: &Option<TextureInfo>, n: usize) -> bool {
    match t {
        None => true,
        Some(ti) => ti.index < n as u64,
    }
}

fn attributes_less(attrs: &Vec<Attribute>, n: usize) -> bool {
    let mut i = 0;
    while i < attrs.len() {
        if attrs[i].accessor >= n as u64 {
            return false;
        }
        i += 1;
    }
    true
}

fn targets_less(targets: &Vec<Vec<Attribute>>, n: usize) -> bool {
    let mut i = 0;
    while i < targets.len() {
        if !attributes_less(&targets[i], n) {
            return false;
        }
        i += 1;
    }
    true
}

fn scene_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.scenes.len() {
        if !all_less(&g.scenes[i].nodes, g.nodes.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn node_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.nodes.len() {
        let n = &g.nodes[i];
        if !all_less(&n.children, g.nodes.len()) || !opt_less(n.mesh, g.meshes.len()) || !opt_less(n.camera, g.cameras.len()) || !opt_less(n.skin, g.skins.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn primitive_refs_ok(g: &Gltf, m: &Mesh) -> bool {
    let mut j = 0;
    while j < m.primitives.len() {
        let p = &m.primitives[j];
        if !attributes_less(&p.attributes, g.accessors.len()) || !targets_less(&p.targets, g.accessors.len()) || !opt_less(p.indices, g.accessors.len()) || !opt_less(p.material, g.materials.len()) {
            return false;
        }
        j += 1;
    }
    true
}

fn mesh_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.meshes.len() {
        if !primitive_refs_ok(g, &g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn sparse_refs_ok(s: &Option<Sparse>, n: usize) -> bool {
    match s {
        None => true,
        Some(s) => s.indices_buffer_view < n as u64 && s.values_buffer_view < n as u64,
    }
}

fn accessor_shape_ok(a: &Accessor) -> bool {
    if a.is_matrix {
        a.components == 4 || a.components == 9 || a.components == 16
    } else {
        a.components >= 1 && a.components <= 4
    }
}

fn accessor_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.accessors.len() {
        if !accessor_shape_ok(&g.accessors[i]) || !opt_less(g.accessors[i].buffer_view, g.buffer_views.len()) || !sparse_refs_ok(&g.accessors[i].sparse, g.buffer_views.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn buffer_view_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.buffer_views.len() {
        if g.buffer_views[i].buffer >= g.buffers.len() as u64 {
            return false;
        }
        i += 1;
    }
    true
}

fn texture_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.textures.len() {
        if !opt_less_u64(g.textures[i].sampler, g.samplers_len) || !opt_less(g.textures[i].source, g.images.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn image_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.images.len() {
        if !opt_less(g.images[i].buffer_view, g.buffer_views.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn material_refs_ok(g: &Gltf) -> bool {
    let nt = g.textures.len();
    let mut i = 0;
    while i < g.materials.len() {
        let m = &g.materials[i];
        if !texture_info_less(&m.base_color_texture, nt) || !texture_info_less(&m.metallic_roughness_texture, nt) || !texture_info_less(&m.normal_texture, nt) || !texture_info_less(&m.occlusion_texture, nt) || !texture_info_less(&m.emissive_texture, nt) {
            return false;
        }
        i += 1;
    }
    true
}

fn skin_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.skins.len() {
        let s = &g.skins[i];
        if !all_less(&s.joints, g.nodes.len()) || !opt_less(s.skeleton, g.nodes.len()) || !opt_less(s.inverse_bind_matrices, g.accessors.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn channel_refs_ok(g: &Gltf, an: &Animation) -> bool {
    let mut c = 0;
    while c < an.channels.len() {
        if an.channels[c].sampler >= an.samplers.len() as u64 || !opt_less(an.channels[c].node, g.nodes.len()) {
            return false;
        }
        c += 1;
    }
    true
}

fn animation_sampler_refs_ok(g: &Gltf, an: &Animation) -> bool {
    let mut s = 0;
    while s < an.samplers.len() {
        if an.samplers[s].input >= g.accessors.len() as u64 || an.samplers[s].output >= g.accessors.len() as u64 {
            return false;
        }
        s += 1;
    }
    true
}

fn animation_refs_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.animations.len() {
        if !channel_refs_ok(g, &g.animations[i]) || !animation_sampler_refs_ok(g, &g.animations[i]) {
            return false;
        }
        i += 1;
    }
    true
}

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
