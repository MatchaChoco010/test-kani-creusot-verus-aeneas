use crate::model::*;
use crate::validate::util::*;
use vstd::prelude::*;

verus! {

pub open spec fn tex_index_lt(t: Option<TextureInfo>, n: int) -> bool {
    match t {
        Some(ti) => ti.index < n,
        None => true,
    }
}

fn texture_info_less(t: &Option<TextureInfo>, n: usize) -> (r: bool)
    ensures
        r == tex_index_lt(*t, n as int),
{
    match t {
        None => true,
        Some(ti) => ti.index < n as u64,
    }
}

fn attributes_less(attrs: &Vec<Attribute>, n: usize) -> (r: bool)
    ensures
        r == (forall|k: int| 0 <= k < attrs.len() ==> #[trigger] attrs_view(attrs@)[k].accessor < n),
{
    let mut i = 0;
    while i < attrs.len()
        invariant
            0 <= i <= attrs.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] attrs_view(attrs@)[k].accessor < n,
        decreases attrs.len() - i,
    {
        proof {
            assert(attrs_view(attrs@)[i as int].accessor == attrs@[i as int].accessor);
        }
        if attrs[i].accessor >= n as u64 {
            return false;
        }
        i += 1;
    }
    true
}

fn targets_less(targets: &Vec<Vec<Attribute>>, n: usize) -> (r: bool)
    ensures
        r == (forall|t: int, k: int|
            0 <= t < targets.len() && 0 <= k < targets_view(targets@)[t].len() ==> #[trigger] targets_view(
                targets@,
            )[t][k].accessor < n),
{
    let mut i = 0;
    while i < targets.len()
        invariant
            0 <= i <= targets.len(),
            forall|t: int, k: int|
                0 <= t < i && 0 <= k < targets_view(targets@)[t].len() ==> #[trigger] targets_view(targets@)[t][k].accessor
                    < n,
        decreases targets.len() - i,
    {
        proof {
            assert(targets_view(targets@)[i as int] == attrs_view(targets@[i as int]@));
        }
        if !attributes_less(&targets[i], n) {
            return false;
        }
        i += 1;
    }
    true
}

fn scene_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|s: int, k: int|
            0 <= s < g@.scenes.len() && 0 <= k < g@.scenes[s].nodes.len() ==> #[trigger] g@.scenes[s].nodes[k]
                < g@.nodes.len()),
{
    let mut i = 0;
    while i < g.scenes.len()
        invariant
            0 <= i <= g.scenes.len(),
            forall|s: int, k: int|
                0 <= s < i && 0 <= k < g@.scenes[s].nodes.len() ==> #[trigger] g@.scenes[s].nodes[k] < g@.nodes.len(),
        decreases g.scenes.len() - i,
    {
        proof {
            assert(g@.scenes[i as int].nodes == g.scenes@[i as int].nodes@);
        }
        if !all_less(&g.scenes[i].nodes, g.nodes.len()) {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn node_refs_s(g: GltfS, n: int) -> bool {
    &&& forall|k: int| 0 <= k < g.nodes[n].children.len() ==> #[trigger] g.nodes[n].children[k] < g.nodes.len()
    &&& opt_lt(g.nodes[n].mesh, g.meshes.len() as int)
    &&& opt_lt(g.nodes[n].camera, g.cameras.len() as int)
    &&& opt_lt(g.nodes[n].skin, g.skins.len() as int)
}

fn node_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|n: int| 0 <= n < g@.nodes.len() ==> #[trigger] node_refs_s(g@, n)),
{
    let mut i = 0;
    while i < g.nodes.len()
        invariant
            0 <= i <= g.nodes.len(),
            forall|n: int| 0 <= n < i ==> #[trigger] node_refs_s(g@, n),
        decreases g.nodes.len() - i,
    {
        proof {
            assert(g@.nodes[i as int].children == g.nodes@[i as int].children@);
            assert(g@.nodes[i as int].mesh == g.nodes@[i as int].mesh);
            assert(g@.nodes[i as int].camera == g.nodes@[i as int].camera);
            assert(g@.nodes[i as int].skin == g.nodes@[i as int].skin);
        }
        let n = &g.nodes[i];
        if !all_less(&n.children, g.nodes.len()) || !opt_less(n.mesh, g.meshes.len()) || !opt_less(n.camera, g.cameras.len()) || !opt_less(n.skin, g.skins.len()) {
            assert(!node_refs_s(g@, i as int));
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn prim_refs_s(g: GltfS, p: PrimitiveS) -> bool {
    &&& forall|k: int| 0 <= k < p.attributes.len() ==> #[trigger] p.attributes[k].accessor < g.accessors.len()
    &&& forall|t: int, k: int|
        0 <= t < p.targets.len() && 0 <= k < p.targets[t].len() ==> #[trigger] p.targets[t][k].accessor < g.accessors.len()
    &&& opt_lt(p.indices, g.accessors.len() as int)
    &&& opt_lt(p.material, g.materials.len() as int)
}

fn primitive_refs_ok(g: &Gltf, m: &Mesh) -> (r: bool)
    ensures
        r == (forall|p: int| 0 <= p < m@.primitives.len() ==> #[trigger] prim_refs_s(g@, m@.primitives[p])),
{
    let mut j = 0;
    while j < m.primitives.len()
        invariant
            0 <= j <= m.primitives.len(),
            forall|p: int| 0 <= p < j ==> #[trigger] prim_refs_s(g@, m@.primitives[p]),
        decreases m.primitives.len() - j,
    {
        let p = &m.primitives[j];
        proof {
            assert(m@.primitives[j as int] == p@);
            assert(m@.primitives[j as int].attributes == attrs_view(p.attributes@));
            assert(m@.primitives[j as int].targets == targets_view(p.targets@));
        }
        if !attributes_less(&p.attributes, g.accessors.len()) || !targets_less(&p.targets, g.accessors.len()) || !opt_less(p.indices, g.accessors.len()) || !opt_less(p.material, g.materials.len()) {
            assert(!prim_refs_s(g@, m@.primitives[j as int]));
            return false;
        }
        j += 1;
    }
    true
}

fn mesh_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|m: int, p: int|
            0 <= m < g@.meshes.len() && 0 <= p < g@.meshes[m].primitives.len() ==> #[trigger] prim_refs_s(
                g@,
                g@.meshes[m].primitives[p],
            )),
{
    let mut i = 0;
    while i < g.meshes.len()
        invariant
            0 <= i <= g.meshes.len(),
            forall|m: int, p: int|
                0 <= m < i && 0 <= p < g@.meshes[m].primitives.len() ==> #[trigger] prim_refs_s(
                    g@,
                    g@.meshes[m].primitives[p],
                ),
        decreases g.meshes.len() - i,
    {
        proof {
            assert(g@.meshes[i as int] == g.meshes@[i as int]@);
        }
        if !primitive_refs_ok(g, &g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn sparse_refs_ok(s: &Option<Sparse>, n: usize) -> (r: bool)
    ensures
        r == (*s matches Some(sp) ==> sp.indices_buffer_view < n && sp.values_buffer_view < n),
{
    match s {
        None => true,
        Some(s) => s.indices_buffer_view < n as u64 && s.values_buffer_view < n as u64,
    }
}

// ---- V.0 refs_ok ----
pub open spec fn accessor_shape_s(a: Accessor) -> bool {
    if a.is_matrix {
        a.components == 4 || a.components == 9 || a.components == 16
    } else {
        1 <= a.components <= 4
    }
}

fn accessor_shape_ok(a: &Accessor) -> (r: bool)
    ensures
        r == accessor_shape_s(*a),
{
    if a.is_matrix {
        a.components == 4 || a.components == 9 || a.components == 16
    } else {
        a.components >= 1 && a.components <= 4
    }
}

pub open spec fn accessor_refs_s(g: GltfS, a: int) -> bool {
    &&& accessor_shape_s(g.accessors[a])
    &&& opt_lt(g.accessors[a].buffer_view, g.buffer_views.len() as int)
    &&& (g.accessors[a].sparse matches Some(sp) ==> sp.indices_buffer_view < g.buffer_views.len()
        && sp.values_buffer_view < g.buffer_views.len())
}

fn accessor_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|a: int| 0 <= a < g@.accessors.len() ==> #[trigger] accessor_refs_s(g@, a)),
{
    let mut i = 0;
    while i < g.accessors.len()
        invariant
            0 <= i <= g.accessors.len(),
            forall|a: int| 0 <= a < i ==> #[trigger] accessor_refs_s(g@, a),
        decreases g.accessors.len() - i,
    {
        if !accessor_shape_ok(&g.accessors[i]) || !opt_less(g.accessors[i].buffer_view, g.buffer_views.len()) || !sparse_refs_ok(&g.accessors[i].sparse, g.buffer_views.len()) {
            assert(!accessor_refs_s(g@, i as int));
            return false;
        }
        i += 1;
    }
    true
}

fn buffer_view_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|b: int| 0 <= b < g@.buffer_views.len() ==> #[trigger] g@.buffer_views[b].buffer < g@.buffers.len()),
{
    let mut i = 0;
    while i < g.buffer_views.len()
        invariant
            0 <= i <= g.buffer_views.len(),
            forall|b: int| 0 <= b < i ==> #[trigger] g@.buffer_views[b].buffer < g@.buffers.len(),
        decreases g.buffer_views.len() - i,
    {
        if g.buffer_views[i].buffer >= g.buffers.len() as u64 {
            return false;
        }
        i += 1;
    }
    true
}

fn texture_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|t: int|
            0 <= t < g@.textures.len() ==> opt_lt(#[trigger] g@.textures[t].sampler, g@.samplers_len as int) && opt_lt(
                g@.textures[t].source,
                g@.images.len() as int,
            )),
{
    let mut i = 0;
    while i < g.textures.len()
        invariant
            0 <= i <= g.textures.len(),
            forall|t: int|
                0 <= t < i ==> opt_lt(#[trigger] g@.textures[t].sampler, g@.samplers_len as int) && opt_lt(
                    g@.textures[t].source,
                    g@.images.len() as int,
                ),
        decreases g.textures.len() - i,
    {
        if !opt_less_u64(g.textures[i].sampler, g.samplers_len) || !opt_less(g.textures[i].source, g.images.len()) {
            return false;
        }
        i += 1;
    }
    true
}

fn image_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|i: int| 0 <= i < g@.images.len() ==> opt_lt(#[trigger] g@.images[i].buffer_view, g@.buffer_views.len() as int)),
{
    let mut i = 0;
    while i < g.images.len()
        invariant
            0 <= i <= g.images.len(),
            forall|k: int| 0 <= k < i ==> opt_lt(#[trigger] g@.images[k].buffer_view, g@.buffer_views.len() as int),
        decreases g.images.len() - i,
    {
        proof {
            assert(g@.images[i as int].buffer_view == g.images@[i as int].buffer_view);
        }
        if !opt_less(g.images[i].buffer_view, g.buffer_views.len()) {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn material_refs_s(mt: Material, nt: int) -> bool {
    &&& tex_index_lt(mt.base_color_texture, nt)
    &&& tex_index_lt(mt.metallic_roughness_texture, nt)
    &&& tex_index_lt(mt.normal_texture, nt)
    &&& tex_index_lt(mt.occlusion_texture, nt)
    &&& tex_index_lt(mt.emissive_texture, nt)
}

fn material_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|m: int| 0 <= m < g@.materials.len() ==> #[trigger] material_refs_s(g@.materials[m], g@.textures.len() as int)),
{
    let nt = g.textures.len();
    let mut i = 0;
    while i < g.materials.len()
        invariant
            nt == g.textures.len(),
            0 <= i <= g.materials.len(),
            forall|m: int| 0 <= m < i ==> #[trigger] material_refs_s(g@.materials[m], g@.textures.len() as int),
        decreases g.materials.len() - i,
    {
        let m = &g.materials[i];
        if !texture_info_less(&m.base_color_texture, nt) || !texture_info_less(&m.metallic_roughness_texture, nt) || !texture_info_less(&m.normal_texture, nt) || !texture_info_less(&m.occlusion_texture, nt) || !texture_info_less(&m.emissive_texture, nt) {
            assert(!material_refs_s(g@.materials[i as int], g@.textures.len() as int));
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn skin_refs_s(g: GltfS, s: int) -> bool {
    &&& forall|k: int| 0 <= k < g.skins[s].joints.len() ==> #[trigger] g.skins[s].joints[k] < g.nodes.len()
    &&& opt_lt(g.skins[s].skeleton, g.nodes.len() as int)
    &&& opt_lt(g.skins[s].inverse_bind_matrices, g.accessors.len() as int)
}

fn skin_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|s: int| 0 <= s < g@.skins.len() ==> #[trigger] skin_refs_s(g@, s)),
{
    let mut i = 0;
    while i < g.skins.len()
        invariant
            0 <= i <= g.skins.len(),
            forall|s: int| 0 <= s < i ==> #[trigger] skin_refs_s(g@, s),
        decreases g.skins.len() - i,
    {
        proof {
            assert(g@.skins[i as int].joints == g.skins@[i as int].joints@);
            assert(g@.skins[i as int].skeleton == g.skins@[i as int].skeleton);
            assert(g@.skins[i as int].inverse_bind_matrices == g.skins@[i as int].inverse_bind_matrices);
        }
        let s = &g.skins[i];
        if !all_less(&s.joints, g.nodes.len()) || !opt_less(s.skeleton, g.nodes.len()) || !opt_less(s.inverse_bind_matrices, g.accessors.len()) {
            assert(!skin_refs_s(g@, i as int));
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn channel_refs_s(g: GltfS, an: AnimationS, c: int) -> bool {
    an.channels[c].sampler < an.samplers.len() && opt_lt(an.channels[c].node, g.nodes.len() as int)
}

fn channel_refs_ok(g: &Gltf, an: &Animation) -> (r: bool)
    ensures
        r == (forall|c: int| 0 <= c < an@.channels.len() ==> #[trigger] channel_refs_s(g@, an@, c)),
{
    let mut c = 0;
    while c < an.channels.len()
        invariant
            0 <= c <= an.channels.len(),
            forall|k: int| 0 <= k < c ==> #[trigger] channel_refs_s(g@, an@, k),
        decreases an.channels.len() - c,
    {
        if an.channels[c].sampler >= an.samplers.len() as u64 || !opt_less(an.channels[c].node, g.nodes.len()) {
            assert(!channel_refs_s(g@, an@, c as int));
            return false;
        }
        c += 1;
    }
    true
}

pub open spec fn sampler_refs_s(g: GltfS, an: AnimationS, s: int) -> bool {
    an.samplers[s].input < g.accessors.len() && an.samplers[s].output < g.accessors.len()
}

fn animation_sampler_refs_ok(g: &Gltf, an: &Animation) -> (r: bool)
    ensures
        r == (forall|s: int| 0 <= s < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, s)),
{
    let mut s = 0;
    while s < an.samplers.len()
        invariant
            0 <= s <= an.samplers.len(),
            forall|k: int| 0 <= k < s ==> #[trigger] sampler_refs_s(g@, an@, k),
        decreases an.samplers.len() - s,
    {
        if an.samplers[s].input >= g.accessors.len() as u64 || an.samplers[s].output >= g.accessors.len() as u64 {
            assert(!sampler_refs_s(g@, an@, s as int));
            return false;
        }
        s += 1;
    }
    true
}

pub open spec fn anim_refs_s(g: GltfS, i: int) -> bool {
    (forall|c: int| 0 <= c < g.animations[i].channels.len() ==> #[trigger] channel_refs_s(g, g.animations[i], c))
        && (forall|s: int| 0 <= s < g.animations[i].samplers.len() ==> #[trigger] sampler_refs_s(g, g.animations[i], s))
}

fn animation_refs_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|i: int|
            0 <= i < g@.animations.len() ==> #[trigger] anim_refs_s(g@, i)),
{
    let mut i = 0;
    while i < g.animations.len()
        invariant
            0 <= i <= g.animations.len(),
            forall|k: int|
                0 <= k < i ==> #[trigger] anim_refs_s(g@, k),
        decreases g.animations.len() - i,
    {
        proof {
            assert(g@.animations[i as int] == g.animations@[i as int]@);
            assert(g@.animations[i as int].channels == g.animations@[i as int].channels@);
            assert(g@.animations[i as int].samplers == g.animations@[i as int].samplers@);
        }
        if !channel_refs_ok(g, &g.animations[i]) || !animation_sampler_refs_ok(g, &g.animations[i]) {
            assert(!anim_refs_s(g@, i as int));
            return false;
        }
        assert(anim_refs_s(g@, i as int));
        i += 1;
    }
    true
}

// MUST-014: インデックスは配列の範囲内
pub open spec fn refs_ok(g: GltfS) -> bool {
    &&& forall|a: int| 0 <= a < g.accessors.len() ==> accessor_shape_s(#[trigger] g.accessors[a])
    &&& opt_lt(g.scene, g.scenes.len() as int)
    &&& forall|s: int, k: int|
        0 <= s < g.scenes.len() && 0 <= k < g.scenes[s].nodes.len() ==> #[trigger] g.scenes[s].nodes[k]
            < g.nodes.len()
    &&& forall|n: int, k: int|
        0 <= n < g.nodes.len() && 0 <= k < g.nodes[n].children.len() ==> #[trigger] g.nodes[n].children[k]
            < g.nodes.len()
    &&& forall|n: int|
        0 <= n < g.nodes.len() ==> {
            &&& opt_lt(#[trigger] g.nodes[n].mesh, g.meshes.len() as int)
            &&& opt_lt(g.nodes[n].camera, g.cameras.len() as int)
            &&& opt_lt(g.nodes[n].skin, g.skins.len() as int)
        }
    &&& forall|m: int, p: int, k: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= k < prim(g, m, p).attributes.len()
            ==> #[trigger] prim(g, m, p).attributes[k].accessor < g.accessors.len()
    &&& forall|m: int, p: int, t: int, k: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= t < prim(g, m, p).targets.len()
            && 0 <= k < prim(g, m, p).targets[t].len() ==> #[trigger] prim(g, m, p).targets[t][k].accessor
            < g.accessors.len()
    &&& forall|m: int, p: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() ==> {
            &&& opt_lt(#[trigger] prim(g, m, p).indices, g.accessors.len() as int)
            &&& opt_lt(prim(g, m, p).material, g.materials.len() as int)
        }
    &&& forall|a: int|
        0 <= a < g.accessors.len() ==> {
            &&& opt_lt(#[trigger] g.accessors[a].buffer_view, g.buffer_views.len() as int)
            &&& (g.accessors[a].sparse matches Some(sp) ==> sp.indices_buffer_view < g.buffer_views.len()
                && sp.values_buffer_view < g.buffer_views.len())
        }
    &&& forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] g.buffer_views[b].buffer < g.buffers.len()
    &&& forall|t: int|
        0 <= t < g.textures.len() ==> opt_lt(#[trigger] g.textures[t].sampler, g.samplers_len as int) && opt_lt(
            g.textures[t].source,
            g.images.len() as int,
        )
    &&& forall|i: int| 0 <= i < g.images.len() ==> opt_lt(#[trigger] g.images[i].buffer_view, g.buffer_views.len() as int)
    &&& forall|m: int|
        0 <= m < g.materials.len() ==> {
            let mt = #[trigger] g.materials[m];
            let nt = g.textures.len() as int;
            &&& tex_index_lt(mt.base_color_texture, nt)
            &&& tex_index_lt(mt.metallic_roughness_texture, nt)
            &&& tex_index_lt(mt.normal_texture, nt)
            &&& tex_index_lt(mt.occlusion_texture, nt)
            &&& tex_index_lt(mt.emissive_texture, nt)
        }
    &&& forall|s: int, k: int|
        0 <= s < g.skins.len() && 0 <= k < g.skins[s].joints.len() ==> #[trigger] g.skins[s].joints[k] < g.nodes.len()
    &&& forall|s: int|
        0 <= s < g.skins.len() ==> opt_lt(#[trigger] g.skins[s].skeleton, g.nodes.len() as int) && opt_lt(
            g.skins[s].inverse_bind_matrices,
            g.accessors.len() as int,
        )
    &&& forall|i: int, c: int|
        0 <= i < g.animations.len() && 0 <= c < g.animations[i].channels.len() ==> {
            let ch = #[trigger] g.animations[i].channels[c];
            ch.sampler < g.animations[i].samplers.len() && opt_lt(ch.node, g.nodes.len() as int)
        }
    &&& forall|i: int, s: int|
        0 <= i < g.animations.len() && 0 <= s < g.animations[i].samplers.len() ==> {
            let sm = #[trigger] g.animations[i].samplers[s];
            sm.input < g.accessors.len() && sm.output < g.accessors.len()
        }
}

pub proof fn lemma_refs_ok_split(g: GltfS)
    ensures
        refs_ok(g) == {
            &&& opt_lt(g.scene, g.scenes.len() as int)
            &&& forall|s: int, k: int|
                0 <= s < g.scenes.len() && 0 <= k < g.scenes[s].nodes.len() ==> #[trigger] g.scenes[s].nodes[k]
                    < g.nodes.len()
            &&& forall|n: int| 0 <= n < g.nodes.len() ==> #[trigger] node_refs_s(g, n)
            &&& forall|m: int, p: int|
                0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() ==> #[trigger] prim_refs_s(
                    g,
                    g.meshes[m].primitives[p],
                )
            &&& forall|a: int| 0 <= a < g.accessors.len() ==> #[trigger] accessor_refs_s(g, a)
            &&& forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] g.buffer_views[b].buffer < g.buffers.len()
            &&& forall|t: int|
                0 <= t < g.textures.len() ==> opt_lt(#[trigger] g.textures[t].sampler, g.samplers_len as int) && opt_lt(
                    g.textures[t].source,
                    g.images.len() as int,
                )
            &&& forall|i: int| 0 <= i < g.images.len() ==> opt_lt(#[trigger] g.images[i].buffer_view, g.buffer_views.len() as int)
            &&& forall|m: int| 0 <= m < g.materials.len() ==> #[trigger] material_refs_s(g.materials[m], g.textures.len() as int)
            &&& forall|s: int| 0 <= s < g.skins.len() ==> #[trigger] skin_refs_s(g, s)
            &&& forall|i: int|
                0 <= i < g.animations.len() ==> #[trigger] anim_refs_s(g, i)
        },
{
    let rhs = {
        &&& opt_lt(g.scene, g.scenes.len() as int)
        &&& forall|n: int| 0 <= n < g.nodes.len() ==> #[trigger] node_refs_s(g, n)
        &&& forall|m: int, p: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() ==> #[trigger] prim_refs_s(
                g,
                g.meshes[m].primitives[p],
            )
        &&& forall|a: int| 0 <= a < g.accessors.len() ==> #[trigger] accessor_refs_s(g, a)
        &&& forall|m: int| 0 <= m < g.materials.len() ==> #[trigger] material_refs_s(g.materials[m], g.textures.len() as int)
        &&& forall|s: int| 0 <= s < g.skins.len() ==> #[trigger] skin_refs_s(g, s)
        &&& forall|i: int|
            0 <= i < g.animations.len() ==> #[trigger] anim_refs_s(g, i)
    };
    if refs_ok(g) {
        assert forall|n: int| 0 <= n < g.nodes.len() implies #[trigger] node_refs_s(g, n) by {
            assert(opt_lt(g.nodes[n].mesh, g.meshes.len() as int));
        }
        assert forall|m: int, p: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() implies #[trigger] prim_refs_s(
            g,
            g.meshes[m].primitives[p],
        ) by {
            assert(opt_lt(prim(g, m, p).indices, g.accessors.len() as int));
            assert forall|k: int| 0 <= k < prim(g, m, p).attributes.len() implies #[trigger] prim(g, m, p).attributes[k].accessor
                < g.accessors.len() by {}
            assert forall|t: int, k: int| 0 <= t < prim(g, m, p).targets.len() && 0 <= k < prim(g, m, p).targets[t].len() implies #[trigger] prim(
                g,
                m,
                p,
            ).targets[t][k].accessor < g.accessors.len() by {}
        }
        assert forall|a: int| 0 <= a < g.accessors.len() implies #[trigger] accessor_refs_s(g, a) by {
            assert(accessor_shape_s(g.accessors[a]));
            assert(opt_lt(g.accessors[a].buffer_view, g.buffer_views.len() as int));
        }
        assert forall|m: int| 0 <= m < g.materials.len() implies #[trigger] material_refs_s(g.materials[m], g.textures.len() as int) by {
            let mt = g.materials[m];
        }
        assert forall|s: int| 0 <= s < g.skins.len() implies #[trigger] skin_refs_s(g, s) by {
            assert(opt_lt(g.skins[s].skeleton, g.nodes.len() as int));
        }
        assert forall|i: int| 0 <= i < g.animations.len() implies #[trigger] anim_refs_s(g, i) by {
            assert forall|c: int| 0 <= c < g.animations[i].channels.len() implies #[trigger] channel_refs_s(g, g.animations[i], c) by {
                let ch = g.animations[i].channels[c];
            }
            assert forall|s: int| 0 <= s < g.animations[i].samplers.len() implies #[trigger] sampler_refs_s(g, g.animations[i], s) by {
                let sm = g.animations[i].samplers[s];
            }
        }
    }
    if rhs {
        assert forall|a: int| 0 <= a < g.accessors.len() implies accessor_shape_s(#[trigger] g.accessors[a]) by {
            assert(accessor_refs_s(g, a));
        }
        assert forall|n: int, k: int|
            0 <= n < g.nodes.len() && 0 <= k < g.nodes[n].children.len() implies #[trigger] g.nodes[n].children[k]
            < g.nodes.len() by {
            assert(node_refs_s(g, n));
        }
        assert forall|n: int| 0 <= n < g.nodes.len() implies {
            &&& opt_lt(#[trigger] g.nodes[n].mesh, g.meshes.len() as int)
            &&& opt_lt(g.nodes[n].camera, g.cameras.len() as int)
            &&& opt_lt(g.nodes[n].skin, g.skins.len() as int)
        } by {
            assert(node_refs_s(g, n));
        }
        assert forall|m: int, p: int, k: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= k < prim(g, m, p).attributes.len()
            implies #[trigger] prim(g, m, p).attributes[k].accessor < g.accessors.len() by {
            assert(prim_refs_s(g, g.meshes[m].primitives[p]));
        }
        assert forall|m: int, p: int, t: int, k: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= t < prim(g, m, p).targets.len()
                && 0 <= k < prim(g, m, p).targets[t].len() implies #[trigger] prim(g, m, p).targets[t][k].accessor
            < g.accessors.len() by {
            assert(prim_refs_s(g, g.meshes[m].primitives[p]));
        }
        assert forall|m: int, p: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() implies {
            &&& opt_lt(#[trigger] prim(g, m, p).indices, g.accessors.len() as int)
            &&& opt_lt(prim(g, m, p).material, g.materials.len() as int)
        } by {
            assert(prim_refs_s(g, g.meshes[m].primitives[p]));
        }
        assert forall|a: int| 0 <= a < g.accessors.len() implies {
            &&& opt_lt(#[trigger] g.accessors[a].buffer_view, g.buffer_views.len() as int)
            &&& (g.accessors[a].sparse matches Some(sp) ==> sp.indices_buffer_view < g.buffer_views.len()
                && sp.values_buffer_view < g.buffer_views.len())
        } by {
            assert(accessor_refs_s(g, a));
        }
        assert forall|m: int| 0 <= m < g.materials.len() implies {
            let mt = #[trigger] g.materials[m];
            let nt = g.textures.len() as int;
            &&& tex_index_lt(mt.base_color_texture, nt)
            &&& tex_index_lt(mt.metallic_roughness_texture, nt)
            &&& tex_index_lt(mt.normal_texture, nt)
            &&& tex_index_lt(mt.occlusion_texture, nt)
            &&& tex_index_lt(mt.emissive_texture, nt)
        } by {
            assert(material_refs_s(g.materials[m], g.textures.len() as int));
        }
        assert forall|s: int, k: int|
            0 <= s < g.skins.len() && 0 <= k < g.skins[s].joints.len() implies #[trigger] g.skins[s].joints[k] < g.nodes.len() by {
            assert(skin_refs_s(g, s));
        }
        assert forall|s: int|
            0 <= s < g.skins.len() implies opt_lt(#[trigger] g.skins[s].skeleton, g.nodes.len() as int) && opt_lt(
            g.skins[s].inverse_bind_matrices,
            g.accessors.len() as int,
        ) by {
            assert(skin_refs_s(g, s));
        }
        assert forall|i: int, c: int|
            0 <= i < g.animations.len() && 0 <= c < g.animations[i].channels.len() implies {
            let ch = #[trigger] g.animations[i].channels[c];
            ch.sampler < g.animations[i].samplers.len() && opt_lt(ch.node, g.nodes.len() as int)
        } by {
            assert(anim_refs_s(g, i));
            assert(channel_refs_s(g, g.animations[i], c));
        }
        assert forall|i: int, s: int|
            0 <= i < g.animations.len() && 0 <= s < g.animations[i].samplers.len() implies {
            let sm = #[trigger] g.animations[i].samplers[s];
            sm.input < g.accessors.len() && sm.output < g.accessors.len()
        } by {
            assert(anim_refs_s(g, i));
            assert(sampler_refs_s(g, g.animations[i], s));
        }
    }
}

// V.0
// MUST-014: インデックスは配列の範囲内
pub fn refs_in_range(g: &Gltf) -> (r: bool)
    ensures
        r == refs_ok(g@),
{
    proof {
        lemma_refs_ok_split(g@);
    }
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

} // verus!
