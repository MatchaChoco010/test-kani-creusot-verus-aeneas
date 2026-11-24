pub mod animation;
pub mod data;
pub mod hierarchy;
pub mod mesh;
pub mod refs;
pub mod resource;
pub mod support;
pub mod util;

use crate::model::*;
use crate::validate::refs::*;
use crate::validate::support::*;
use crate::validate::util::*;
use crate::validate::hierarchy::*;
use crate::validate::mesh::*;
use crate::validate::animation::*;
use crate::validate::data::*;
use crate::validate::resource::*;
use vstd::prelude::*;

verus! {

// ---- V.2 rules_ok ----
// A1
// MUST-012: minVersion ≤ version
pub open spec fn a1(g: GltfS) -> bool {
    g.min_version matches Some((a, b)) ==> a < g.version_major || (a == g.version_major && b <= g.version_minor)
}

// A1
// MUST-012: minVersion ≤ version
fn asset_ok(g: &Gltf) -> (r: bool)
    ensures
        r == a1(g@),
{
    match g.min_version {
        None => true,
        Some((a, b)) => a < g.version_major || (a == g.version_major && b <= g.version_minor),
    }
}

// A2
pub open spec fn a2(g: GltfS) -> bool {
    // MUST-154: extensionsUsed は重複なし
    &&& seq_unique(g.extensions_used)
    // MUST-156: extensionsRequired は重複なし
    &&& seq_unique(g.extensions_required)
    // MUST-157: extensionsRequired ⊆ extensionsUsed
    &&& forall|i: int| 0 <= i < g.extensions_required.len() ==> seq_contains(g.extensions_used, #[trigger] g.extensions_required[i])
    // MUST-153: 使う拡張は extensionsUsed に列挙
    &&& forall|x: Seq<u8>| #[trigger] g.extensions_present.contains(x) ==> seq_contains(g.extensions_used, x)
}

pub proof fn lemma_set_forall(v: Seq<Seq<u8>>, w: Seq<Seq<u8>>)
    ensures
        (forall|x: Seq<u8>| #[trigger] seq_iset(v).contains(x) ==> seq_contains(w, x)) == (forall|k: int|
            0 <= k < v.len() ==> seq_contains(w, #[trigger] v[k])),
{
    if forall|k: int| 0 <= k < v.len() ==> seq_contains(w, #[trigger] v[k]) {
        assert forall|x: Seq<u8>| #[trigger] seq_iset(v).contains(x) implies seq_contains(w, x) by {
            let k = v.index_of(x);
            assert(v[k] == x);
        }
    }
    if forall|x: Seq<u8>| #[trigger] seq_iset(v).contains(x) ==> seq_contains(w, x) {
        assert forall|k: int| 0 <= k < v.len() implies seq_contains(w, #[trigger] v[k]) by {
            assert(v.contains(v[k]));
            assert(seq_iset(v).contains(v[k]));
        }
    }
}

pub proof fn lemma_a2(g: &Gltf)
    ensures
        a2(g@) == (seq_unique(strings_view(g.extensions_used@)) && seq_unique(strings_view(g.extensions_required@))
            && (forall|k: int|
            0 <= k < g.extensions_required.len() ==> seq_contains(
                strings_view(g.extensions_used@),
                #[trigger] strings_view(g.extensions_required@)[k],
            )) && (forall|k: int|
            0 <= k < g.extensions_present.len() ==> seq_contains(
                strings_view(g.extensions_used@),
                #[trigger] strings_view(g.extensions_present@)[k],
            ))),
{
    let u = strings_view(g.extensions_used@);
    let q = strings_view(g.extensions_required@);
    let e = strings_view(g.extensions_present@);
    lemma_set_forall(e, u);
    assert(g@.extensions_present == seq_iset(e));
    assert((forall|x: Seq<u8>| #[trigger] g@.extensions_present.contains(x) ==> seq_contains(u, x)) == (forall|x: Seq<u8>|
        #[trigger] seq_iset(e).contains(x) ==> seq_contains(u, x)));
    assert(g@.extensions_used == u);
    assert(g@.extensions_required == q);
    assert((forall|i: int| 0 <= i < q.len() ==> seq_contains(u, #[trigger] q[i])) == (forall|k: int|
        0 <= k < g.extensions_required.len() ==> seq_contains(u, #[trigger] q[k])));
    assert((forall|k: int| 0 <= k < e.len() ==> seq_contains(u, #[trigger] e[k])) == (forall|k: int|
        0 <= k < g.extensions_present.len() ==> seq_contains(u, #[trigger] e[k])));
}

// A2
// MUST-153, MUST-154, MUST-156, MUST-157: extensionsUsed / extensionsRequired の規則
fn extensions_ok(g: &Gltf) -> (r: bool)
    ensures
        r == a2(g@),
{
    proof {
        lemma_a2(g);
    }
    strings_unique(&g.extensions_used) && strings_unique(&g.extensions_required) && strings_subset(&g.extensions_required, &g.extensions_used) && strings_subset(&g.extensions_present, &g.extensions_used)
}

// C1
// MUST-133, MUST-134: type に対応する射影のプロパティが必要
pub open spec fn camera_rule(c: Camera) -> bool {
    (c.kind == CAMERA_PERSPECTIVE ==> c.has_perspective) && (c.kind == CAMERA_ORTHOGRAPHIC ==> c.has_orthographic)
}

// C1
// MUST-133, MUST-134: type に対応する射影のプロパティが必要
fn cameras_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|i: int| 0 <= i < g@.cameras.len() ==> camera_rule(#[trigger] g@.cameras[i])),
{
    let mut i = 0;
    while i < g.cameras.len()
        invariant
            0 <= i <= g.cameras.len(),
            forall|k: int| 0 <= k < i ==> camera_rule(#[trigger] g@.cameras[k]),
        decreases g.cameras.len() - i,
    {
        let c = &g.cameras[i];
        if (c.kind == CAMERA_PERSPECTIVE && !c.has_perspective) || (c.kind == CAMERA_ORTHOGRAPHIC && !c.has_orthographic) {
            assert(!camera_rule(g@.cameras[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn rules_ok_s(g: GltfS) -> bool {
    &&& a1(g)
    &&& a2(g)
    &&& h1(g)
    &&& h2(g)
    &&& h3(g)
    &&& h4(g)
    &&& meshes_rules(g)
    &&& s1(g)
    &&& s2(g)
    &&& an1(g)
    &&& an2(g)
    &&& forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] view_rule(g, b)
    &&& forall|i: int| 0 <= i < g.accessors.len() ==> #[trigger] accessor_rule(g, i)
    &&& forall|b: int| 0 <= b < g.buffers.len() ==> #[trigger] buffer_rule(g, b)
    &&& forall|i: int| 0 <= i < g.images.len() ==> image_rule(#[trigger] g.images[i])
    &&& forall|i: int| 0 <= i < g.cameras.len() ==> camera_rule(#[trigger] g.cameras[i])
}

// V.2
pub fn rules_ok(g: &Gltf) -> (r: bool)
    requires
        refs_ok(g@),
        supported_s(g@),
    ensures
        r == rules_ok_s(g@),
{
    asset_ok(g) && extensions_ok(g) && graph_ok(g) && meshes_ok(g) && animations_ok(g) && data_ok(g) && buffers_ok(g) && images_ok(g) && cameras_ok(g)
}

pub open spec fn valid(g: GltfS) -> bool {
    refs_ok(g) && supported_s(g) && rules_ok_s(g)
}

// V2 / T2
pub fn validate(g: &Gltf) -> (r: Result<(), GltfError>)
    ensures
        r is Ok == valid(g@),
        r matches Err(GltfError::Unsupported) ==> refs_ok(g@) && !supported_s(g@),
        r matches Err(GltfError::Invalid) ==> !refs_ok(g@) || (supported_s(g@) && !rules_ok_s(g@)),
        !(r matches Err(GltfError::Glb)) && !(r matches Err(GltfError::Json)),
{
    if !refs_in_range(g) {
        Err(GltfError::Invalid)
    } else if !supported(g) {
        Err(GltfError::Unsupported)
    } else if !rules_ok(g) {
        Err(GltfError::Invalid)
    } else {
        Ok(())
    }
}

} // verus!
