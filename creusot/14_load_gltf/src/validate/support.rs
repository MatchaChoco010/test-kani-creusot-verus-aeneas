use creusot_std::prelude::*;
use crate::model::*;

#[logic(open)]
pub fn known_ct(ct: Int) -> bool {
    pearlite! { ct == 5120 || ct == 5121 || ct == 5122 || ct == 5123 || ct == 5125 || ct == 5126 }
}

#[ensures(result == known_ct(ct@))]
#[check(terminates)]
fn known_component_type(ct: u64) -> bool {
    ct == 5120 || ct == 5121 || ct == 5122 || ct == 5123 || ct == 5125 || ct == 5126
}

#[ensures(result == forall<i> 0 <= i && i < g.accessors@.len() ==> known_ct(g.accessors@[i].component_type@))]
#[check(terminates)]
fn component_types_known(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.accessors@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> known_ct(g.accessors@[k].component_type@))]
    #[variant(g.accessors@.len() - i@)]
    while i < g.accessors.len() {
        if !known_component_type(g.accessors[i].component_type) {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == forall<j> 0 <= j && j < m.primitives@.len() ==> m.primitives@[j].mode@ <= 6)]
#[check(terminates)]
fn primitive_modes_known(m: &Mesh) -> bool {
    let mut j = 0;
    #[invariant(j@ <= m.primitives@.len())]
    #[invariant(forall<k> 0 <= k && k < j@ ==> m.primitives@[k].mode@ <= 6)]
    #[variant(m.primitives@.len() - j@)]
    while j < m.primitives.len() {
        if m.primitives[j].mode > 6 {
            return false;
        }
        j += 1;
    }
    true
}

#[ensures(result == forall<i, j> 0 <= i && i < g.meshes@.len() && 0 <= j && j < g.meshes@[i].primitives@.len() ==> g.meshes@[i].primitives@[j].mode@ <= 6)]
#[check(terminates)]
fn modes_known(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.meshes@.len())]
    #[invariant(forall<k, j> 0 <= k && k < i@ && 0 <= j && j < g.meshes@[k].primitives@.len() ==> g.meshes@[k].primitives@[j].mode@ <= 6)]
    #[variant(g.meshes@.len() - i@)]
    while i < g.meshes.len() {
        if !primitive_modes_known(&g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

// MUST-011: minVersion にこのローダーが対応する
#[logic(open)]
pub fn min_version_ok(v: Option<(u64, u64)>) -> bool {
    pearlite! {
        match v {
            None => true,
            Some((a, b)) => a@ < 2 || (a@ == 2 && b@ == 0),
        }
    }
}

#[ensures(result == min_version_ok(v))]
#[check(terminates)]
fn min_version_supported(v: Option<(u64, u64)>) -> bool {
    match v {
        None => true,
        Some((a, b)) => a < 2 || (a == 2 && b == 0),
    }
}

// V.1: このローダーが扱えること
#[logic(open)]
pub fn supported_spec(g: Gltf) -> bool {
    pearlite! {
        g.version_major@ == 2
        && min_version_ok(g.min_version)
        && g.extensions_required@.len() == 0
        && (forall<i> 0 <= i && i < g.accessors@.len() ==> known_ct(g.accessors@[i].component_type@))
        && (forall<i, j> 0 <= i && i < g.meshes@.len() && 0 <= j && j < g.meshes@[i].primitives@.len() ==>
            g.meshes@[i].primitives@[j].mode@ <= 6)
    }
}

// MUST-011: minVersion にこのローダーが対応する
#[ensures(result == supported_spec(*g))]
#[check(terminates)]
pub fn supported(g: &Gltf) -> bool {
    g.version_major == 2 && min_version_supported(g.min_version) && g.extensions_required.len() == 0 && component_types_known(g) && modes_known(g)
}
