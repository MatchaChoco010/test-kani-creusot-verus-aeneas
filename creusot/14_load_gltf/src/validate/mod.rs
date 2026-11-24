pub mod animation;
pub mod data;
pub mod hierarchy;
pub mod mesh;
pub mod refs;
pub mod resource;
pub mod support;
pub mod util;

use creusot_std::prelude::*;
use crate::model::*;
use crate::validate::refs::*;
use crate::validate::support::*;
use crate::validate::util::*;
use crate::validate::hierarchy::*;
use crate::validate::mesh::*;
use crate::validate::animation::*;
use crate::validate::data::*;
use crate::validate::resource::*;

// A1: min_version ≤ (version_major, version_minor)（辞書順）
// MUST-012: minVersion ≤ version
#[logic(open)]
pub fn asset_spec(g: Gltf) -> bool {
    pearlite! {
        match g.min_version {
            None => true,
            Some((a, b)) => a@ < g.version_major@ || (a@ == g.version_major@ && b@ <= g.version_minor@),
        }
    }
}

// MUST-012: minVersion ≤ version
#[ensures(result == asset_spec(*g))]
#[check(terminates)]
fn asset_ok(g: &Gltf) -> bool {
    match g.min_version {
        None => true,
        Some((a, b)) => a < g.version_major || (a == g.version_major && b <= g.version_minor),
    }
}

// A2
// MUST-153, MUST-154, MUST-156, MUST-157: 使う拡張は extensionsUsed にあり、重複がなく、extensionsRequired ⊆ extensionsUsed
#[logic(open)]
pub fn extensions_spec(g: Gltf) -> bool {
    pearlite! {
        str_unique(g.extensions_used@)
            && str_unique(g.extensions_required@)
            && str_subset(g.extensions_required@, g.extensions_used@)
            && str_subset(g.extensions_present@, g.extensions_used@)
    }
}

// MUST-153, MUST-154, MUST-156, MUST-157: 使う拡張は extensionsUsed にあり、重複がなく、extensionsRequired ⊆ extensionsUsed
#[ensures(result == extensions_spec(*g))]
#[check(terminates)]
fn extensions_ok(g: &Gltf) -> bool {
    strings_unique(&g.extensions_used) && strings_unique(&g.extensions_required) && strings_subset(&g.extensions_required, &g.extensions_used) && strings_subset(&g.extensions_present, &g.extensions_used)
}

// C1
// MUST-133, MUST-134: type に応じて perspective / orthographic が必要
#[logic(open)]
pub fn cameras_spec(g: Gltf) -> bool {
    pearlite! {
        forall<i> 0 <= i && i < g.cameras@.len() ==>
            (g.cameras@[i].kind@ == CAMERA_PERSPECTIVE@ ==> g.cameras@[i].has_perspective)
            && (g.cameras@[i].kind@ == CAMERA_ORTHOGRAPHIC@ ==> g.cameras@[i].has_orthographic)
    }
}

// MUST-133, MUST-134: type に応じて perspective / orthographic が必要
#[ensures(result == cameras_spec(*g))]
#[check(terminates)]
fn cameras_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.cameras@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> (g.cameras@[k].kind@ == CAMERA_PERSPECTIVE@ ==> g.cameras@[k].has_perspective) && (g.cameras@[k].kind@ == CAMERA_ORTHOGRAPHIC@ ==> g.cameras@[k].has_orthographic))]
    #[variant(g.cameras@.len() - i@)]
    while i < g.cameras.len() {
        let c = &g.cameras[i];
        if (c.kind == CAMERA_PERSPECTIVE && !c.has_perspective) || (c.kind == CAMERA_ORTHOGRAPHIC && !c.has_orthographic) {
            return false;
        }
        i += 1;
    }
    true
}

// V.2 rules_ok(g)
#[logic(open)]
pub fn rules_spec(g: Gltf) -> bool {
    pearlite! {
        asset_spec(g) && extensions_spec(g) && graph_spec(g) && meshes_spec(g) && animations_spec(g)
            && data_spec(g) && buffers_spec(g) && images_spec(g) && cameras_spec(g)
    }
}

#[requires(refs_ok(*g) && supported_spec(*g))]
#[ensures(result == rules_spec(*g))]
#[check(terminates)]
pub fn rules_ok(g: &Gltf) -> bool {
    asset_ok(g) && extensions_ok(g) && graph_ok(g) && meshes_ok(g) && animations_ok(g) && data_ok(g) && buffers_ok(g) && images_ok(g) && cameras_ok(g)
}

// valid(g) = refs_ok(g) ∧ supported(g) ∧ rules_ok(g)
#[logic(open)]
pub fn valid(g: Gltf) -> bool {
    pearlite! { refs_ok(g) && supported_spec(g) && rules_spec(g) }
}

// T2: validate の結果
#[logic(open)]
pub fn validate_res(g: Gltf, r: Result<(), GltfError>) -> bool {
    pearlite! {
        (r == Ok(()) == valid(g))
            && match r {
                Ok(()) => true,
                Err(GltfError::Unsupported) => refs_ok(g) && !supported_spec(g),
                Err(GltfError::Invalid) => !refs_ok(g) || (supported_spec(g) && !rules_spec(g)),
                Err(_) => false,
            }
    }
}

#[ensures(validate_res(*g, result))]
#[check(terminates)]
pub fn validate(g: &Gltf) -> Result<(), GltfError> {
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
