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

fn asset_ok(g: &Gltf) -> bool {
    match g.min_version {
        None => true,
        Some((a, b)) => a < g.version_major || (a == g.version_major && b <= g.version_minor),
    }
}

fn extensions_ok(g: &Gltf) -> bool {
    strings_unique(&g.extensions_used) && strings_unique(&g.extensions_required) && strings_subset(&g.extensions_required, &g.extensions_used) && strings_subset(&g.extensions_present, &g.extensions_used)
}

fn cameras_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.cameras.len() {
        let c = &g.cameras[i];
        if (c.kind == CAMERA_PERSPECTIVE && !c.has_perspective) || (c.kind == CAMERA_ORTHOGRAPHIC && !c.has_orthographic) {
            return false;
        }
        i += 1;
    }
    true
}

pub fn rules_ok(g: &Gltf) -> bool {
    asset_ok(g) && extensions_ok(g) && graph_ok(g) && meshes_ok(g) && animations_ok(g) && data_ok(g) && buffers_ok(g) && images_ok(g) && cameras_ok(g)
}

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
