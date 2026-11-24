use crate::model::*;

fn known_component_type(ct: u64) -> bool {
    ct == 5120 || ct == 5121 || ct == 5122 || ct == 5123 || ct == 5125 || ct == 5126
}

fn component_types_known(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.accessors.len() {
        if !known_component_type(g.accessors[i].component_type) {
            return false;
        }
        i += 1;
    }
    true
}

fn primitive_modes_known(m: &Mesh) -> bool {
    let mut j = 0;
    while j < m.primitives.len() {
        if m.primitives[j].mode > 6 {
            return false;
        }
        j += 1;
    }
    true
}

fn modes_known(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.meshes.len() {
        if !primitive_modes_known(&g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn min_version_supported(v: Option<(u64, u64)>) -> bool {
    match v {
        None => true,
        Some((a, b)) => a < 2 || (a == 2 && b == 0),
    }
}

pub fn supported(g: &Gltf) -> bool {
    g.version_major == 2 && min_version_supported(g.min_version) && g.extensions_required.len() == 0 && component_types_known(g) && modes_known(g)
}
