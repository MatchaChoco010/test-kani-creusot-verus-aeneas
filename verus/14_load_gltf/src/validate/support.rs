use crate::model::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::validate::util::*;

verus! {

// ---- V.1 supported ----
pub open spec fn known_ct(ct: u64) -> bool {
    ct == 5120 || ct == 5121 || ct == 5122 || ct == 5123 || ct == 5125 || ct == 5126
}

fn known_component_type(ct: u64) -> (r: bool)
    ensures
        r == known_ct(ct),
{
    ct == 5120 || ct == 5121 || ct == 5122 || ct == 5123 || ct == 5125 || ct == 5126
}

fn component_types_known(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|a: int| 0 <= a < g@.accessors.len() ==> known_ct(#[trigger] g@.accessors[a].component_type)),
{
    let mut i = 0;
    while i < g.accessors.len()
        invariant
            0 <= i <= g.accessors.len(),
            forall|a: int| 0 <= a < i ==> known_ct(#[trigger] g@.accessors[a].component_type),
        decreases g.accessors.len() - i,
    {
        if !known_component_type(g.accessors[i].component_type) {
            return false;
        }
        i += 1;
    }
    true
}

fn primitive_modes_known(m: &Mesh) -> (r: bool)
    ensures
        r == (forall|p: int| 0 <= p < m@.primitives.len() ==> #[trigger] m@.primitives[p].mode <= 6),
{
    let mut j = 0;
    while j < m.primitives.len()
        invariant
            0 <= j <= m.primitives.len(),
            forall|p: int| 0 <= p < j ==> #[trigger] m@.primitives[p].mode <= 6,
        decreases m.primitives.len() - j,
    {
        proof {
            assert(m@.primitives[j as int].mode == m.primitives@[j as int].mode);
        }
        if m.primitives[j].mode > 6 {
            return false;
        }
        j += 1;
    }
    true
}

fn modes_known(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|m: int, p: int|
            0 <= m < g@.meshes.len() && 0 <= p < g@.meshes[m].primitives.len() ==> #[trigger] prim(g@, m, p).mode <= 6),
{
    let mut i = 0;
    while i < g.meshes.len()
        invariant
            0 <= i <= g.meshes.len(),
            forall|m: int, p: int|
                0 <= m < i && 0 <= p < g@.meshes[m].primitives.len() ==> #[trigger] prim(g@, m, p).mode <= 6,
        decreases g.meshes.len() - i,
    {
        proof {
            assert(g@.meshes[i as int] == g.meshes@[i as int]@);
        }
        if !primitive_modes_known(&g.meshes[i]) {
            proof {
                let p = choose|p: int| 0 <= p < g@.meshes[i as int].primitives.len() && !(g@.meshes[i as int].primitives[p].mode <= 6);
                assert(!(prim(g@, i as int, p).mode <= 6));
            }
            return false;
        }
        i += 1;
    }
    true
}

fn min_version_supported(v: Option<(u64, u64)>) -> (r: bool)
    ensures
        r == (v matches Some((a, b)) ==> a < 2 || (a == 2 && b == 0)),
{
    match v {
        None => true,
        Some((a, b)) => a < 2 || (a == 2 && b == 0),
    }
}

// MUST-011: minVersion に対応しなければ読み込まない
pub open spec fn supported_s(g: GltfS) -> bool {
    &&& g.version_major == 2
    &&& (g.min_version matches Some((a, b)) ==> a < 2 || (a == 2 && b == 0))
    &&& g.extensions_required.len() == 0
    &&& forall|a: int| 0 <= a < g.accessors.len() ==> known_ct(#[trigger] g.accessors[a].component_type)
    &&& forall|m: int, p: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() ==> #[trigger] prim(g, m, p).mode <= 6
}

// V.1
// MUST-011: minVersion に対応しなければ読み込まない
pub fn supported(g: &Gltf) -> (r: bool)
    ensures
        r == supported_s(g@),
{
    g.version_major == 2 && min_version_supported(g.min_version) && g.extensions_required.len() == 0 && component_types_known(g) && modes_known(g)
}

} // verus!
