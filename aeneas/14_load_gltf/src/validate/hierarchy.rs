use crate::model::*;
use crate::validate::util::*;
use crate::validate::mesh::*;

fn assign_parent(parent: &mut Vec<Option<u64>>, p: u64, children: &Vec<u64>) -> bool {
    let mut k = 0;
    while k < children.len() {
        let c = children[k] as usize;
        if parent[c].is_some() {
            return false;
        }
        parent[c] = Some(p);
        k += 1;
    }
    true
}

fn none_vec(n: usize) -> Vec<Option<u64>> {
    let mut v: Vec<Option<u64>> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(None);
        i += 1;
    }
    v
}

pub fn parents(g: &Gltf) -> Option<Vec<Option<u64>>> {
    let mut parent = none_vec(g.nodes.len());
    let mut i = 0;
    while i < g.nodes.len() {
        if !assign_parent(&mut parent, i as u64, &g.nodes[i].children) {
            return None;
        }
        i += 1;
    }
    Some(parent)
}

pub fn root_of(parent: &Vec<Option<u64>>, n: u64) -> Option<u64> {
    let mut cur = n;
    let mut steps = 0;
    while steps < parent.len() {
        match parent[cur as usize] {
            None => return Some(cur),
            Some(p) => cur = p,
        }
        steps += 1;
    }
    None
}

fn is_ancestor_or_self(parent: &Vec<Option<u64>>, a: u64, n: u64) -> bool {
    let mut cur = n;
    let mut steps = 0;
    while steps < parent.len() {
        if cur == a {
            return true;
        }
        match parent[cur as usize] {
            None => return false,
            Some(p) => cur = p,
        }
        steps += 1;
    }
    false
}

fn skinned_mesh_ok(m: &Mesh) -> bool {
    let mut p = 0;
    while p < m.primitives.len() {
        if !has_semantic(&m.primitives[p].attributes, SEM_JOINTS, 0) {
            return false;
        }
        p += 1;
    }
    true
}

fn node_ok(g: &Gltf, parent: &Vec<Option<u64>>, i: usize) -> bool {
    let n = &g.nodes[i];
    if !unique(&n.children) || (n.has_matrix && n.has_trs) || ((n.skin.is_some() || n.weights_len.is_some()) && n.mesh.is_none()) {
        return false;
    }
    if root_of(parent, i as u64).is_none() {
        return false;
    }
    match n.mesh {
        None => true,
        Some(m) => {
            let mesh = &g.meshes[m as usize];
            let weights_ok = match n.weights_len {
                None => true,
                Some(w) => w == morph_target_count(mesh),
            };
            weights_ok && (n.skin.is_none() || skinned_mesh_ok(mesh))
        }
    }
}

fn nodes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut i = 0;
    while i < g.nodes.len() {
        if !node_ok(g, parent, i) {
            return false;
        }
        i += 1;
    }
    true
}

fn all_roots(parent: &Vec<Option<u64>>, nodes: &Vec<u64>) -> bool {
    let mut k = 0;
    while k < nodes.len() {
        if parent[nodes[k] as usize].is_some() {
            return false;
        }
        k += 1;
    }
    true
}

fn scenes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut s = 0;
    while s < g.scenes.len() {
        if !unique(&g.scenes[s].nodes) || !all_roots(parent, &g.scenes[s].nodes) {
            return false;
        }
        s += 1;
    }
    true
}

fn joints_ok(parent: &Vec<Option<u64>>, sk: &Skin, root: Option<u64>) -> bool {
    let mut k = 0;
    while k < sk.joints.len() {
        if !opt_eq(root_of(parent, sk.joints[k]), root) {
            return false;
        }
        match sk.skeleton {
            None => {}
            Some(r) => {
                if !is_ancestor_or_self(parent, r, sk.joints[k]) {
                    return false;
                }
            }
        }
        k += 1;
    }
    true
}

fn skin_ok(g: &Gltf, parent: &Vec<Option<u64>>, sk: &Skin) -> bool {
    if sk.joints.len() == 0 || !unique(&sk.joints) {
        return false;
    }
    if !joints_ok(parent, sk, root_of(parent, sk.joints[0])) {
        return false;
    }
    match sk.inverse_bind_matrices {
        None => true,
        Some(m) => {
            let a = &g.accessors[m as usize];
            a.is_matrix && a.components == 16 && float32(a) && a.count >= sk.joints.len() as u64
        }
    }
}

fn skin_list_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut i = 0;
    while i < g.skins.len() {
        if !skin_ok(g, parent, &g.skins[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn skin_scene_ok(g: &Gltf, jr: Option<u64>, nr: Option<u64>) -> bool {
    let mut sc = 0;
    while sc < g.scenes.len() {
        let nodes = &g.scenes[sc].nodes;
        let node_in = match nr {
            None => false,
            Some(r) => contains(nodes, r),
        };
        let joint_in = match jr {
            None => false,
            Some(r) => contains(nodes, r),
        };
        if node_in && !joint_in {
            return false;
        }
        sc += 1;
    }
    true
}

fn skinned_nodes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut i = 0;
    while i < g.nodes.len() {
        match g.nodes[i].skin {
            None => {}
            Some(s) => {
                let sk = &g.skins[s as usize];
                if sk.joints.len() == 0 || !skin_scene_ok(g, root_of(parent, sk.joints[0]), root_of(parent, i as u64)) {
                    return false;
                }
            }
        }
        i += 1;
    }
    true
}

fn skins_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    skin_list_ok(g, parent) && skinned_nodes_ok(g, parent)
}

pub(crate) fn graph_ok(g: &Gltf) -> bool {
    match parents(g) {
        None => false,
        Some(parent) => nodes_ok(g, &parent) && scenes_ok(g, &parent) && skins_ok(g, &parent),
    }
}
