use creusot_std::prelude::*;
use crate::model::*;
use crate::validate::util::*;
use crate::validate::mesh::*;
#[cfg(creusot)]
use creusot_std::logic::{Mapping, try_such_that};
#[cfg(creusot)]
use crate::validate::refs::*;

#[requires(all_lt(children@, parent@.len()))]
#[ensures((^parent)@.len() == parent@.len())]
#[ensures(result ==> unique_seq(children@)
    && (forall<j> 0 <= j && j < children@.len() ==> parent@[children@[j]@] == None)
    && forall<c> 0 <= c && c < parent@.len() ==>
        (^parent)@[c] == if (exists<j> 0 <= j && j < children@.len() && children@[j]@ == c) { Some(p) } else { parent@[c] })]
#[ensures(!result ==> !(unique_seq(children@) && forall<j> 0 <= j && j < children@.len() ==> parent@[children@[j]@] == None))]
#[check(terminates)]
fn assign_parent(parent: &mut Vec<Option<u64>>, p: u64, children: &Vec<u64>) -> bool {
    let _old = snapshot!(*parent);
    let mut k = 0;
    #[invariant(k@ <= children@.len())]
    #[invariant(parent@.len() == _old@.len())]
    #[invariant(forall<a, b> 0 <= a && a < b && b < k@ ==> children@[a] != children@[b])]
    #[invariant(forall<j> 0 <= j && j < k@ ==> _old@[children@[j]@] == None)]
    #[invariant(forall<c> 0 <= c && c < _old@.len() ==>
        parent@[c] == if (exists<j> 0 <= j && j < k@ && children@[j]@ == c) { Some(p) } else { _old@[c] })]
    #[variant(children@.len() - k@)]
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

#[ensures(result@.len() == n@ && forall<k> 0 <= k && k < n@ ==> result@[k] == None)]
#[check(terminates)]
fn none_vec(n: usize) -> Vec<Option<u64>> {
    let mut v: Vec<Option<u64>> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= n@)]
    #[invariant(v@.len() == i@ && forall<k> 0 <= k && k < i@ ==> v@[k] == None)]
    #[variant(n@ - i@)]
    while i < n {
        v.push(None);
        i += 1;
    }
    v
}

// ノード p の children の k 番目
#[logic(open)]
pub fn child(g: Gltf, p: Int, k: Int) -> Int {
    pearlite! { g.nodes@[p].children@[k]@ }
}

#[logic(open)]
pub fn child_pos(g: Gltf, p: Int, k: Int) -> bool {
    pearlite! { 0 <= p && p < g.nodes@.len() && 0 <= k && k < g.nodes@[p].children@.len() }
}

// H1: すべての children 配列を通して、各ノード番号は高々 1 回
// MUST-016, MUST-017: 各ノードの親は 0 か 1
#[logic(open)]
pub fn h1(g: Gltf) -> bool {
    pearlite! {
        forall<p1, k1, p2, k2> child_pos(g, p1, k1) && child_pos(g, p2, k2) && child(g, p1, k1) == child(g, p2, k2)
            ==> p1 == p2 && k1 == k2
    }
}

#[logic(open)]
pub fn is_parent(g: Gltf, p: Int, c: Int) -> bool {
    pearlite! { exists<k> child_pos(g, p, k) && child(g, p, k) == c }
}

// parent(c): c を children に含むノード（なければ None）
#[logic(open)]
pub fn parent_of(g: Gltf, c: Int) -> Option<Int> {
    pearlite! { try_such_that(|p: Int| is_parent(g, p, c)) }
}

#[logic(open)]
pub fn gpar(g: Gltf) -> Mapping<Int, Option<Int>> {
    pearlite! { |c: Int| parent_of(g, c) }
}

// 以下は実行コードの親配列についての補助定義と補題

#[logic(open)]
pub fn ppar(par: Seq<Option<u64>>) -> Mapping<Int, Option<Int>> {
    pearlite! { |c: Int| if 0 <= c && c < par.len() { opt_int(par[c]) } else { None } }
}

#[logic(open)]
pub fn par_ok(par: Seq<Option<u64>>, n: Int) -> bool {
    pearlite! {
        par.len() == n && forall<c> 0 <= c && c < n ==> match par[c] {
            None => true,
            Some(p) => p@ < n,
        }
    }
}

// H1 のもとで、親の候補が分かれば parent_of が決まる
#[logic(opaque)]
#[requires(h1(g))]
#[ensures(forall<q> is_parent(g, q, c) ==> parent_of(g, c) == Some(q))]
#[ensures((forall<q> !is_parent(g, q, c)) ==> parent_of(g, c) == None)]
pub fn lemma_parent_of(g: Gltf, c: Int) {}

// MUST-016, MUST-017: 各ノードの親は 0 か 1
#[requires(refs_ok(*g))]
#[ensures(match result {
    None => !h1(*g),
    Some(par) => h1(*g) && par_ok(par@, g.nodes@.len()) && ppar(par@) == gpar(*g),
})]
#[check(terminates)]
pub fn parents(g: &Gltf) -> Option<Vec<Option<u64>>> {
    let mut parent = none_vec(g.nodes.len());
    let mut i = 0;
    #[invariant(i@ <= g.nodes@.len())]
    #[invariant(parent@.len() == g.nodes@.len())]
    #[invariant(forall<p1, k1, p2, k2> child_pos(*g, p1, k1) && child_pos(*g, p2, k2) && p1 < i@ && p2 < i@
        && child(*g, p1, k1) == child(*g, p2, k2) ==> p1 == p2 && k1 == k2)]
    #[invariant(forall<c> 0 <= c && c < g.nodes@.len() ==> match parent@[c] {
        None => forall<q, k> child_pos(*g, q, k) && q < i@ ==> child(*g, q, k) != c,
        Some(q) => q@ < i@ && is_parent(*g, q@, c),
    })]
    #[variant(g.nodes@.len() - i@)]
    while i < g.nodes.len() {
        if !assign_parent(&mut parent, i as u64, &g.nodes[i].children) {
            return None;
        }
        i += 1;
    }
    snapshot!(lemma_parent_of(*g, 0));
    proof_assert!(ppar(parent@).ext_eq(gpar(*g)));
    Some(parent)
}

// n から parent を k 回たどったノード
#[logic(open)]
#[variant(k)]
pub fn walk(pf: Mapping<Int, Option<Int>>, n: Int, k: Int) -> Option<Int> {
    pearlite! {
        if k <= 0 { Some(n) } else {
            match walk(pf, n, k - 1) {
                None => None,
                Some(x) => pf[x],
            }
        }
    }
}

// n から b ノード以内にたどり着く、親のないノード r
#[logic(open)]
pub fn is_root_w(pf: Mapping<Int, Option<Int>>, b: Int, n: Int, r: Int) -> bool {
    pearlite! { exists<k> 0 <= k && k < b && walk(pf, n, k) == Some(r) && pf[r] == None }
}

#[logic(open)]
pub fn root_w(pf: Mapping<Int, Option<Int>>, b: Int, n: Int) -> Option<Int> {
    pearlite! { try_such_that(|r: Int| is_root_w(pf, b, n, r)) }
}

#[logic(open)]
pub fn not_root(pf: Mapping<Int, Option<Int>>, o: Option<Int>) -> bool {
    pearlite! {
        match o {
            None => false,
            Some(y) => pf[y] != None,
        }
    }
}

// たどれる限り、それより前のノードはどれも親を持つ
#[logic(opaque)]
#[variant(k)]
#[requires(0 <= k)]
#[ensures(walk(pf, n, k) != None ==> forall<j> 0 <= j && j < k ==> not_root(pf, walk(pf, n, j)))]
pub fn lemma_walk_prefix(pf: Mapping<Int, Option<Int>>, n: Int, k: Int) {
    if k > 0 {
        lemma_walk_prefix(pf, n, k - 1)
    }
}

// 根は一意
#[logic(opaque)]
#[ensures(forall<r1, r2> is_root_w(pf, b, n, r1) && is_root_w(pf, b, n, r2) ==> r1 == r2)]
#[ensures(match root_w(pf, b, n) {
    Some(r) => is_root_w(pf, b, n, r),
    None => forall<r> !is_root_w(pf, b, n, r),
})]
pub fn lemma_root_unique(pf: Mapping<Int, Option<Int>>, b: Int, n: Int) {
    lemma_walk_prefix(pf, n, 0)
}

#[requires(par_ok(parent@, parent@.len()))]
#[requires(n@ < parent@.len())]
#[ensures(opt_int(result) == root_w(ppar(parent@), parent@.len(), n@))]
#[check(terminates)]
pub fn root_of(parent: &Vec<Option<u64>>, n: u64) -> Option<u64> {
    snapshot!(lemma_root_unique(ppar(parent@), parent@.len(), n@));
    let mut cur = n;
    let mut steps = 0;
    #[invariant(steps@ <= parent@.len())]
    #[invariant(cur@ < parent@.len())]
    #[invariant(walk(ppar(parent@), n@, steps@) == Some(cur@))]
    #[invariant(forall<j> 0 <= j && j < steps@ ==> not_root(ppar(parent@), walk(ppar(parent@), n@, j)))]
    #[variant(parent@.len() - steps@)]
    while steps < parent.len() {
        proof_assert!(ppar(parent@)[cur@] == opt_int(parent@[cur@]));
        proof_assert!(parent@[cur@] == None ==> is_root_w(ppar(parent@), parent@.len(), n@, cur@));
        match parent[cur as usize] {
            None => return Some(cur),
            Some(p) => cur = p,
        }
        steps += 1;
    }
    None
}

// a が n の祖先または n 自身
#[logic(open)]
pub fn anc_w(pf: Mapping<Int, Option<Int>>, a: Int, n: Int) -> bool {
    pearlite! { exists<k> 0 <= k && walk(pf, n, k) == Some(a) }
}

#[requires(par_ok(parent@, parent@.len()))]
#[requires(n@ < parent@.len())]
#[requires(exists<r> is_root_w(ppar(parent@), parent@.len(), n@, r))]
#[ensures(result == anc_w(ppar(parent@), a@, n@))]
#[check(terminates)]
fn is_ancestor_or_self(parent: &Vec<Option<u64>>, a: u64, n: u64) -> bool {
    snapshot!(lemma_walk_prefix(ppar(parent@), n@, 0));
    let mut cur = n;
    let mut steps = 0;
    #[invariant(steps@ <= parent@.len())]
    #[invariant(cur@ < parent@.len())]
    #[invariant(walk(ppar(parent@), n@, steps@) == Some(cur@))]
    #[invariant(forall<j> 0 <= j && j < steps@ ==>
        walk(ppar(parent@), n@, j) != Some(a@) && not_root(ppar(parent@), walk(ppar(parent@), n@, j)))]
    #[variant(parent@.len() - steps@)]
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

// MUST-104: スキンのメッシュのプリミティブは JOINTS_0 を持つ
#[ensures(result == forall<p> 0 <= p && p < m.primitives@.len() ==> has_sem(m.primitives@[p].attributes@, SEM_JOINTS@, 0))]
#[check(terminates)]
fn skinned_mesh_ok(m: &Mesh) -> bool {
    let mut p = 0;
    #[invariant(p@ <= m.primitives@.len())]
    #[invariant(forall<k> 0 <= k && k < p@ ==> has_sem(m.primitives@[k].attributes@, SEM_JOINTS@, 0))]
    #[variant(m.primitives@.len() - p@)]
    while p < m.primitives.len() {
        if !has_semantic(&m.primitives[p].attributes, SEM_JOINTS, 0) {
            return false;
        }
        p += 1;
    }
    true
}

#[logic(open)]
pub fn has_root(g: Gltf, n: Int) -> bool {
    pearlite! { exists<r> is_root_w(gpar(g), g.nodes@.len(), n, r) }
}

// H3（ノード i）
// MUST-018, MUST-102, MUST-103, MUST-104: children は重複なし、weights の長さ、skin なら mesh と JOINTS_0 が必要
#[logic(open)]
pub fn h3_node(g: Gltf, i: Int) -> bool {
    pearlite! {
        let n = g.nodes@[i];
        unique_seq(n.children@)
            && !(n.has_matrix && n.has_trs)
            && (n.skin != None || n.weights_len != None ==> n.mesh != None)
            && match n.mesh {
                None => true,
                Some(m) => (match n.weights_len {
                        None => true,
                        Some(w) => w@ == morph_count(g.meshes@[m@]),
                    })
                    && (n.skin != None ==> forall<p> 0 <= p && p < g.meshes@[m@].primitives@.len() ==>
                        has_sem(g.meshes@[m@].primitives@[p].attributes@, SEM_JOINTS@, 0)),
            }
    }
}

// MUST-016, MUST-017: 循環がなく、親をたどると根に着く
// MUST-018, MUST-102, MUST-103: children は重複なし、weights の長さ = モーフターゲットの数、skin なら mesh が必要
#[requires(refs_ok(*g))]
#[requires(par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g))]
#[requires(i@ < g.nodes@.len())]
#[ensures(result == (h3_node(*g, i@) && has_root(*g, i@)))]
#[check(terminates)]
fn node_ok(g: &Gltf, parent: &Vec<Option<u64>>, i: usize) -> bool {
    snapshot!(lemma_root_unique(gpar(*g), g.nodes@.len(), i@));
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

// H2: 各ノードから parent をたどると |N| ノード以内に根に着く
// MUST-016, MUST-017: 循環がなく、親をたどると根に着く
#[logic(open)]
pub fn h2(g: Gltf) -> bool {
    pearlite! { forall<n> 0 <= n && n < g.nodes@.len() ==> has_root(g, n) }
}

#[logic(open)]
pub fn h3(g: Gltf) -> bool {
    pearlite! { forall<i> 0 <= i && i < g.nodes@.len() ==> h3_node(g, i) }
}

#[requires(refs_ok(*g) && par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g))]
#[ensures(result == (h2(*g) && h3(*g)))]
#[check(terminates)]
fn nodes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.nodes@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> h3_node(*g, k) && has_root(*g, k))]
    #[variant(g.nodes@.len() - i@)]
    while i < g.nodes.len() {
        if !node_ok(g, parent, i) {
            return false;
        }
        i += 1;
    }
    true
}

#[requires(all_lt(nodes@, parent@.len()))]
#[ensures(result == forall<k> 0 <= k && k < nodes@.len() ==> parent@[nodes@[k]@] == None)]
#[check(terminates)]
fn all_roots(parent: &Vec<Option<u64>>, nodes: &Vec<u64>) -> bool {
    let mut k = 0;
    #[invariant(k@ <= nodes@.len())]
    #[invariant(forall<j> 0 <= j && j < k@ ==> parent@[nodes@[j]@] == None)]
    #[variant(nodes@.len() - k@)]
    while k < nodes.len() {
        if parent[nodes[k] as usize].is_some() {
            return false;
        }
        k += 1;
    }
    true
}

// H4
// MUST-015: scene.nodes は重複なし
#[logic(open)]
pub fn h4(g: Gltf) -> bool {
    pearlite! {
        forall<s> 0 <= s && s < g.scenes@.len() ==>
            unique_seq(g.scenes@[s].nodes@)
            && forall<k> 0 <= k && k < g.scenes@[s].nodes@.len() ==> parent_of(g, g.scenes@[s].nodes@[k]@) == None
    }
}

// MUST-015: scene.nodes は重複なし
#[requires(refs_ok(*g) && par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g))]
#[ensures(result == h4(*g))]
#[check(terminates)]
fn scenes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut s = 0;
    #[invariant(s@ <= g.scenes@.len())]
    #[invariant(forall<k> 0 <= k && k < s@ ==> unique_seq(g.scenes@[k].nodes@) && forall<j> 0 <= j && j < g.scenes@[k].nodes@.len() ==> parent_of(*g, g.scenes@[k].nodes@[j]@) == None)]
    #[variant(g.scenes@.len() - s@)]
    while s < g.scenes.len() {
        if !unique(&g.scenes[s].nodes) || !all_roots(parent, &g.scenes[s].nodes) {
            return false;
        }
        s += 1;
    }
    true
}

// MUST-100, MUST-101: 関節には共通の祖先があり、skeleton はその祖先
#[requires(par_ok(parent@, parent@.len()) && all_lt(sk.joints@, parent@.len()) && forall<k> 0 <= k && k < sk.joints@.len() ==> exists<r> is_root_w(ppar(parent@), parent@.len(), sk.joints@[k]@, r))]
#[ensures(result == forall<k> 0 <= k && k < sk.joints@.len() ==> root_w(ppar(parent@), parent@.len(), sk.joints@[k]@) == opt_int(root) && match sk.skeleton { None => true, Some(r) => anc_w(ppar(parent@), r@, sk.joints@[k]@) })]
#[check(terminates)]
fn joints_ok(parent: &Vec<Option<u64>>, sk: &Skin, root: Option<u64>) -> bool {
    let mut k = 0;
    #[invariant(k@ <= sk.joints@.len())]
    #[invariant(forall<j> 0 <= j && j < k@ ==> root_w(ppar(parent@), parent@.len(), sk.joints@[j]@) == opt_int(root) && match sk.skeleton { None => true, Some(r) => anc_w(ppar(parent@), r@, sk.joints@[j]@) })]
    #[variant(sk.joints@.len() - k@)]
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

#[logic(open)]
pub fn root_spec(g: Gltf, n: Int) -> Option<Int> {
    pearlite! { root_w(gpar(g), g.nodes@.len(), n) }
}

// S1（スキン sk）
// MUST-096, MUST-097, MUST-100, MUST-101: joints は重複なし、逆バインド行列の型と要素数、関節に共通の祖先、skeleton はその祖先
#[logic(open)]
pub fn s1_skin(g: Gltf, sk: Skin) -> bool {
    pearlite! {
        sk.joints@.len() > 0
            && unique_seq(sk.joints@)
            && (forall<k> 0 <= k && k < sk.joints@.len() ==> root_spec(g, sk.joints@[k]@) == root_spec(g, sk.joints@[0]@))
            && (match sk.skeleton {
                None => true,
                Some(r) => forall<k> 0 <= k && k < sk.joints@.len() ==> anc_w(gpar(g), r@, sk.joints@[k]@),
            })
            && match sk.inverse_bind_matrices {
                None => true,
                Some(a) => g.accessors@[a@].is_matrix && g.accessors@[a@].components@ == 16
                    && g.accessors@[a@].component_type@ == 5126 && g.accessors@[a@].count@ >= sk.joints@.len(),
            }
    }
}

// MUST-096, MUST-097: joints は重複なし、逆バインド行列のアクセサーの型と要素数
#[requires(refs_ok(*g) && par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g) && h2(*g))]
#[requires(all_lt(sk.joints@, g.nodes@.len()) && opt_lt(sk.inverse_bind_matrices, g.accessors@.len()))]
#[ensures(result == s1_skin(*g, *sk))]
#[check(terminates)]
fn skin_ok(g: &Gltf, parent: &Vec<Option<u64>>, sk: &Skin) -> bool {
    if sk.joints.len() == 0 || !unique(&sk.joints) {
        return false;
    }
    proof_assert!(forall<k> 0 <= k && k < sk.joints@.len() ==> has_root(*g, sk.joints@[k]@));
    proof_assert!(forall<k> 0 <= k && k < sk.joints@.len() ==>
        exists<r> is_root_w(ppar(parent@), parent@.len(), sk.joints@[k]@, r));
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

#[logic(open)]
pub fn s1(g: Gltf) -> bool {
    pearlite! { forall<s> 0 <= s && s < g.skins@.len() ==> s1_skin(g, g.skins@[s]) }
}

#[requires(refs_ok(*g) && par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g) && h2(*g))]
#[ensures(result == s1(*g))]
#[check(terminates)]
fn skin_list_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.skins@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> s1_skin(*g, g.skins@[k]))]
    #[variant(g.skins@.len() - i@)]
    while i < g.skins.len() {
        if !skin_ok(g, parent, &g.skins[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(open)]
pub fn in_nodes(o: Option<Int>, nodes: Seq<u64>) -> bool {
    pearlite! {
        match o {
            None => false,
            Some(r) => exists<k> 0 <= k && k < nodes.len() && nodes[k]@ == r,
        }
    }
}

// MUST-105: スキンの関節の共通の祖先は同じシーンに属する
#[ensures(result == forall<k> 0 <= k && k < g.scenes@.len() ==> in_nodes(opt_int(nr), g.scenes@[k].nodes@) ==> in_nodes(opt_int(jr), g.scenes@[k].nodes@))]
#[check(terminates)]
fn skin_scene_ok(g: &Gltf, jr: Option<u64>, nr: Option<u64>) -> bool {
    let mut sc = 0;
    #[invariant(sc@ <= g.scenes@.len())]
    #[invariant(forall<k> 0 <= k && k < sc@ ==> in_nodes(opt_int(nr), g.scenes@[k].nodes@) ==> in_nodes(opt_int(jr), g.scenes@[k].nodes@))]
    #[variant(g.scenes@.len() - sc@)]
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

// skinned_nodes_ok が調べる条件（S1 のもとで S2 と同値）
#[logic(open)]
pub fn skinned_nodes_spec(g: Gltf) -> bool {
    pearlite! {
        forall<i> 0 <= i && i < g.nodes@.len() ==> match g.nodes@[i].skin {
            None => true,
            Some(s) => g.skins@[s@].joints@.len() > 0 && forall<sc> 0 <= sc && sc < g.scenes@.len() ==>
                in_nodes(root_spec(g, i), g.scenes@[sc].nodes@)
                    ==> in_nodes(root_spec(g, g.skins@[s@].joints@[0]@), g.scenes@[sc].nodes@),
        }
    }
}

#[requires(refs_ok(*g) && par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g))]
#[ensures(result == skinned_nodes_spec(*g))]
#[check(terminates)]
fn skinned_nodes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.nodes@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> match g.nodes@[k].skin {
        None => true,
        Some(s) => g.skins@[s@].joints@.len() > 0 && forall<sc> 0 <= sc && sc < g.scenes@.len() ==>
            in_nodes(root_spec(*g, k), g.scenes@[sc].nodes@)
                ==> in_nodes(root_spec(*g, g.skins@[s@].joints@[0]@), g.scenes@[sc].nodes@),
    })]
    #[variant(g.nodes@.len() - i@)]
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

#[requires(refs_ok(*g) && par_ok(parent@, g.nodes@.len()) && ppar(parent@) == gpar(*g) && h2(*g))]
#[ensures(result == (s1(*g) && skinned_nodes_spec(*g)))]
#[check(terminates)]
fn skins_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> bool {
    skin_list_ok(g, parent) && skinned_nodes_ok(g, parent)
}

// S2
// MUST-105: スキンの関節の共通の祖先は同じシーンに属する
#[logic(open)]
pub fn s2(g: Gltf) -> bool {
    pearlite! {
        forall<i> 0 <= i && i < g.nodes@.len() ==> match g.nodes@[i].skin {
            None => true,
            Some(s) => forall<sc> 0 <= sc && sc < g.scenes@.len() ==>
                in_nodes(root_spec(g, i), g.scenes@[sc].nodes@)
                    ==> in_nodes(root_spec(g, g.skins@[s@].joints@[0]@), g.scenes@[sc].nodes@),
        }
    }
}

#[logic(open)]
pub fn graph_spec(g: Gltf) -> bool {
    pearlite! { h1(g) && h2(g) && h3(g) && h4(g) && s1(g) && s2(g) }
}

#[requires(refs_ok(*g))]
#[ensures(result == graph_spec(*g))]
#[check(terminates)]
pub(crate) fn graph_ok(g: &Gltf) -> bool {
    match parents(g) {
        None => false,
        Some(parent) => nodes_ok(g, &parent) && scenes_ok(g, &parent) && skins_ok(g, &parent),
    }
}
