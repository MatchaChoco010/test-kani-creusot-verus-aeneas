use crate::model::*;
use crate::validate::util::*;
use crate::validate::mesh::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::validate::refs::*;

verus! {

fn assign_parent(parent: &mut Vec<Option<u64>>, p: u64, children: &Vec<u64>) -> (r: bool)
    requires
        forall|k: int| 0 <= k < children.len() ==> #[trigger] children@[k] < old(parent).len(),
    ensures
        final(parent)@.len() == old(parent)@.len(),
        r ==> (forall|k: int| 0 <= k < children.len() ==> (#[trigger] old(parent)@[children@[k] as int]) is None),
        r ==> seq_unique(children@),
        r ==> forall|c: int|
            0 <= c < old(parent)@.len() ==> #[trigger] final(parent)@[c] == (if seq_contains(children@, c as u64) {
                Some(p)
            } else {
                old(parent)@[c]
            }),
        !r ==> (exists|k: int| 0 <= k < children.len() && (#[trigger] old(parent)@[children@[k] as int]) is Some) || !seq_unique(
            children@,
        ),
{
    let ghost p0 = parent@;
    proof {
        assert(p0.len() == parent.len());
    }
    let mut k = 0;
    while k < children.len()
        invariant
            p0 == old(parent)@,
            p0.len() <= usize::MAX,
            forall|j: int| 0 <= j < children.len() ==> #[trigger] children@[j] < p0.len(),
            parent@.len() == p0.len(),
            0 <= k <= children.len(),
            forall|j: int| 0 <= j < k ==> (#[trigger] p0[children@[j] as int]) is None,
            forall|a: int, b: int| 0 <= a < b < k ==> children@[a] != children@[b],
            forall|c: int|
                0 <= c < p0.len() ==> #[trigger] parent@[c] == (if seq_contains(children@.subrange(0, k as int), c as u64) {
                    Some(p)
                } else {
                    p0[c]
                }),
        decreases children.len() - k,
    {
        let c = children[k] as usize;
        if parent[c].is_some() {
            proof {
                if p0[c as int] is None {
                    assert(seq_contains(children@.subrange(0, k as int), c as u64));
                    let j = choose|j: int| 0 <= j < k && children@.subrange(0, k as int)[j] == c as u64;
                    assert(children@[j] == children@[k as int]);
                }
            }
            return false;
        }
        proof {
            assert forall|j: int| 0 <= j < k implies children@[j] != children@[k as int] by {
                if children@[j] == children@[k as int] {
                    assert(children@.subrange(0, k as int)[j] == children@[j]);
                }
            }
        }
        parent[c] = Some(p);
        k += 1;
        proof {
            assert forall|x: int| 0 <= x < p0.len() implies #[trigger] parent@[x] == (if seq_contains(children@.subrange(0, k as int), x as u64) {
                Some(p)
            } else {
                p0[x]
            }) by {
                let s1 = children@.subrange(0, k - 1);
                let s2 = children@.subrange(0, k as int);
                if seq_contains(s1, x as u64) {
                    let j = choose|j: int| 0 <= j < s1.len() && s1[j] == x as u64;
                    assert(s2[j] == x as u64);
                }
                assert(s2[k - 1] == children@[k - 1]);
                if seq_contains(s2, x as u64) && x != c {
                    let j = choose|j: int| 0 <= j < s2.len() && s2[j] == x as u64;
                    if j < k - 1 {
                        assert(s1[j] == x as u64);
                    }
                }
                if x == c {
                    assert(s2[k - 1] == x as u64);
                }
            }
        }
    }
    proof {
        assert(children@.subrange(0, k as int) =~= children@);
    }
    true
}

fn none_vec(n: usize) -> (r: Vec<Option<u64>>)
    ensures
        r@.len() == n,
        forall|c: int| 0 <= c < n ==> (#[trigger] r@[c]) is None,
{
    let mut v: Vec<Option<u64>> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@.len() == i,
            forall|c: int| 0 <= c < i ==> (#[trigger] v@[c]) is None,
        decreases n - i,
    {
        v.push(None);
        i += 1;
    }
    v
}

// H1: すべての children 配列を通して各ノードは高々 1 回現れる
// MUST-016, MUST-017: 各ノードの親は高々 1 つ
pub open spec fn h1(g: GltfS) -> bool {
    forall|p1: int, k1: int, p2: int, k2: int|
        0 <= p1 < g.nodes.len() && 0 <= k1 < g.nodes[p1].children.len() && 0 <= p2 < g.nodes.len() && 0 <= k2
            < g.nodes[p2].children.len() && #[trigger] g.nodes[p1].children[k1] == #[trigger] g.nodes[p2].children[k2]
            ==> p1 == p2 && k1 == k2
}

pub open spec fn is_child_of(g: GltfS, c: int, p: int) -> bool {
    0 <= p < g.nodes.len() && exists|k: int| 0 <= k < g.nodes[p].children.len() && g.nodes[p].children[k] == c
}

pub open spec fn has_parent(g: GltfS, c: int) -> bool {
    exists|p: int| #[trigger] is_child_of(g, c, p)
}

pub open spec fn parent_of(g: GltfS, c: int) -> int {
    choose|p: int| #[trigger] is_child_of(g, c, p)
}

// 親ベクトルの正しさ: pv[c] = Some(q) ⇔ c は N[q] の子
pub open spec fn parent_vec_ok(g: GltfS, pv: Seq<Option<u64>>) -> bool {
    &&& pv.len() == g.nodes.len()
    &&& forall|c: int|
        0 <= c < pv.len() ==> match #[trigger] pv[c] {
            Some(q) => q < g.nodes.len() && is_child_of(g, c, q as int) && has_parent(g, c) && parent_of(g, c) == q,
            None => !has_parent(g, c),
        }
}

pub open spec fn assigned(g: GltfS, i: int, kk: int, q: int, k: int) -> bool {
    0 <= q < g.nodes.len() && 0 <= k < g.nodes[q].children.len() && (q < i || (q == i && k < kk))
}

pub open spec fn h1_upto(g: GltfS, i: int, kk: int) -> bool {
    forall|p1: int, k1: int, p2: int, k2: int|
        assigned(g, i, kk, p1, k1) && assigned(g, i, kk, p2, k2) && #[trigger] g.nodes[p1].children[k1]
            == #[trigger] g.nodes[p2].children[k2] ==> p1 == p2 && k1 == k2
}

pub open spec fn pv_partial(g: GltfS, pv: Seq<Option<u64>>, i: int) -> bool {
    &&& pv.len() == g.nodes.len()
    &&& forall|c: int|
        0 <= c < pv.len() && (#[trigger] pv[c]) is Some ==> exists|k: int|
            assigned(g, i, 0, pv[c]->Some_0 as int, k) && #[trigger] g.nodes[pv[c]->Some_0 as int].children[k] == c
    &&& forall|q: int, k: int| assigned(g, i, 0, q, k) ==> pv[#[trigger] g.nodes[q].children[k] as int] == Some(q as u64)
    &&& h1_upto(g, i, 0)
}

pub proof fn lemma_h1_parent_unique(g: GltfS, c: int, q: int)
    requires
        h1(g),
        is_child_of(g, c, q),
    ensures
        has_parent(g, c),
        parent_of(g, c) == q,
{
    assert(has_parent(g, c));
    let q2 = parent_of(g, c);
    assert(is_child_of(g, c, q2));
    let k1 = choose|k: int| 0 <= k < g.nodes[q].children.len() && g.nodes[q].children[k] == c;
    let k2 = choose|k: int| 0 <= k < g.nodes[q2].children.len() && g.nodes[q2].children[k] == c;
    assert(g.nodes[q].children[k1] == g.nodes[q2].children[k2]);
}

pub proof fn lemma_pv_step(g: GltfS, pb: Seq<Option<u64>>, pa: Seq<Option<u64>>, i: int)
    requires
        refs_ok(g),
        g.nodes.len() <= usize::MAX,
        0 <= i < g.nodes.len(),
        pv_partial(g, pb, i),
        pa.len() == pb.len(),
        forall|k: int| 0 <= k < g.nodes[i].children.len() ==> (#[trigger] pb[g.nodes[i].children[k] as int]) is None,
        seq_unique(g.nodes[i].children),
        forall|c: int|
            0 <= c < pb.len() ==> #[trigger] pa[c] == (if seq_contains(g.nodes[i].children, c as u64) {
                Some(i as u64)
            } else {
                pb[c]
            }),
    ensures
        pv_partial(g, pa, i + 1),
{
    let ch = g.nodes[i].children;
    assert forall|c: int| 0 <= c < pa.len() && (#[trigger] pa[c]) is Some implies exists|k: int|
        assigned(g, i + 1, 0, pa[c]->Some_0 as int, k) && #[trigger] g.nodes[pa[c]->Some_0 as int].children[k] == c by {
        if seq_contains(ch, c as u64) {
            let k = choose|k: int| 0 <= k < ch.len() && ch[k] == c as u64;
            assert(pa[c]->Some_0 as int == i);
            assert(assigned(g, i + 1, 0, i, k) && g.nodes[i].children[k] == c);
        } else {
            assert(pb[c] is Some);
            let q = pb[c]->Some_0 as int;
            let k = choose|k: int| assigned(g, i, 0, pb[c]->Some_0 as int, k) && #[trigger] g.nodes[pb[c]->Some_0 as int].children[k] == c;
            assert(pa[c]->Some_0 as int == q);
            assert(assigned(g, i + 1, 0, q, k) && g.nodes[q].children[k] == c);
        }
    }
    assert forall|q: int, k: int| assigned(g, i + 1, 0, q, k) implies pa[#[trigger] g.nodes[q].children[k] as int] == Some(q as u64) by {
        let c = g.nodes[q].children[k] as int;
        assert(c < pb.len());
        if q == i {
            assert(seq_contains(ch, c as u64));
        } else {
            assert(assigned(g, i, 0, q, k));
            assert(pb[c] == Some(q as u64));
            if seq_contains(ch, c as u64) {
                let k2 = choose|k2: int| 0 <= k2 < ch.len() && ch[k2] == c as u64;
                assert(pb[g.nodes[i].children[k2] as int] is None);
            }
        }
    }
    assert forall|p1: int, k1: int, p2: int, k2: int|
        assigned(g, i + 1, 0, p1, k1) && assigned(g, i + 1, 0, p2, k2) && #[trigger] g.nodes[p1].children[k1]
            == #[trigger] g.nodes[p2].children[k2] implies p1 == p2 && k1 == k2 by {
        if p1 == i && p2 == i {
        } else if p1 == i {
            assert(assigned(g, i, 0, p2, k2));
            assert(pb[g.nodes[p2].children[k2] as int] == Some(p2 as u64));
            assert(pb[g.nodes[i].children[k1] as int] is None);
        } else if p2 == i {
            assert(assigned(g, i, 0, p1, k1));
            assert(pb[g.nodes[p1].children[k1] as int] == Some(p1 as u64));
            assert(pb[g.nodes[i].children[k2] as int] is None);
        } else {
            assert(assigned(g, i, 0, p1, k1));
            assert(assigned(g, i, 0, p2, k2));
        }
    }
}

pub proof fn lemma_pv_final(g: GltfS, pv: Seq<Option<u64>>)
    requires
        refs_ok(g),
        pv_partial(g, pv, g.nodes.len() as int),
    ensures
        h1(g),
        parent_vec_ok(g, pv),
{
    let n = g.nodes.len() as int;
    assert forall|p1: int, k1: int, p2: int, k2: int|
        0 <= p1 < g.nodes.len() && 0 <= k1 < g.nodes[p1].children.len() && 0 <= p2 < g.nodes.len() && 0 <= k2
            < g.nodes[p2].children.len() && #[trigger] g.nodes[p1].children[k1] == #[trigger] g.nodes[p2].children[k2]
        implies p1 == p2 && k1 == k2 by {
        assert(assigned(g, n, 0, p1, k1));
        assert(assigned(g, n, 0, p2, k2));
    }
    assert forall|c: int| 0 <= c < pv.len() implies match #[trigger] pv[c] {
        Some(q) => q < g.nodes.len() && is_child_of(g, c, q as int) && has_parent(g, c) && parent_of(g, c) == q,
        None => !has_parent(g, c),
    } by {
        match pv[c] {
            Some(q) => {
                let k = choose|k: int| assigned(g, n, 0, q as int, k) && #[trigger] g.nodes[q as int].children[k] == c;
                assert(is_child_of(g, c, q as int));
                lemma_h1_parent_unique(g, c, q as int);
            },
            None => {
                if has_parent(g, c) {
                    let q = choose|q: int| #[trigger] is_child_of(g, c, q);
                    let k = choose|k: int| 0 <= k < g.nodes[q].children.len() && g.nodes[q].children[k] == c;
                    assert(assigned(g, n, 0, q, k));
                    assert(pv[g.nodes[q].children[k] as int] == Some(q as u64));
                }
            },
        }
    }
}

// H1 と親ベクトル
// MUST-016, MUST-017: 各ノードの親は高々 1 つ
pub fn parents(g: &Gltf) -> (r: Option<Vec<Option<u64>>>)
    requires
        refs_ok(g@),
    ensures
        match r {
            None => !h1(g@),
            Some(pv) => h1(g@) && parent_vec_ok(g@, pv@),
        },
{
    let mut parent = none_vec(g.nodes.len());
    let mut i = 0;
    while i < g.nodes.len()
        invariant
            refs_ok(g@),
            0 <= i <= g.nodes.len(),
            pv_partial(g@, parent@, i as int),
        decreases g.nodes.len() - i,
    {
        let ghost pb = parent@;
        proof {
            assert(g@.nodes[i as int].children == g.nodes@[i as int].children@);
            assert forall|k: int| 0 <= k < g.nodes@[i as int].children@.len() implies #[trigger] g.nodes@[i as int].children@[k]
                < pb.len() by {
                assert(g@.nodes[i as int].children[k] < g@.nodes.len());
            }
        }
        if !assign_parent(&mut parent, i as u64, &g.nodes[i].children) {
            proof {
                let ch = g@.nodes[i as int].children;
                if exists|k: int| 0 <= k < ch.len() && (#[trigger] pb[ch[k] as int]) is Some {
                    let k = choose|k: int| 0 <= k < ch.len() && (#[trigger] pb[ch[k] as int]) is Some;
                    let c = ch[k] as int;
                    let q = pb[c]->Some_0 as int;
                    let k2 = choose|k2: int| assigned(g@, i as int, 0, q, k2) && #[trigger] g@.nodes[q].children[k2] == c;
                    assert(g@.nodes[q].children[k2] == g@.nodes[i as int].children[k]);
                } else {
                    let (a, b) = choose|a: int, b: int| 0 <= a < b < ch.len() && ch[a] == ch[b];
                    assert(g@.nodes[i as int].children[a] == g@.nodes[i as int].children[b]);
                }
            }
            return None;
        }
        proof {
            lemma_pv_step(g@, pb, parent@, i as int);
        }
        i += 1;
    }
    proof {
        lemma_pv_final(g@, parent@);
    }
    Some(parent)
}

// 親ベクトル上で n から k 回たどった位置
pub open spec fn pv_walk(pv: Seq<Option<u64>>, n: int, k: nat) -> Option<int>
    decreases k,
{
    if k == 0 {
        Some(n)
    } else {
        match pv_walk(pv, n, (k - 1) as nat) {
            Some(c) => if 0 <= c < pv.len() {
                match pv[c] {
                    Some(q) => Some(q as int),
                    None => None,
                }
            } else {
                None
            },
            None => None,
        }
    }
}

pub open spec fn root_of_post(pv: Seq<Option<u64>>, n: int, r: Option<u64>) -> bool {
    match r {
        Some(x) => exists|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(x as int) && pv[x as int] is None,
        None => forall|k: nat| k < pv.len() ==> (#[trigger] pv_walk(pv, n, k) matches Some(c) && 0 <= c < pv.len()
            && pv[c] is Some),
    }
}

pub fn root_of(parent: &Vec<Option<u64>>, n: u64) -> (r: Option<u64>)
    requires
        n < parent.len(),
        forall|c: int| 0 <= c < parent.len() ==> (#[trigger] parent@[c] matches Some(q) ==> q < parent.len()),
    ensures
        root_of_post(parent@, n as int, r),
{
    let mut cur = n;
    let mut steps = 0;
    while steps < parent.len()
        invariant
            n < parent.len(),
            forall|c: int| 0 <= c < parent.len() ==> (#[trigger] parent@[c] matches Some(q) ==> q < parent.len()),
            0 <= steps <= parent.len(),
            cur < parent.len(),
            pv_walk(parent@, n as int, steps as nat) == Some(cur as int),
            forall|k: nat| k < steps ==> (#[trigger] pv_walk(parent@, n as int, k) matches Some(c) && 0 <= c < parent.len()
                && parent@[c] is Some),
        decreases parent.len() - steps,
    {
        let ghost s0 = steps as nat;
        match parent[cur as usize] {
            None => return Some(cur),
            Some(p) => cur = p,
        }
        steps += 1;
        proof {
            assert(pv_walk(parent@, n as int, steps as nat) == Some(cur as int));
            assert forall|k: nat| k < steps implies (#[trigger] pv_walk(parent@, n as int, k) matches Some(c) && 0 <= c
                < parent.len() && parent@[c] is Some) by {
                if k < s0 {
                } else {
                    assert(k == s0);
                }
            }
        }
    }
    None
}

pub proof fn lemma_pv_walk_none_mono(pv: Seq<Option<u64>>, n: int, k1: nat, k2: nat)
    requires
        k1 <= k2,
        pv_walk(pv, n, k1) is None,
    ensures
        pv_walk(pv, n, k2) is None,
    decreases k2 - k1,
{
    if k1 < k2 {
        lemma_pv_walk_none_mono(pv, n, k1, (k2 - 1) as nat);
    }
}

fn is_ancestor_or_self(parent: &Vec<Option<u64>>, a: u64, n: u64) -> (r: bool)
    requires
        n < parent.len(),
        forall|c: int| 0 <= c < parent.len() ==> (#[trigger] parent@[c] matches Some(q) ==> q < parent.len()),
    ensures
        r == exists|k: nat| k < parent.len() && #[trigger] pv_walk(parent@, n as int, k) == Some(a as int),
{
    let mut cur = n;
    let mut steps = 0;
    while steps < parent.len()
        invariant
            n < parent.len(),
            forall|c: int| 0 <= c < parent.len() ==> (#[trigger] parent@[c] matches Some(q) ==> q < parent.len()),
            0 <= steps <= parent.len(),
            cur < parent.len(),
            pv_walk(parent@, n as int, steps as nat) == Some(cur as int),
            forall|k: nat| k < steps ==> #[trigger] pv_walk(parent@, n as int, k) != Some(a as int),
        decreases parent.len() - steps,
    {
        let ghost s0 = steps as nat;
        if cur == a {
            return true;
        }
        proof {
            if parent@[cur as int] is None {
                assert forall|k: nat| k < parent.len() implies #[trigger] pv_walk(parent@, n as int, k) != Some(a as int) by {
                    if k > s0 {
                        lemma_pv_walk_none_mono(parent@, n as int, s0 + 1, k);
                    }
                }
            }
        }
        match parent[cur as usize] {
            None => return false,
            Some(p) => cur = p,
        }
        steps += 1;
        proof {
            assert(pv_walk(parent@, n as int, steps as nat) == Some(cur as int));
            assert forall|k: nat| k < steps implies #[trigger] pv_walk(parent@, n as int, k) != Some(a as int) by {
                if k == s0 {
                }
            }
        }
    }
    false
}

// MUST-104: スキンのメッシュのプリミティブは JOINTS_0 を持つ
fn skinned_mesh_ok(m: &Mesh) -> (r: bool)
    ensures
        r == (forall|p: int| 0 <= p < m@.primitives.len() ==> has_sem(#[trigger] m@.primitives[p].attributes, SEM_JOINTS, 0)),
{
    let mut p = 0;
    while p < m.primitives.len()
        invariant
            0 <= p <= m.primitives.len(),
            forall|q: int| 0 <= q < p ==> has_sem(#[trigger] m@.primitives[q].attributes, SEM_JOINTS, 0),
        decreases m.primitives.len() - p,
    {
        proof {
            assert(m@.primitives[p as int].attributes == attrs_view(m.primitives@[p as int].attributes@));
        }
        if !has_semantic(&m.primitives[p].attributes, SEM_JOINTS, 0) {
            return false;
        }
        p += 1;
    }
    true
}

// n から parent を k 回たどった位置
pub open spec fn walk(g: GltfS, n: int, k: nat) -> Option<int>
    decreases k,
{
    if k == 0 {
        Some(n)
    } else {
        match walk(g, n, (k - 1) as nat) {
            Some(c) => if has_parent(g, c) {
                Some(parent_of(g, c))
            } else {
                None
            },
            None => None,
        }
    }
}

// n から |N| 未満の歩数で親のないノードに着く
pub open spec fn reaches_root(g: GltfS, n: int) -> bool {
    exists|k: nat| k < g.nodes.len() && (#[trigger] walk(g, n, k) matches Some(r) && !has_parent(g, r))
}

pub open spec fn root(g: GltfS, n: int) -> int {
    let k = choose|k: nat| k < g.nodes.len() && (#[trigger] walk(g, n, k) matches Some(r) && !has_parent(g, r));
    walk(g, n, k)->Some_0
}

pub proof fn lemma_walk_eq(g: GltfS, pv: Seq<Option<u64>>, n: int, k: nat)
    requires
        parent_vec_ok(g, pv),
        0 <= n < g.nodes.len(),
    ensures
        pv_walk(pv, n, k) == walk(g, n, k),
        pv_walk(pv, n, k) matches Some(c) ==> 0 <= c < g.nodes.len(),
    decreases k,
{
    if k > 0 {
        lemma_walk_eq(g, pv, n, (k - 1) as nat);
        match pv_walk(pv, n, (k - 1) as nat) {
            Some(c) => {
                assert(match pv[c] {
                    Some(q) => q < g.nodes.len() && is_child_of(g, c, q as int) && has_parent(g, c) && parent_of(g, c) == q,
                    None => !has_parent(g, c),
                });
            },
            None => {},
        }
    }
}

pub proof fn lemma_walk_none_mono(g: GltfS, n: int, k1: nat, k2: nat)
    requires
        k1 <= k2,
        walk(g, n, k1) is None,
    ensures
        walk(g, n, k2) is None,
    decreases k2 - k1,
{
    if k1 < k2 {
        lemma_walk_none_mono(g, n, k1, (k2 - 1) as nat);
    }
}

// 根に着く歩数は一意
pub proof fn lemma_root_step_unique(g: GltfS, n: int, k1: nat, k2: nat)
    requires
        walk(g, n, k1) matches Some(r) && !has_parent(g, r),
        walk(g, n, k2) matches Some(r) && !has_parent(g, r),
    ensures
        k1 == k2,
{
    if k1 < k2 {
        assert(walk(g, n, k1 + 1) is None);
        lemma_walk_none_mono(g, n, (k1 + 1) as nat, k2);
    } else if k2 < k1 {
        assert(walk(g, n, k2 + 1) is None);
        lemma_walk_none_mono(g, n, (k2 + 1) as nat, k1);
    }
}

pub proof fn lemma_root_at(g: GltfS, n: int, k: nat)
    requires
        k < g.nodes.len(),
        walk(g, n, k) matches Some(r) && !has_parent(g, r),
    ensures
        reaches_root(g, n),
        root(g, n) == walk(g, n, k)->Some_0,
{
    let k2 = choose|k2: nat| k2 < g.nodes.len() && (#[trigger] walk(g, n, k2) matches Some(r) && !has_parent(g, r));
    lemma_root_step_unique(g, n, k, k2);
}

// pv 上の root_of の結果と H2 / root の対応
pub proof fn lemma_root_of_spec(g: GltfS, pv: Seq<Option<u64>>, n: int)
    requires
        parent_vec_ok(g, pv),
        0 <= n < g.nodes.len(),
    ensures
        forall|r: Option<u64>| #[trigger] root_of_post(pv, n, r) ==> (r is Some == reaches_root(g, n)) && (r matches Some(x) ==> x == root(g, n)),
{
    assert forall|r: Option<u64>| #[trigger] root_of_post(pv, n, r) implies (r is Some == reaches_root(g, n)) && (r matches Some(x) ==> x == root(g, n)) by {
        lemma_root_of_one(g, pv, n, r);
    }
}

pub proof fn lemma_root_of_one(g: GltfS, pv: Seq<Option<u64>>, n: int, r: Option<u64>)
    requires
        parent_vec_ok(g, pv),
        0 <= n < g.nodes.len(),
        root_of_post(pv, n, r),
    ensures
        r is Some == reaches_root(g, n),
        r matches Some(x) ==> x == root(g, n),
{
    match r {
        Some(x) => {
            let k = choose|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(x as int) && pv[x as int] is None;
            lemma_walk_eq(g, pv, n, k);
            assert(!has_parent(g, x as int)) by {
                assert(match pv[x as int] {
                    Some(q) => q < g.nodes.len() && is_child_of(g, x as int, q as int) && has_parent(g, x as int) && parent_of(g, x as int) == q,
                    None => !has_parent(g, x as int),
                });
            }
            lemma_root_at(g, n, k);
        },
        None => {
            if reaches_root(g, n) {
                let k = choose|k: nat| k < g.nodes.len() && (#[trigger] walk(g, n, k) matches Some(r) && !has_parent(g, r));
                lemma_walk_eq(g, pv, n, k);
                assert(pv_walk(pv, n, k) matches Some(c) && 0 <= c < pv.len() && pv[c] is Some);
                let c = walk(g, n, k)->Some_0;
                assert(match pv[c] {
                    Some(q) => q < g.nodes.len() && is_child_of(g, c, q as int) && has_parent(g, c) && parent_of(g, c) == q,
                    None => !has_parent(g, c),
                });
            }
        },
    }
}

// H2 と H3（ノード 1 つ分）
pub open spec fn node_rule(g: GltfS, i: int) -> bool {
    let n = g.nodes[i];
    &&& seq_unique(n.children)
    &&& !(n.has_matrix && n.has_trs)
    &&& ((n.skin is Some || n.weights_len is Some) ==> n.mesh is Some)
    &&& reaches_root(g, i)
    &&& (n.mesh matches Some(m) ==> (n.weights_len matches Some(w) ==> w == morph_count(g.meshes[m as int])))
    &&& (n.mesh matches Some(m) ==> (n.skin is Some ==> forall|p: int|
        0 <= p < g.meshes[m as int].primitives.len() ==> has_sem(
            #[trigger] g.meshes[m as int].primitives[p].attributes,
            SEM_JOINTS,
            0,
        )))
}

// MUST-016, MUST-017, MUST-018, MUST-102, MUST-103, MUST-104: ノード 1 つ分の規則
fn node_ok(g: &Gltf, parent: &Vec<Option<u64>>, i: usize) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
        i < g.nodes.len(),
    ensures
        r == node_rule(g@, i as int),
{
    proof {
        assert(g@.nodes[i as int] == g.nodes@[i as int]@);
        lemma_refs_ok_split(g@);
        assert(node_refs_s(g@, i as int));
        assert forall|c: int| 0 <= c < parent.len() implies (#[trigger] parent@[c] matches Some(q) ==> q < parent.len()) by {
            assert(match parent@[c] {
                Some(q) => q < g@.nodes.len() && is_child_of(g@, c, q as int) && has_parent(g@, c) && parent_of(g@, c) == q,
                None => !has_parent(g@, c),
            });
        }
    }
    let n = &g.nodes[i];
    if !unique(&n.children) || (n.has_matrix && n.has_trs) || ((n.skin.is_some() || n.weights_len.is_some()) && n.mesh.is_none()) {
        return false;
    }
    proof {
        lemma_root_of_spec(g@, parent@, i as int);
    }
    if root_of(parent, i as u64).is_none() {
        return false;
    }
    match n.mesh {
        None => true,
        Some(m) => {
            let mesh = &g.meshes[m as usize];
            proof {
                assert(g@.meshes[m as int] == mesh@);
            }
            let weights_ok = match n.weights_len {
                None => true,
                Some(w) => w == morph_target_count(mesh),
            };
            weights_ok && (n.skin.is_none() || skinned_mesh_ok(mesh))
        }
    }
}

fn nodes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
    ensures
        r == (forall|i: int| 0 <= i < g@.nodes.len() ==> #[trigger] node_rule(g@, i)),
{
    let mut i = 0;
    while i < g.nodes.len()
        invariant
            refs_ok(g@),
            parent_vec_ok(g@, parent@),
            0 <= i <= g.nodes.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] node_rule(g@, k),
        decreases g.nodes.len() - i,
    {
        if !node_ok(g, parent, i) {
            return false;
        }
        i += 1;
    }
    true
}

fn all_roots(parent: &Vec<Option<u64>>, nodes: &Vec<u64>) -> (r: bool)
    requires
        forall|k: int| 0 <= k < nodes.len() ==> #[trigger] nodes@[k] < parent.len(),
    ensures
        r == (forall|k: int| 0 <= k < nodes.len() ==> (#[trigger] parent@[nodes@[k] as int]) is None),
{
    let mut k = 0;
    while k < nodes.len()
        invariant
            forall|j: int| 0 <= j < nodes.len() ==> #[trigger] nodes@[j] < parent.len(),
            0 <= k <= nodes.len(),
            forall|j: int| 0 <= j < k ==> (#[trigger] parent@[nodes@[j] as int]) is None,
        decreases nodes.len() - k,
    {
        if parent[nodes[k] as usize].is_some() {
            return false;
        }
        k += 1;
    }
    true
}

// H4
// MUST-015: scene.nodes は重複なし
pub open spec fn h4(g: GltfS) -> bool {
    forall|s: int|
        0 <= s < g.scenes.len() ==> seq_unique(#[trigger] g.scenes[s].nodes) && forall|k: int|
            0 <= k < g.scenes[s].nodes.len() ==> !has_parent(g, g.scenes[s].nodes[k] as int)
}

// H4
// MUST-015: scene.nodes は重複なし
fn scenes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
    ensures
        r == h4(g@),
{
    let mut s = 0;
    while s < g.scenes.len()
        invariant
            refs_ok(g@),
            parent_vec_ok(g@, parent@),
            0 <= s <= g.scenes.len(),
            forall|x: int|
                0 <= x < s ==> seq_unique(#[trigger] g@.scenes[x].nodes) && forall|k: int|
                    0 <= k < g@.scenes[x].nodes.len() ==> !has_parent(g@, g@.scenes[x].nodes[k] as int),
        decreases g.scenes.len() - s,
    {
        proof {
            assert(g@.scenes[s as int].nodes == g.scenes@[s as int].nodes@);
            assert forall|k: int| 0 <= k < g.scenes@[s as int].nodes@.len() implies #[trigger] g.scenes@[s as int].nodes@[k]
                < parent.len() by {
                assert(g@.scenes[s as int].nodes[k] < g@.nodes.len());
            }
            assert forall|k: int| 0 <= k < g@.scenes[s as int].nodes.len() && (#[trigger] parent@[g@.scenes[s as int].nodes[k] as int]) is Some
                implies has_parent(g@, g@.scenes[s as int].nodes[k] as int) by {
                let c = g@.scenes[s as int].nodes[k] as int;
                assert(g@.scenes[s as int].nodes[k] < g@.nodes.len());
                assert(match parent@[c] {
                    Some(q) => q < g@.nodes.len() && is_child_of(g@, c, q as int) && has_parent(g@, c) && parent_of(g@, c) == q,
                    None => !has_parent(g@, c),
                });
            }
        }
        if !unique(&g.scenes[s].nodes) || !all_roots(parent, &g.scenes[s].nodes) {
            return false;
        }
        assert forall|k: int| 0 <= k < g@.scenes[s as int].nodes.len() implies !has_parent(g@, g@.scenes[s as int].nodes[k] as int) by {
            let c = g@.scenes[s as int].nodes[k] as int;
            assert(g.scenes@[s as int].nodes@[k] == c);
            assert(parent@[c] is None);
            assert(match parent@[c] {
                Some(q) => q < g@.nodes.len() && is_child_of(g@, c, q as int) && has_parent(g@, c) && parent_of(g@, c) == q,
                None => !has_parent(g@, c),
            });
        }
        s += 1;
    }
    true
}

// root_of の結果（root_of_post を満たす値は一意）
pub open spec fn pv_root(pv: Seq<Option<u64>>, n: int) -> Option<u64> {
    choose|r: Option<u64>| root_of_post(pv, n, r)
}

pub open spec fn pv_closed(pv: Seq<Option<u64>>) -> bool {
    forall|c: int| 0 <= c < pv.len() ==> (#[trigger] pv[c] matches Some(q) ==> q < pv.len())
}

pub proof fn lemma_pv_walk_after_root(pv: Seq<Option<u64>>, n: int, k: nat, x: int)
    requires
        pv_walk(pv, n, k) == Some(x),
        0 <= x < pv.len(),
        pv[x] is None,
    ensures
        forall|k2: nat| k2 > k ==> #[trigger] pv_walk(pv, n, k2) is None,
{
    assert forall|k2: nat| k2 > k implies #[trigger] pv_walk(pv, n, k2) is None by {
        assert(pv_walk(pv, n, k + 1) is None);
        lemma_pv_walk_none_mono(pv, n, k + 1, k2);
    }
}

pub proof fn lemma_root_of_post_unique(pv: Seq<Option<u64>>, n: int, r1: Option<u64>, r2: Option<u64>)
    requires
        pv_closed(pv),
        0 <= n < pv.len(),
        root_of_post(pv, n, r1),
        root_of_post(pv, n, r2),
    ensures
        r1 == r2,
{
    match (r1, r2) {
        (Some(x), Some(y)) => {
            let kx = choose|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(x as int) && pv[x as int] is None;
            let ky = choose|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(y as int) && pv[y as int] is None;
            lemma_root_of_bounded(pv, n, kx, x);
            lemma_root_of_bounded(pv, n, ky, y);
            lemma_pv_walk_after_root(pv, n, kx, x as int);
            lemma_pv_walk_after_root(pv, n, ky, y as int);
        },
        (Some(x), None) => {
            let kx = choose|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(x as int) && pv[x as int] is None;
            assert(pv_walk(pv, n, kx) matches Some(c) && 0 <= c < pv.len() && pv[c] is Some);
        },
        (None, Some(y)) => {
            let ky = choose|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(y as int) && pv[y as int] is None;
            assert(pv_walk(pv, n, ky) matches Some(c) && 0 <= c < pv.len() && pv[c] is Some);
        },
        (None, None) => {},
    }
}

// 根に着いた後で値が変わらないことから x < |pv| を導く
pub proof fn lemma_root_of_bounded(pv: Seq<Option<u64>>, n: int, k: nat, x: u64)
    requires
        pv_walk(pv, n, k) == Some(x as int),
        pv_closed(pv),
        0 <= n < pv.len(),
    ensures
        x < pv.len(),
{
    if k > 0 {
        let prev = pv_walk(pv, n, (k - 1) as nat);
        assert(prev matches Some(c) && 0 <= c < pv.len());
        let c = prev->Some_0;
        assert(pv[c] matches Some(q) ==> q < pv.len());
    }
}

pub proof fn lemma_pv_root(pv: Seq<Option<u64>>, n: int, r: Option<u64>)
    requires
        pv_closed(pv),
        0 <= n < pv.len(),
        root_of_post(pv, n, r),
    ensures
        pv_root(pv, n) == r,
{
    let r2 = pv_root(pv, n);
    assert(root_of_post(pv, n, r2));
    lemma_root_of_post_unique(pv, n, r, r2);
}

// MUST-100, MUST-101: 関節の共通の根と skeleton
fn joints_ok(parent: &Vec<Option<u64>>, sk: &Skin, root: Option<u64>) -> (r: bool)
    requires
        pv_closed(parent@),
        sk.joints.len() > 0,
        root == pv_root(parent@, sk.joints@[0] as int),
        forall|k: int| 0 <= k < sk.joints.len() ==> #[trigger] sk.joints@[k] < parent.len(),
    ensures
        r == (forall|k: int|
            0 <= k < sk.joints.len() ==> pv_root(parent@, #[trigger] sk.joints@[k] as int) == pv_root(parent@, sk.joints@[0] as int) && (sk.skeleton matches Some(
                rr,
            ) ==> exists|j: nat| j < parent.len() && #[trigger] pv_walk(parent@, sk.joints@[k] as int, j) == Some(rr as int))),
{
    let mut k = 0;
    while k < sk.joints.len()
        invariant
            pv_closed(parent@),
            root == pv_root(parent@, sk.joints@[0] as int),
            forall|x: int| 0 <= x < sk.joints.len() ==> #[trigger] sk.joints@[x] < parent.len(),
            0 <= k <= sk.joints.len(),
            forall|x: int|
                0 <= x < k ==> pv_root(parent@, #[trigger] sk.joints@[x] as int) == pv_root(parent@, sk.joints@[0] as int) && (sk.skeleton matches Some(rr)
                    ==> exists|j: nat| j < parent.len() && #[trigger] pv_walk(parent@, sk.joints@[x] as int, j) == Some(
                    rr as int,
                )),
        decreases sk.joints.len() - k,
    {
        proof {
            assert forall|r: Option<u64>| #[trigger] root_of_post(parent@, sk.joints@[k as int] as int, r) implies pv_root(
                parent@,
                sk.joints@[k as int] as int,
            ) == r by {
                lemma_pv_root(parent@, sk.joints@[k as int] as int, r);
            }
        }
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

// H2
// MUST-016, MUST-017: 循環がなく、すべてのノードが根に着く
pub open spec fn h2(g: GltfS) -> bool {
    forall|n: int| 0 <= n < g.nodes.len() ==> #[trigger] reaches_root(g, n)
}

pub open spec fn ancestor_or_self(g: GltfS, a: int, n: int) -> bool {
    exists|k: nat| #[trigger] walk(g, n, k) == Some(a)
}

// is_ancestor_or_self の結果と ancestor_or_self（n が根に着く場合）
pub proof fn lemma_ancestor_spec(g: GltfS, pv: Seq<Option<u64>>, a: int, n: int)
    requires
        parent_vec_ok(g, pv),
        0 <= n < g.nodes.len(),
        reaches_root(g, n),
    ensures
        (exists|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(a)) == ancestor_or_self(g, a, n),
{
    let k0 = choose|k: nat| k < g.nodes.len() && (#[trigger] walk(g, n, k) matches Some(r) && !has_parent(g, r));
    if ancestor_or_self(g, a, n) {
        let k = choose|k: nat| #[trigger] walk(g, n, k) == Some(a);
        if k > k0 {
            assert(walk(g, n, k0 + 1) is None);
            lemma_walk_none_mono(g, n, (k0 + 1) as nat, k);
        }
        lemma_walk_eq(g, pv, n, k);
    }
    if exists|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(a) {
        let k = choose|k: nat| k < pv.len() && #[trigger] pv_walk(pv, n, k) == Some(a);
        lemma_walk_eq(g, pv, n, k);
    }
}

pub proof fn lemma_pv_root_g(g: GltfS, pv: Seq<Option<u64>>, n: int)
    requires
        pv.len() <= usize::MAX,
        parent_vec_ok(g, pv),
        0 <= n < g.nodes.len(),
        h2(g),
    ensures
        pv_root(pv, n) == Some(root(g, n) as u64),
        0 <= root(g, n) < g.nodes.len(),
{
    assert(reaches_root(g, n));
    let k = choose|k: nat| k < g.nodes.len() && (#[trigger] walk(g, n, k) matches Some(r) && !has_parent(g, r));
    lemma_walk_eq(g, pv, n, k);
    let x = walk(g, n, k)->Some_0;
    assert(match pv[x] {
        Some(q) => q < g.nodes.len() && is_child_of(g, x, q as int) && has_parent(g, x) && parent_of(g, x) == q,
        None => !has_parent(g, x),
    });
    assert(root_of_post(pv, n, Some(x as u64)));
    lemma_pv_closed(g, pv);
    lemma_pv_root(pv, n, Some(x as u64));
    lemma_root_at(g, n, k);
}

pub open spec fn skin_rule(g: GltfS, sk: SkinS) -> bool {
    &&& sk.joints.len() > 0
    &&& seq_unique(sk.joints)
    &&& forall|k: int| 0 <= k < sk.joints.len() ==> root(g, #[trigger] sk.joints[k] as int) == root(g, sk.joints[0] as int)
    &&& (sk.skeleton matches Some(r) ==> forall|k: int|
        0 <= k < sk.joints.len() ==> ancestor_or_self(g, r as int, #[trigger] sk.joints[k] as int))
    &&& (sk.inverse_bind_matrices matches Some(a) ==> {
        let acc = g.accessors[a as int];
        acc.is_matrix && acc.components == 16 && f32_s(acc) && acc.count >= sk.joints.len()
    })
}

pub proof fn lemma_pv_closed(g: GltfS, pv: Seq<Option<u64>>)
    requires
        parent_vec_ok(g, pv),
    ensures
        pv_closed(pv),
{
    assert forall|c: int| 0 <= c < pv.len() implies (#[trigger] pv[c] matches Some(q) ==> q < pv.len()) by {
        assert(match pv[c] {
            Some(q) => q < g.nodes.len() && is_child_of(g, c, q as int) && has_parent(g, c) && parent_of(g, c) == q,
            None => !has_parent(g, c),
        });
    }
}

// MUST-096, MUST-097, MUST-100, MUST-101: スキン 1 つ分の規則
fn skin_ok(g: &Gltf, parent: &Vec<Option<u64>>, sk: &Skin) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
        h2(g@),
        forall|k: int| 0 <= k < sk.joints.len() ==> #[trigger] sk.joints@[k] < g.nodes.len(),
        sk.inverse_bind_matrices matches Some(a) ==> a < g.accessors.len(),
    ensures
        r == skin_rule(g@, sk@),
{
    proof {
        lemma_pv_closed(g@, parent@);
        assert forall|k: int| 0 <= k < sk.joints.len() implies pv_root(parent@, #[trigger] sk.joints@[k] as int) == Some(
            root(g@, sk.joints@[k] as int) as u64,
        ) && 0 <= root(g@, sk.joints@[k] as int) < g.nodes.len() by {
            lemma_pv_root_g(g@, parent@, sk.joints@[k] as int);
        }
        assert forall|k: int, rr: u64| 0 <= k < sk.joints.len() implies (exists|j: nat|
            j < parent.len() && #[trigger] pv_walk(parent@, sk.joints@[k] as int, j) == Some(rr as int)) == #[trigger] ancestor_or_self(
            g@,
            rr as int,
            sk.joints@[k] as int,
        ) by {
            lemma_ancestor_spec(g@, parent@, rr as int, sk.joints@[k] as int);
        }
        if sk.joints.len() > 0 {
            assert forall|r: Option<u64>| #[trigger] root_of_post(parent@, sk.joints@[0] as int, r) implies pv_root(
                parent@,
                sk.joints@[0] as int,
            ) == r by {
                lemma_pv_root(parent@, sk.joints@[0] as int, r);
            }
        }
    }
    if sk.joints.len() == 0 || !unique(&sk.joints) {
        return false;
    }
    if !joints_ok(parent, sk, root_of(parent, sk.joints[0])) {
        proof {
            let k = choose|k: int|
                !(0 <= k < sk.joints.len() ==> pv_root(parent@, #[trigger] sk.joints@[k] as int) == pv_root(parent@, sk.joints@[0] as int)
                    && (sk.skeleton matches Some(rr) ==> exists|j: nat|
                    j < parent.len() && #[trigger] pv_walk(parent@, sk.joints@[k] as int, j) == Some(rr as int)));
            if pv_root(parent@, sk.joints@[k] as int) != pv_root(parent@, sk.joints@[0] as int) {
                assert(root(g@, sk@.joints[k] as int) != root(g@, sk@.joints[0] as int));
            } else {
                assert(!ancestor_or_self(g@, sk.skeleton->Some_0 as int, sk@.joints[k] as int));
            }
        }
        return false;
    }
    proof {
        assert forall|k: int| 0 <= k < sk@.joints.len() implies root(g@, #[trigger] sk@.joints[k] as int) == root(g@, sk@.joints[0] as int) by {
            assert(pv_root(parent@, sk.joints@[k] as int) == pv_root(parent@, sk.joints@[0] as int));
        }
        if sk.skeleton is Some {
            assert forall|k: int| 0 <= k < sk@.joints.len() implies ancestor_or_self(g@, sk.skeleton->Some_0 as int, #[trigger] sk@.joints[k] as int) by {
                assert(sk.joints@[k] == sk@.joints[k]);
            }
        }
    }
    match sk.inverse_bind_matrices {
        None => true,
        Some(m) => {
            let a = &g.accessors[m as usize];
            a.is_matrix && a.components == 16 && float32(a) && a.count >= sk.joints.len() as u64
        }
    }
}

fn skin_list_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
        h2(g@),
    ensures
        r == (forall|s: int| 0 <= s < g@.skins.len() ==> #[trigger] skin_rule(g@, g@.skins[s])),
{
    let mut i = 0;
    while i < g.skins.len()
        invariant
            refs_ok(g@),
            parent_vec_ok(g@, parent@),
            h2(g@),
            0 <= i <= g.skins.len(),
            forall|s: int| 0 <= s < i ==> #[trigger] skin_rule(g@, g@.skins[s]),
        decreases g.skins.len() - i,
    {
        proof {
            assert(g@.skins[i as int] == g.skins@[i as int]@);
            assert forall|k: int| 0 <= k < g.skins@[i as int].joints.len() implies #[trigger] g.skins@[i as int].joints@[k] < g.nodes.len() by {
                assert(g@.skins[i as int].joints[k] < g@.nodes.len());
            }
            lemma_refs_ok_split(g@);
            assert(skin_refs_s(g@, i as int));
        }
        if !skin_ok(g, parent, &g.skins[i]) {
            assert(!skin_rule(g@, g@.skins[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

// MUST-105: スキンを持つノードのシーンに関節の共通の祖先も属する
fn skin_scene_ok(g: &Gltf, jr: Option<u64>, nr: Option<u64>) -> (r: bool)
    ensures
        r == (forall|sc: int|
            0 <= sc < g@.scenes.len() ==> ((nr matches Some(x) && seq_contains(#[trigger] g@.scenes[sc].nodes, x)) ==> (jr matches Some(
                y,
            ) && seq_contains(g@.scenes[sc].nodes, y)))),
{
    let mut sc = 0;
    while sc < g.scenes.len()
        invariant
            0 <= sc <= g.scenes.len(),
            forall|x: int|
                0 <= x < sc ==> ((nr matches Some(v) && seq_contains(#[trigger] g@.scenes[x].nodes, v)) ==> (jr matches Some(
                    y,
                ) && seq_contains(g@.scenes[x].nodes, y))),
        decreases g.scenes.len() - sc,
    {
        proof {
            assert(g@.scenes[sc as int].nodes == g.scenes@[sc as int].nodes@);
        }
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

// S2
// MUST-105: スキンを持つノードのシーンに関節の共通の祖先も属する
pub open spec fn s2(g: GltfS) -> bool {
    forall|i: int, sc: int|
        0 <= i < g.nodes.len() && 0 <= sc < g.scenes.len() && (#[trigger] g.nodes[i].skin) is Some && seq_contains(
            #[trigger] g.scenes[sc].nodes,
            root(g, i) as u64,
        ) ==> seq_contains(
            g.scenes[sc].nodes,
            root(g, g.skins[g.nodes[i].skin->Some_0 as int].joints[0] as int) as u64,
        )
}

// MUST-105: スキンを持つノードのシーンに関節の共通の祖先も属する
fn skinned_nodes_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
        h2(g@),
        forall|s: int| 0 <= s < g@.skins.len() ==> (#[trigger] g@.skins[s]).joints.len() > 0,
    ensures
        r == s2(g@),
{
    proof {
        lemma_refs_ok_split(g@);
    }
    let mut i = 0;
    while i < g.nodes.len()
        invariant
            refs_ok(g@),
            parent_vec_ok(g@, parent@),
            h2(g@),
            forall|s: int| 0 <= s < g@.skins.len() ==> (#[trigger] g@.skins[s]).joints.len() > 0,
            0 <= i <= g.nodes.len(),
            forall|n: int, sc: int|
                0 <= n < i && 0 <= sc < g@.scenes.len() && (#[trigger] g@.nodes[n].skin) is Some && seq_contains(
                    #[trigger] g@.scenes[sc].nodes,
                    root(g@, n) as u64,
                ) ==> seq_contains(g@.scenes[sc].nodes, root(g@, g@.skins[g@.nodes[n].skin->Some_0 as int].joints[0] as int) as u64),
        decreases g.nodes.len() - i,
    {
        proof {
            assert(g@.nodes[i as int] == g.nodes@[i as int]@);
            assert(node_refs_s(g@, i as int));
            lemma_pv_root_g(g@, parent@, i as int);
            lemma_pv_closed(g@, parent@);
            assert forall|r: Option<u64>| #[trigger] root_of_post(parent@, i as int, r) implies pv_root(parent@, i as int) == r by {
                lemma_pv_root(parent@, i as int, r);
            }
        }
        match g.nodes[i].skin {
            None => {}
            Some(s) => {
                let sk = &g.skins[s as usize];
                proof {
                    assert(g@.skins[s as int] == sk@);
                    assert(skin_refs_s(g@, s as int));
                    let j0 = sk@.joints[0] as int;
                    assert(j0 < g@.nodes.len());
                    lemma_pv_root_g(g@, parent@, j0);
                    assert forall|r: Option<u64>| #[trigger] root_of_post(parent@, j0, r) implies pv_root(parent@, j0) == r by {
                        lemma_pv_root(parent@, j0, r);
                    }
                }
                if sk.joints.len() == 0 || !skin_scene_ok(g, root_of(parent, sk.joints[0]), root_of(parent, i as u64)) {
                    return false;
                }
            }
        }
        i += 1;
    }
    true
}

// S1
pub open spec fn s1(g: GltfS) -> bool {
    forall|s: int|
        0 <= s < g.skins.len() ==> {
            let sk = #[trigger] g.skins[s];
            &&& sk.joints.len() > 0
            // MUST-096: joints は重複なし
            &&& seq_unique(sk.joints)
            // MUST-101: 関節には共通の祖先（共通の根）がある
            &&& forall|k: int| 0 <= k < sk.joints.len() ==> root(g, #[trigger] sk.joints[k] as int) == root(g, sk.joints[0] as int)
            // MUST-100: skeleton は全関節の祖先（または自身）
            &&& (sk.skeleton matches Some(r) ==> forall|k: int|
                0 <= k < sk.joints.len() ==> ancestor_or_self(g, r as int, #[trigger] sk.joints[k] as int))
            // MUST-097: 逆バインド行列は MAT4 の float で要素数 ≥ 関節の数
            &&& (sk.inverse_bind_matrices matches Some(a) ==> {
                let acc = g.accessors[a as int];
                acc.is_matrix && acc.components == 16 && f32_s(acc) && acc.count >= sk.joints.len()
            })
        }
}

pub proof fn lemma_s1(g: GltfS)
    ensures
        s1(g) == (forall|s: int| 0 <= s < g.skins.len() ==> #[trigger] skin_rule(g, g.skins[s])),
{
    if s1(g) {
        assert forall|s: int| 0 <= s < g.skins.len() implies #[trigger] skin_rule(g, g.skins[s]) by {
            let sk = g.skins[s];
        }
    }
    if forall|s: int| 0 <= s < g.skins.len() ==> #[trigger] skin_rule(g, g.skins[s]) {
        assert forall|s: int| 0 <= s < g.skins.len() implies {
            let sk = #[trigger] g.skins[s];
            &&& sk.joints.len() > 0
            &&& seq_unique(sk.joints)
            &&& forall|k: int| 0 <= k < sk.joints.len() ==> root(g, #[trigger] sk.joints[k] as int) == root(g, sk.joints[0] as int)
            &&& (sk.skeleton matches Some(r) ==> forall|k: int|
                0 <= k < sk.joints.len() ==> ancestor_or_self(g, r as int, #[trigger] sk.joints[k] as int))
            &&& (sk.inverse_bind_matrices matches Some(a) ==> {
                let acc = g.accessors[a as int];
                acc.is_matrix && acc.components == 16 && f32_s(acc) && acc.count >= sk.joints.len()
            })
        } by {
            assert(skin_rule(g, g.skins[s]));
        }
    }
}

// S1 と S2
fn skins_ok(g: &Gltf, parent: &Vec<Option<u64>>) -> (r: bool)
    requires
        refs_ok(g@),
        parent_vec_ok(g@, parent@),
        h2(g@),
    ensures
        r == (s1(g@) && s2(g@)),
{
    proof {
        lemma_s1(g@);
    }
    skin_list_ok(g, parent) && skinned_nodes_ok(g, parent)
}

// H3
pub open spec fn h3(g: GltfS) -> bool {
    forall|i: int|
        0 <= i < g.nodes.len() ==> {
            let n = #[trigger] g.nodes[i];
            // MUST-018: children は重複なし
            &&& seq_unique(n.children)
            &&& !(n.has_matrix && n.has_trs)
            // MUST-103: skin があれば mesh も必要
            &&& ((n.skin is Some || n.weights_len is Some) ==> n.mesh is Some)
            // MUST-102: node.weights の長さ = モーフターゲットの数
            &&& (n.mesh matches Some(m) ==> (n.weights_len matches Some(w) ==> w == morph_count(g.meshes[m as int])))
            // MUST-104: スキンのメッシュのプリミティブは JOINTS_0 を持つ（WEIGHTS_0 は MUST-091）
            &&& (n.mesh matches Some(m) ==> (n.skin is Some ==> forall|p: int|
                0 <= p < g.meshes[m as int].primitives.len() ==> has_sem(
                    #[trigger] g.meshes[m as int].primitives[p].attributes,
                    SEM_JOINTS,
                    0,
                )))
        }
}

pub proof fn lemma_nodes_rule(g: GltfS)
    ensures
        (forall|i: int| 0 <= i < g.nodes.len() ==> #[trigger] node_rule(g, i)) == (h2(g) && h3(g)),
{
    if forall|i: int| 0 <= i < g.nodes.len() ==> #[trigger] node_rule(g, i) {
        assert forall|n: int| 0 <= n < g.nodes.len() implies #[trigger] reaches_root(g, n) by {
            assert(node_rule(g, n));
        }
        assert forall|i: int| 0 <= i < g.nodes.len() implies {
            let n = #[trigger] g.nodes[i];
            &&& seq_unique(n.children)
            &&& !(n.has_matrix && n.has_trs)
            &&& ((n.skin is Some || n.weights_len is Some) ==> n.mesh is Some)
            &&& (n.mesh matches Some(m) ==> (n.weights_len matches Some(w) ==> w == morph_count(g.meshes[m as int])))
            &&& (n.mesh matches Some(m) ==> (n.skin is Some ==> forall|p: int|
                0 <= p < g.meshes[m as int].primitives.len() ==> has_sem(
                    #[trigger] g.meshes[m as int].primitives[p].attributes,
                    SEM_JOINTS,
                    0,
                )))
        } by {
            assert(node_rule(g, i));
        }
    }
    if h2(g) && h3(g) {
        assert forall|i: int| 0 <= i < g.nodes.len() implies #[trigger] node_rule(g, i) by {
            assert(reaches_root(g, i));
            let n = g.nodes[i];
        }
    }
}

// H1–H4, S1, S2
pub(crate) fn graph_ok(g: &Gltf) -> (r: bool)
    requires
        refs_ok(g@),
    ensures
        r == (h1(g@) && h2(g@) && h3(g@) && h4(g@) && s1(g@) && s2(g@)),
{
    proof {
        lemma_nodes_rule(g@);
    }
    match parents(g) {
        None => false,
        Some(parent) => nodes_ok(g, &parent) && scenes_ok(g, &parent) && skins_ok(g, &parent),
    }
}

} // verus!
