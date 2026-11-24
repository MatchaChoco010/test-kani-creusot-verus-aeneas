use crate::model::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::validate::util::*;
#[cfg(verus_only)]
use crate::validate::refs::*;

verus! {

pub open spec fn cs_s(ct: u64) -> int {
    if ct == 5120 || ct == 5121 {
        1
    } else if ct == 5122 || ct == 5123 {
        2
    } else {
        4
    }
}

pub fn component_size(ct: u64) -> (r: u64)
    ensures
        r as int == cs_s(ct),
{
    if ct == 5120 || ct == 5121 {
        1
    } else if ct == 5122 || ct == 5123 {
        2
    } else {
        4
    }
}

pub open spec fn roundup4(x: int) -> int {
    (x + 3) / 4 * 4
}

// 要素サイズ（行列は列ごとに 4 バイト境界へ詰める、adoc 1266）
pub open spec fn elem_size_s(a: Accessor) -> int {
    if a.is_matrix {
        let rows: int = if a.components == 4 { 2 } else if a.components == 9 { 3 } else { 4 };
        rows * roundup4(cs_s(a.component_type) * rows)
    } else {
        a.components * cs_s(a.component_type)
    }
}

pub fn element_size(a: &Accessor) -> (r: u64)
    requires
        accessor_shape_s(*a),
    ensures
        r as int == elem_size_s(*a),
        r >= 1,
{
    let cs = component_size(a.component_type);
    if a.is_matrix {
        let rows = if a.components == 4 { 2 } else if a.components == 9 { 3 } else { 4 };
        (cs * rows + 3) / 4 * 4 * rows
    } else {
        a.components * cs
    }
}

fn fits(offset: u64, count: u64, stride: u64, size: u64, limit: u64) -> (r: bool)
    requires
        count >= 1,
    ensures
        r == (offset + (count - 1) * stride + size <= limit),
{
    proof {
        assert((count - 1) * stride >= 0) by (nonlinear_arith)
            requires
                count >= 1,
        ;
    }
    match (count - 1).checked_mul(stride) {
        None => false,
        Some(x) => match offset.checked_add(x) {
            None => false,
            Some(y) => match y.checked_add(size) {
                None => false,
                Some(z) => z <= limit,
            },
        },
    }
}

pub struct Roles {
    pub attribute: Vec<bool>,
    pub index: Vec<bool>,
    pub ibm: Vec<bool>,
}

fn false_vec(n: usize) -> (r: Vec<bool>)
    ensures
        r@.len() == n,
        forall|k: int| 0 <= k < n ==> !#[trigger] r@[k],
{
    let mut v: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@.len() == i,
            forall|k: int| 0 <= k < i ==> !#[trigger] v@[k],
        decreases n - i,
    {
        v.push(false);
        i += 1;
    }
    v
}

fn zero_vec(n: usize) -> (r: Vec<u64>)
    ensures
        r@.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] r@[k] == 0,
{
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            v@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] == 0,
        decreases n - i,
    {
        v.push(0);
        i += 1;
    }
    v
}

pub open spec fn attrs_use(attrs: Seq<AttributeS>, a: int) -> bool {
    exists|k: int| 0 <= k < attrs.len() && #[trigger] attrs[k].accessor == a
}

fn mark_attributes(roles: &mut Vec<bool>, attrs: &Vec<Attribute>)
    requires
        forall|k: int| 0 <= k < attrs.len() ==> #[trigger] attrs@[k].accessor < old(roles)@.len(),
    ensures
        final(roles)@.len() == old(roles)@.len(),
        forall|a: int| 0 <= a < old(roles)@.len() ==> #[trigger] final(roles)@[a] == (old(roles)@[a] || attrs_use(attrs_view(attrs@), a)),
{
    let ghost r0 = roles@;
    let mut i = 0;
    while i < attrs.len()
        invariant
            r0 == old(roles)@,
            forall|k: int| 0 <= k < attrs.len() ==> #[trigger] attrs@[k].accessor < r0.len(),
            roles@.len() == r0.len(),
            0 <= i <= attrs.len(),
            forall|a: int| 0 <= a < r0.len() ==> #[trigger] roles@[a] == (r0[a] || attrs_use(attrs_view(attrs@.subrange(0, i as int)), a)),
        decreases attrs.len() - i,
    {
        proof {
            let s1 = attrs_view(attrs@.subrange(0, i as int));
            let s2 = attrs_view(attrs@.subrange(0, i + 1));
            assert forall|a: int| attrs_use(s2, a) == (attrs_use(s1, a) || a == attrs@[i as int].accessor) by {
                if attrs_use(s2, a) {
                    let k = choose|k: int| 0 <= k < s2.len() && #[trigger] s2[k].accessor == a;
                    if k < i {
                        assert(s1[k].accessor == a);
                    }
                }
                if attrs_use(s1, a) {
                    let k = choose|k: int| 0 <= k < s1.len() && #[trigger] s1[k].accessor == a;
                    assert(s2[k].accessor == a);
                }
                if a == attrs@[i as int].accessor {
                    assert(s2[i as int].accessor == a);
                }
            }
        }
        roles[attrs[i].accessor as usize] = true;
        i += 1;
    }
    proof {
        assert(attrs@.subrange(0, attrs.len() as int) =~= attrs@);
    }
}

pub open spec fn prim_uses(p: PrimitiveS, a: int) -> bool {
    attrs_use(p.attributes, a) || exists|t: int| 0 <= t < p.targets.len() && attrs_use(#[trigger] p.targets[t], a)
}

fn mark_primitive(r: &mut Roles, p: &Primitive)
    requires
        forall|k: int| 0 <= k < p@.attributes.len() ==> #[trigger] p@.attributes[k].accessor < old(r).attribute@.len(),
        forall|t: int, k: int|
            0 <= t < p@.targets.len() && 0 <= k < p@.targets[t].len() ==> #[trigger] p@.targets[t][k].accessor < old(
                r,
            ).attribute@.len(),
        p.indices matches Some(ix) ==> ix < old(r).index@.len(),
    ensures
        final(r).attribute@.len() == old(r).attribute@.len(),
        final(r).index@.len() == old(r).index@.len(),
        final(r).ibm@ == old(r).ibm@,
        forall|a: int| 0 <= a < old(r).attribute@.len() ==> #[trigger] final(r).attribute@[a] == (old(r).attribute@[a] || prim_uses(p@, a)),
        forall|a: int| 0 <= a < old(r).index@.len() ==> #[trigger] final(r).index@[a] == (old(r).index@[a] || p.indices == Some(a as u64)),
{
    let ghost a0 = r.attribute@;
    proof {
        assert(r.index@.len() == r.index.len());
        assert forall|k: int| 0 <= k < p.attributes.len() implies #[trigger] p.attributes@[k].accessor < r.attribute@.len() by {
            assert(p@.attributes[k].accessor == p.attributes@[k].accessor);
        }
    }
    mark_attributes(&mut r.attribute, &p.attributes);
    let mut t = 0;
    while t < p.targets.len()
        invariant
            a0 == old(r).attribute@,
            r.index@ == old(r).index@,
            r.ibm@ == old(r).ibm@,
            r.attribute@.len() == a0.len(),
            forall|t2: int, k: int|
                0 <= t2 < p@.targets.len() && 0 <= k < p@.targets[t2].len() ==> #[trigger] p@.targets[t2][k].accessor < a0.len(),
            0 <= t <= p.targets.len(),
            forall|a: int|
                0 <= a < a0.len() ==> #[trigger] r.attribute@[a] == (a0[a] || attrs_use(p@.attributes, a) || exists|t2: int|
                    0 <= t2 < t && attrs_use(#[trigger] p@.targets[t2], a)),
        decreases p.targets.len() - t,
    {
        proof {
            assert(p@.targets[t as int] == attrs_view(p.targets@[t as int]@));
            assert forall|k: int| 0 <= k < p.targets@[t as int].len() implies #[trigger] p.targets@[t as int]@[k].accessor < r.attribute@.len() by {
                assert(p@.targets[t as int][k].accessor == p.targets@[t as int]@[k].accessor);
            }
        }
        mark_attributes(&mut r.attribute, &p.targets[t]);
        t += 1;
        proof {
            assert forall|a: int| 0 <= a < a0.len() implies #[trigger] r.attribute@[a] == (a0[a] || attrs_use(p@.attributes, a) || exists|t2: int|
                0 <= t2 < t && attrs_use(#[trigger] p@.targets[t2], a)) by {
                if exists|t2: int| 0 <= t2 < t && attrs_use(#[trigger] p@.targets[t2], a) {
                    let t2 = choose|t2: int| 0 <= t2 < t && attrs_use(#[trigger] p@.targets[t2], a);
                    if t2 < t - 1 {
                    } else {
                        assert(t2 == t - 1);
                    }
                }
            }
        }
    }
    match p.indices {
        None => {}
        Some(ix) => r.index[ix as usize] = true,
    }
}

pub open spec fn mesh_uses_attr(m: MeshS, a: int) -> bool {
    exists|p: int| 0 <= p < m.primitives.len() && prim_uses(#[trigger] m.primitives[p], a)
}

pub open spec fn mesh_uses_idx(m: MeshS, a: int) -> bool {
    exists|p: int| 0 <= p < m.primitives.len() && #[trigger] m.primitives[p].indices == Some(a as u64)
}

pub open spec fn prim_refs_s_len(p: PrimitiveS, na: int, ni: int) -> bool {
    &&& forall|k: int| 0 <= k < p.attributes.len() ==> #[trigger] p.attributes[k].accessor < na
    &&& forall|t: int, k: int| 0 <= t < p.targets.len() && 0 <= k < p.targets[t].len() ==> #[trigger] p.targets[t][k].accessor < na
    &&& (p.indices matches Some(ix) ==> ix < ni)
}

fn mark_mesh(r: &mut Roles, m: &Mesh)
    requires
        forall|p: int| 0 <= p < m@.primitives.len() ==> #[trigger] prim_refs_s_len(m@.primitives[p], old(r).attribute@.len() as int, old(r).index@.len() as int),
    ensures
        final(r).attribute@.len() == old(r).attribute@.len(),
        final(r).index@.len() == old(r).index@.len(),
        final(r).ibm@ == old(r).ibm@,
        forall|a: int| 0 <= a < old(r).attribute@.len() ==> #[trigger] final(r).attribute@[a] == (old(r).attribute@[a] || mesh_uses_attr(m@, a)),
        forall|a: int| 0 <= a < old(r).index@.len() ==> #[trigger] final(r).index@[a] == (old(r).index@[a] || mesh_uses_idx(m@, a)),
{
    let ghost a0 = r.attribute@;
    let ghost i0 = r.index@;
    let mut j = 0;
    while j < m.primitives.len()
        invariant
            a0 == old(r).attribute@,
            i0 == old(r).index@,
            r.ibm@ == old(r).ibm@,
            r.attribute@.len() == a0.len(),
            r.index@.len() == i0.len(),
            forall|p: int| 0 <= p < m@.primitives.len() ==> #[trigger] prim_refs_s_len(m@.primitives[p], a0.len() as int, i0.len() as int),
            0 <= j <= m.primitives.len(),
            forall|a: int| 0 <= a < a0.len() ==> #[trigger] r.attribute@[a] == (a0[a] || exists|p: int| 0 <= p < j && prim_uses(#[trigger] m@.primitives[p], a)),
            forall|a: int| 0 <= a < i0.len() ==> #[trigger] r.index@[a] == (i0[a] || exists|p: int| 0 <= p < j && #[trigger] m@.primitives[p].indices == Some(a as u64)),
        decreases m.primitives.len() - j,
    {
        proof {
            assert(m@.primitives[j as int] == m.primitives@[j as int]@);
            assert(prim_refs_s_len(m@.primitives[j as int], a0.len() as int, i0.len() as int));
        }
        mark_primitive(r, &m.primitives[j]);
        j += 1;
        proof {
            assert forall|a: int| 0 <= a < a0.len() implies #[trigger] r.attribute@[a] == (a0[a] || exists|p: int| 0 <= p < j && prim_uses(#[trigger] m@.primitives[p], a)) by {
                if exists|p: int| 0 <= p < j && prim_uses(#[trigger] m@.primitives[p], a) {
                    let p = choose|p: int| 0 <= p < j && prim_uses(#[trigger] m@.primitives[p], a);
                    if p == j - 1 {
                    }
                }
            }
            assert forall|a: int| 0 <= a < i0.len() implies #[trigger] r.index@[a] == (i0[a] || exists|p: int| 0 <= p < j && #[trigger] m@.primitives[p].indices == Some(a as u64)) by {
                if exists|p: int| 0 <= p < j && #[trigger] m@.primitives[p].indices == Some(a as u64) {
                    let p = choose|p: int| 0 <= p < j && #[trigger] m@.primitives[p].indices == Some(a as u64);
                    if p == j - 1 {
                    }
                }
            }
        }
    }
}

fn mark_meshes(r: &mut Roles, g: &Gltf)
    requires
        refs_ok(g@),
        old(r).attribute@.len() == g.accessors.len(),
        old(r).index@.len() == g.accessors.len(),
    ensures
        final(r).attribute@.len() == old(r).attribute@.len(),
        final(r).index@.len() == old(r).index@.len(),
        final(r).ibm@ == old(r).ibm@,
        forall|a: int| 0 <= a < old(r).attribute@.len() ==> #[trigger] final(r).attribute@[a] == (old(r).attribute@[a] || exists|m: int| 0 <= m < g@.meshes.len() && mesh_uses_attr(#[trigger] g@.meshes[m], a)),
        forall|a: int| 0 <= a < old(r).index@.len() ==> #[trigger] final(r).index@[a] == (old(r).index@[a] || exists|m: int| 0 <= m < g@.meshes.len() && mesh_uses_idx(#[trigger] g@.meshes[m], a)),
{
    let ghost a0 = r.attribute@;
    let ghost i0 = r.index@;
    proof {
        lemma_refs_ok_split(g@);
    }
    let mut i = 0;
    while i < g.meshes.len()
        invariant
            refs_ok(g@),
            forall|m: int, p: int|
                0 <= m < g@.meshes.len() && 0 <= p < g@.meshes[m].primitives.len() ==> #[trigger] prim_refs_s(
                    g@,
                    g@.meshes[m].primitives[p],
                ),
            a0 == old(r).attribute@,
            i0 == old(r).index@,
            a0.len() == g.accessors.len(),
            i0.len() == g.accessors.len(),
            r.ibm@ == old(r).ibm@,
            r.attribute@.len() == a0.len(),
            r.index@.len() == i0.len(),
            0 <= i <= g.meshes.len(),
            forall|a: int| 0 <= a < a0.len() ==> #[trigger] r.attribute@[a] == (a0[a] || exists|m: int| 0 <= m < i && mesh_uses_attr(#[trigger] g@.meshes[m], a)),
            forall|a: int| 0 <= a < i0.len() ==> #[trigger] r.index@[a] == (i0[a] || exists|m: int| 0 <= m < i && mesh_uses_idx(#[trigger] g@.meshes[m], a)),
        decreases g.meshes.len() - i,
    {
        proof {
            assert(g@.meshes[i as int] == g.meshes@[i as int]@);
            assert forall|p: int| 0 <= p < g@.meshes[i as int].primitives.len() implies #[trigger] prim_refs_s_len(g@.meshes[i as int].primitives[p], a0.len() as int, i0.len() as int) by {
                assert(prim_refs_s(g@, g@.meshes[i as int].primitives[p]));
            }
        }
        mark_mesh(r, &g.meshes[i]);
        i += 1;
        proof {
            assert forall|a: int| 0 <= a < a0.len() implies #[trigger] r.attribute@[a] == (a0[a] || exists|m: int| 0 <= m < i && mesh_uses_attr(#[trigger] g@.meshes[m], a)) by {
                if exists|m: int| 0 <= m < i && mesh_uses_attr(#[trigger] g@.meshes[m], a) {
                    let m = choose|m: int| 0 <= m < i && mesh_uses_attr(#[trigger] g@.meshes[m], a);
                    if m == i - 1 {
                    }
                }
            }
            assert forall|a: int| 0 <= a < i0.len() implies #[trigger] r.index@[a] == (i0[a] || exists|m: int| 0 <= m < i && mesh_uses_idx(#[trigger] g@.meshes[m], a)) by {
                if exists|m: int| 0 <= m < i && mesh_uses_idx(#[trigger] g@.meshes[m], a) {
                    let m = choose|m: int| 0 <= m < i && mesh_uses_idx(#[trigger] g@.meshes[m], a);
                    if m == i - 1 {
                    }
                }
            }
        }
    }
}

pub open spec fn ibm_acc(g: GltfS, a: int) -> bool {
    exists|s: int| 0 <= s < g.skins.len() && #[trigger] g.skins[s].inverse_bind_matrices == Some(a as u64)
}

fn mark_skins(r: &mut Roles, g: &Gltf)
    requires
        refs_ok(g@),
        old(r).ibm@.len() == g.accessors.len(),
    ensures
        final(r).attribute@ == old(r).attribute@,
        final(r).index@ == old(r).index@,
        final(r).ibm@.len() == old(r).ibm@.len(),
        forall|a: int| 0 <= a < old(r).ibm@.len() ==> #[trigger] final(r).ibm@[a] == (old(r).ibm@[a] || ibm_acc(g@, a)),
{
    let ghost b0 = r.ibm@;
    proof {
        lemma_refs_ok_split(g@);
    }
    let mut i = 0;
    while i < g.skins.len()
        invariant
            refs_ok(g@),
            forall|s: int| 0 <= s < g@.skins.len() ==> #[trigger] skin_refs_s(g@, s),
            b0 == old(r).ibm@,
            b0.len() == g.accessors.len(),
            r.attribute@ == old(r).attribute@,
            r.index@ == old(r).index@,
            r.ibm@.len() == b0.len(),
            0 <= i <= g.skins.len(),
            forall|a: int| 0 <= a < b0.len() ==> #[trigger] r.ibm@[a] == (b0[a] || exists|s: int| 0 <= s < i && #[trigger] g@.skins[s].inverse_bind_matrices == Some(a as u64)),
        decreases g.skins.len() - i,
    {
        proof {
            assert(g@.skins[i as int].inverse_bind_matrices == g.skins@[i as int].inverse_bind_matrices);
            assert(skin_refs_s(g@, i as int));
        }
        match g.skins[i].inverse_bind_matrices {
            None => {}
            Some(m) => r.ibm[m as usize] = true,
        }
        i += 1;
        proof {
            assert forall|a: int| 0 <= a < b0.len() implies #[trigger] r.ibm@[a] == (b0[a] || exists|s: int| 0 <= s < i && #[trigger] g@.skins[s].inverse_bind_matrices == Some(a as u64)) by {
                if exists|s: int| 0 <= s < i && #[trigger] g@.skins[s].inverse_bind_matrices == Some(a as u64) {
                    let s = choose|s: int| 0 <= s < i && #[trigger] g@.skins[s].inverse_bind_matrices == Some(a as u64);
                    if s == i - 1 {
                    }
                }
            }
        }
    }
}

// アクセサの役割とバッファビューの用途
pub open spec fn attr_acc(g: GltfS, a: int) -> bool {
    (exists|m: int, p: int, k: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= k < prim(g, m, p).attributes.len()
            && #[trigger] prim(g, m, p).attributes[k].accessor == a) || (exists|m: int, p: int, t: int, k: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= t < prim(g, m, p).targets.len() && 0
            <= k < prim(g, m, p).targets[t].len() && #[trigger] prim(g, m, p).targets[t][k].accessor == a)
}

pub open spec fn idx_acc(g: GltfS, a: int) -> bool {
    exists|m: int, p: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && #[trigger] prim(g, m, p).indices == Some(
            a as u64,
        )
}

// アクセサの役割が正しく記録されている
pub open spec fn roles_ok(g: GltfS, r: Roles) -> bool {
    &&& r.attribute@.len() == g.accessors.len()
    &&& r.index@.len() == g.accessors.len()
    &&& r.ibm@.len() == g.accessors.len()
    &&& forall|a: int| 0 <= a < g.accessors.len() ==> #[trigger] r.attribute@[a] == attr_acc(g, a)
    &&& forall|a: int| 0 <= a < g.accessors.len() ==> #[trigger] r.index@[a] == idx_acc(g, a)
    &&& forall|a: int| 0 <= a < g.accessors.len() ==> #[trigger] r.ibm@[a] == ibm_acc(g, a)
}

pub proof fn lemma_attr_acc(g: GltfS, a: int)
    ensures
        attr_acc(g, a) == exists|m: int| 0 <= m < g.meshes.len() && mesh_uses_attr(#[trigger] g.meshes[m], a),
        idx_acc(g, a) == exists|m: int| 0 <= m < g.meshes.len() && mesh_uses_idx(#[trigger] g.meshes[m], a),
{
    if attr_acc(g, a) {
        if exists|m: int, p: int, k: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= k < prim(g, m, p).attributes.len()
                && #[trigger] prim(g, m, p).attributes[k].accessor == a {
            let (m, p, k) = choose|m: int, p: int, k: int|
                0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= k < prim(g, m, p).attributes.len()
                    && #[trigger] prim(g, m, p).attributes[k].accessor == a;
            assert(attrs_use(prim(g, m, p).attributes, a));
            assert(prim_uses(g.meshes[m].primitives[p], a));
            assert(mesh_uses_attr(g.meshes[m], a));
        } else {
            let (m, p, t, k) = choose|m: int, p: int, t: int, k: int|
                0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && 0 <= t < prim(g, m, p).targets.len() && 0
                    <= k < prim(g, m, p).targets[t].len() && #[trigger] prim(g, m, p).targets[t][k].accessor == a;
            assert(attrs_use(prim(g, m, p).targets[t], a));
            assert(prim_uses(g.meshes[m].primitives[p], a));
            assert(mesh_uses_attr(g.meshes[m], a));
        }
    }
    if exists|m: int| 0 <= m < g.meshes.len() && mesh_uses_attr(#[trigger] g.meshes[m], a) {
        let m = choose|m: int| 0 <= m < g.meshes.len() && mesh_uses_attr(#[trigger] g.meshes[m], a);
        let p = choose|p: int| 0 <= p < g.meshes[m].primitives.len() && prim_uses(#[trigger] g.meshes[m].primitives[p], a);
        if attrs_use(prim(g, m, p).attributes, a) {
            let k = choose|k: int| 0 <= k < prim(g, m, p).attributes.len() && #[trigger] prim(g, m, p).attributes[k].accessor == a;
            assert(prim(g, m, p).attributes[k].accessor == a);
        } else {
            let t = choose|t: int| 0 <= t < prim(g, m, p).targets.len() && attrs_use(#[trigger] prim(g, m, p).targets[t], a);
            let k = choose|k: int| 0 <= k < prim(g, m, p).targets[t].len() && #[trigger] prim(g, m, p).targets[t][k].accessor == a;
            assert(prim(g, m, p).targets[t][k].accessor == a);
        }
    }
    if idx_acc(g, a) {
        let (m, p) = choose|m: int, p: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() && #[trigger] prim(g, m, p).indices == Some(a as u64);
        assert(mesh_uses_idx(g.meshes[m], a));
    }
    if exists|m: int| 0 <= m < g.meshes.len() && mesh_uses_idx(#[trigger] g.meshes[m], a) {
        let m = choose|m: int| 0 <= m < g.meshes.len() && mesh_uses_idx(#[trigger] g.meshes[m], a);
        let p = choose|p: int| 0 <= p < g.meshes[m].primitives.len() && #[trigger] g.meshes[m].primitives[p].indices == Some(a as u64);
        assert(prim(g, m, p).indices == Some(a as u64));
    }
}

pub fn accessor_roles(g: &Gltf) -> (r: Roles)
    requires
        refs_ok(g@),
    ensures
        roles_ok(g@, r),
{
    let n = g.accessors.len();
    let mut r = Roles { attribute: false_vec(n), index: false_vec(n), ibm: false_vec(n) };
    mark_meshes(&mut r, g);
    mark_skins(&mut r, g);
    proof {
        assert forall|a: int| 0 <= a < g@.accessors.len() implies #[trigger] r.attribute@[a] == attr_acc(g@, a) by {
            lemma_attr_acc(g@, a);
        }
        assert forall|a: int| 0 <= a < g@.accessors.len() implies #[trigger] r.index@[a] == idx_acc(g@, a) by {
            lemma_attr_acc(g@, a);
        }
        assert forall|a: int| 0 <= a < g@.accessors.len() implies #[trigger] r.ibm@[a] == ibm_acc(g@, a) by {
        }
    }
    r
}

pub struct ViewUse {
    pub attribute: Vec<bool>,
    pub attribute_count: Vec<u64>,
    pub index: Vec<bool>,
    pub ibm: Vec<bool>,
    pub sparse: Vec<bool>,
    pub image: Vec<bool>,
    pub animation: Vec<bool>,
    pub accessor: Vec<bool>,
    pub non_attribute: Vec<bool>,
}

pub open spec fn acc_in_view(g: GltfS, a: int, b: int) -> bool {
    0 <= a < g.accessors.len() && g.accessors[a].buffer_view == Some(b as u64)
}

pub open spec fn use_attr(g: GltfS, b: int) -> bool {
    exists|a: int| #[trigger] acc_in_view(g, a, b) && attr_acc(g, a)
}

pub open spec fn use_idx(g: GltfS, b: int) -> bool {
    exists|a: int| #[trigger] acc_in_view(g, a, b) && idx_acc(g, a)
}

pub open spec fn use_ibm(g: GltfS, b: int) -> bool {
    exists|a: int| #[trigger] acc_in_view(g, a, b) && ibm_acc(g, a)
}

pub open spec fn use_sparse(g: GltfS, b: int) -> bool {
    exists|a: int|
        0 <= a < g.accessors.len() && (#[trigger] g.accessors[a].sparse matches Some(sp) && (sp.indices_buffer_view == b
            || sp.values_buffer_view == b))
}

// b を bufferView とするアクセサーがある（使われないアクセサーも含む）
pub open spec fn use_accessor(g: GltfS, b: int) -> bool {
    exists|a: int| #[trigger] acc_in_view(g, a, b)
}

// b を bufferView とする、頂点属性でないアクセサーがある（使われないアクセサーも含む）
pub open spec fn use_non_attr(g: GltfS, b: int) -> bool {
    exists|a: int| #[trigger] acc_in_view(g, a, b) && !attr_acc(g, a)
}

// attr_count(b) < 2: b を参照する属性アクセサは高々 1 つ
pub open spec fn attr_count_lt2(g: GltfS, b: int) -> bool {
    forall|a1: int, a2: int|
        #[trigger] acc_in_view(g, a1, b) && attr_acc(g, a1) && #[trigger] acc_in_view(g, a2, b) && attr_acc(g, a2) ==> a1
            == a2
}

// 属性アクセサの数についての記録（0、1、2 以上を区別する）
pub open spec fn count_rel(g: GltfS, cnt: u64, b: int, i: int) -> bool {
    &&& (cnt == 0) == (forall|a: int| 0 <= a < i ==> !(#[trigger] acc_in_view(g, a, b) && attr_acc(g, a)))
    &&& (cnt <= 1) == (forall|a1: int, a2: int|
        0 <= a1 < i && 0 <= a2 < i && #[trigger] acc_in_view(g, a1, b) && attr_acc(g, a1) && #[trigger] acc_in_view(g, a2, b)
            && attr_acc(g, a2) ==> a1 == a2)
}

pub open spec fn sparse_upto(g: GltfS, b: int, i: int) -> bool {
    exists|a: int|
        0 <= a < i && (#[trigger] g.accessors[a].sparse matches Some(sp) && (sp.indices_buffer_view == b || sp.values_buffer_view == b))
}

// 1 アクセサ分の記録の更新
pub proof fn lemma_mark_step(g: GltfS, roles: Roles, ub: ViewUse, ua: ViewUse, i: int)
    requires
        g.buffer_views.len() <= usize::MAX,
        roles_ok(g, roles),
        0 <= i < g.accessors.len(),
        accessor_refs_s(g, i),
        ub.attribute@.len() == g.buffer_views.len(),
        ub.attribute_count@.len() == g.buffer_views.len(),
        ub.index@.len() == g.buffer_views.len(),
        ub.ibm@.len() == g.buffer_views.len(),
        ub.sparse@.len() == g.buffer_views.len(),
        ub.accessor@.len() == g.buffer_views.len(),
        ub.non_attribute@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ub.accessor@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g, a, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ub.non_attribute@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g, a, b) && !attr_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ub.attribute@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] count_rel(g, ub.attribute_count@[b], b, i),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ub.index@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g, a, b) && idx_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ub.ibm@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g, a, b) && ibm_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ub.sparse@[b] == sparse_upto(g, b, i),
        ua.image@ == ub.image@,
        ua.animation@ == ub.animation@,
        ({
            let acc = g.accessors[i];
            &&& match acc.buffer_view {
                None => ua.attribute@ == ub.attribute@ && ua.attribute_count@ == ub.attribute_count@ && ua.index@ == ub.index@
                    && ua.ibm@ == ub.ibm@ && ua.accessor@ == ub.accessor@ && ua.non_attribute@ == ub.non_attribute@,
                Some(bv) => {
                    &&& ua.accessor@ == ub.accessor@.update(bv as int, true)
                    &&& ua.non_attribute@ == (if !roles.attribute@[i] { ub.non_attribute@.update(bv as int, true) } else { ub.non_attribute@ })
                    &&& ua.attribute@ == (if roles.attribute@[i] { ub.attribute@.update(bv as int, true) } else { ub.attribute@ })
                    &&& ua.attribute_count@ == (if roles.attribute@[i] {
                        ub.attribute_count@.update(bv as int, if ub.attribute_count@[bv as int] == u64::MAX { u64::MAX } else { (ub.attribute_count@[bv as int] + 1) as u64 })
                    } else {
                        ub.attribute_count@
                    })
                    &&& ua.index@ == (if roles.index@[i] { ub.index@.update(bv as int, true) } else { ub.index@ })
                    &&& ua.ibm@ == (if roles.ibm@[i] { ub.ibm@.update(bv as int, true) } else { ub.ibm@ })
                },
            }
            &&& match acc.sparse {
                None => ua.sparse@ == ub.sparse@,
                Some(s) => ua.sparse@ == ub.sparse@.update(s.indices_buffer_view as int, true).update(s.values_buffer_view as int, true),
            }
        }),
    ensures
        ua.attribute@.len() == g.buffer_views.len(),
        ua.attribute_count@.len() == g.buffer_views.len(),
        ua.index@.len() == g.buffer_views.len(),
        ua.ibm@.len() == g.buffer_views.len(),
        ua.sparse@.len() == g.buffer_views.len(),
        ua.accessor@.len() == g.buffer_views.len(),
        ua.non_attribute@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ua.accessor@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ua.non_attribute@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && !attr_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ua.attribute@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] count_rel(g, ua.attribute_count@[b], b, i + 1),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ua.index@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && idx_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ua.ibm@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && ibm_acc(g, a),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] ua.sparse@[b] == sparse_upto(g, b, i + 1),
{
    let acc = g.accessors[i];
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] ua.accessor@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) by {
        if exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) {
            let a = choose|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b);
            if a < i {
                assert(ub.accessor@[b]);
            }
        }
        if ua.accessor@[b] && !ub.accessor@[b] {
            assert(acc_in_view(g, i, b));
        }
    }
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] ua.non_attribute@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && !attr_acc(g, a) by {
        if exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && !attr_acc(g, a) {
            let a = choose|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && !attr_acc(g, a);
            if a == i {
                assert(!roles.attribute@[i]);
            } else {
                assert(ub.non_attribute@[b]);
            }
        }
        if ua.non_attribute@[b] && !ub.non_attribute@[b] {
            assert(acc_in_view(g, i, b) && !attr_acc(g, i));
        }
    }
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] ua.attribute@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a) by {
        if exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a) {
            let a = choose|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a);
            if a == i {
                assert(roles.attribute@[i]);
            }
        }
        if ua.attribute@[b] && !ub.attribute@[b] {
            assert(acc_in_view(g, i, b) && attr_acc(g, i));
        }
    }
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] ua.index@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && idx_acc(g, a) by {
        if exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && idx_acc(g, a) {
            let a = choose|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && idx_acc(g, a);
            if a == i {
                assert(roles.index@[i]);
            }
        }
        if ua.index@[b] && !ub.index@[b] {
            assert(acc_in_view(g, i, b) && idx_acc(g, i));
        }
    }
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] ua.ibm@[b] == exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && ibm_acc(g, a) by {
        if exists|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && ibm_acc(g, a) {
            let a = choose|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && ibm_acc(g, a);
            if a == i {
                assert(roles.ibm@[i]);
            }
        }
        if ua.ibm@[b] && !ub.ibm@[b] {
            assert(acc_in_view(g, i, b) && ibm_acc(g, i));
        }
    }
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] count_rel(g, ua.attribute_count@[b], b, i + 1) by {
        assert(count_rel(g, ub.attribute_count@[b], b, i));
        let hit = acc_in_view(g, i, b) && attr_acc(g, i);
        if hit {
            assert(roles.attribute@[i]);
            let c0 = ub.attribute_count@[b];
            if c0 == 0 {
                assert forall|a1: int, a2: int|
                    0 <= a1 < i + 1 && 0 <= a2 < i + 1 && #[trigger] acc_in_view(g, a1, b) && attr_acc(g, a1) && #[trigger] acc_in_view(g, a2, b)
                        && attr_acc(g, a2) implies a1 == a2 by {
                    if a1 < i {
                        assert(!(acc_in_view(g, a1, b) && attr_acc(g, a1)));
                    }
                    if a2 < i {
                        assert(!(acc_in_view(g, a2, b) && attr_acc(g, a2)));
                    }
                }
            } else {
                let a1 = choose|a: int| 0 <= a < i && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a);
                assert(acc_in_view(g, a1, b) && attr_acc(g, a1) && acc_in_view(g, i, b) && attr_acc(g, i));
            }
        } else {
            assert forall|a: int| 0 <= a < i + 1 && #[trigger] acc_in_view(g, a, b) && attr_acc(g, a) implies a < i by {}
        }
    }
    assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] ua.sparse@[b] == sparse_upto(g, b, i + 1) by {
        if sparse_upto(g, b, i + 1) {
            let a = choose|a: int| 0 <= a < i + 1 && (#[trigger] g.accessors[a].sparse matches Some(sp) && (sp.indices_buffer_view == b || sp.values_buffer_view == b));
            if a < i {
                assert(sparse_upto(g, b, i));
            }
        }
        if sparse_upto(g, b, i) {
            let a = choose|a: int| 0 <= a < i && (#[trigger] g.accessors[a].sparse matches Some(sp) && (sp.indices_buffer_view == b || sp.values_buffer_view == b));
            assert(0 <= a < i + 1);
        }
        if ua.sparse@[b] && !ub.sparse@[b] {
            assert(0 <= i < i + 1);
        }
    }
}

fn mark_accessor_views(u: &mut ViewUse, g: &Gltf, roles: &Roles)
    requires
        refs_ok(g@),
        roles_ok(g@, *roles),
        old(u).attribute@.len() == g.buffer_views.len(),
        old(u).attribute_count@.len() == g.buffer_views.len(),
        old(u).index@.len() == g.buffer_views.len(),
        old(u).ibm@.len() == g.buffer_views.len(),
        old(u).sparse@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).attribute@[b],
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] old(u).attribute_count@[b] == 0,
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).index@[b],
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).ibm@[b],
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).sparse@[b],
        old(u).accessor@.len() == g.buffer_views.len(),
        old(u).non_attribute@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).accessor@[b],
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).non_attribute@[b],
    ensures
        final(u).image@ == old(u).image@,
        final(u).animation@ == old(u).animation@,
        final(u).accessor@.len() == g.buffer_views.len(),
        final(u).non_attribute@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).accessor@[b] == use_accessor(g@, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).non_attribute@[b] == use_non_attr(g@, b),
        final(u).attribute@.len() == g.buffer_views.len(),
        final(u).attribute_count@.len() == g.buffer_views.len(),
        final(u).index@.len() == g.buffer_views.len(),
        final(u).ibm@.len() == g.buffer_views.len(),
        final(u).sparse@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).attribute@[b] == use_attr(g@, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> (#[trigger] final(u).attribute_count@[b] <= 1) == attr_count_lt2(g@, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).index@[b] == use_idx(g@, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).ibm@[b] == use_ibm(g@, b),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).sparse@[b] == use_sparse(g@, b),
{
    proof {
        lemma_refs_ok_split(g@);
    }
    let ghost u0 = *u;
    let mut i = 0;
    while i < g.accessors.len()
        invariant
            refs_ok(g@),
            roles_ok(g@, *roles),
            forall|a: int| 0 <= a < g@.accessors.len() ==> #[trigger] accessor_refs_s(g@, a),
            u0 == *old(u),
            u.image@ == u0.image@,
            u.animation@ == u0.animation@,
            u.attribute@.len() == g.buffer_views.len(),
            u.attribute_count@.len() == g.buffer_views.len(),
            u.index@.len() == g.buffer_views.len(),
            u.ibm@.len() == g.buffer_views.len(),
            u.sparse@.len() == g.buffer_views.len(),
            u.accessor@.len() == g.buffer_views.len(),
            u.non_attribute@.len() == g.buffer_views.len(),
            0 <= i <= g.accessors.len(),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.accessor@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g@, a, b),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.non_attribute@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g@, a, b) && !attr_acc(g@, a),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.attribute@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g@, a, b) && attr_acc(g@, a),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] count_rel(g@, u.attribute_count@[b], b, i as int),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.index@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g@, a, b) && idx_acc(g@, a),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.ibm@[b] == exists|a: int| 0 <= a < i && #[trigger] acc_in_view(g@, a, b) && ibm_acc(g@, a),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.sparse@[b] == sparse_upto(g@, b, i as int),
        decreases g.accessors.len() - i,
    {
        let ghost ub = *u;
        let ghost ii = i as int;
        proof {
            assert(accessor_refs_s(g@, ii));
        }
        let a = &g.accessors[i];
        match a.buffer_view {
            None => {}
            Some(bv) => {
                let b = bv as usize;
                u.accessor[b] = true;
                if !roles.attribute[i] {
                    u.non_attribute[b] = true;
                }
                if roles.attribute[i] {
                    u.attribute[b] = true;
                    u.attribute_count[b] = u.attribute_count[b].saturating_add(1);
                }
                if roles.index[i] {
                    u.index[b] = true;
                }
                if roles.ibm[i] {
                    u.ibm[b] = true;
                }
            }
        }
        match &a.sparse {
            None => {}
            Some(s) => {
                u.sparse[s.indices_buffer_view as usize] = true;
                u.sparse[s.values_buffer_view as usize] = true;
            }
        }
        i += 1;
        proof {
            assert(g@.buffer_views.len() == g.buffer_views.len());
            lemma_mark_step(g@, *roles, ub, *u, ii);
        }
    }
    proof {
        assert forall|b: int| 0 <= b < g.buffer_views.len() implies (#[trigger] u.attribute_count@[b] <= 1) == attr_count_lt2(g@, b) by {
            assert(count_rel(g@, u.attribute_count@[b], b, g.accessors.len() as int));
        }
        assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.sparse@[b] == use_sparse(g@, b) by {
            assert(sparse_upto(g@, b, g.accessors.len() as int) == use_sparse(g@, b));
        }
        assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.accessor@[b] == use_accessor(g@, b) by {
            if use_accessor(g@, b) {
                let a = choose|a: int| #[trigger] acc_in_view(g@, a, b);
                assert(0 <= a < g.accessors.len() && acc_in_view(g@, a, b));
            }
        }
        assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.non_attribute@[b] == use_non_attr(g@, b) by {
            if use_non_attr(g@, b) {
                let a = choose|a: int| #[trigger] acc_in_view(g@, a, b) && !attr_acc(g@, a);
                assert(0 <= a < g.accessors.len() && acc_in_view(g@, a, b) && !attr_acc(g@, a));
            }
        }
    }
}

pub open spec fn use_image(g: GltfS, b: int) -> bool {
    exists|i: int| 0 <= i < g.images.len() && #[trigger] g.images[i].buffer_view == Some(b as u64)
}

fn mark_image_views(u: &mut ViewUse, g: &Gltf)
    requires
        refs_ok(g@),
        old(u).image@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).image@[b],
    ensures
        final(u).attribute@ == old(u).attribute@,
        final(u).attribute_count@ == old(u).attribute_count@,
        final(u).index@ == old(u).index@,
        final(u).ibm@ == old(u).ibm@,
        final(u).sparse@ == old(u).sparse@,
        final(u).animation@ == old(u).animation@,
        final(u).accessor@ == old(u).accessor@,
        final(u).non_attribute@ == old(u).non_attribute@,
        final(u).image@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).image@[b] == use_image(g@, b),
{
    proof {
        lemma_refs_ok_split(g@);
    }
    let ghost u0 = *u;
    let mut i = 0;
    while i < g.images.len()
        invariant
            refs_ok(g@),
            forall|k: int| 0 <= k < g@.images.len() ==> opt_lt(#[trigger] g@.images[k].buffer_view, g@.buffer_views.len() as int),
            u0 == *old(u),
            u.attribute@ == u0.attribute@,
            u.attribute_count@ == u0.attribute_count@,
            u.index@ == u0.index@,
            u.ibm@ == u0.ibm@,
            u.sparse@ == u0.sparse@,
            u.animation@ == u0.animation@,
            u.accessor@ == u0.accessor@,
            u.non_attribute@ == u0.non_attribute@,
            u.image@.len() == g.buffer_views.len(),
            0 <= i <= g.images.len(),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.image@[b] == exists|k: int| 0 <= k < i && #[trigger] g@.images[k].buffer_view == Some(b as u64),
        decreases g.images.len() - i,
    {
        proof {
            assert(g@.images[i as int].buffer_view == g.images@[i as int].buffer_view);
            assert(opt_lt(g@.images[i as int].buffer_view, g@.buffer_views.len() as int));
        }
        match g.images[i].buffer_view {
            None => {}
            Some(bv) => u.image[bv as usize] = true,
        }
        i += 1;
        proof {
            assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.image@[b] == exists|k: int| 0 <= k < i && #[trigger] g@.images[k].buffer_view == Some(b as u64) by {
                if exists|k: int| 0 <= k < i && #[trigger] g@.images[k].buffer_view == Some(b as u64) {
                    let k = choose|k: int| 0 <= k < i && #[trigger] g@.images[k].buffer_view == Some(b as u64);
                    if k == i - 1 {
                    }
                }
            }
        }
    }
}

fn mark_accessor_view(v: &mut Vec<bool>, g: &Gltf, accessor: u64)
    requires
        accessor < g.accessors.len(),
        opt_lt(g@.accessors[accessor as int].buffer_view, old(v)@.len() as int),
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|b: int| 0 <= b < old(v)@.len() ==> #[trigger] final(v)@[b] == (old(v)@[b] || acc_in_view(g@, accessor as int, b)),
{
    proof {
        assert(v@.len() == v.len());
    }
    match g.accessors[accessor as usize].buffer_view {
        None => {}
        Some(bv) => v[bv as usize] = true,
    }
}

pub open spec fn sampler_uses(g: GltfS, sm: AnimationSampler, b: int) -> bool {
    acc_in_view(g, sm.input as int, b) || acc_in_view(g, sm.output as int, b)
}

fn mark_animation_views(u: &mut ViewUse, g: &Gltf, an: &Animation)
    requires
        refs_ok(g@),
        forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
        old(u).animation@.len() == g.buffer_views.len(),
    ensures
        final(u).attribute@ == old(u).attribute@,
        final(u).attribute_count@ == old(u).attribute_count@,
        final(u).index@ == old(u).index@,
        final(u).ibm@ == old(u).ibm@,
        final(u).sparse@ == old(u).sparse@,
        final(u).image@ == old(u).image@,
        final(u).accessor@ == old(u).accessor@,
        final(u).non_attribute@ == old(u).non_attribute@,
        final(u).animation@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).animation@[b] == (old(u).animation@[b] || exists|s: int| 0 <= s < an@.samplers.len() && sampler_uses(g@, #[trigger] an@.samplers[s], b)),
{
    proof {
        lemma_refs_ok_split(g@);
    }
    let ghost u0 = *u;
    let mut s = 0;
    while s < an.samplers.len()
        invariant
            refs_ok(g@),
            forall|a: int| 0 <= a < g@.accessors.len() ==> #[trigger] accessor_refs_s(g@, a),
            forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
            u0 == *old(u),
            u.attribute@ == u0.attribute@,
            u.attribute_count@ == u0.attribute_count@,
            u.index@ == u0.index@,
            u.ibm@ == u0.ibm@,
            u.sparse@ == u0.sparse@,
            u.image@ == u0.image@,
            u.accessor@ == u0.accessor@,
            u.non_attribute@ == u0.non_attribute@,
            u.animation@.len() == g.buffer_views.len(),
            0 <= s <= an.samplers.len(),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.animation@[b] == (u0.animation@[b] || exists|x: int| 0 <= x < s && sampler_uses(g@, #[trigger] an@.samplers[x], b)),
        decreases an.samplers.len() - s,
    {
        proof {
            assert(sampler_refs_s(g@, an@, s as int));
            assert(accessor_refs_s(g@, an@.samplers[s as int].input as int));
            assert(accessor_refs_s(g@, an@.samplers[s as int].output as int));
        }
        mark_accessor_view(&mut u.animation, g, an.samplers[s].input);
        mark_accessor_view(&mut u.animation, g, an.samplers[s].output);
        s += 1;
        proof {
            assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.animation@[b] == (u0.animation@[b] || exists|x: int| 0 <= x < s && sampler_uses(g@, #[trigger] an@.samplers[x], b)) by {
                if exists|x: int| 0 <= x < s && sampler_uses(g@, #[trigger] an@.samplers[x], b) {
                    let x = choose|x: int| 0 <= x < s && sampler_uses(g@, #[trigger] an@.samplers[x], b);
                    if x == s - 1 {
                    }
                }
                if sampler_uses(g@, an@.samplers[s - 1], b) {
                    assert(0 <= s - 1 < s);
                }
            }
        }
    }
}

pub open spec fn use_anim(g: GltfS, b: int) -> bool {
    exists|i: int, s: int|
        0 <= i < g.animations.len() && 0 <= s < g.animations[i].samplers.len() && (acc_in_view(
            g,
            (#[trigger] g.animations[i].samplers[s]).input as int,
            b,
        ) || acc_in_view(g, g.animations[i].samplers[s].output as int, b))
}

fn mark_animations_views(u: &mut ViewUse, g: &Gltf)
    requires
        refs_ok(g@),
        old(u).animation@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> !#[trigger] old(u).animation@[b],
    ensures
        final(u).attribute@ == old(u).attribute@,
        final(u).attribute_count@ == old(u).attribute_count@,
        final(u).index@ == old(u).index@,
        final(u).ibm@ == old(u).ibm@,
        final(u).sparse@ == old(u).sparse@,
        final(u).image@ == old(u).image@,
        final(u).accessor@ == old(u).accessor@,
        final(u).non_attribute@ == old(u).non_attribute@,
        final(u).animation@.len() == g.buffer_views.len(),
        forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] final(u).animation@[b] == use_anim(g@, b),
{
    proof {
        lemma_refs_ok_split(g@);
    }
    let ghost u0 = *u;
    let mut i = 0;
    while i < g.animations.len()
        invariant
            refs_ok(g@),
            forall|k: int| 0 <= k < g@.animations.len() ==> #[trigger] anim_refs_s(g@, k),
            u0 == *old(u),
            u.attribute@ == u0.attribute@,
            u.attribute_count@ == u0.attribute_count@,
            u.index@ == u0.index@,
            u.ibm@ == u0.ibm@,
            u.sparse@ == u0.sparse@,
            u.image@ == u0.image@,
            u.accessor@ == u0.accessor@,
            u.non_attribute@ == u0.non_attribute@,
            u.animation@.len() == g.buffer_views.len(),
            0 <= i <= g.animations.len(),
            forall|b: int| 0 <= b < g.buffer_views.len() ==> #[trigger] u.animation@[b] == exists|k: int, s: int|
                0 <= k < i && 0 <= s < g@.animations[k].samplers.len() && sampler_uses(g@, #[trigger] g@.animations[k].samplers[s], b),
        decreases g.animations.len() - i,
    {
        proof {
            assert(g@.animations[i as int] == g.animations@[i as int]@);
            assert(anim_refs_s(g@, i as int));
        }
        mark_animation_views(u, g, &g.animations[i]);
        i += 1;
        proof {
            assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.animation@[b] == exists|k: int, s: int|
                0 <= k < i && 0 <= s < g@.animations[k].samplers.len() && sampler_uses(g@, #[trigger] g@.animations[k].samplers[s], b) by {
                if exists|k: int, s: int| 0 <= k < i && 0 <= s < g@.animations[k].samplers.len() && sampler_uses(g@, #[trigger] g@.animations[k].samplers[s], b) {
                    let (k, s) = choose|k: int, s: int| 0 <= k < i && 0 <= s < g@.animations[k].samplers.len() && sampler_uses(g@, #[trigger] g@.animations[k].samplers[s], b);
                    if k == i - 1 {
                    }
                }
                if exists|s: int| 0 <= s < g@.animations[i - 1].samplers.len() && sampler_uses(g@, #[trigger] g@.animations[i - 1].samplers[s], b) {
                    let s = choose|s: int| 0 <= s < g@.animations[i - 1].samplers.len() && sampler_uses(g@, #[trigger] g@.animations[i - 1].samplers[s], b);
                    assert(sampler_uses(g@, g@.animations[i - 1].samplers[s], b));
                }
            }
        }
    }
    proof {
        assert forall|b: int| 0 <= b < g.buffer_views.len() implies #[trigger] u.animation@[b] == use_anim(g@, b) by {
            if use_anim(g@, b) {
                let (k, s) = choose|k: int, s: int| 0 <= k < g@.animations.len() && 0 <= s < g@.animations[k].samplers.len() && (acc_in_view(
                    g@,
                    (#[trigger] g@.animations[k].samplers[s]).input as int,
                    b,
                ) || acc_in_view(g@, g@.animations[k].samplers[s].output as int, b));
                assert(sampler_uses(g@, g@.animations[k].samplers[s], b));
            }
        }
    }
}

pub open spec fn view_use_ok(g: GltfS, u: ViewUse) -> bool {
    let n = g.buffer_views.len();
    &&& u.attribute@.len() == n && u.attribute_count@.len() == n && u.index@.len() == n && u.ibm@.len() == n
    &&& u.sparse@.len() == n && u.image@.len() == n && u.animation@.len() == n
    &&& u.accessor@.len() == n && u.non_attribute@.len() == n
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.accessor@[b] == use_accessor(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.non_attribute@[b] == use_non_attr(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.attribute@[b] == use_attr(g, b)
    &&& forall|b: int| 0 <= b < n ==> (#[trigger] u.attribute_count@[b] <= 1) == attr_count_lt2(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.index@[b] == use_idx(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.ibm@[b] == use_ibm(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.sparse@[b] == use_sparse(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.image@[b] == use_image(g, b)
    &&& forall|b: int| 0 <= b < n ==> #[trigger] u.animation@[b] == use_anim(g, b)
}

// MUST-026, MUST-027, MUST-038, MUST-039, MUST-046, MUST-050: bufferView の用途
pub fn view_use(g: &Gltf, roles: &Roles) -> (r: ViewUse)
    requires
        refs_ok(g@),
        roles_ok(g@, *roles),
    ensures
        view_use_ok(g@, r),
{
    let n = g.buffer_views.len();
    let mut u = ViewUse {
        attribute: false_vec(n),
        attribute_count: zero_vec(n),
        index: false_vec(n),
        ibm: false_vec(n),
        sparse: false_vec(n),
        image: false_vec(n),
        animation: false_vec(n),
        accessor: false_vec(n),
        non_attribute: false_vec(n),
    };
    mark_accessor_views(&mut u, g, roles);
    mark_image_views(&mut u, g);
    mark_animations_views(&mut u, g);
    u
}

pub open spec fn use_other(g: GltfS, b: int) -> bool {
    use_anim(g, b) || use_sparse(g, b)
}

pub open spec fn b2i(x: bool) -> int {
    if x { 1 } else { 0 }
}

// B1–B4（1 バッファビュー分）
pub open spec fn view_rule(g: GltfS, b: int) -> bool {
    let bv = g.buffer_views[b];
    let attr = use_attr(g, b);
    let idx = use_idx(g, b);
    let ibm = use_ibm(g, b);
    let other = use_other(g, b);
    let image = use_image(g, b);
    &&& bv.byte_length > 0
    // MUST-025: bufferView はバッファーに収まる
    &&& bv.byte_offset + bv.byte_length <= g.buffers[bv.buffer as int].byte_length
    // MUST-026: 頂点・インデックス・逆バインド行列・画像の bufferView は 1 種類のデータだけ
    &&& ((attr || idx || ibm || image) ==> b2i(attr) + b2i(idx) + b2i(ibm) + b2i(other) + b2i(image) <= 1)
    // MUST-027: 画像の bufferView はアクセサーと sparse から使わない
    &&& (image ==> !use_accessor(g, b) && !use_sparse(g, b))
    // MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039, MUST-046, MUST-050, MUST-072, MUST-098, MUST-110, MUST-142, MUST-146: byteStride の規則
    &&& match bv.byte_stride {
        None => attr_count_lt2(g, b),
        Some(st) => 4 <= st <= 252 && st % 4 == 0 && st <= bv.byte_length && !idx && !ibm && !other && !image
            && !use_non_attr(g, b) && bv.target != Some(34963u64),
    }
    // MUST-028, MUST-046, MUST-050, MUST-070, MUST-072, MUST-090, MUST-098, MUST-110, MUST-142, MUST-146: target の規則
    &&& (bv.target matches Some(t) ==> !(attr && t != 34962) && !(idx && t != 34963) && !ibm && !other && !image)
}

// B1–B4
// MUST-025, MUST-026, MUST-027, MUST-028, MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039, MUST-046, MUST-050, MUST-070, MUST-072, MUST-090, MUST-098, MUST-110, MUST-142, MUST-146: bufferView 1 つ分の規則
fn buffer_view_ok(g: &Gltf, u: &ViewUse, b: usize) -> (r: bool)
    requires
        refs_ok(g@),
        view_use_ok(g@, *u),
        b < g.buffer_views.len(),
    ensures
        r == view_rule(g@, b as int),
{
    proof {
        lemma_refs_ok_split(g@);
        assert(g@.buffer_views[b as int].buffer < g@.buffers.len());
        assert(g@.buffers[g@.buffer_views[b as int].buffer as int].byte_length == g.buffers@[g@.buffer_views[b as int].buffer as int].byte_length);
    }
    let bv = &g.buffer_views[b];
    let in_buffer = match bv.byte_offset.checked_add(bv.byte_length) {
        None => false,
        Some(end) => end <= g.buffers[bv.buffer as usize].byte_length,
    };
    let attr = u.attribute[b];
    let idx = u.index[b];
    let ibm = u.ibm[b];
    let other = u.animation[b] || u.sparse[b];
    let image = u.image[b];
    let kinds = (attr as u64) + (idx as u64) + (ibm as u64) + (other as u64) + (image as u64);
    let one_kind = !(attr || idx || ibm || image) || kinds <= 1;
    let image_alone = !image || (!u.accessor[b] && !u.sparse[b]);
    let non_vertex = idx || ibm || other || image || u.non_attribute[b];
    bv.byte_length > 0
        && in_buffer
        && one_kind
        && image_alone
        && stride_ok(bv, u.attribute_count[b], non_vertex)
        && target_ok(bv.target, attr, idx, ibm || other || image)
}

// MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039, MUST-046, MUST-050, MUST-072, MUST-098, MUST-110, MUST-142, MUST-146: byteStride の規則
fn stride_ok(bv: &BufferView, attribute_count: u64, non_vertex: bool) -> (r: bool)
    ensures
        r == match bv.byte_stride {
            None => attribute_count <= 1,
            Some(st) => 4 <= st <= 252 && st % 4 == 0 && st <= bv.byte_length && !non_vertex && bv.target != Some(34963u64),
        },
{
    match bv.byte_stride {
        None => attribute_count <= 1,
        Some(st) => st >= 4 && st <= 252 && st % 4 == 0 && st <= bv.byte_length && !non_vertex && !opt_eq(bv.target, Some(34963)),
    }
}

// MUST-028, MUST-046, MUST-050, MUST-070, MUST-072, MUST-090, MUST-098, MUST-110, MUST-142, MUST-146: target の規則
fn target_ok(target: Option<u64>, attr: bool, idx: bool, other: bool) -> (r: bool)
    ensures
        r == (target matches Some(t) ==> !(attr && t != 34962) && !(idx && t != 34963) && !other),
{
    match target {
        None => true,
        Some(t) => !(attr && t != 34962) && !(idx && t != 34963) && !other,
    }
}

fn buffer_views_ok(g: &Gltf, u: &ViewUse) -> (r: bool)
    requires
        refs_ok(g@),
        view_use_ok(g@, *u),
    ensures
        r == (forall|b: int| 0 <= b < g@.buffer_views.len() ==> #[trigger] view_rule(g@, b)),
{
    let mut b = 0;
    while b < g.buffer_views.len()
        invariant
            refs_ok(g@),
            view_use_ok(g@, *u),
            0 <= b <= g.buffer_views.len(),
            forall|x: int| 0 <= x < b ==> #[trigger] view_rule(g@, x),
        decreases g.buffer_views.len() - b,
    {
        if !buffer_view_ok(g, u, b) {
            return false;
        }
        b += 1;
    }
    true
}

pub open spec fn accessor_view_rule(g: GltfS, a: Accessor, is_attribute: bool) -> bool {
    let cs = cs_s(a.component_type);
    let size = elem_size_s(a);
    match a.buffer_view {
        None => a.byte_offset is None,
        Some(b) => {
            let bv = g.buffer_views[b as int];
            let offset: int = match a.byte_offset {
                Some(o) => o as int,
                None => 0,
            };
            let stride: int = match bv.byte_stride {
                Some(st) => st as int,
                None => size,
            };
            &&& offset % cs == 0
            &&& (bv.byte_offset as int) % cs == 0
            &&& (bv.byte_stride matches Some(st) ==> st as int >= size && (st as int) % cs == 0)
            &&& (is_attribute ==> offset % 4 == 0 && (cs % 4 == 0 || bv.byte_stride is Some))
            &&& offset + (a.count - 1) * stride + size <= bv.byte_length
        },
    }
}

// MUST-034, MUST-036, MUST-037, MUST-040, MUST-041, MUST-042: アクセサーと bufferView の規則
fn accessor_view_ok(g: &Gltf, a: &Accessor, is_attribute: bool) -> (r: bool)
    requires
        accessor_shape_s(*a),
        a.count > 0,
        opt_lt(a.buffer_view, g.buffer_views.len() as int),
    ensures
        r == accessor_view_rule(g@, *a, is_attribute),
{
    let cs = component_size(a.component_type);
    let size = element_size(a);
    match a.buffer_view {
        None => a.byte_offset.is_none(),
        Some(b) => {
            let bv = &g.buffer_views[b as usize];
            let offset = match a.byte_offset {
                Some(o) => o,
                None => 0,
            };
            let stride = match bv.byte_stride {
                None => size,
                Some(st) => st,
            };
            let stride_ok = match bv.byte_stride {
                None => true,
                Some(st) => st >= size && st % cs == 0,
            };
            offset % cs == 0
                && bv.byte_offset % cs == 0
                && stride_ok
                && (!is_attribute || (offset % 4 == 0 && (cs % 4 == 0 || bv.byte_stride.is_some())))
                && fits(offset, a.count, stride, size, bv.byte_length)
        }
    }
}

pub open spec fn sparse_rule(g: GltfS, a: Accessor) -> bool {
    a.sparse matches Some(sp) ==> {
        let cs = cs_s(a.component_type);
        let size = elem_size_s(a);
        let isz = cs_s(sp.indices_component_type);
        let ib = g.buffer_views[sp.indices_buffer_view as int];
        let vb = g.buffer_views[sp.values_buffer_view as int];
        &&& 0 < sp.count <= a.count
        &&& (sp.indices_component_type == 5121 || sp.indices_component_type == 5123 || sp.indices_component_type == 5125)
        &&& (sp.indices_byte_offset as int) % isz == 0
        &&& (ib.byte_offset as int) % isz == 0
        &&& (sp.values_byte_offset as int) % cs == 0
        &&& (vb.byte_offset as int) % cs == 0
        &&& sp.indices_byte_offset + sp.count * isz <= ib.byte_length
        &&& sp.values_byte_offset + sp.count * size <= vb.byte_length
    }
}

// MUST-044, MUST-045, MUST-047, MUST-048, MUST-051, MUST-052: sparse の規則
fn sparse_ok(g: &Gltf, a: &Accessor) -> (r: bool)
    requires
        accessor_shape_s(*a),
        a.sparse matches Some(sp) ==> sp.indices_buffer_view < g.buffer_views.len() && sp.values_buffer_view < g.buffer_views.len(),
    ensures
        r == sparse_rule(g@, *a),
{
    match &a.sparse {
        None => true,
        Some(s) => {
            let cs = component_size(a.component_type);
            let size = element_size(a);
            let ict = s.indices_component_type;
            if s.count == 0 || s.count > a.count || !(ict == 5121 || ict == 5123 || ict == 5125) {
                return false;
            }
            let isz = component_size(ict);
            let ib = &g.buffer_views[s.indices_buffer_view as usize];
            let vb = &g.buffer_views[s.values_buffer_view as usize];
            proof {
                let c = s.count as int;
                assert(s.indices_byte_offset + (c - 1) * isz + isz == s.indices_byte_offset + c * isz) by (nonlinear_arith);
                assert(s.values_byte_offset + (c - 1) * size + size == s.values_byte_offset + c * size) by (nonlinear_arith);
            }
            s.indices_byte_offset % isz == 0
                && ib.byte_offset % isz == 0
                && s.values_byte_offset % cs == 0
                && vb.byte_offset % cs == 0
                && fits(s.indices_byte_offset, s.count, isz, isz, ib.byte_length)
                && fits(s.values_byte_offset, s.count, size, size, vb.byte_length)
        }
    }
}

fn bounds_len_ok(l: Option<u64>, components: u64) -> (r: bool)
    ensures
        r == (l matches Some(n) ==> n == components),
{
    match l {
        None => true,
        Some(n) => n == components,
    }
}

// AC1–AC3（1 アクセサ分）
pub open spec fn accessor_rule(g: GltfS, i: int) -> bool {
    let a = g.accessors[i];
    let cs = cs_s(a.component_type);
    let size = elem_size_s(a);
    &&& a.count > 0
    // MUST-035: 5125 / 5126 は normalized にしない
    &&& !(a.normalized && (a.component_type == 5125 || a.component_type == 5126))
    // MUST-053: min / max の長さ = 成分数
    &&& (a.min_len matches Some(n) ==> n == a.components)
    &&& (a.max_len matches Some(n) ==> n == a.components)
    &&& match a.buffer_view {
        // MUST-034: bufferView がなければ byteOffset もない
        None => a.byte_offset is None,
        Some(b) => {
            let bv = g.buffer_views[b as int];
            let offset: int = match a.byte_offset {
                Some(o) => o as int,
                None => 0,
            };
            let stride: int = match bv.byte_stride {
                Some(st) => st as int,
                None => size,
            };
            // MUST-037: オフセットは成分の大きさの倍数
            &&& offset % cs == 0
            &&& (bv.byte_offset as int) % cs == 0
            // MUST-040, MUST-041: byteStride ≥ 要素の大きさ、成分の大きさの倍数
            &&& (bv.byte_stride matches Some(st) ==> st as int >= size && (st as int) % cs == 0)
            // MUST-042: 頂点属性の要素は 4 バイト境界
            &&& (attr_acc(g, i) ==> offset % 4 == 0 && (cs % 4 == 0 || bv.byte_stride is Some))
            // MUST-036: アクセサーは bufferView に収まる
            &&& offset + (a.count - 1) * stride + size <= bv.byte_length
        },
    }
    &&& (a.sparse matches Some(sp) ==> {
        let isz = cs_s(sp.indices_component_type);
        let ib = g.buffer_views[sp.indices_buffer_view as int];
        let vb = g.buffer_views[sp.values_buffer_view as int];
        // MUST-044: 0 < sparse.count ≤ count
        &&& 0 < sp.count <= a.count
        // MUST-045: sparse のインデックスは符号なし整数型
        &&& (sp.indices_component_type == 5121 || sp.indices_component_type == 5123 || sp.indices_component_type == 5125)
        // MUST-047, MUST-051: sparse のオフセットの境界
        &&& (sp.indices_byte_offset as int) % isz == 0
        &&& (ib.byte_offset as int) % isz == 0
        &&& (sp.values_byte_offset as int) % cs == 0
        &&& (vb.byte_offset as int) % cs == 0
        // MUST-048, MUST-052: sparse は bufferView に収まる
        &&& sp.indices_byte_offset + sp.count * isz <= ib.byte_length
        &&& sp.values_byte_offset + sp.count * size <= vb.byte_length
    })
}

// AC1–AC3
// MUST-034, MUST-035, MUST-036, MUST-037, MUST-040, MUST-041, MUST-042, MUST-044, MUST-045, MUST-047, MUST-048, MUST-051, MUST-052, MUST-053: アクセサー 1 つ分の規則
fn accessor_ok(g: &Gltf, roles: &Roles, i: usize) -> (r: bool)
    requires
        refs_ok(g@),
        roles_ok(g@, *roles),
        i < g.accessors.len(),
    ensures
        r == accessor_rule(g@, i as int),
{
    proof {
        lemma_refs_ok_split(g@);
        assert(accessor_refs_s(g@, i as int));
    }
    let a = &g.accessors[i];
    a.count > 0
        && !(a.normalized && (a.component_type == 5125 || a.component_type == 5126))
        && bounds_len_ok(a.min_len, a.components)
        && bounds_len_ok(a.max_len, a.components)
        && accessor_view_ok(g, a, roles.attribute[i])
        && sparse_ok(g, a)
}

fn accessors_ok(g: &Gltf, roles: &Roles) -> (r: bool)
    requires
        refs_ok(g@),
        roles_ok(g@, *roles),
    ensures
        r == (forall|i: int| 0 <= i < g@.accessors.len() ==> #[trigger] accessor_rule(g@, i)),
{
    let mut i = 0;
    while i < g.accessors.len()
        invariant
            refs_ok(g@),
            roles_ok(g@, *roles),
            0 <= i <= g.accessors.len(),
            forall|x: int| 0 <= x < i ==> #[trigger] accessor_rule(g@, x),
        decreases g.accessors.len() - i,
    {
        if !accessor_ok(g, roles, i) {
            return false;
        }
        i += 1;
    }
    true
}

pub(crate) fn data_ok(g: &Gltf) -> (r: bool)
    requires
        refs_ok(g@),
    ensures
        r == ((forall|b: int| 0 <= b < g@.buffer_views.len() ==> #[trigger] view_rule(g@, b)) && (forall|i: int|
            0 <= i < g@.accessors.len() ==> #[trigger] accessor_rule(g@, i))),
{
    let roles = accessor_roles(g);
    let u = view_use(g, &roles);
    buffer_views_ok(g, &u) && accessors_ok(g, &roles)
}

} // verus!
