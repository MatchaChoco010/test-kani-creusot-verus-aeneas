use creusot_std::prelude::*;
use crate::model::*;
#[cfg(creusot)]
use crate::validate::refs::*;
#[cfg(creusot)]
use crate::validate::support::*;
#[cfg(creusot)]
use crate::validate::util::*;

#[logic(open)]
pub fn comp_size(ct: Int) -> Int {
    pearlite! {
        if ct == 5120 || ct == 5121 { 1 }
        else if ct == 5122 || ct == 5123 { 2 }
        else if ct == 5125 || ct == 5126 { 4 }
        else { 0 }
    }
}

#[ensures(known_ct(ct@) ==> result@ == comp_size(ct@))]
#[ensures(result@ == 1 || result@ == 2 || result@ == 4)]
#[check(terminates)]
pub fn component_size(ct: u64) -> u64 {
    if ct == 5120 || ct == 5121 {
        1
    } else if ct == 5122 || ct == 5123 {
        2
    } else {
        4
    }
}

// 行列の列数（= 行数）
#[logic(open)]
pub fn mat_dim(c: Int) -> Int {
    pearlite! { if c == 4 { 2 } else if c == 9 { 3 } else if c == 16 { 4 } else { 0 } }
}

#[logic(open)]
pub fn roundup4(x: Int) -> Int {
    pearlite! { if x % 4 == 0 { x } else { x + (4 - x % 4) } }
}

// 要素の大きさ（行列は列ごとに 4 バイト境界へ切り上げる）
#[logic(open)]
pub fn elem_size(a: Accessor) -> Int {
    pearlite! {
        let cs = comp_size(a.component_type@);
        if a.is_matrix { mat_dim(a.components@) * roundup4(cs * mat_dim(a.components@)) }
        else { a.components@ * cs }
    }
}

#[requires(shape_ok(*a))]
#[ensures(known_ct(a.component_type@) ==> result@ == elem_size(*a))]
#[check(terminates)]
pub fn element_size(a: &Accessor) -> u64 {
    let cs = component_size(a.component_type);
    if a.is_matrix {
        let rows = if a.components == 4 { 2 } else if a.components == 9 { 3 } else { 4 };
        (cs * rows + 3) / 4 * 4 * rows
    } else {
        a.components * cs
    }
}

#[requires(count@ >= 1)]
#[ensures(result == (offset@ + (count@ - 1) * stride@ + size@ <= limit@))]
#[check(terminates)]
fn fits(offset: u64, count: u64, stride: u64, size: u64, limit: u64) -> bool {
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

#[ensures(result@.len() == n@ && forall<k> 0 <= k && k < n@ ==> !result@[k])]
#[check(terminates)]
fn false_vec(n: usize) -> Vec<bool> {
    let mut v: Vec<bool> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= n@ && v@.len() == i@ && forall<k> 0 <= k && k < i@ ==> !v@[k])]
    #[variant(n@ - i@)]
    while i < n {
        v.push(false);
        i += 1;
    }
    v
}

#[ensures(result@.len() == n@ && forall<k> 0 <= k && k < n@ ==> result@[k]@ == 0)]
#[check(terminates)]
fn zero_vec(n: usize) -> Vec<u64> {
    let mut v: Vec<u64> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= n@ && v@.len() == i@ && forall<k> 0 <= k && k < i@ ==> v@[k]@ == 0)]
    #[variant(n@ - i@)]
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

#[requires(attrs_lt(attrs@, roles@.len()))]
#[ensures((^roles)@.len() == roles@.len())]
#[ensures(forall<a> 0 <= a && a < roles@.len() ==>
    (^roles)@[a] == (roles@[a] || exists<k> 0 <= k && k < attrs@.len() && attrs@[k].accessor@ == a))]
#[check(terminates)]
fn mark_attributes(roles: &mut Vec<bool>, attrs: &Vec<Attribute>) {
    let _old = snapshot!(*roles);
    let mut i = 0;
    #[invariant(i@ <= attrs@.len() && roles@.len() == _old@.len())]
    #[invariant(forall<a> 0 <= a && a < _old@.len() ==>
        roles@[a] == (_old@[a] || exists<k> 0 <= k && k < i@ && attrs@[k].accessor@ == a))]
    #[variant(attrs@.len() - i@)]
    while i < attrs.len() {
        roles[attrs[i].accessor as usize] = true;
        i += 1;
    }
}

// プリミティブ p の属性か morph target の属性がアクセサ a を使う
#[logic(open)]
pub fn prim_attr_use(p: Primitive, a: Int) -> bool {
    pearlite! {
        (exists<k> 0 <= k && k < p.attributes@.len() && p.attributes@[k].accessor@ == a)
            || (exists<t, k> 0 <= t && t < p.targets@.len() && 0 <= k && k < p.targets@[t]@.len()
                && p.targets@[t]@[k].accessor@ == a)
    }
}

#[requires(attrs_lt(p.attributes@, r.attribute@.len()))]
#[requires(forall<t> 0 <= t && t < p.targets@.len() ==> attrs_lt(p.targets@[t]@, r.attribute@.len()))]
#[requires(opt_lt(p.indices, r.index@.len()))]
#[ensures((^r).attribute@.len() == r.attribute@.len() && (^r).index@.len() == r.index@.len() && (^r).ibm == r.ibm)]
#[ensures(forall<a> 0 <= a && a < r.attribute@.len() ==> (^r).attribute@[a] == (r.attribute@[a] || prim_attr_use(*p, a)))]
#[ensures(forall<a> 0 <= a && a < r.index@.len() ==> (^r).index@[a] == (r.index@[a] || opt_int(p.indices) == Some(a)))]
#[check(terminates)]
fn mark_primitive(r: &mut Roles, p: &Primitive) {
    let _old = snapshot!(*r);
    mark_attributes(&mut r.attribute, &p.attributes);
    let mut t = 0;
    #[invariant(t@ <= p.targets@.len() && r.attribute@.len() == _old.attribute@.len() && r.index == _old.index && r.ibm == _old.ibm)]
    #[invariant(forall<a> 0 <= a && a < _old.attribute@.len() ==> r.attribute@[a] == (_old.attribute@[a]
        || (exists<k> 0 <= k && k < p.attributes@.len() && p.attributes@[k].accessor@ == a)
        || (exists<u, k> 0 <= u && u < t@ && 0 <= k && k < p.targets@[u]@.len() && p.targets@[u]@[k].accessor@ == a)))]
    #[variant(p.targets@.len() - t@)]
    while t < p.targets.len() {
        mark_attributes(&mut r.attribute, &p.targets[t]);
        t += 1;
    }
    match p.indices {
        None => {}
        Some(ix) => r.index[ix as usize] = true,
    }
}

#[logic(open)]
pub fn primitive_refs_n(p: Primitive, na: Int, ni: Int) -> bool {
    pearlite! {
        attrs_lt(p.attributes@, na)
            && (forall<t> 0 <= t && t < p.targets@.len() ==> attrs_lt(p.targets@[t]@, na))
            && opt_lt(p.indices, ni)
    }
}

#[requires(forall<j> 0 <= j && j < m.primitives@.len() ==> primitive_refs_n(m.primitives@[j], r.attribute@.len(), r.index@.len()))]
#[ensures((^r).attribute@.len() == r.attribute@.len() && (^r).index@.len() == r.index@.len() && (^r).ibm == r.ibm)]
#[ensures(forall<a> 0 <= a && a < r.attribute@.len() ==> (^r).attribute@[a] == (r.attribute@[a]
    || exists<j> 0 <= j && j < m.primitives@.len() && prim_attr_use(m.primitives@[j], a)))]
#[ensures(forall<a> 0 <= a && a < r.index@.len() ==> (^r).index@[a] == (r.index@[a]
    || exists<j> 0 <= j && j < m.primitives@.len() && opt_int(m.primitives@[j].indices) == Some(a)))]
#[check(terminates)]
fn mark_mesh(r: &mut Roles, m: &Mesh) {
    let _old = snapshot!(*r);
    let mut j = 0;
    #[invariant(j@ <= m.primitives@.len())]
    #[invariant(r.attribute@.len() == _old.attribute@.len() && r.index@.len() == _old.index@.len() && r.ibm == _old.ibm)]
    #[invariant(forall<a> 0 <= a && a < _old.attribute@.len() ==> r.attribute@[a] == (_old.attribute@[a]
        || exists<q> 0 <= q && q < j@ && prim_attr_use(m.primitives@[q], a)))]
    #[invariant(forall<a> 0 <= a && a < _old.index@.len() ==> r.index@[a] == (_old.index@[a]
        || exists<q> 0 <= q && q < j@ && opt_int(m.primitives@[q].indices) == Some(a)))]
    #[variant(m.primitives@.len() - j@)]
    while j < m.primitives.len() {
        mark_primitive(r, &m.primitives[j]);
        j += 1;
    }
}

#[logic(open)]
pub fn attr_acc(g: Gltf, a: Int) -> bool {
    pearlite! {
        exists<i, j> 0 <= i && i < g.meshes@.len() && 0 <= j && j < g.meshes@[i].primitives@.len()
            && prim_attr_use(g.meshes@[i].primitives@[j], a)
    }
}

#[logic(open)]
pub fn idx_acc(g: Gltf, a: Int) -> bool {
    pearlite! {
        exists<i, j> 0 <= i && i < g.meshes@.len() && 0 <= j && j < g.meshes@[i].primitives@.len()
            && opt_int(g.meshes@[i].primitives@[j].indices) == Some(a)
    }
}

#[requires(refs_ok(*g))]
#[requires(r.attribute@.len() == g.accessors@.len() && r.index@.len() == g.accessors@.len())]
#[ensures((^r).attribute@.len() == r.attribute@.len() && (^r).index@.len() == r.index@.len() && (^r).ibm == r.ibm)]
#[ensures(forall<a> 0 <= a && a < g.accessors@.len() ==> (^r).attribute@[a] == (r.attribute@[a] || attr_acc(*g, a)))]
#[ensures(forall<a> 0 <= a && a < g.accessors@.len() ==> (^r).index@[a] == (r.index@[a] || idx_acc(*g, a)))]
#[check(terminates)]
fn mark_meshes(r: &mut Roles, g: &Gltf) {
    let _old = snapshot!(*r);
    let mut i = 0;
    #[invariant(i@ <= g.meshes@.len())]
    #[invariant(r.attribute@.len() == _old.attribute@.len() && r.index@.len() == _old.index@.len() && r.ibm == _old.ibm)]
    #[invariant(forall<a> 0 <= a && a < g.accessors@.len() ==> r.attribute@[a] == (_old.attribute@[a]
        || exists<x, j> 0 <= x && x < i@ && 0 <= j && j < g.meshes@[x].primitives@.len() && prim_attr_use(g.meshes@[x].primitives@[j], a)))]
    #[invariant(forall<a> 0 <= a && a < g.accessors@.len() ==> r.index@[a] == (_old.index@[a]
        || exists<x, j> 0 <= x && x < i@ && 0 <= j && j < g.meshes@[x].primitives@.len() && opt_int(g.meshes@[x].primitives@[j].indices) == Some(a)))]
    #[variant(g.meshes@.len() - i@)]
    while i < g.meshes.len() {
        mark_mesh(r, &g.meshes[i]);
        i += 1;
    }
}

#[logic(open)]
pub fn ibm_acc(g: Gltf, a: Int) -> bool {
    pearlite! { exists<s> 0 <= s && s < g.skins@.len() && opt_int(g.skins@[s].inverse_bind_matrices) == Some(a) }
}

#[requires(refs_ok(*g))]
#[requires(r.ibm@.len() == g.accessors@.len())]
#[ensures((^r).attribute == r.attribute && (^r).index == r.index && (^r).ibm@.len() == r.ibm@.len())]
#[ensures(forall<a> 0 <= a && a < g.accessors@.len() ==> (^r).ibm@[a] == (r.ibm@[a] || ibm_acc(*g, a)))]
#[check(terminates)]
fn mark_skins(r: &mut Roles, g: &Gltf) {
    let _old = snapshot!(*r);
    let mut i = 0;
    #[invariant(i@ <= g.skins@.len())]
    #[invariant(r.attribute == _old.attribute && r.index == _old.index && r.ibm@.len() == _old.ibm@.len())]
    #[invariant(forall<a> 0 <= a && a < g.accessors@.len() ==> r.ibm@[a] == (_old.ibm@[a]
        || exists<s> 0 <= s && s < i@ && opt_int(g.skins@[s].inverse_bind_matrices) == Some(a)))]
    #[variant(g.skins@.len() - i@)]
    while i < g.skins.len() {
        match g.skins[i].inverse_bind_matrices {
            None => {}
            Some(m) => r.ibm[m as usize] = true,
        }
        i += 1;
    }
}

#[logic(open)]
pub fn roles_spec(g: Gltf, r: Roles) -> bool {
    pearlite! {
        r.attribute@.len() == g.accessors@.len() && r.index@.len() == g.accessors@.len() && r.ibm@.len() == g.accessors@.len()
            && forall<a> 0 <= a && a < g.accessors@.len() ==>
                r.attribute@[a] == attr_acc(g, a) && r.index@[a] == idx_acc(g, a) && r.ibm@[a] == ibm_acc(g, a)
    }
}

#[requires(refs_ok(*g))]
#[ensures(roles_spec(*g, result))]
#[check(terminates)]
pub fn accessor_roles(g: &Gltf) -> Roles {
    let n = g.accessors.len();
    let mut r = Roles { attribute: false_vec(n), index: false_vec(n), ibm: false_vec(n) };
    mark_meshes(&mut r, g);
    mark_skins(&mut r, g);
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

#[logic(open)]
pub fn in_view(g: Gltf, a: Int, b: Int) -> bool {
    pearlite! { opt_int(g.accessors@[a].buffer_view) == Some(b) }
}

#[logic(open)]
pub fn attr_use(g: Gltf, b: Int) -> bool {
    pearlite! { exists<a> 0 <= a && a < g.accessors@.len() && attr_acc(g, a) && in_view(g, a, b) }
}

#[logic(open)]
pub fn idx_use(g: Gltf, b: Int) -> bool {
    pearlite! { exists<a> 0 <= a && a < g.accessors@.len() && idx_acc(g, a) && in_view(g, a, b) }
}

#[logic(open)]
pub fn ibm_use(g: Gltf, b: Int) -> bool {
    pearlite! { exists<a> 0 <= a && a < g.accessors@.len() && ibm_acc(g, a) && in_view(g, a, b) }
}

#[logic(open)]
pub fn sparse_use(g: Gltf, b: Int) -> bool {
    pearlite! {
        exists<a> 0 <= a && a < g.accessors@.len() && match g.accessors@[a].sparse {
            None => false,
            Some(sp) => sp.indices_buffer_view@ == b || sp.values_buffer_view@ == b,
        }
    }
}

#[logic(open)]
pub fn acc_use(g: Gltf, b: Int) -> bool {
    pearlite! { exists<a> 0 <= a && a < g.accessors@.len() && in_view(g, a, b) }
}

#[logic(open)]
pub fn non_attr_use(g: Gltf, b: Int) -> bool {
    pearlite! { exists<a> 0 <= a && a < g.accessors@.len() && !attr_acc(g, a) && in_view(g, a, b) }
}

// アクセサ 0..n のうち、属性アクセサで bufferView = b のものの数
#[logic(open)]
#[variant(n)]
pub fn attr_count_upto(g: Gltf, b: Int, n: Int) -> Int {
    pearlite! {
        if n <= 0 { 0 }
        else { attr_count_upto(g, b, n - 1) + if attr_acc(g, n - 1) && in_view(g, n - 1, b) { 1 } else { 0 } }
    }
}

#[logic(open)]
pub fn attr_count(g: Gltf, b: Int) -> Int {
    pearlite! { attr_count_upto(g, b, g.accessors@.len()) }
}

#[logic(opaque)]
#[variant(n)]
#[requires(0 <= n)]
#[ensures(0 <= attr_count_upto(g, b, n) && attr_count_upto(g, b, n) <= n)]
pub fn lemma_attr_count_bound(g: Gltf, b: Int, n: Int) {
    if n > 0 {
        lemma_attr_count_bound(g, b, n - 1)
    }
}

#[requires(refs_ok(*g) && roles_spec(*g, *roles))]
#[requires(u.attribute@.len() == g.buffer_views@.len() && u.attribute_count@.len() == g.buffer_views@.len())]
#[requires(u.index@.len() == g.buffer_views@.len() && u.ibm@.len() == g.buffer_views@.len() && u.sparse@.len() == g.buffer_views@.len())]
#[requires(u.accessor@.len() == g.buffer_views@.len() && u.non_attribute@.len() == g.buffer_views@.len())]
#[requires(forall<b> 0 <= b && b < g.buffer_views@.len() ==>
    !u.attribute@[b] && u.attribute_count@[b]@ == 0 && !u.index@[b] && !u.ibm@[b] && !u.sparse@[b]
    && !u.accessor@[b] && !u.non_attribute@[b])]
#[ensures((^u).image == u.image && (^u).animation == u.animation)]
#[ensures((^u).attribute@.len() == u.attribute@.len() && (^u).attribute_count@.len() == u.attribute_count@.len())]
#[ensures((^u).index@.len() == u.index@.len() && (^u).ibm@.len() == u.ibm@.len() && (^u).sparse@.len() == u.sparse@.len())]
#[ensures((^u).accessor@.len() == u.accessor@.len() && (^u).non_attribute@.len() == u.non_attribute@.len())]
#[ensures(forall<b> 0 <= b && b < g.buffer_views@.len() ==>
    (^u).attribute@[b] == attr_use(*g, b) && (^u).attribute_count@[b]@ == attr_count(*g, b)
    && (^u).index@[b] == idx_use(*g, b) && (^u).ibm@[b] == ibm_use(*g, b) && (^u).sparse@[b] == sparse_use(*g, b)
    && (^u).accessor@[b] == acc_use(*g, b) && (^u).non_attribute@[b] == non_attr_use(*g, b))]
#[check(terminates)]
fn mark_accessor_views(u: &mut ViewUse, g: &Gltf, roles: &Roles) {
    let _old = snapshot!(*u);
    let mut i = 0;
    #[invariant(i@ <= g.accessors@.len())]
    #[invariant(u.image == _old.image && u.animation == _old.animation)]
    #[invariant(u.attribute@.len() == _old.attribute@.len() && u.attribute_count@.len() == _old.attribute_count@.len())]
    #[invariant(u.index@.len() == _old.index@.len() && u.ibm@.len() == _old.ibm@.len() && u.sparse@.len() == _old.sparse@.len())]
    #[invariant(u.accessor@.len() == _old.accessor@.len() && u.non_attribute@.len() == _old.non_attribute@.len())]
    #[invariant(forall<b> 0 <= b && b < g.buffer_views@.len() ==>
        u.attribute@[b] == (exists<a> 0 <= a && a < i@ && attr_acc(*g, a) && in_view(*g, a, b))
        && u.attribute_count@[b]@ == attr_count_upto(*g, b, i@)
        && u.index@[b] == (exists<a> 0 <= a && a < i@ && idx_acc(*g, a) && in_view(*g, a, b))
        && u.ibm@[b] == (exists<a> 0 <= a && a < i@ && ibm_acc(*g, a) && in_view(*g, a, b))
        && u.sparse@[b] == (exists<a> 0 <= a && a < i@ && match g.accessors@[a].sparse {
            None => false,
            Some(sp) => sp.indices_buffer_view@ == b || sp.values_buffer_view@ == b,
        })
        && u.accessor@[b] == (exists<a> 0 <= a && a < i@ && in_view(*g, a, b))
        && u.non_attribute@[b] == (exists<a> 0 <= a && a < i@ && !attr_acc(*g, a) && in_view(*g, a, b)))]
    #[variant(g.accessors@.len() - i@)]
    while i < g.accessors.len() {
        let a = &g.accessors[i];
        match a.buffer_view {
            None => {}
            Some(bv) => {
                let b = bv as usize;
                snapshot!(lemma_attr_count_bound(*g, b@, i@));
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
    }
}

#[logic(open)]
pub fn image_use(g: Gltf, b: Int) -> bool {
    pearlite! { exists<i> 0 <= i && i < g.images@.len() && opt_int(g.images@[i].buffer_view) == Some(b) }
}

#[requires(refs_ok(*g) && u.image@.len() == g.buffer_views@.len())]
#[requires(forall<b> 0 <= b && b < g.buffer_views@.len() ==> !u.image@[b])]
#[ensures((^u).attribute == u.attribute && (^u).attribute_count == u.attribute_count && (^u).index == u.index)]
#[ensures((^u).ibm == u.ibm && (^u).sparse == u.sparse && (^u).animation == u.animation)]
#[ensures((^u).accessor == u.accessor && (^u).non_attribute == u.non_attribute)]
#[ensures((^u).image@.len() == u.image@.len())]
#[ensures(forall<b> 0 <= b && b < g.buffer_views@.len() ==> (^u).image@[b] == image_use(*g, b))]
#[check(terminates)]
fn mark_image_views(u: &mut ViewUse, g: &Gltf) {
    let _old = snapshot!(*u);
    let mut i = 0;
    #[invariant(i@ <= g.images@.len())]
    #[invariant(u.attribute == _old.attribute && u.attribute_count == _old.attribute_count && u.index == _old.index)]
    #[invariant(u.ibm == _old.ibm && u.sparse == _old.sparse && u.animation == _old.animation)]
    #[invariant(u.accessor == _old.accessor && u.non_attribute == _old.non_attribute)]
    #[invariant(u.image@.len() == _old.image@.len())]
    #[invariant(forall<b> 0 <= b && b < g.buffer_views@.len() ==>
        u.image@[b] == exists<k> 0 <= k && k < i@ && opt_int(g.images@[k].buffer_view) == Some(b))]
    #[variant(g.images@.len() - i@)]
    while i < g.images.len() {
        match g.images[i].buffer_view {
            None => {}
            Some(bv) => u.image[bv as usize] = true,
        }
        i += 1;
    }
}

#[requires(refs_ok(*g) && accessor@ < g.accessors@.len() && v@.len() == g.buffer_views@.len())]
#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<b> 0 <= b && b < v@.len() ==> (^v)@[b] == (v@[b] || in_view(*g, accessor@, b)))]
#[check(terminates)]
fn mark_accessor_view(v: &mut Vec<bool>, g: &Gltf, accessor: u64) {
    match g.accessors[accessor as usize].buffer_view {
        None => {}
        Some(bv) => v[bv as usize] = true,
    }
}

#[requires(refs_ok(*g) && animation_refs(*g, *an) && u.animation@.len() == g.buffer_views@.len())]
#[ensures((^u).attribute == u.attribute && (^u).attribute_count == u.attribute_count && (^u).index == u.index)]
#[ensures((^u).ibm == u.ibm && (^u).sparse == u.sparse && (^u).image == u.image)]
#[ensures((^u).accessor == u.accessor && (^u).non_attribute == u.non_attribute)]
#[ensures((^u).animation@.len() == u.animation@.len())]
#[ensures(forall<b> 0 <= b && b < g.buffer_views@.len() ==> (^u).animation@[b] == (u.animation@[b]
    || exists<s> 0 <= s && s < an.samplers@.len() && (in_view(*g, an.samplers@[s].input@, b) || in_view(*g, an.samplers@[s].output@, b))))]
#[check(terminates)]
fn mark_animation_views(u: &mut ViewUse, g: &Gltf, an: &Animation) {
    let _old = snapshot!(*u);
    let mut s = 0;
    #[invariant(s@ <= an.samplers@.len())]
    #[invariant(u.attribute == _old.attribute && u.attribute_count == _old.attribute_count && u.index == _old.index)]
    #[invariant(u.ibm == _old.ibm && u.sparse == _old.sparse && u.image == _old.image)]
    #[invariant(u.accessor == _old.accessor && u.non_attribute == _old.non_attribute)]
    #[invariant(u.animation@.len() == _old.animation@.len())]
    #[invariant(forall<b> 0 <= b && b < g.buffer_views@.len() ==> u.animation@[b] == (_old.animation@[b]
        || exists<q> 0 <= q && q < s@ && (in_view(*g, an.samplers@[q].input@, b) || in_view(*g, an.samplers@[q].output@, b))))]
    #[variant(an.samplers@.len() - s@)]
    while s < an.samplers.len() {
        mark_accessor_view(&mut u.animation, g, an.samplers[s].input);
        mark_accessor_view(&mut u.animation, g, an.samplers[s].output);
        s += 1;
    }
}

#[logic(open)]
pub fn anim_use(g: Gltf, b: Int) -> bool {
    pearlite! {
        exists<i, s> 0 <= i && i < g.animations@.len() && 0 <= s && s < g.animations@[i].samplers@.len()
            && (in_view(g, g.animations@[i].samplers@[s].input@, b) || in_view(g, g.animations@[i].samplers@[s].output@, b))
    }
}

#[requires(refs_ok(*g) && u.animation@.len() == g.buffer_views@.len())]
#[requires(forall<b> 0 <= b && b < g.buffer_views@.len() ==> !u.animation@[b])]
#[ensures((^u).attribute == u.attribute && (^u).attribute_count == u.attribute_count && (^u).index == u.index)]
#[ensures((^u).ibm == u.ibm && (^u).sparse == u.sparse && (^u).image == u.image)]
#[ensures((^u).accessor == u.accessor && (^u).non_attribute == u.non_attribute)]
#[ensures((^u).animation@.len() == u.animation@.len())]
#[ensures(forall<b> 0 <= b && b < g.buffer_views@.len() ==> (^u).animation@[b] == anim_use(*g, b))]
#[check(terminates)]
fn mark_animations_views(u: &mut ViewUse, g: &Gltf) {
    let _old = snapshot!(*u);
    let mut i = 0;
    #[invariant(i@ <= g.animations@.len())]
    #[invariant(u.attribute == _old.attribute && u.attribute_count == _old.attribute_count && u.index == _old.index)]
    #[invariant(u.ibm == _old.ibm && u.sparse == _old.sparse && u.image == _old.image)]
    #[invariant(u.accessor == _old.accessor && u.non_attribute == _old.non_attribute)]
    #[invariant(u.animation@.len() == _old.animation@.len())]
    #[invariant(forall<b> 0 <= b && b < g.buffer_views@.len() ==> u.animation@[b] == exists<x, s> 0 <= x && x < i@
        && 0 <= s && s < g.animations@[x].samplers@.len()
        && (in_view(*g, g.animations@[x].samplers@[s].input@, b) || in_view(*g, g.animations@[x].samplers@[s].output@, b)))]
    #[variant(g.animations@.len() - i@)]
    while i < g.animations.len() {
        mark_animation_views(u, g, &g.animations[i]);
        i += 1;
    }
}

#[logic(open)]
pub fn use_spec(g: Gltf, u: ViewUse) -> bool {
    pearlite! {
        let n = g.buffer_views@.len();
        u.attribute@.len() == n && u.attribute_count@.len() == n && u.index@.len() == n && u.ibm@.len() == n
            && u.sparse@.len() == n && u.image@.len() == n && u.animation@.len() == n
            && u.accessor@.len() == n && u.non_attribute@.len() == n
            && forall<b> 0 <= b && b < n ==>
                u.attribute@[b] == attr_use(g, b) && u.attribute_count@[b]@ == attr_count(g, b)
                && u.index@[b] == idx_use(g, b) && u.ibm@[b] == ibm_use(g, b) && u.sparse@[b] == sparse_use(g, b)
                && u.image@[b] == image_use(g, b) && u.animation@[b] == anim_use(g, b)
                && u.accessor@[b] == acc_use(g, b) && u.non_attribute@[b] == non_attr_use(g, b)
    }
}

// MUST-026, MUST-027, MUST-038, MUST-039, MUST-046, MUST-050: bufferView ごとの用途
#[requires(refs_ok(*g) && roles_spec(*g, *roles))]
#[ensures(use_spec(*g, result))]
#[check(terminates)]
pub fn view_use(g: &Gltf, roles: &Roles) -> ViewUse {
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

#[logic(open)]
pub fn at_most_one(a: bool, b: bool, c: bool, d: bool, e: bool) -> bool {
    pearlite! {
        !(a && b) && !(a && c) && !(a && d) && !(a && e) && !(b && c) && !(b && d) && !(b && e)
            && !(c && d) && !(c && e) && !(d && e)
    }
}

// B1〜B4
// MUST-025, MUST-026, MUST-027: bufferView はバッファーに収まり、1 種類のデータだけで、画像の bufferView はアクセサーと sparse から使わない
// MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039: byteStride は 2 つ以上の頂点属性なら必要、頂点属性以外なら持たず、4 の倍数で 4〜252、byteLength 以下
// MUST-028, MUST-070, MUST-090: target は頂点属性なら頂点配列、他の種類のデータなら持たない
// MUST-046, MUST-050, MUST-072, MUST-098, MUST-110, MUST-142, MUST-146: インデックス・sparse・逆バインド行列・画像・アニメーションの bufferView の byteStride と target
#[logic(open)]
pub fn bv_rule(g: Gltf, b: Int) -> bool {
    pearlite! {
        let bv = g.buffer_views@[b];
        let attr = attr_use(g, b);
        let idx = idx_use(g, b);
        let ibm = ibm_use(g, b);
        let other = anim_use(g, b) || sparse_use(g, b);
        let image = image_use(g, b);
        let vertex_or_image = attr || idx || ibm || image;
        bv.byte_length@ > 0
            && bv.byte_offset@ + bv.byte_length@ <= g.buffers@[bv.buffer@].byte_length@
            && (vertex_or_image ==> at_most_one(attr, idx, ibm, other, image))
            && (image ==> !acc_use(g, b) && !sparse_use(g, b))
            && match bv.byte_stride {
                None => attr_count(g, b) < 2,
                Some(st) => 4 <= st@ && st@ <= 252 && st@ % 4 == 0 && st@ <= bv.byte_length@
                    && !idx && !ibm && !other && !image && !non_attr_use(g, b) && bv.target != Some(34963u64),
            }
            && match bv.target {
                None => true,
                Some(t) => !(attr && t@ != 34962) && !(idx && t@ != 34963) && !ibm && !other && !image,
            }
    }
}

// MUST-025, MUST-026, MUST-027: bufferView はバッファーに収まり、1 種類のデータだけで、画像の bufferView はアクセサーと sparse から使わない
#[requires(refs_ok(*g) && use_spec(*g, *u) && b@ < g.buffer_views@.len())]
#[ensures(result == bv_rule(*g, b@))]
#[check(terminates)]
fn buffer_view_ok(g: &Gltf, u: &ViewUse, b: usize) -> bool {
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

// MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039: byteStride は 2 つ以上の頂点属性なら必要、頂点属性以外なら持たず、4 の倍数で 4〜252、byteLength 以下
// MUST-046, MUST-050, MUST-072, MUST-098, MUST-110, MUST-142, MUST-146: インデックス・sparse・逆バインド行列・画像・アニメーションの bufferView は byteStride を持たない
#[ensures(result == match bv.byte_stride {
    None => attribute_count@ <= 1,
    Some(st) => 4 <= st@ && st@ <= 252 && st@ % 4 == 0 && st@ <= bv.byte_length@ && !non_vertex && bv.target != Some(34963u64),
})]
#[check(terminates)]
fn stride_ok(bv: &BufferView, attribute_count: u64, non_vertex: bool) -> bool {
    match bv.byte_stride {
        None => attribute_count <= 1,
        Some(st) => st >= 4 && st <= 252 && st % 4 == 0 && st <= bv.byte_length && !non_vertex && !opt_eq(bv.target, Some(34963)),
    }
}

// MUST-028, MUST-070, MUST-090: target は頂点属性なら頂点配列、他の種類のデータなら持たない
// MUST-046, MUST-050, MUST-072, MUST-098, MUST-110, MUST-142, MUST-146: インデックスの target は要素配列、sparse・逆バインド行列・画像・アニメーションは target を持たない
#[ensures(result == match target {
    None => true,
    Some(t) => !(attr && t@ != 34962) && !(idx && t@ != 34963) && !other,
})]
#[check(terminates)]
fn target_ok(target: Option<u64>, attr: bool, idx: bool, other: bool) -> bool {
    match target {
        None => true,
        Some(t) => !(attr && t != 34962) && !(idx && t != 34963) && !other,
    }
}

#[requires(refs_ok(*g) && use_spec(*g, *u))]
#[ensures(result == forall<b> 0 <= b && b < g.buffer_views@.len() ==> bv_rule(*g, b))]
#[check(terminates)]
fn buffer_views_ok(g: &Gltf, u: &ViewUse) -> bool {
    let mut b = 0;
    #[invariant(b@ <= g.buffer_views@.len())]
    #[invariant(forall<k> 0 <= k && k < b@ ==> bv_rule(*g, k))]
    #[variant(g.buffer_views@.len() - b@)]
    while b < g.buffer_views.len() {
        if !buffer_view_ok(g, u, b) {
            return false;
        }
        b += 1;
    }
    true
}

// AC2（attr: 属性アクセサか）
// MUST-034, MUST-036, MUST-037, MUST-040, MUST-041, MUST-042: アクセサーの byteOffset・境界・byteStride と bufferView に収まること
#[logic(open)]
pub fn ac2(g: Gltf, a: Accessor, attr: bool) -> bool {
    pearlite! {
        match a.buffer_view {
            None => a.byte_offset == None,
            Some(b) => {
                let bv = g.buffer_views@[b@];
                let off = match a.byte_offset { None => 0, Some(o) => o@ };
                let cs = comp_size(a.component_type@);
                let size = elem_size(a);
                let stride = match bv.byte_stride { None => size, Some(st) => st@ };
                off % cs == 0
                    && bv.byte_offset@ % cs == 0
                    && match bv.byte_stride { None => true, Some(st) => st@ >= size && st@ % cs == 0 }
                    && (attr ==> off % 4 == 0 && (cs % 4 == 0 || bv.byte_stride != None))
                    && off + (a.count@ - 1) * stride + size <= bv.byte_length@
            }
        }
    }
}

// MUST-034, MUST-036, MUST-037, MUST-040, MUST-041, MUST-042: アクセサーの byteOffset・境界・byteStride と bufferView に収まること
#[requires(opt_lt(a.buffer_view, g.buffer_views@.len()) && shape_ok(*a) && known_ct(a.component_type@) && a.count@ > 0)]
#[ensures(result == ac2(*g, *a, is_attribute))]
#[check(terminates)]
fn accessor_view_ok(g: &Gltf, a: &Accessor, is_attribute: bool) -> bool {
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

// AC3
// MUST-044, MUST-045, MUST-047, MUST-048, MUST-051, MUST-052: sparse の count・インデックスの型・オフセットの境界・bufferView に収まること
#[logic(open)]
pub fn ac3(g: Gltf, a: Accessor) -> bool {
    pearlite! {
        match a.sparse {
            None => true,
            Some(sp) => {
                let ict = sp.indices_component_type@;
                let isz = comp_size(ict);
                let cs = comp_size(a.component_type@);
                let size = elem_size(a);
                let ib = g.buffer_views@[sp.indices_buffer_view@];
                let vb = g.buffer_views@[sp.values_buffer_view@];
                0 < sp.count@ && sp.count@ <= a.count@
                    && (ict == 5121 || ict == 5123 || ict == 5125)
                    && sp.indices_byte_offset@ % isz == 0
                    && ib.byte_offset@ % isz == 0
                    && sp.values_byte_offset@ % cs == 0
                    && vb.byte_offset@ % cs == 0
                    && sp.indices_byte_offset@ + sp.count@ * isz <= ib.byte_length@
                    && sp.values_byte_offset@ + sp.count@ * size <= vb.byte_length@
            }
        }
    }
}

// MUST-044, MUST-045, MUST-047, MUST-048, MUST-051, MUST-052: sparse の count・インデックスの型・オフセットの境界・bufferView に収まること
#[requires(sparse_refs(a.sparse, g.buffer_views@.len()) && shape_ok(*a) && known_ct(a.component_type@))]
#[ensures(result == ac3(*g, *a))]
#[check(terminates)]
fn sparse_ok(g: &Gltf, a: &Accessor) -> bool {
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
            s.indices_byte_offset % isz == 0
                && ib.byte_offset % isz == 0
                && s.values_byte_offset % cs == 0
                && vb.byte_offset % cs == 0
                && fits(s.indices_byte_offset, s.count, isz, isz, ib.byte_length)
                && fits(s.values_byte_offset, s.count, size, size, vb.byte_length)
        }
    }
}

#[logic(open)]
pub fn len_ok(l: Option<u64>, c: Int) -> bool {
    pearlite! {
        match l {
            None => true,
            Some(n) => n@ == c,
        }
    }
}

// MUST-053: min / max の長さ = 成分数
#[ensures(result == len_ok(l, components@))]
#[check(terminates)]
fn bounds_len_ok(l: Option<u64>, components: u64) -> bool {
    match l {
        None => true,
        Some(n) => n == components,
    }
}

// AC1
// MUST-035, MUST-053: 5125/5126 は normalized にせず、min / max の長さ = 成分数
#[logic(open)]
pub fn ac1(a: Accessor) -> bool {
    pearlite! {
        a.count@ > 0
            && !(a.normalized && (a.component_type@ == 5125 || a.component_type@ == 5126))
            && len_ok(a.min_len, a.components@)
            && len_ok(a.max_len, a.components@)
    }
}

#[logic(open)]
pub fn ac_rule(g: Gltf, i: Int) -> bool {
    pearlite! { ac1(g.accessors@[i]) && ac2(g, g.accessors@[i], attr_acc(g, i)) && ac3(g, g.accessors@[i]) }
}

// MUST-035, MUST-053: 5125/5126 は normalized にせず、min / max の長さ = 成分数
#[requires(refs_ok(*g) && supported_spec(*g) && roles_spec(*g, *roles) && i@ < g.accessors@.len())]
#[ensures(result == ac_rule(*g, i@))]
#[check(terminates)]
fn accessor_ok(g: &Gltf, roles: &Roles, i: usize) -> bool {
    let a = &g.accessors[i];
    a.count > 0
        && !(a.normalized && (a.component_type == 5125 || a.component_type == 5126))
        && bounds_len_ok(a.min_len, a.components)
        && bounds_len_ok(a.max_len, a.components)
        && accessor_view_ok(g, a, roles.attribute[i])
        && sparse_ok(g, a)
}

#[requires(refs_ok(*g) && supported_spec(*g) && roles_spec(*g, *roles))]
#[ensures(result == forall<i> 0 <= i && i < g.accessors@.len() ==> ac_rule(*g, i))]
#[check(terminates)]
fn accessors_ok(g: &Gltf, roles: &Roles) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.accessors@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> ac_rule(*g, k))]
    #[variant(g.accessors@.len() - i@)]
    while i < g.accessors.len() {
        if !accessor_ok(g, roles, i) {
            return false;
        }
        i += 1;
    }
    true
}

// B1〜B4, AC1〜AC3
#[logic(open)]
pub fn data_spec(g: Gltf) -> bool {
    pearlite! {
        (forall<b> 0 <= b && b < g.buffer_views@.len() ==> bv_rule(g, b))
            && (forall<i> 0 <= i && i < g.accessors@.len() ==> ac_rule(g, i))
    }
}

#[requires(refs_ok(*g) && supported_spec(*g))]
#[ensures(result == data_spec(*g))]
#[check(terminates)]
pub(crate) fn data_ok(g: &Gltf) -> bool {
    let roles = accessor_roles(g);
    let u = view_use(g, &roles);
    buffer_views_ok(g, &u) && accessors_ok(g, &roles)
}
