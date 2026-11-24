use creusot_std::prelude::*;
use crate::model::*;
use crate::validate::util::*;
#[cfg(creusot)]
use crate::json::number::*;
#[cfg(creusot)]
use crate::validate::refs::*;

pub const SEM_OTHER: u64 = 0;

pub const SEM_POSITION: u64 = 1;

pub const SEM_NORMAL: u64 = 2;

pub const SEM_TANGENT: u64 = 3;

pub const SEM_TEXCOORD: u64 = 4;

pub const SEM_COLOR: u64 = 5;

pub const SEM_JOINTS: u64 = 6;

pub const SEM_WEIGHTS: u64 = 7;

pub const SEM_INVALID: u64 = 8;

#[logic(open)]
pub fn has_prefix(s: Seq<u8>, p: Seq<u8>) -> bool {
    pearlite! { p.len() <= s.len() && forall<k> 0 <= k && k < p.len() ==> s[k] == p[k] }
}

#[ensures(result == has_prefix(s@, p@))]
#[check(terminates)]
pub(crate) fn starts_with(s: &Vec<u8>, p: &[u8]) -> bool {
    if s.len() < p.len() {
        return false;
    }
    let mut i = 0;
    #[invariant(i@ <= p@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> s@[k] == p@[k])]
    #[variant(p@.len() - i@)]
    while i < p.len() {
        if s[i] != p[i] {
            return false;
        }
        i += 1;
    }
    true
}

#[requires(start@ <= s@.len() && s@.len() - start@ <= 9)]
#[ensures(match result {
    None => exists<k> start@ <= k && k < s@.len() && !is_dec(s@[k]),
    Some(v) => (forall<k> start@ <= k && k < s@.len() ==> is_dec(s@[k])) && v@ == dec_val(s@[start@..]),
})]
#[check(terminates)]
fn decimal_digits(s: &Vec<u8>, start: usize) -> Option<u64> {
    let mut v: u64 = 0;
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= s@.len())]
    #[invariant(forall<k> start@ <= k && k < i@ ==> is_dec(s@[k]))]
    #[invariant(v@ == dec_val(s@[start@..i@]))]
    #[invariant(v@ < pow10(i@ - start@))]
    #[variant(s@.len() - i@)]
    while i < s.len() {
        if s[i] < b'0' || s[i] > b'9' {
            return None;
        }
        snapshot!(lemma_dec_val_snoc(s@[start@..], i@ - start@));
        proof_assert!(s@[start@..][..i@ - start@].ext_eq(s@[start@..i@]));
        proof_assert!(s@[start@..][..i@ - start@ + 1].ext_eq(s@[start@..i@ + 1]));
        snapshot!(lemma_pow10_le(i@ - start@, 8));
        v = v * 10 + (s[i] - b'0') as u64;
        i += 1;
    }
    proof_assert!(s@[start@..i@].ext_eq(s@[start@..]));
    Some(v)
}

// セット番号: 1〜9 桁の 10 進数で、先頭が 0 なのは "0" だけ
// MUST-060, MUST-061, MUST-062: 集合の番号は 9 桁以下の 10 進整数で、先頭に 0 を付けない
#[logic(open)]
pub fn set_index(s: Seq<u8>) -> Option<Int> {
    pearlite! {
        if 1 <= s.len() && s.len() <= 9 && (forall<k> 0 <= k && k < s.len() ==> is_dec(s[k])) && (s[0]@ != 48 || s.len() == 1) {
            Some(dec_val(s))
        } else {
            None
        }
    }
}

// MUST-060, MUST-061, MUST-062: 集合の番号は 9 桁以下の 10 進整数で、先頭に 0 を付けない
#[requires(start@ <= s@.len())]
#[ensures(opt_int(result) == set_index(s@[start@..]))]
#[check(terminates)]
fn parse_set_index(s: &Vec<u8>, start: usize) -> Option<u64> {
    let n = s.len() - start;
    if n == 0 || n > 9 || (s[start] == b'0' && n > 1) {
        None
    } else {
        decimal_digits(s, start)
    }
}

#[logic(open)]
pub fn lit_position() -> Seq<u8> { seq![80u8, 79u8, 83u8, 73u8, 84u8, 73u8, 79u8, 78u8] }

#[logic(open)]
pub fn lit_normal() -> Seq<u8> { seq![78u8, 79u8, 82u8, 77u8, 65u8, 76u8] }

#[logic(open)]
pub fn lit_tangent() -> Seq<u8> { seq![84u8, 65u8, 78u8, 71u8, 69u8, 78u8, 84u8] }

#[logic(open)]
pub fn lit_texcoord() -> Seq<u8> { seq![84u8, 69u8, 88u8, 67u8, 79u8, 79u8, 82u8, 68u8, 95u8] }

#[logic(open)]
pub fn lit_color() -> Seq<u8> { seq![67u8, 79u8, 76u8, 79u8, 82u8, 95u8] }

#[logic(open)]
pub fn lit_joints() -> Seq<u8> { seq![74u8, 79u8, 73u8, 78u8, 84u8, 83u8, 95u8] }

#[logic(open)]
pub fn lit_weights() -> Seq<u8> { seq![87u8, 69u8, 73u8, 71u8, 72u8, 84u8, 83u8, 95u8] }

#[logic(open)]
pub fn indexed_semantic(n: Seq<u8>, p: Seq<u8>, kind: Int) -> (Int, Int) {
    pearlite! {
        match set_index(n[p.len()..]) {
            Some(v) => (kind, v),
            None => (SEM_INVALID@, 0),
        }
    }
}

// 属性名の意味 (kind, セット番号)
// MUST-063: TEXCOORD_ などの後ろが正しい番号でなければ無効
#[logic(open)]
pub fn semantic_spec(n: Seq<u8>) -> (Int, Int) {
    pearlite! {
        if seq_is(n, lit_position()) { (SEM_POSITION@, 0) }
        else if seq_is(n, lit_normal()) { (SEM_NORMAL@, 0) }
        else if seq_is(n, lit_tangent()) { (SEM_TANGENT@, 0) }
        else if has_prefix(n, lit_texcoord()) { indexed_semantic(n, lit_texcoord(), SEM_TEXCOORD@) }
        else if has_prefix(n, lit_color()) { indexed_semantic(n, lit_color(), SEM_COLOR@) }
        else if has_prefix(n, lit_joints()) { indexed_semantic(n, lit_joints(), SEM_JOINTS@) }
        else if has_prefix(n, lit_weights()) { indexed_semantic(n, lit_weights(), SEM_WEIGHTS@) }
        else { (SEM_OTHER@, 0) }
    }
}

// MUST-063: TEXCOORD_ などの後ろが正しい番号でなければ無効
#[ensures((result.0@, result.1@) == semantic_spec(name@))]
#[check(terminates)]
pub fn semantic(name: &Vec<u8>) -> (u64, u64) {
    if bytes_eq(name, &[b'P', b'O', b'S', b'I', b'T', b'I', b'O', b'N']) {
        return (SEM_POSITION, 0);
    }
    if bytes_eq(name, &[b'N', b'O', b'R', b'M', b'A', b'L']) {
        return (SEM_NORMAL, 0);
    }
    if bytes_eq(name, &[b'T', b'A', b'N', b'G', b'E', b'N', b'T']) {
        return (SEM_TANGENT, 0);
    }
    let (kind, plen) = if starts_with(name, &[b'T', b'E', b'X', b'C', b'O', b'O', b'R', b'D', b'_']) {
        (SEM_TEXCOORD, 9)
    } else if starts_with(name, &[b'C', b'O', b'L', b'O', b'R', b'_']) {
        (SEM_COLOR, 6)
    } else if starts_with(name, &[b'J', b'O', b'I', b'N', b'T', b'S', b'_']) {
        (SEM_JOINTS, 7)
    } else if starts_with(name, &[b'W', b'E', b'I', b'G', b'H', b'T', b'S', b'_']) {
        (SEM_WEIGHTS, 8)
    } else {
        return (SEM_OTHER, 0);
    };
    match parse_set_index(name, plen) {
        Some(n) => (kind, n),
        None => (SEM_INVALID, 0),
    }
}

#[logic(open)]
pub fn uint_ty(a: Accessor) -> bool {
    pearlite! { !a.normalized && (a.component_type@ == 5121 || a.component_type@ == 5123) }
}

// 行列でない VECn / SCALAR
#[logic(open)]
pub fn vec_n(a: Accessor, n: Int) -> bool {
    pearlite! { !a.is_matrix && a.components@ == n }
}

// 意味ごとに許される accessor の型（adoc 1645, 1922）
// MUST-059, MUST-086: 属性とモーフターゲットの属性の型の表
#[logic(open)]
pub fn allowed_type(kind: Int, a: Accessor, morph: bool) -> bool {
    pearlite! {
        if kind == SEM_OTHER@ { true }
        else if kind == SEM_POSITION@ || kind == SEM_NORMAL@ { vec_n(a, 3) && f32_ty(a) }
        else if kind == SEM_TANGENT@ { (if morph { vec_n(a, 3) } else { vec_n(a, 4) }) && f32_ty(a) }
        else if kind == SEM_TEXCOORD@ { vec_n(a, 2) && (f32_ty(a) || unorm_ty(a) || (morph && snorm_ty(a))) }
        else if kind == SEM_COLOR@ { (vec_n(a, 3) || vec_n(a, 4)) && (f32_ty(a) || unorm_ty(a) || (morph && snorm_ty(a))) }
        else if kind == SEM_JOINTS@ { !morph && vec_n(a, 4) && uint_ty(a) }
        else if kind == SEM_WEIGHTS@ { !morph && vec_n(a, 4) && (f32_ty(a) || unorm_ty(a)) }
        else { false }
    }
}

// MUST-059, MUST-086: 属性とモーフターゲットの属性の型の表
#[ensures(result == allowed_type(kind@, *a, morph))]
#[check(terminates)]
fn attribute_type_ok(kind: u64, a: &Accessor, morph: bool) -> bool {
    if kind == SEM_OTHER {
        true
    } else if a.is_matrix {
        false
    } else if kind == SEM_POSITION || kind == SEM_NORMAL {
        a.components == 3 && float32(a)
    } else if kind == SEM_TANGENT {
        a.components == (if morph { 3 } else { 4 }) && float32(a)
    } else if kind == SEM_TEXCOORD {
        a.components == 2 && (float32(a) || unorm8_16(a) || (morph && snorm8_16(a)))
    } else if kind == SEM_COLOR {
        (a.components == 3 || a.components == 4) && (float32(a) || unorm8_16(a) || (morph && snorm8_16(a)))
    } else if kind == SEM_JOINTS {
        !morph && a.components == 4 && !a.normalized && (a.component_type == 5121 || a.component_type == 5123)
    } else if kind == SEM_WEIGHTS {
        !morph && a.components == 4 && (float32(a) || unorm8_16(a))
    } else {
        false
    }
}

#[logic(open)]
pub fn has_sem(attrs: Seq<Attribute>, kind: Int, set: Int) -> bool {
    pearlite! { exists<i> 0 <= i && i < attrs.len() && semantic_spec(attrs[i].name@) == (kind, set) }
}

#[ensures(result == has_sem(attrs@, kind@, set@))]
#[check(terminates)]
pub(crate) fn has_semantic(attrs: &Vec<Attribute>, kind: u64, set: u64) -> bool {
    let mut i = 0;
    #[invariant(i@ <= attrs@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> semantic_spec(attrs@[k].name@) != (kind@, set@))]
    #[variant(attrs@.len() - i@)]
    while i < attrs.len() {
        let (k, n) = semantic(&attrs[i].name);
        if k == kind && n == set {
            return true;
        }
        i += 1;
    }
    false
}

#[logic(open)]
pub fn has_attr_name(attrs: Seq<Attribute>, name: Seq<u8>) -> bool {
    pearlite! { exists<j> 0 <= j && j < attrs.len() && attrs[j].name@ == name }
}

#[ensures(result == has_attr_name(attrs@, name@))]
#[check(terminates)]
fn has_name(attrs: &Vec<Attribute>, name: &Vec<u8>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= attrs@.len())]
    #[invariant(forall<j> 0 <= j && j < i@ ==> attrs@[j].name@ != name@)]
    #[variant(attrs@.len() - i@)]
    while i < attrs.len() {
        if bytes_eq(&attrs[i].name, name) {
            return true;
        }
        i += 1;
    }
    false
}

// M2: 属性集合 attrs の i 番目の属性の条件（morph はモーフターゲットの属性か、base はプリミティブの属性）
// MUST-057, MUST-063, MUST-066, MUST-088: 名前は有効で、POSITION は min / max が必要
// MUST-064, MUST-069, MUST-083, MUST-089, MUST-091: 番号に欠けがなく、要素数が等しく、モーフの名前は attributes にあり、JOINTS_n と WEIGHTS_n は対
#[logic(open)]
pub fn attr_spec(g: Gltf, attrs: Seq<Attribute>, i: Int, morph: bool, base: Seq<Attribute>, count: Int) -> bool {
    pearlite! {
        let sem = semantic_spec(attrs[i].name@);
        let acc = g.accessors@[attrs[i].accessor@];
        sem.0 != SEM_INVALID@
            && allowed_type(sem.0, acc, morph)
            && acc.count@ == count
            && (morph ==> has_attr_name(base, attrs[i].name@))
            && (sem.0 == SEM_POSITION@ ==> acc.min_len != None && acc.max_len != None)
            && (SEM_TEXCOORD@ <= sem.0 && sem.0 <= SEM_WEIGHTS@ && sem.1 > 0 ==> has_sem(attrs, sem.0, sem.1 - 1))
            && (sem.0 == SEM_JOINTS@ ==> has_sem(attrs, SEM_WEIGHTS@, sem.1))
            && (sem.0 == SEM_WEIGHTS@ ==> has_sem(attrs, SEM_JOINTS@, sem.1))
    }
}

// MUST-057, MUST-063, MUST-066, MUST-088: 名前は有効で、POSITION は min / max が必要
// MUST-064, MUST-069, MUST-083, MUST-089, MUST-091: 番号に欠けがなく、要素数が等しく、モーフの名前は attributes にあり、JOINTS_n と WEIGHTS_n は対
#[requires(i@ < attrs@.len())]
#[requires(attrs_lt(attrs@, g.accessors@.len()))]
#[ensures(result == attr_spec(*g, attrs@, i@, morph, base@, count@))]
#[check(terminates)]
fn attribute_ok(g: &Gltf, attrs: &Vec<Attribute>, i: usize, morph: bool, base: &Vec<Attribute>, count: u64) -> bool {
    let acc = &g.accessors[attrs[i].accessor as usize];
    let (kind, set) = semantic(&attrs[i].name);
    kind != SEM_INVALID
        && attribute_type_ok(kind, acc, morph)
        && acc.count == count
        && (!morph || has_name(base, &attrs[i].name))
        && (kind != SEM_POSITION || (acc.min_len.is_some() && acc.max_len.is_some()))
        && (kind < SEM_TEXCOORD || kind > SEM_WEIGHTS || set == 0 || has_semantic(attrs, kind, set - 1))
        && (kind != SEM_JOINTS || has_semantic(attrs, SEM_WEIGHTS, set))
        && (kind != SEM_WEIGHTS || has_semantic(attrs, SEM_JOINTS, set))
}

#[logic(open)]
pub fn attrs_spec(g: Gltf, attrs: Seq<Attribute>, morph: bool, base: Seq<Attribute>, count: Int) -> bool {
    pearlite! { forall<i> 0 <= i && i < attrs.len() ==> attr_spec(g, attrs, i, morph, base, count) }
}

#[requires(attrs_lt(attrs@, g.accessors@.len()))]
#[ensures(result == attrs_spec(*g, attrs@, morph, base@, count@))]
#[check(terminates)]
fn attributes_ok(g: &Gltf, attrs: &Vec<Attribute>, morph: bool, base: &Vec<Attribute>, count: u64) -> bool {
    let mut i = 0;
    #[invariant(i@ <= attrs@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> attr_spec(*g, attrs@, k, morph, base@, count@))]
    #[variant(attrs@.len() - i@)]
    while i < attrs.len() {
        if !attribute_ok(g, attrs, i, morph, base, count) {
            return false;
        }
        i += 1;
    }
    true
}

#[requires(primitive_refs(*g, *p))]
#[ensures(result == forall<t> 0 <= t && t < p.targets@.len() ==> attrs_spec(*g, p.targets@[t]@, true, p.attributes@, count@))]
#[check(terminates)]
fn targets_ok(g: &Gltf, p: &Primitive, count: u64) -> bool {
    let mut t = 0;
    #[invariant(t@ <= p.targets@.len())]
    #[invariant(forall<k> 0 <= k && k < t@ ==> attrs_spec(*g, p.targets@[k]@, true, p.attributes@, count@))]
    #[variant(p.targets@.len() - t@)]
    while t < p.targets.len() {
        if !attributes_ok(g, &p.targets[t], true, &p.attributes, count) {
            return false;
        }
        t += 1;
    }
    true
}

// targets を持つ最初のプリミティブ（k 番目以降で）の targets の数。なければ 0
#[logic(open)]
#[variant(ps.len() - k)]
pub fn first_targets(ps: Seq<Primitive>, k: Int) -> Int {
    pearlite! {
        if k < 0 || k >= ps.len() { 0 }
        else if ps[k].targets@.len() > 0 { ps[k].targets@.len() }
        else { first_targets(ps, k + 1) }
    }
}

#[logic(open)]
pub fn morph_count(m: Mesh) -> Int {
    pearlite! { first_targets(m.primitives@, 0) }
}

#[ensures(result@ == morph_count(*m))]
#[check(terminates)]
pub(crate) fn morph_target_count(m: &Mesh) -> u64 {
    let mut i = 0;
    #[invariant(i@ <= m.primitives@.len())]
    #[invariant(first_targets(m.primitives@, 0) == first_targets(m.primitives@, i@))]
    #[variant(m.primitives@.len() - i@)]
    while i < m.primitives.len() {
        if m.primitives[i].targets.len() > 0 {
            return m.primitives[i].targets.len() as u64;
        }
        i += 1;
    }
    0
}

// M4: モードごとの頂点数（モード 7 以上は supported で除かれる）
// MUST-075, MUST-076, MUST-077, MUST-078, MUST-079, MUST-080, MUST-081: モードごとの頂点数
#[logic(open)]
pub fn vertices_spec(mode: Int, n: Int) -> bool {
    pearlite! {
        n > 0 && (
            if mode == 0 { true }
            else if mode == 1 { n % 2 == 0 }
            else if mode == 2 || mode == 3 { n >= 2 }
            else if mode == 4 { n % 3 == 0 }
            else { n >= 3 }
        )
    }
}

// MUST-075, MUST-076, MUST-077, MUST-078, MUST-079, MUST-080, MUST-081: モードごとの頂点数
#[ensures(result == vertices_spec(mode@, n@))]
#[check(terminates)]
fn vertex_count_ok(mode: u64, n: u64) -> bool {
    if n == 0 {
        false
    } else if mode == 0 {
        true
    } else if mode == 1 {
        n % 2 == 0
    } else if mode == 2 || mode == 3 {
        n >= 2
    } else if mode == 4 {
        n % 3 == 0
    } else {
        n >= 3
    }
}

// M5
#[logic(open)]
pub fn texcoord_spec(t: Option<TextureInfo>, attrs: Seq<Attribute>) -> bool {
    pearlite! {
        match t {
            None => true,
            Some(ti) => has_sem(attrs, SEM_TEXCOORD@, ti.tex_coord@),
        }
    }
}

#[ensures(result == texcoord_spec(*t, attrs@))]
#[check(terminates)]
fn texcoord_ok(t: &Option<TextureInfo>, attrs: &Vec<Attribute>) -> bool {
    match t {
        None => true,
        Some(ti) => has_semantic(attrs, SEM_TEXCOORD, ti.tex_coord),
    }
}

// MUST-124: マテリアルのテクスチャに対応する TEXCOORD が必要
#[logic(open)]
pub fn material_texcoord_spec(m: Material, attrs: Seq<Attribute>) -> bool {
    pearlite! {
        texcoord_spec(m.base_color_texture, attrs) && texcoord_spec(m.metallic_roughness_texture, attrs)
            && texcoord_spec(m.normal_texture, attrs) && texcoord_spec(m.occlusion_texture, attrs)
            && texcoord_spec(m.emissive_texture, attrs)
    }
}

// MUST-124: マテリアルのテクスチャに対応する TEXCOORD が必要
#[ensures(result == material_texcoord_spec(*mat, attrs@))]
#[check(terminates)]
fn material_texcoords_ok(mat: &Material, attrs: &Vec<Attribute>) -> bool {
    texcoord_ok(&mat.base_color_texture, attrs) && texcoord_ok(&mat.metallic_roughness_texture, attrs) && texcoord_ok(&mat.normal_texture, attrs) && texcoord_ok(&mat.occlusion_texture, attrs) && texcoord_ok(&mat.emissive_texture, attrs)
}

// M3
// MUST-071: インデックスのアクセサーは SCALAR で符号なし整数
#[logic(open)]
pub fn index_spec(a: Accessor) -> bool {
    pearlite! {
        vec_n(a, 1) && !a.normalized && (a.component_type@ == 5121 || a.component_type@ == 5123 || a.component_type@ == 5125)
    }
}

// MUST-071: インデックスのアクセサーは SCALAR で符号なし整数
#[ensures(result == index_spec(*a))]
#[check(terminates)]
fn index_accessor_ok(a: &Accessor) -> bool {
    a.components == 1 && !a.is_matrix && !a.normalized && (a.component_type == 5121 || a.component_type == 5123 || a.component_type == 5125)
}

// count = 最初の属性の accessor の count
#[logic(open)]
pub fn prim_count(g: Gltf, p: Primitive) -> Int {
    pearlite! { g.accessors@[p.attributes@[0].accessor@].count@ }
}

#[logic(open)]
pub fn prim_vertices(g: Gltf, p: Primitive) -> Int {
    pearlite! {
        match p.indices {
            None => prim_count(g, p),
            Some(ix) => g.accessors@[ix@].count@,
        }
    }
}

// M1（targets の数）、M2〜M5 をプリミティブ p について
// MUST-084: メッシュ内のモーフターゲットの数は等しい
#[logic(open)]
pub fn primitive_spec(g: Gltf, p: Primitive, mc: Int) -> bool {
    pearlite! {
        (p.targets@.len() > 0 ==> p.targets@.len() == mc)
        && p.attributes@.len() > 0
        && attrs_spec(g, p.attributes@, false, p.attributes@, prim_count(g, p))
        && (forall<t> 0 <= t && t < p.targets@.len() ==> attrs_spec(g, p.targets@[t]@, true, p.attributes@, prim_count(g, p)))
        && (match p.indices { None => true, Some(ix) => index_spec(g.accessors@[ix@]) })
        && vertices_spec(p.mode@, prim_vertices(g, p))
        && (match p.material { None => true, Some(m) => material_texcoord_spec(g.materials@[m@], p.attributes@) })
    }
}

// MUST-084: メッシュ内のモーフターゲットの数は等しい
#[requires(primitive_refs(*g, *p))]
#[ensures(result == primitive_spec(*g, *p, targets@))]
#[check(terminates)]
fn primitive_ok(g: &Gltf, p: &Primitive, targets: u64) -> bool {
    if p.attributes.len() == 0 || (p.targets.len() > 0 && p.targets.len() as u64 != targets) {
        return false;
    }
    let count = g.accessors[p.attributes[0].accessor as usize].count;
    if !attributes_ok(g, &p.attributes, false, &p.attributes, count) || !targets_ok(g, p, count) {
        return false;
    }
    let vertices = match p.indices {
        None => count,
        Some(ix) => g.accessors[ix as usize].count,
    };
    let indices_ok = match p.indices {
        None => true,
        Some(ix) => index_accessor_ok(&g.accessors[ix as usize]),
    };
    let material_ok = match p.material {
        None => true,
        Some(m) => material_texcoords_ok(&g.materials[m as usize], &p.attributes),
    };
    indices_ok && vertex_count_ok(p.mode, vertices) && material_ok
}

#[requires(forall<j> 0 <= j && j < mesh.primitives@.len() ==> primitive_refs(*g, mesh.primitives@[j]))]
#[ensures(result == forall<j> 0 <= j && j < mesh.primitives@.len() ==> primitive_spec(*g, mesh.primitives@[j], targets@))]
#[check(terminates)]
fn primitives_ok(g: &Gltf, mesh: &Mesh, targets: u64) -> bool {
    let mut j = 0;
    #[invariant(j@ <= mesh.primitives@.len())]
    #[invariant(forall<k> 0 <= k && k < j@ ==> primitive_spec(*g, mesh.primitives@[k], targets@))]
    #[variant(mesh.primitives@.len() - j@)]
    while j < mesh.primitives.len() {
        if !primitive_ok(g, &mesh.primitives[j], targets) {
            return false;
        }
        j += 1;
    }
    true
}

// MUST-085: mesh.weights の長さ = モーフターゲットの数
#[logic(open)]
pub fn mesh_spec(g: Gltf, m: Mesh) -> bool {
    pearlite! {
        (match m.weights_len { None => true, Some(w) => w@ == morph_count(m) })
        && forall<j> 0 <= j && j < m.primitives@.len() ==> primitive_spec(g, m.primitives@[j], morph_count(m))
    }
}

// MUST-085: mesh.weights の長さ = モーフターゲットの数
#[requires(forall<j> 0 <= j && j < mesh.primitives@.len() ==> primitive_refs(*g, mesh.primitives@[j]))]
#[ensures(result == mesh_spec(*g, *mesh))]
#[check(terminates)]
fn mesh_ok(g: &Gltf, mesh: &Mesh) -> bool {
    let targets = morph_target_count(mesh);
    let weights_ok = match mesh.weights_len {
        None => true,
        Some(w) => w == targets,
    };
    weights_ok && primitives_ok(g, mesh, targets)
}

// M1〜M5
#[logic(open)]
pub fn meshes_spec(g: Gltf) -> bool {
    pearlite! { forall<i> 0 <= i && i < g.meshes@.len() ==> mesh_spec(g, g.meshes@[i]) }
}

#[requires(refs_ok(*g))]
#[ensures(result == meshes_spec(*g))]
#[check(terminates)]
pub(crate) fn meshes_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.meshes@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> mesh_spec(*g, g.meshes@[k]))]
    #[variant(g.meshes@.len() - i@)]
    while i < g.meshes.len() {
        if !mesh_ok(g, &g.meshes[i]) {
            return false;
        }
        i += 1;
    }
    true
}
