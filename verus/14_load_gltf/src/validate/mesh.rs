use crate::model::*;
use crate::validate::util::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::json::number::*;
#[cfg(verus_only)]
use crate::validate::refs::*;
#[cfg(verus_only)]
use crate::validate::support::*;

verus! {

pub const SEM_OTHER: u64 = 0;
pub const SEM_POSITION: u64 = 1;
pub const SEM_NORMAL: u64 = 2;
pub const SEM_TANGENT: u64 = 3;
pub const SEM_TEXCOORD: u64 = 4;
pub const SEM_COLOR: u64 = 5;
pub const SEM_JOINTS: u64 = 6;
pub const SEM_WEIGHTS: u64 = 7;
pub const SEM_INVALID: u64 = 8;

// 意味論（adoc 1626–1700）
pub open spec fn has_prefix(s: Seq<u8>, p: Seq<u8>) -> bool {
    p.len() <= s.len() && s.subrange(0, p.len() as int) == p
}

pub(crate) fn starts_with(s: &Vec<u8>, p: &[u8]) -> (r: bool)
    ensures
        r == has_prefix(s@, p@),
{
    if s.len() < p.len() {
        return false;
    }
    let mut i = 0;
    while i < p.len()
        invariant
            p.len() <= s.len(),
            0 <= i <= p.len(),
            forall|k: int| 0 <= k < i ==> s@[k] == p@[k],
        decreases p.len() - i,
    {
        if s[i] != p[i] {
            assert(s@.subrange(0, p.len() as int)[i as int] == s@[i as int]);
            return false;
        }
        i += 1;
    }
    assert(s@.subrange(0, p.len() as int) =~= p@);
    true
}

fn decimal_digits(s: &Vec<u8>, start: usize) -> (r: Option<u64>)
    requires
        start <= s.len(),
        s.len() - start <= 9,
    ensures
        r == (if forall|k: int| start <= k < s.len() ==> digit(#[trigger] s@[k]) {
            Some(digits_val(dec_digits(s@.subrange(start as int, s.len() as int))) as u64)
        } else {
            None::<u64>
        }),
{
    let mut v: u64 = 0;
    let mut i = start;
    proof {
        assert(dec_digits(s@.subrange(start as int, start as int)) =~= Seq::<u8>::empty());
    }
    while i < s.len()
        invariant
            start <= i <= s.len(),
            s.len() - start <= 9,
            forall|k: int| start <= k < i ==> digit(#[trigger] s@[k]),
            v as nat == digits_val(dec_digits(s@.subrange(start as int, i as int))),
            v < pow10((i - start) as nat),
        decreases s.len() - i,
    {
        if s[i] < b'0' || s[i] > b'9' {
            return None;
        }
        proof {
            let a = dec_digits(s@.subrange(start as int, i as int));
            let b = dec_digits(s@.subrange(start as int, i + 1));
            assert(b.drop_last() =~= a);
            assert(b.last() == s@[i as int] - b'0');
            lemma_pow10_le_1e9((i + 1 - start) as nat);
            assert(pow10((i + 1 - start) as nat) == 10 * pow10((i - start) as nat));
        }
        v = v * 10 + (s[i] - b'0') as u64;
        i += 1;
    }
    Some(v)
}

// 1–9 桁の 10 進数（先頭 0 は "0" のみ）
// MUST-060, MUST-061, MUST-062: 集合の番号は先頭に 0 のない 9 桁以下の 10 進整数
pub open spec fn set_index(s: Seq<u8>) -> Option<u64> {
    if 1 <= s.len() <= 9 && (forall|k: int| 0 <= k < s.len() ==> digit(#[trigger] s[k])) && (s[0] != b'0' || s.len()
        == 1) {
        Some(digits_val(dec_digits(s)) as u64)
    } else {
        None
    }
}

// MUST-060, MUST-061, MUST-062: 集合の番号は先頭に 0 のない 9 桁以下の 10 進整数
fn parse_set_index(s: &Vec<u8>, start: usize) -> (r: Option<u64>)
    requires
        start <= s.len(),
    ensures
        r == set_index(s@.subrange(start as int, s.len() as int)),
{
    let ghost t = s@.subrange(start as int, s.len() as int);
    proof {
        assert forall|k: int| start <= k < s.len() implies s@[k] == t[k - start] by {}
        if forall|k: int| start <= k < s.len() ==> digit(#[trigger] s@[k]) {
            assert forall|k: int| 0 <= k < t.len() implies digit(#[trigger] t[k]) by {
                assert(digit(s@[k + start]));
            }
        }
        if forall|k: int| 0 <= k < t.len() ==> digit(#[trigger] t[k]) {
            assert forall|k: int| start <= k < s.len() implies digit(#[trigger] s@[k]) by {
                assert(digit(t[k - start]));
            }
        }
    }
    let n = s.len() - start;
    if n == 0 || n > 9 || (s[start] == b'0' && n > 1) {
        None
    } else {
        decimal_digits(s, start)
    }
}

pub open spec fn indexed_semantic(name: Seq<u8>, kind: u64, plen: int) -> (u64, u64) {
    match set_index(name.subrange(plen, name.len() as int)) {
        Some(n) => (kind, n),
        None => (SEM_INVALID, 0),
    }
}

// MUST-063: TEXCOORD_ などの後ろが正しい番号でなければ SEM_INVALID
pub open spec fn semantic_s(name: Seq<u8>) -> (u64, u64) {
    if name == seq![b'P', b'O', b'S', b'I', b'T', b'I', b'O', b'N'] {
        (SEM_POSITION, 0)
    } else if name == seq![b'N', b'O', b'R', b'M', b'A', b'L'] {
        (SEM_NORMAL, 0)
    } else if name == seq![b'T', b'A', b'N', b'G', b'E', b'N', b'T'] {
        (SEM_TANGENT, 0)
    } else if has_prefix(name, seq![b'T', b'E', b'X', b'C', b'O', b'O', b'R', b'D', b'_']) {
        indexed_semantic(name, SEM_TEXCOORD, 9)
    } else if has_prefix(name, seq![b'C', b'O', b'L', b'O', b'R', b'_']) {
        indexed_semantic(name, SEM_COLOR, 6)
    } else if has_prefix(name, seq![b'J', b'O', b'I', b'N', b'T', b'S', b'_']) {
        indexed_semantic(name, SEM_JOINTS, 7)
    } else if has_prefix(name, seq![b'W', b'E', b'I', b'G', b'H', b'T', b'S', b'_']) {
        indexed_semantic(name, SEM_WEIGHTS, 8)
    } else {
        (SEM_OTHER, 0)
    }
}

// MUST-063: TEXCOORD_ などの後ろが正しい番号でなければ SEM_INVALID
pub fn semantic(name: &Vec<u8>) -> (r: (u64, u64))
    ensures
        r == semantic_s(name@),
{
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

// adoc 1645 / 1922 の表
// MUST-059, MUST-086: 属性・モーフターゲットの属性の型の表
pub open spec fn attr_type_s(kind: u64, a: Accessor, morph: bool) -> bool {
    if kind == SEM_OTHER {
        true
    } else if kind == SEM_POSITION || kind == SEM_NORMAL {
        !a.is_matrix && a.components == 3 && f32_s(a)
    } else if kind == SEM_TANGENT {
        !a.is_matrix && (if morph { a.components == 3 } else { a.components == 4 }) && f32_s(a)
    } else if kind == SEM_TEXCOORD {
        !a.is_matrix && a.components == 2 && (f32_s(a) || unorm_s(a) || (morph && snorm_s(a)))
    } else if kind == SEM_COLOR {
        !a.is_matrix && (a.components == 3 || a.components == 4) && (f32_s(a) || unorm_s(a) || (morph && snorm_s(a)))
    } else if kind == SEM_JOINTS {
        !morph && !a.is_matrix && a.components == 4 && !a.normalized && (a.component_type == 5121 || a.component_type
            == 5123)
    } else if kind == SEM_WEIGHTS {
        !morph && !a.is_matrix && a.components == 4 && (f32_s(a) || unorm_s(a))
    } else {
        false
    }
}

// MUST-059, MUST-086: 属性・モーフターゲットの属性の型の表
fn attribute_type_ok(kind: u64, a: &Accessor, morph: bool) -> (r: bool)
    ensures
        r == attr_type_s(kind, *a, morph),
{
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

pub open spec fn has_sem(attrs: Seq<AttributeS>, kind: u64, set: u64) -> bool {
    exists|k: int| 0 <= k < attrs.len() && #[trigger] semantic_s(attrs[k].name) == (kind, set)
}

pub(crate) fn has_semantic(attrs: &Vec<Attribute>, kind: u64, set: u64) -> (r: bool)
    ensures
        r == has_sem(attrs_view(attrs@), kind, set),
{
    let mut i = 0;
    while i < attrs.len()
        invariant
            0 <= i <= attrs.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] semantic_s(attrs_view(attrs@)[k].name) != (kind, set),
        decreases attrs.len() - i,
    {
        proof {
            assert(attrs_view(attrs@)[i as int].name == attrs@[i as int].name@);
        }
        let (k, n) = semantic(&attrs[i].name);
        if k == kind && n == set {
            return true;
        }
        i += 1;
    }
    false
}

fn has_name(attrs: &Vec<Attribute>, name: &Vec<u8>) -> (r: bool)
    ensures
        r == exists|j: int| 0 <= j < attrs.len() && #[trigger] attrs_view(attrs@)[j].name == name@,
{
    let mut i = 0;
    while i < attrs.len()
        invariant
            0 <= i <= attrs.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] attrs_view(attrs@)[k].name != name@,
        decreases attrs.len() - i,
    {
        proof {
            assert(attrs_view(attrs@)[i as int].name == attrs@[i as int].name@);
        }
        if bytes_eq(&attrs[i].name, name) {
            return true;
        }
        i += 1;
    }
    false
}

// M2 の属性 1 つ分の条件（attrs は属性集合、base はプリミティブの attributes）
pub open spec fn attr_rule(g: GltfS, attrs: Seq<AttributeS>, k: int, morph: bool, base: Seq<AttributeS>, count: u64) -> bool {
    let acc = g.accessors[attrs[k].accessor as int];
    let (kind, set) = semantic_s(attrs[k].name);
    // MUST-063: TEXCOORD_ などの後ろは正しい番号
    &&& kind != SEM_INVALID
    &&& attr_type_s(kind, acc, morph)
    // MUST-069, MUST-089: 属性・モーフターゲットの要素数は等しい
    &&& acc.count == count
    // MUST-083: モーフターゲットの名前は attributes にある
    &&& (morph ==> exists|j: int| 0 <= j < base.len() && #[trigger] base[j].name == attrs[k].name)
    // MUST-057, MUST-066, MUST-088: POSITION は min / max が必要
    &&& (kind == SEM_POSITION ==> acc.min_len is Some && acc.max_len is Some)
    // MUST-064: 集合の番号に欠けがない
    &&& (SEM_TEXCOORD <= kind <= SEM_WEIGHTS && set > 0 ==> has_sem(attrs, kind, (set - 1) as u64))
    // MUST-091: JOINTS_n と WEIGHTS_n は対で存在
    &&& (kind == SEM_JOINTS ==> has_sem(attrs, SEM_WEIGHTS, set))
    &&& (kind == SEM_WEIGHTS ==> has_sem(attrs, SEM_JOINTS, set))
}

// MUST-057, MUST-063, MUST-064, MUST-066, MUST-069, MUST-083, MUST-088, MUST-089, MUST-091: 属性 1 つ分の規則
fn attribute_ok(g: &Gltf, attrs: &Vec<Attribute>, i: usize, morph: bool, base: &Vec<Attribute>, count: u64) -> (r: bool)
    requires
        i < attrs.len(),
        attrs@[i as int].accessor < g.accessors.len(),
    ensures
        r == attr_rule(g@, attrs_view(attrs@), i as int, morph, attrs_view(base@), count),
{
    proof {
        assert(attrs_view(attrs@)[i as int] == attrs@[i as int]@);
    }
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

pub open spec fn attrs_rule(g: GltfS, attrs: Seq<AttributeS>, morph: bool, base: Seq<AttributeS>, count: u64) -> bool {
    forall|k: int| 0 <= k < attrs.len() ==> #[trigger] attr_rule(g, attrs, k, morph, base, count)
}

fn attributes_ok(g: &Gltf, attrs: &Vec<Attribute>, morph: bool, base: &Vec<Attribute>, count: u64) -> (r: bool)
    requires
        forall|k: int| 0 <= k < attrs.len() ==> #[trigger] attrs@[k].accessor < g.accessors.len(),
    ensures
        r == attrs_rule(g@, attrs_view(attrs@), morph, attrs_view(base@), count),
{
    let mut i = 0;
    while i < attrs.len()
        invariant
            forall|k: int| 0 <= k < attrs.len() ==> #[trigger] attrs@[k].accessor < g.accessors.len(),
            0 <= i <= attrs.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] attr_rule(g@, attrs_view(attrs@), k, morph, attrs_view(base@), count),
        decreases attrs.len() - i,
    {
        if !attribute_ok(g, attrs, i, morph, base, count) {
            return false;
        }
        i += 1;
    }
    true
}

fn targets_ok(g: &Gltf, p: &Primitive, count: u64) -> (r: bool)
    requires
        prim_refs_s(g@, p@),
    ensures
        r == (forall|t: int| 0 <= t < p@.targets.len() ==> attrs_rule(g@, #[trigger] p@.targets[t], true, p@.attributes, count)),
{
    let mut t = 0;
    while t < p.targets.len()
        invariant
            prim_refs_s(g@, p@),
            0 <= t <= p.targets.len(),
            forall|x: int| 0 <= x < t ==> attrs_rule(g@, #[trigger] p@.targets[x], true, p@.attributes, count),
        decreases p.targets.len() - t,
    {
        proof {
            assert(p@.targets[t as int] == attrs_view(p.targets@[t as int]@));
            assert forall|k: int| 0 <= k < p.targets@[t as int].len() implies #[trigger] p.targets@[t as int]@[k].accessor
                < g.accessors.len() by {
                assert(p@.targets[t as int][k].accessor == p.targets@[t as int]@[k].accessor);
            }
        }
        if !attributes_ok(g, &p.targets[t], true, &p.attributes, count) {
            return false;
        }
        t += 1;
    }
    true
}

// M1: 最初に targets を持つプリミティブの targets の数、なければ 0
pub open spec fn first_targets_at(mesh: MeshS, p: int) -> bool {
    0 <= p < mesh.primitives.len() && mesh.primitives[p].targets.len() > 0 && forall|q: int|
        0 <= q < p ==> #[trigger] mesh.primitives[q].targets.len() == 0
}

pub open spec fn morph_count(mesh: MeshS) -> nat {
    if exists|p: int| 0 <= p < mesh.primitives.len() && #[trigger] mesh.primitives[p].targets.len() > 0 {
        let p = choose|p: int| first_targets_at(mesh, p);
        mesh.primitives[p].targets.len()
    } else {
        0
    }
}

pub proof fn lemma_first_targets(mesh: MeshS, p: int)
    requires
        first_targets_at(mesh, p),
    ensures
        morph_count(mesh) == mesh.primitives[p].targets.len(),
{
    let q = choose|q: int| first_targets_at(mesh, q);
    assert(first_targets_at(mesh, q));
    if q < p {
        assert(mesh.primitives[q].targets.len() == 0);
    } else if p < q {
        assert(mesh.primitives[p].targets.len() == 0);
    }
}

pub(crate) fn morph_target_count(m: &Mesh) -> (r: u64)
    ensures
        r == morph_count(m@),
{
    let mut i = 0;
    while i < m.primitives.len()
        invariant
            0 <= i <= m.primitives.len(),
            forall|q: int| 0 <= q < i ==> #[trigger] m@.primitives[q].targets.len() == 0,
        decreases m.primitives.len() - i,
    {
        proof {
            assert(m@.primitives[i as int].targets.len() == m.primitives@[i as int].targets.len());
        }
        if m.primitives[i].targets.len() > 0 {
            proof {
                assert(first_targets_at(m@, i as int));
                lemma_first_targets(m@, i as int);
            }
            return m.primitives[i].targets.len() as u64;
        }
        i += 1;
    }
    0
}

// MUST-075, MUST-076, MUST-077, MUST-078, MUST-079, MUST-080, MUST-081: 頂点数の規則
pub open spec fn vertex_count_s(mode: u64, n: u64) -> bool {
    &&& n > 0
    &&& mode == 1 ==> n % 2 == 0
    &&& (mode == 2 || mode == 3) ==> n >= 2
    &&& mode == 4 ==> n % 3 == 0
    &&& (mode == 5 || mode == 6) ==> n >= 3
}

// MUST-075, MUST-076, MUST-077, MUST-078, MUST-079, MUST-080, MUST-081: 頂点数の規則
fn vertex_count_ok(mode: u64, n: u64) -> (r: bool)
    requires
        mode <= 6,
    ensures
        r == vertex_count_s(mode, n),
{
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

pub open spec fn texcoord_s(t: Option<TextureInfo>, attrs: Seq<AttributeS>) -> bool {
    t matches Some(ti) ==> has_sem(attrs, SEM_TEXCOORD, ti.tex_coord)
}

fn texcoord_ok(t: &Option<TextureInfo>, attrs: &Vec<Attribute>) -> (r: bool)
    ensures
        r == texcoord_s(*t, attrs_view(attrs@)),
{
    match t {
        None => true,
        Some(ti) => has_semantic(attrs, SEM_TEXCOORD, ti.tex_coord),
    }
}

// MUST-124: テクスチャが使う TEXCOORD が必要
pub open spec fn material_texcoords_s(mt: Material, attrs: Seq<AttributeS>) -> bool {
    &&& texcoord_s(mt.base_color_texture, attrs)
    &&& texcoord_s(mt.metallic_roughness_texture, attrs)
    &&& texcoord_s(mt.normal_texture, attrs)
    &&& texcoord_s(mt.occlusion_texture, attrs)
    &&& texcoord_s(mt.emissive_texture, attrs)
}

// MUST-124: テクスチャが使う TEXCOORD が必要
fn material_texcoords_ok(mat: &Material, attrs: &Vec<Attribute>) -> (r: bool)
    ensures
        r == material_texcoords_s(*mat, attrs_view(attrs@)),
{
    texcoord_ok(&mat.base_color_texture, attrs) && texcoord_ok(&mat.metallic_roughness_texture, attrs) && texcoord_ok(&mat.normal_texture, attrs) && texcoord_ok(&mat.occlusion_texture, attrs) && texcoord_ok(&mat.emissive_texture, attrs)
}

// MUST-071: インデックスのアクセサーは SCALAR の符号なし整数
pub open spec fn index_accessor_s(a: Accessor) -> bool {
    a.components == 1 && !a.is_matrix && !a.normalized && (a.component_type == 5121 || a.component_type == 5123
        || a.component_type == 5125)
}

// MUST-071: インデックスのアクセサーは SCALAR の符号なし整数
fn index_accessor_ok(a: &Accessor) -> (r: bool)
    ensures
        r == index_accessor_s(*a),
{
    a.components == 1 && !a.is_matrix && !a.normalized && (a.component_type == 5121 || a.component_type == 5123 || a.component_type == 5125)
}

// M2–M5（1 プリミティブ分）
pub open spec fn prim_rules(g: GltfS, p: PrimitiveS) -> bool {
    &&& p.attributes.len() > 0
    &&& ({
        let count = g.accessors[p.attributes[0].accessor as int].count;
        &&& attrs_rule(g, p.attributes, false, p.attributes, count)
        &&& forall|t: int| 0 <= t < p.targets.len() ==> attrs_rule(g, #[trigger] p.targets[t], true, p.attributes, count)
        &&& (p.indices matches Some(i) ==> index_accessor_s(g.accessors[i as int]))
        &&& vertex_count_s(
            p.mode,
            match p.indices {
                Some(i) => g.accessors[i as int].count,
                None => count,
            },
        )
        &&& (p.material matches Some(m) ==> material_texcoords_s(g.materials[m as int], p.attributes))
    })
}pub open spec fn prim_full_rule(g: GltfS, p: PrimitiveS, targets: int) -> bool {
    (p.targets.len() > 0 ==> p.targets.len() == targets) && prim_rules(g, p)
}

// MUST-084: モーフターゲットの数はメッシュ内で等しい
fn primitive_ok(g: &Gltf, p: &Primitive, targets: u64) -> (r: bool)
    requires
        prim_refs_s(g@, p@),
        p.mode <= 6,
    ensures
        r == prim_full_rule(g@, p@, targets as int),
{
    proof {
        assert forall|k: int| 0 <= k < p.attributes.len() implies #[trigger] p.attributes@[k].accessor < g.accessors.len() by {
            assert(p@.attributes[k].accessor == p.attributes@[k].accessor);
        }
        if p.attributes.len() > 0 {
            assert(p@.attributes[0].accessor == p.attributes@[0].accessor);
        }
    }
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

fn primitives_ok(g: &Gltf, mesh: &Mesh, targets: u64) -> (r: bool)
    requires
        forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] prim_refs_s(g@, mesh@.primitives[p]),
        forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] mesh@.primitives[p].mode <= 6,
    ensures
        r == (forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] prim_full_rule(g@, mesh@.primitives[p], targets as int)),
{
    let mut j = 0;
    while j < mesh.primitives.len()
        invariant
            forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] prim_refs_s(g@, mesh@.primitives[p]),
            forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] mesh@.primitives[p].mode <= 6,
            0 <= j <= mesh.primitives.len(),
            forall|p: int| 0 <= p < j ==> #[trigger] prim_full_rule(g@, mesh@.primitives[p], targets as int),
        decreases mesh.primitives.len() - j,
    {
        proof {
            assert(mesh@.primitives[j as int] == mesh.primitives@[j as int]@);
            assert(mesh@.primitives[j as int].mode == mesh.primitives@[j as int].mode);
        }
        if !primitive_ok(g, &mesh.primitives[j], targets) {
            return false;
        }
        j += 1;
    }
    true
}pub open spec fn mesh_rule(g: GltfS, mesh: MeshS) -> bool {
    &&& (mesh.weights_len matches Some(w) ==> w == morph_count(mesh))
    &&& forall|p: int| 0 <= p < mesh.primitives.len() ==> #[trigger] prim_full_rule(g, mesh.primitives[p], morph_count(mesh) as int)
}

// MUST-084, MUST-085: モーフターゲットの数は等しく、mesh.weights の長さと一致
fn mesh_ok(g: &Gltf, mesh: &Mesh) -> (r: bool)
    requires
        forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] prim_refs_s(g@, mesh@.primitives[p]),
        forall|p: int| 0 <= p < mesh@.primitives.len() ==> #[trigger] mesh@.primitives[p].mode <= 6,
    ensures
        r == mesh_rule(g@, mesh@),
{
    let targets = morph_target_count(mesh);
    let weights_ok = match mesh.weights_len {
        None => true,
        Some(w) => w == targets,
    };
    weights_ok && primitives_ok(g, mesh, targets)
}

// MUST-084, MUST-085: モーフターゲットの数は等しく、mesh.weights の長さと一致
pub open spec fn m1(g: GltfS) -> bool {
    forall|m: int|
        0 <= m < g.meshes.len() ==> {
            &&& forall|p: int|
                0 <= p < g.meshes[m].primitives.len() && #[trigger] prim(g, m, p).targets.len() > 0 ==> prim(
                    g,
                    m,
                    p,
                ).targets.len() == morph_count(g.meshes[m])
            &&& (#[trigger] g.meshes[m].weights_len matches Some(w) ==> w == morph_count(g.meshes[m]))
        }
}

pub open spec fn meshes_rules(g: GltfS) -> bool {
    &&& m1(g)
    &&& forall|m: int, p: int|
        0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() ==> prim_rules(g, #[trigger] prim(g, m, p))
}

pub proof fn lemma_meshes_rules(g: GltfS)
    ensures
        meshes_rules(g) == (forall|m: int| 0 <= m < g.meshes.len() ==> #[trigger] mesh_rule(g, g.meshes[m])),
{
    if meshes_rules(g) {
        assert forall|m: int| 0 <= m < g.meshes.len() implies #[trigger] mesh_rule(g, g.meshes[m]) by {
            assert(g.meshes[m].weights_len matches Some(w) ==> w == morph_count(g.meshes[m]));
            assert forall|p: int| 0 <= p < g.meshes[m].primitives.len() implies #[trigger] prim_full_rule(g, g.meshes[m].primitives[p], morph_count(g.meshes[m]) as int) by {
                assert(prim_rules(g, prim(g, m, p)));
                if prim(g, m, p).targets.len() > 0 {
                    assert(prim(g, m, p).targets.len() == morph_count(g.meshes[m]));
                }
            }
        }
    }
    if forall|m: int| 0 <= m < g.meshes.len() ==> #[trigger] mesh_rule(g, g.meshes[m]) {
        assert forall|m: int| 0 <= m < g.meshes.len() implies {
            &&& forall|p: int|
                0 <= p < g.meshes[m].primitives.len() && #[trigger] prim(g, m, p).targets.len() > 0 ==> prim(
                    g,
                    m,
                    p,
                ).targets.len() == morph_count(g.meshes[m])
            &&& (#[trigger] g.meshes[m].weights_len matches Some(w) ==> w == morph_count(g.meshes[m]))
        } by {
            assert(mesh_rule(g, g.meshes[m]));
            assert forall|p: int| 0 <= p < g.meshes[m].primitives.len() && #[trigger] prim(g, m, p).targets.len() > 0 implies prim(
                g,
                m,
                p,
            ).targets.len() == morph_count(g.meshes[m]) by {
                assert(prim_full_rule(g, g.meshes[m].primitives[p], morph_count(g.meshes[m]) as int));
            }
        }
        assert forall|m: int, p: int|
            0 <= m < g.meshes.len() && 0 <= p < g.meshes[m].primitives.len() implies prim_rules(g, #[trigger] prim(g, m, p)) by {
            assert(mesh_rule(g, g.meshes[m]));
            assert(prim_full_rule(g, g.meshes[m].primitives[p], morph_count(g.meshes[m]) as int));
        }
    }
}

// M1–M5
pub(crate) fn meshes_ok(g: &Gltf) -> (r: bool)
    requires
        refs_ok(g@),
        supported_s(g@),
    ensures
        r == meshes_rules(g@),
{
    proof {
        lemma_refs_ok_split(g@);
        lemma_meshes_rules(g@);
    }
    let mut i = 0;
    while i < g.meshes.len()
        invariant
            refs_ok(g@),
            supported_s(g@),
            forall|m: int, p: int|
                0 <= m < g@.meshes.len() && 0 <= p < g@.meshes[m].primitives.len() ==> #[trigger] prim_refs_s(
                    g@,
                    g@.meshes[m].primitives[p],
                ),
            0 <= i <= g.meshes.len(),
            forall|m: int| 0 <= m < i ==> #[trigger] mesh_rule(g@, g@.meshes[m]),
        decreases g.meshes.len() - i,
    {
        proof {
            assert(g@.meshes[i as int] == g.meshes@[i as int]@);
            assert forall|p: int| 0 <= p < g@.meshes[i as int].primitives.len() implies #[trigger] g@.meshes[i as int].primitives[p].mode <= 6 by {
                assert(prim(g@, i as int, p).mode <= 6);
            }
        }
        if !mesh_ok(g, &g.meshes[i]) {
            proof {
                lemma_meshes_rules(g@);
            }
            assert(!mesh_rule(g@, g@.meshes[i as int]));
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
