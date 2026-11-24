use crate::json::*;
use crate::json::number::*;
use crate::model::*;
use crate::read::access::*;
use vstd::prelude::*;

verus! {

// 読み取り結果が仕様の値と一致し、ext に仕様の拡張名が追加された
pub open spec fn got<T>(s: Option<(T, Ext)>, v: T, a: Seq<Vec<u8>>, b: Seq<Vec<u8>>) -> bool {
    s matches Some((x, e)) && x == v && ext_grow(a, b, e)
}

pub open spec fn extra_key(extra: u64) -> Option<Seq<u8>> {
    if extra == 1 {
        Some(seq![b's', b'c', b'a', b'l', b'e'])
    } else if extra == 2 {
        Some(seq![b's', b't', b'r', b'e', b'n', b'g', b't', b'h'])
    } else {
        None
    }
}

pub open spec fn uint_or_s(o: Ms, k: Seq<u8>, dflt: u64) -> Option<u64> {
    match get_uint_s(o, k) {
        Some(Some(x)) => Some(x),
        Some(None) => Some(dflt),
        None => None,
    }
}

// textureInfo（extra は normalTexture の scale / occlusionTexture の strength）
pub open spec fn texture_info_s(v: JsonS, extra: Option<Seq<u8>>) -> Option<(TextureInfo, Ext)> {
    match v {
        JsonS::Object(o) => {
            let e = ext_s(o);
            let index = req_uint_s(o, seq![b'i', b'n', b'd', b'e', b'x']);
            let tc = uint_or_s(o, seq![b't', b'e', b'x', b'C', b'o', b'o', b'r', b'd'], 0);
            let x = match extra {
                None => true,
                Some(k) => check_number_s(o, k) is Some,
            };
            if e is Some && index is Some && tc is Some && x {
                Some((TextureInfo { index: index->Some_0, tex_coord: tc->Some_0 }, e->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

fn read_texture_info(d: &Vec<JsonNode>, id: usize, extra: u64, ext: &mut Vec<Vec<u8>>) -> (r: Result<TextureInfo, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(texture_info_s(tree(d@, id as int), extra_key(extra)), x, old(ext)@, final(ext)@),
            Err(_) => texture_info_s(tree(d@, id as int), extra_key(extra)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let index = match req_uint(d, o, &[b'i', b'n', b'd', b'e', b'x']) { Ok(v) => v, Err(()) => return Err(()) };
    let tex_coord = match get_uint(d, o, &[b't', b'e', b'x', b'C', b'o', b'o', b'r', b'd']) {
        Ok(Some(v)) => v,
        Ok(None) => 0,
        Err(()) => return Err(()),
    };
    if extra == 1 {
        match check_number(d, o, &[b's', b'c', b'a', b'l', b'e']) { Err(()) => return Err(()), Ok(_) => {} }
    } else if extra == 2 {
        match check_number(d, o, &[b's', b't', b'r', b'e', b'n', b'g', b't', b'h']) { Err(()) => return Err(()), Ok(_) => {} }
    }
    Ok(TextureInfo { index, tex_coord })
}

pub proof fn lemma_ext_refl(a: Seq<Vec<u8>>)
    ensures
        ext_grow(a, a, ISet::empty()),
{
}

pub open spec fn opt_texture_info_s(o: Ms, k: Seq<u8>, extra: Option<Seq<u8>>) -> Option<(Option<TextureInfo>, Ext)> {
    match lookup(o, k) {
        None => Some((None, ISet::empty())),
        Some(v) => match texture_info_s(v, extra) {
            Some((t, e)) => Some((Some(t), e)),
            None => None,
        },
    }
}

fn opt_texture_info(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8], extra: u64, ext: &mut Vec<Vec<u8>>) -> (r: Result<Option<TextureInfo>, ()>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(x) => got(opt_texture_info_s(mt(d@, o@), key@, extra_key(extra)), x, old(ext)@, final(ext)@),
            Err(_) => opt_texture_info_s(mt(d@, o@), key@, extra_key(extra)) is None,
        },
{
    proof {
        lemma_lookup(d@, o@, key@);
        lemma_ext_refl(ext@);
    }
    match find_member(o, key) {
        None => Ok(None),
        Some(i) => match read_texture_info(d, o[i].value, extra, ext) {
            Ok(t) => Ok(Some(t)),
            Err(()) => Err(()),
        },
    }
}

pub open spec fn pbr_s(o: Ms) -> Option<(Option<TextureInfo>, Option<TextureInfo>, Ext)> {
    match get_object_s(o, seq![b'p', b'b', b'r', b'M', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'R', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's']) {
        None => None,
        Some(None) => Some((None, None, ISet::empty())),
        Some(Some(p)) => {
            let e = ext_s(p);
            let bcf = check_number_array_s(p, seq![b'b', b'a', b's', b'e', b'C', b'o', b'l', b'o', b'r', b'F', b'a', b'c', b't', b'o', b'r'], 4);
            let mf = check_number_s(p, seq![b'm', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'F', b'a', b'c', b't', b'o', b'r']);
            let rf = check_number_s(p, seq![b'r', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's', b'F', b'a', b'c', b't', b'o', b'r']);
            let bct = opt_texture_info_s(p, seq![b'b', b'a', b's', b'e', b'C', b'o', b'l', b'o', b'r', b'T', b'e', b'x', b't', b'u', b'r', b'e'], None);
            let mrt = opt_texture_info_s(p, seq![b'm', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'R', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's', b'T', b'e', b'x', b't', b'u', b'r', b'e'], None);
            if e is Some && bcf is Some && mf is Some && rf is Some && bct is Some && mrt is Some {
                Some((bct->Some_0.0, mrt->Some_0.0, e->Some_0.union(bct->Some_0.1).union(mrt->Some_0.1)))
            } else {
                None
            }
        },
    }
}

pub open spec fn material_s(v: JsonS) -> Option<(Material, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let pbr = pbr_s(o);
            let nt = opt_texture_info_s(o, seq![b'n', b'o', b'r', b'm', b'a', b'l', b'T', b'e', b'x', b't', b'u', b'r', b'e'], Some(seq![b's', b'c', b'a', b'l', b'e']));
            let ot = opt_texture_info_s(o, seq![b'o', b'c', b'c', b'l', b'u', b's', b'i', b'o', b'n', b'T', b'e', b'x', b't', b'u', b'r', b'e'], Some(seq![b's', b't', b'r', b'e', b'n', b'g', b't', b'h']));
            let et = opt_texture_info_s(o, seq![b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'T', b'e', b'x', b't', b'u', b'r', b'e'], None);
            let ef = check_number_array_s(o, seq![b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'F', b'a', b'c', b't', b'o', b'r'], 3);
            let am = get_string_s(o, seq![b'a', b'l', b'p', b'h', b'a', b'M', b'o', b'd', b'e']);
            let ac = check_number_s(o, seq![b'a', b'l', b'p', b'h', b'a', b'C', b'u', b't', b'o', b'f', b'f']);
            let ds = get_bool_s(o, seq![b'd', b'o', b'u', b'b', b'l', b'e', b'S', b'i', b'd', b'e', b'd']);
            if c is Some && pbr is Some && nt is Some && ot is Some && et is Some && ef is Some && am is Some && ac is Some && ds is Some {
                Some((
                    Material {
                        base_color_texture: pbr->Some_0.0,
                        metallic_roughness_texture: pbr->Some_0.1,
                        normal_texture: nt->Some_0.0,
                        occlusion_texture: ot->Some_0.0,
                        emissive_texture: et->Some_0.0,
                    },
                    c->Some_0.union(pbr->Some_0.2).union(nt->Some_0.1).union(ot->Some_0.1).union(et->Some_0.1),
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_material(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Material, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(material_s(tree(d@, id as int)), x, old(ext)@, final(ext)@),
            Err(_) => material_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let mut base_color_texture: Option<TextureInfo> = None;
    let mut metallic_roughness_texture: Option<TextureInfo> = None;
    match get_object(d, o, &[b'p', b'b', b'r', b'M', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'R', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's']) {
        Err(()) => return Err(()),
        Ok(None) => {}
        Ok(Some(p)) => {
            match check_extensions(d, p, ext) { Err(()) => return Err(()), Ok(()) => {} }
            match check_number_array(d, p, &[b'b', b'a', b's', b'e', b'C', b'o', b'l', b'o', b'r', b'F', b'a', b'c', b't', b'o', b'r'], 4) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'm', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'F', b'a', b'c', b't', b'o', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'r', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's', b'F', b'a', b'c', b't', b'o', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
            base_color_texture = match opt_texture_info(d, p, &[b'b', b'a', b's', b'e', b'C', b'o', b'l', b'o', b'r', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
            metallic_roughness_texture = match opt_texture_info(d, p, &[b'm', b'e', b't', b'a', b'l', b'l', b'i', b'c', b'R', b'o', b'u', b'g', b'h', b'n', b'e', b's', b's', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
        }
    }
    let normal_texture = match opt_texture_info(d, o, &[b'n', b'o', b'r', b'm', b'a', b'l', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 1, ext) { Ok(t) => t, Err(()) => return Err(()) };
    let occlusion_texture = match opt_texture_info(d, o, &[b'o', b'c', b'c', b'l', b'u', b's', b'i', b'o', b'n', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 2, ext) { Ok(t) => t, Err(()) => return Err(()) };
    let emissive_texture = match opt_texture_info(d, o, &[b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
    match check_number_array(d, o, &[b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'F', b'a', b'c', b't', b'o', b'r'], 3) { Err(()) => return Err(()), Ok(_) => {} }
    match get_string(d, o, &[b'a', b'l', b'p', b'h', b'a', b'M', b'o', b'd', b'e']) { Err(()) => return Err(()), Ok(_) => {} }
    match check_number(d, o, &[b'a', b'l', b'p', b'h', b'a', b'C', b'u', b't', b'o', b'f', b'f']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_bool(d, o, &[b'd', b'o', b'u', b'b', b'l', b'e', b'S', b'i', b'd', b'e', b'd']) { Err(()) => return Err(()), Ok(_) => {} }
    proof {
        lemma_ext_refl(ext@);
    }
    Ok(Material { base_color_texture, metallic_roughness_texture, normal_texture, occlusion_texture, emissive_texture })
}

pub proof fn lemma_filter_step(m: Ms, i: int)
    requires
        0 <= i,
    ensures
        idx_seq((i + 1) as nat).filter(not_over_pred(m)) == (if not_overridden(m, i) {
            idx_seq(i as nat).filter(not_over_pred(m)).push(i)
        } else {
            idx_seq(i as nat).filter(not_over_pred(m))
        }),
{
    let s = idx_seq((i + 1) as nat);
    assert(s.drop_last() =~= idx_seq(i as nat));
    assert(s.last() == i);
    reveal_with_fuel(Seq::filter, 1);
}

pub proof fn lemma_attr_push(m: Ms, ob: Seq<Attribute>, oa: Seq<Attribute>, i: int)
    requires
        0 <= i < m.len(),
        not_overridden(m, i),
        attrs_view(ob) == attr_entries(m, idx_seq(i as nat).filter(not_over_pred(m))),
        oa.len() == ob.len() + 1,
        forall|k: int| 0 <= k < ob.len() ==> #[trigger] oa[k] == ob[k],
        oa[ob.len() as int]@ == (AttributeS { name: m[i].0, accessor: uint_val(m[i].1)->Some_0 }),
    ensures
        attrs_view(oa) == attr_entries(m, idx_seq(i as nat).filter(not_over_pred(m)).push(i)),
{
    let f = idx_seq(i as nat).filter(not_over_pred(m));
    assert(attrs_view(ob).len() == ob.len());
    assert(attr_entries(m, f).len() == f.len());
    assert(attrs_view(oa) =~= attr_entries(m, f.push(i))) by {
        assert forall|k: int| 0 <= k < ob.len() implies attrs_view(oa)[k] == attr_entries(m, f.push(i))[k] by {
            assert(attrs_view(ob)[k] == attr_entries(m, f)[k]);
            assert(f.push(i)[k] == f[k]);
            assert(attrs_view(oa)[k] == oa[k]@);
            assert(attrs_view(ob)[k] == ob[k]@);
        }
        assert(attrs_view(oa)[ob.len() as int] == oa[ob.len() as int]@);
        assert(f.push(i)[f.len() as int] == i);
    }
}

// 上書きされないメンバーだけをメンバー順に残す
pub open spec fn idx_seq(n: nat) -> Seq<int> {
    Seq::new(n, |i: int| i)
}

pub open spec fn not_over_pred(o: Ms) -> spec_fn(int) -> bool {
    |i: int| not_overridden(o, i)
}

pub open spec fn attr_entries(o: Ms, idx: Seq<int>) -> Seq<AttributeS> {
    idx.map_values(|i: int| AttributeS { name: o[i].0, accessor: uint_val(o[i].1)->Some_0 })
}

pub open spec fn last_entries(o: Ms) -> Seq<AttributeS> {
    attr_entries(o, idx_seq(o.len()).filter(not_over_pred(o)))
}

fn attribute_entries(d: &Vec<JsonNode>, o: &Vec<Member>) -> (r: Result<Vec<Attribute>, ()>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => (forall|i: int| 0 <= i < o.len() && #[trigger] not_overridden(mt(d@, o@), i) ==> uint_val(mt(d@, o@)[i].1) is Some)
                && attrs_view(v@) == last_entries(mt(d@, o@)),
            Err(_) => !(forall|i: int| 0 <= i < o.len() && #[trigger] not_overridden(mt(d@, o@), i) ==> uint_val(mt(d@, o@)[i].1) is Some),
        },
{
    let mut out: Vec<Attribute> = Vec::new();
    let mut i = 0;
    while i < o.len()
        invariant
            numbers_wf(d@),
            0 <= i <= o.len(),
            ctx(d@, o@) ==> forall|k: int| 0 <= k < i && #[trigger] not_overridden(mt(d@, o@), k) ==> uint_val(mt(d@, o@)[k].1) is Some,
            ctx(d@, o@) ==> attrs_view(out@) == attr_entries(mt(d@, o@), idx_seq(i as nat).filter(not_over_pred(mt(d@, o@)))),
        decreases o.len() - i,
    {
        let ghost ob = out@;
        proof {
            lemma_last_key(d@, o@, i as int);
            if ctx(d@, o@) {
                lemma_node_tree(d@, o@[i as int].value as int);
                lemma_filter_step(mt(d@, o@), i as int);
            }
        }
        if is_last_member(o, i) {
            proof {
                lemma_num_u64_all();
            }
            match node_at(d, o[i].value) {
                Some(JsonNode::Number(n)) => match number_to_u64(n) {
                    Some(v) => out.push(Attribute { name: copy_key(&o[i].key), accessor: v }),
                    None => return Err(()),
                },
                _ => return Err(()),
            }
            proof {
                if ctx(d@, o@) {
                    lemma_attr_push(mt(d@, o@), ob, out@, i as int);
                }
            }
        }
        i += 1;
    }
    proof {
        if ctx(d@, o@) {
            assert(idx_seq(o.len() as nat) =~= idx_seq(o@.len()));
        }
    }
    Ok(out)
}

// attributes / targets の対応（上書きされないメンバーの値はすべて uint）
// MUST-058, MUST-082: attributes / targets は名前からアクセサーへの平らな対応
pub open spec fn attr_map_s(v: JsonS, allow_empty: bool) -> Option<Seq<AttributeS>> {
    match v {
        JsonS::Object(o) => if (o.len() > 0 || allow_empty) && forall|i: int|
            0 <= i < o.len() && #[trigger] not_overridden(o, i) ==> uint_val(o[i].1) is Some {
            Some(last_entries(o))
        } else {
            None
        },
        _ => None,
    }
}

// MUST-058, MUST-082: attributes / targets は名前からアクセサーへの平らな対応
fn read_attribute_map(d: &Vec<JsonNode>, id: usize, allow_empty: bool) -> (r: Result<Vec<Attribute>, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(v) => attr_map_s(tree(d@, id as int), allow_empty) == Some(attrs_view(v@)),
            Err(_) => attr_map_s(tree(d@, id as int), allow_empty) is None,
        },
{
    match as_object(d, id) {
        Err(()) => Err(()),
        Ok(o) => {
            if o.len() == 0 && !allow_empty {
                Err(())
            } else {
                attribute_entries(d, o)
            }
        }
    }
}

pub open spec fn targets_s(a: Seq<JsonS>) -> Option<Seq<Seq<AttributeS>>> {
    if forall|i: int| 0 <= i < a.len() ==> (#[trigger] attr_map_s(a[i], true)) is Some {
        Some(Seq::new(a.len(), |i: int| attr_map_s(a[i], true)->Some_0))
    } else {
        None
    }
}

pub open spec fn primitive_s(v: JsonS) -> Option<(PrimitiveS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let e = ext_s(o);
            let attrs = match lookup(o, seq![b'a', b't', b't', b'r', b'i', b'b', b'u', b't', b'e', b's']) {
                None => None,
                Some(x) => attr_map_s(x, false),
            };
            let indices = get_uint_s(o, seq![b'i', b'n', b'd', b'i', b'c', b'e', b's']);
            let material = get_uint_s(o, seq![b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l']);
            let mode = uint_or_s(o, seq![b'm', b'o', b'd', b'e'], 4);
            let targets = match get_array_s(o, seq![b't', b'a', b'r', b'g', b'e', b't', b's']) {
                None => None,
                Some(None) => Some(Seq::empty()),
                Some(Some(a)) => targets_s(a),
            };
            if e is Some && attrs is Some && indices is Some && material is Some && mode is Some && targets is Some {
                Some((
                    PrimitiveS {
                        attributes: attrs->Some_0,
                        indices: indices->Some_0,
                        material: material->Some_0,
                        mode: mode->Some_0,
                        targets: targets->Some_0,
                    },
                    e->Some_0,
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

fn read_primitive(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Primitive, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(primitive_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => primitive_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    proof {
        lemma_lookup(d@, o@, seq![b'a', b't', b't', b'r', b'i', b'b', b'u', b't', b'e', b's']);
    }
    let attributes = match find_member(o, &[b'a', b't', b't', b'r', b'i', b'b', b'u', b't', b'e', b's']) {
        None => return Err(()),
        Some(i) => match read_attribute_map(d, o[i].value, false) { Ok(a) => a, Err(()) => return Err(()) },
    };
    let indices = match get_uint(d, o, &[b'i', b'n', b'd', b'i', b'c', b'e', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    let material = match get_uint(d, o, &[b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l']) { Ok(v) => v, Err(()) => return Err(()) };
    let mode = match get_uint(d, o, &[b'm', b'o', b'd', b'e']) { Ok(Some(v)) => v, Ok(None) => 4, Err(()) => return Err(()) };
    let targets = match get_array(d, o, &[b't', b'a', b'r', b'g', b'e', b't', b's']) {
        Err(()) => return Err(()),
        Ok(None) => Vec::new(),
        Ok(Some(a)) => match read_target_items(d, a) {
            Ok(t) => t,
            Err(()) => return Err(()),
        },
    };
    proof {
        assert(targets_view(Seq::<Vec<Attribute>>::empty()) =~= Seq::<Seq<AttributeS>>::empty());
    }
    Ok(Primitive { attributes, indices, material, mode, targets })
}

fn read_target_items(d: &Vec<JsonNode>, a: &Vec<usize>) -> (r: Result<Vec<Vec<Attribute>>, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => targets_s(trees(d@, a@)) == Some(targets_view(v@)),
            Err(_) => targets_s(trees(d@, a@)) is None,
        },
{
    let mut out: Vec<Vec<Attribute>> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            numbers_wf(d@),
            0 <= i <= a.len(),
            out@.len() == i,
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> #[trigger] attr_map_s(trees(d@, a@)[k], true) == Some(targets_view(out@)[k]),
        decreases a.len() - i,
    {
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                assert(trees(d@, a@)[i as int] == tree(d@, a@[i as int] as int));
                assert(attr_map_s(tree(d@, a@[i as int] as int), true) is None ==> attr_map_s(trees(d@, a@)[i as int], true) is None);
            }
        }
        match read_attribute_map(d, a[i], true) {
            Ok(t) => out.push(t),
            Err(()) => return Err(()),
        }
        proof {
            assert forall|k: int| 0 <= k < i implies targets_view(out@)[k] == targets_view(ob)[k] by {}
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            assert(Seq::new(trees(d@, a@).len(), |k: int| attr_map_s(trees(d@, a@)[k], true)->Some_0) =~= targets_view(out@));
        }
    }
    Ok(out)
}

pub open spec fn union_upto<T>(t: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>, i: int) -> Ext {
    ISet::new(|x: Seq<u8>| exists|k: int| 0 <= k < i && (#[trigger] f(t[k]))->Some_0.1.contains(x))
}

pub open spec fn items_inv<T>(t: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>, v: Seq<T>, i: int, e0: Seq<Vec<u8>>, cur: Seq<Vec<u8>>) -> bool {
    &&& v.len() == i
    &&& forall|k: int| 0 <= k < i ==> (#[trigger] f(t[k])) is Some && v[k] == f(t[k])->Some_0.0
    &&& ext_grow(e0, cur, union_upto(t, f, i))
}

pub proof fn lemma_items_init<T>(t: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>, e0: Seq<Vec<u8>>)
    ensures
        items_inv(t, f, Seq::empty(), 0, e0, e0),
{
}

pub proof fn lemma_items_step<T>(
    t: Seq<JsonS>,
    f: spec_fn(JsonS) -> Option<(T, Ext)>,
    ob: Seq<T>,
    oa: Seq<T>,
    i: int,
    e0: Seq<Vec<u8>>,
    eb: Seq<Vec<u8>>,
    ea: Seq<Vec<u8>>,
)
    requires
        0 <= i < t.len(),
        items_inv(t, f, ob, i, e0, eb),
        oa.len() == ob.len() + 1,
        forall|k: int| 0 <= k < ob.len() ==> #[trigger] oa[k] == ob[k],
        got(f(t[i]), oa[ob.len() as int], eb, ea),
    ensures
        items_inv(t, f, oa, i + 1, e0, ea),
{
    assert forall|k: int| 0 <= k < i + 1 implies (#[trigger] f(t[k])) is Some && oa[k] == f(t[k])->Some_0.0 by {
        if k < i {
            assert(oa[k] == ob[k]);
        }
    }
    assert forall|x: Seq<u8>| #[trigger] ext_set(ea).contains(x) == (ext_set(e0).contains(x) || union_upto(t, f, i + 1).contains(x)) by {
        if union_upto(t, f, i + 1).contains(x) {
            let k = choose|k: int| 0 <= k < i + 1 && (#[trigger] f(t[k]))->Some_0.1.contains(x);
            if k < i {
                assert(union_upto(t, f, i).contains(x));
            }
        }
        if union_upto(t, f, i).contains(x) {
            let k = choose|k: int| 0 <= k < i && (#[trigger] f(t[k]))->Some_0.1.contains(x);
            assert(0 <= k < i + 1);
        }
        if f(t[i])->Some_0.1.contains(x) {
            assert(union_upto(t, f, i + 1).contains(x));
        }
    }
}

pub proof fn lemma_items_done<T>(t: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>, v: Seq<T>, e0: Seq<Vec<u8>>, cur: Seq<Vec<u8>>)
    requires
        items_inv(t, f, v, t.len() as int, e0, cur),
    ensures
        got(items_s(t, f), v, e0, cur),
{
    let s = items_s(t, f);
    assert(s is Some);
    assert(s->Some_0.0 =~= v);
    assert forall|x: Seq<u8>| #[trigger] ext_set(cur).contains(x) == (ext_set(e0).contains(x) || s->Some_0.1.contains(x)) by {
        assert(s->Some_0.1.contains(x) == union_upto(t, f, t.len() as int).contains(x));
    }
}

pub proof fn lemma_items_fail<T>(t: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>, i: int)
    requires
        0 <= i < t.len(),
    ensures
        f(t[i]) is None ==> items_s(t, f) is None,
{
}

// 配列の各要素を規則 f で読む
pub open spec fn items_s<T>(a: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>) -> Option<(Seq<T>, Ext)> {
    if forall|i: int| 0 <= i < a.len() ==> (#[trigger] f(a[i])) is Some {
        Some((
            Seq::new(a.len(), |i: int| f(a[i])->Some_0.0),
            ISet::new(|x: Seq<u8>| exists|i: int| 0 <= i < a.len() && (#[trigger] f(a[i]))->Some_0.1.contains(x)),
        ))
    } else {
        None
    }
}

pub open spec fn primitive_f() -> spec_fn(JsonS) -> Option<(PrimitiveS, Ext)> {
    |v: JsonS| primitive_s(v)
}

fn read_primitive_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Primitive>, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), primitive_f()), prims_view(v@), old(ext)@, final(ext)@),
            Err(e) => items_s(trees(d@, a@), primitive_f()) is None,
        },
{
    let mut out: Vec<Primitive> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), primitive_f(), e0);
        assert(prims_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), primitive_f(), prims_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = prims_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), primitive_f(), i as int);
            }
        }
        match read_primitive(d, a[i], ext) {
            Ok(p) => out.push(p),
            Err(()) => return Err(()),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), primitive_f(), ob, prims_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), primitive_f(), prims_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

pub open spec fn mesh_s(v: JsonS) -> Option<(MeshS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let prims = match get_array_s(o, seq![b'p', b'r', b'i', b'm', b'i', b't', b'i', b'v', b'e', b's']) {
                Some(Some(a)) => items_s(a, primitive_f()),
                _ => None,
            };
            let w = get_number_array_len_s(o, seq![b'w', b'e', b'i', b'g', b'h', b't', b's']);
            if c is Some && prims is Some && w is Some {
                Some((MeshS { primitives: prims->Some_0.0, weights_len: w->Some_0 }, c->Some_0.union(prims->Some_0.1)))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_mesh(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Mesh, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(mesh_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => mesh_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let primitives = match get_array(d, o, &[b'p', b'r', b'i', b'm', b'i', b't', b'i', b'v', b'e', b's']) {
        Ok(Some(a)) => match read_primitive_items(d, a, ext) {
            Ok(p) => p,
            Err(()) => return Err(()),
        },
        _ => return Err(()),
    };
    let weights_len = match get_number_array_len(d, o, &[b'w', b'e', b'i', b'g', b'h', b't', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Mesh { primitives, weights_len })
}

pub open spec fn node_s(v: JsonS) -> Option<(NodeS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let children = get_uint_array_s(o, seq![b'c', b'h', b'i', b'l', b'd', b'r', b'e', b'n']);
            let mesh = get_uint_s(o, seq![b'm', b'e', b's', b'h']);
            let camera = get_uint_s(o, seq![b'c', b'a', b'm', b'e', b'r', b'a']);
            let skin = get_uint_s(o, seq![b's', b'k', b'i', b'n']);
            let m = check_number_array_s(o, seq![b'm', b'a', b't', b'r', b'i', b'x'], 16);
            let t = check_number_array_s(o, seq![b't', b'r', b'a', b'n', b's', b'l', b'a', b't', b'i', b'o', b'n'], 3);
            let r = check_number_array_s(o, seq![b'r', b'o', b't', b'a', b't', b'i', b'o', b'n'], 4);
            let s = check_number_array_s(o, seq![b's', b'c', b'a', b'l', b'e'], 3);
            let w = get_number_array_len_s(o, seq![b'w', b'e', b'i', b'g', b'h', b't', b's']);
            if c is Some && children is Some && mesh is Some && camera is Some && skin is Some && m is Some && t is Some
                && r is Some && s is Some && w is Some {
                Some((
                    NodeS {
                        children: match children->Some_0 {
                            Some(x) => x,
                            None => Seq::empty(),
                        },
                        mesh: mesh->Some_0,
                        camera: camera->Some_0,
                        skin: skin->Some_0,
                        has_matrix: m->Some_0,
                        has_trs: t->Some_0 || r->Some_0 || s->Some_0,
                        weights_len: w->Some_0,
                    },
                    c->Some_0,
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_node(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Node, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(node_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => node_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let children = match get_uint_array(d, o, &[b'c', b'h', b'i', b'l', b'd', b'r', b'e', b'n']) {
        Ok(Some(c)) => c,
        Ok(None) => Vec::new(),
        Err(()) => return Err(()),
    };
    let mesh = match get_uint(d, o, &[b'm', b'e', b's', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let camera = match get_uint(d, o, &[b'c', b'a', b'm', b'e', b'r', b'a']) { Ok(v) => v, Err(()) => return Err(()) };
    let skin = match get_uint(d, o, &[b's', b'k', b'i', b'n']) { Ok(v) => v, Err(()) => return Err(()) };
    let has_matrix = match check_number_array(d, o, &[b'm', b'a', b't', b'r', b'i', b'x'], 16) { Ok(b) => b, Err(()) => return Err(()) };
    let has_t = match check_number_array(d, o, &[b't', b'r', b'a', b'n', b's', b'l', b'a', b't', b'i', b'o', b'n'], 3) { Ok(b) => b, Err(()) => return Err(()) };
    let has_r = match check_number_array(d, o, &[b'r', b'o', b't', b'a', b't', b'i', b'o', b'n'], 4) { Ok(b) => b, Err(()) => return Err(()) };
    let has_s = match check_number_array(d, o, &[b's', b'c', b'a', b'l', b'e'], 3) { Ok(b) => b, Err(()) => return Err(()) };
    let weights_len = match get_number_array_len(d, o, &[b'w', b'e', b'i', b'g', b'h', b't', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Node { children, mesh, camera, skin, has_matrix, has_trs: has_t || has_r || has_s, weights_len })
}

pub open spec fn scene_s(v: JsonS) -> Option<(SceneS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let nodes = get_uint_array_s(o, seq![b'n', b'o', b'd', b'e', b's']);
            if c is Some && nodes is Some {
                Some((
                    SceneS {
                        nodes: match nodes->Some_0 {
                            Some(x) => x,
                            None => Seq::empty(),
                        },
                    },
                    c->Some_0,
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_scene(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Scene, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(scene_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => scene_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let nodes = match get_uint_array(d, o, &[b'n', b'o', b'd', b'e', b's']) {
        Ok(Some(c)) => c,
        Ok(None) => Vec::new(),
        Err(()) => return Err(()),
    };
    Ok(Scene { nodes })
}

pub open spec fn type_s(t: Seq<u8>) -> Option<(u64, bool)> {
    if t == seq![b'S', b'C', b'A', b'L', b'A', b'R'] {
        Some((1, false))
    } else if t == seq![b'V', b'E', b'C', b'2'] {
        Some((2, false))
    } else if t == seq![b'V', b'E', b'C', b'3'] {
        Some((3, false))
    } else if t == seq![b'V', b'E', b'C', b'4'] {
        Some((4, false))
    } else if t == seq![b'M', b'A', b'T', b'2'] {
        Some((4, true))
    } else if t == seq![b'M', b'A', b'T', b'3'] {
        Some((9, true))
    } else if t == seq![b'M', b'A', b'T', b'4'] {
        Some((16, true))
    } else {
        None
    }
}

fn type_components(t: &Vec<u8>) -> (r: Option<(u64, bool)>)
    ensures
        r == type_s(t@),
{
    if bytes_eq(t, &[b'S', b'C', b'A', b'L', b'A', b'R']) {
        Some((1, false))
    } else if bytes_eq(t, &[b'V', b'E', b'C', b'2']) {
        Some((2, false))
    } else if bytes_eq(t, &[b'V', b'E', b'C', b'3']) {
        Some((3, false))
    } else if bytes_eq(t, &[b'V', b'E', b'C', b'4']) {
        Some((4, false))
    } else if bytes_eq(t, &[b'M', b'A', b'T', b'2']) {
        Some((4, true))
    } else if bytes_eq(t, &[b'M', b'A', b'T', b'3']) {
        Some((9, true))
    } else if bytes_eq(t, &[b'M', b'A', b'T', b'4']) {
        Some((16, true))
    } else {
        None
    }
}

pub open spec fn k_buffer_view() -> Seq<u8> {
    seq![b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']
}

pub open spec fn k_byte_offset() -> Seq<u8> {
    seq![b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']
}

pub open spec fn k_component_type() -> Seq<u8> {
    seq![b'c', b'o', b'm', b'p', b'o', b'n', b'e', b'n', b't', b'T', b'y', b'p', b'e']
}

// MUST-043: sparse の必須プロパティ
pub open spec fn sparse_s(v: JsonS) -> Option<(Sparse, Ext)> {
    match v {
        JsonS::Object(o) => {
            let e = ext_s(o);
            let count = req_uint_s(o, seq![b'c', b'o', b'u', b'n', b't']);
            match (get_object_s(o, seq![b'i', b'n', b'd', b'i', b'c', b'e', b's']), get_object_s(o, seq![b'v', b'a', b'l', b'u', b'e', b's'])) {
                (Some(Some(ind)), Some(Some(val))) => {
                    let ei = ext_s(ind);
                    let ibv = req_uint_s(ind, k_buffer_view());
                    let ibo = uint_or_s(ind, k_byte_offset(), 0);
                    let ict = req_uint_s(ind, k_component_type());
                    let ev = ext_s(val);
                    let vbv = req_uint_s(val, k_buffer_view());
                    let vbo = uint_or_s(val, k_byte_offset(), 0);
                    if e is Some && count is Some && ei is Some && ibv is Some && ibo is Some && ict is Some && ev is Some && vbv is Some
                        && vbo is Some {
                        Some((
                            Sparse {
                                count: count->Some_0,
                                indices_buffer_view: ibv->Some_0,
                                indices_byte_offset: ibo->Some_0,
                                indices_component_type: ict->Some_0,
                                values_buffer_view: vbv->Some_0,
                                values_byte_offset: vbo->Some_0,
                            },
                            e->Some_0.union(ei->Some_0).union(ev->Some_0),
                        ))
                    } else {
                        None
                    }
                },
                _ => None,
            }
        },
        _ => None,
    }
}

// MUST-043: sparse の必須プロパティ
fn read_sparse(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Sparse, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(sparse_s(tree(d@, id as int)), x, old(ext)@, final(ext)@),
            Err(_) => sparse_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let count = match req_uint(d, o, &[b'c', b'o', b'u', b'n', b't']) { Ok(v) => v, Err(()) => return Err(()) };
    let ind = match get_object(d, o, &[b'i', b'n', b'd', b'i', b'c', b'e', b's']) { Ok(Some(x)) => x, _ => return Err(()) };
    match check_extensions(d, ind, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let indices_buffer_view = match req_uint(d, ind, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let indices_byte_offset = match get_uint(d, ind, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    let indices_component_type = match req_uint(d, ind, &[b'c', b'o', b'm', b'p', b'o', b'n', b'e', b'n', b't', b'T', b'y', b'p', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let val = match get_object(d, o, &[b'v', b'a', b'l', b'u', b'e', b's']) { Ok(Some(x)) => x, _ => return Err(()) };
    match check_extensions(d, val, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let values_buffer_view = match req_uint(d, val, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let values_byte_offset = match get_uint(d, val, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    Ok(Sparse { count, indices_buffer_view, indices_byte_offset, indices_component_type, values_buffer_view, values_byte_offset })
}

// (U) 型が既知でないアクセサ
pub open spec fn u_accessor(v: JsonS) -> bool {
    v matches JsonS::Object(o) && (get_string_s(o, seq![b't', b'y', b'p', b'e']) matches Some(Some(t)) && type_s(t) is None)
}

// strict = false のときは (U) を規則違反としない（Invalid の判定用）
pub open spec fn accessor_s(v: JsonS, strict: bool) -> Option<(Accessor, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let bv = get_uint_s(o, k_buffer_view());
            let bo = get_uint_s(o, k_byte_offset());
            let ct = req_uint_s(o, k_component_type());
            let nm = get_bool_s(o, seq![b'n', b'o', b'r', b'm', b'a', b'l', b'i', b'z', b'e', b'd']);
            let count = req_uint_s(o, seq![b'c', b'o', b'u', b'n', b't']);
            let ty = get_string_s(o, seq![b't', b'y', b'p', b'e']);
            let tc: Option<(u64, bool)> = match ty {
                Some(Some(t)) => match type_s(t) {
                    Some(x) => Some(x),
                    None => if strict {
                        None
                    } else {
                        Some((0, false))
                    },
                },
                _ => None,
            };
            let mn = get_number_array_len_s(o, seq![b'm', b'i', b'n']);
            let mx = get_number_array_len_s(o, seq![b'm', b'a', b'x']);
            let sp: Option<(Option<Sparse>, Ext)> = match lookup(o, seq![b's', b'p', b'a', b'r', b's', b'e']) {
                None => Some((None, ISet::empty())),
                Some(x) => match sparse_s(x) {
                    Some((s, e)) => Some((Some(s), e)),
                    None => None,
                },
            };
            if c is Some && bv is Some && bo is Some && ct is Some && nm is Some && count is Some && tc is Some && mn is Some
                && mx is Some && sp is Some {
                Some((
                    Accessor {
                        buffer_view: bv->Some_0,
                        byte_offset: bo->Some_0,
                        component_type: ct->Some_0,
                        normalized: match nm->Some_0 {
                            Some(b) => b,
                            None => false,
                        },
                        count: count->Some_0,
                        components: tc->Some_0.0,
                        is_matrix: tc->Some_0.1,
                        min_len: mn->Some_0,
                        max_len: mx->Some_0,
                        sparse: sp->Some_0.0,
                    },
                    c->Some_0.union(sp->Some_0.1),
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_accessor(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Accessor, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(accessor_s(tree(d@, id as int), true), x, old(ext)@, final(ext)@) && accessor_s(tree(d@, id as int), false)
                == accessor_s(tree(d@, id as int), true),
            Err(GltfError::Invalid) => accessor_s(tree(d@, id as int), false) is None && accessor_s(tree(d@, id as int), true) is None,
            Err(GltfError::Unsupported) => u_accessor(tree(d@, id as int)) && accessor_s(tree(d@, id as int), true) is None,
            Err(_) => false,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let buffer_view = match get_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let byte_offset = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let component_type = match req_uint(d, o, &[b'c', b'o', b'm', b'p', b'o', b'n', b'e', b'n', b't', b'T', b'y', b'p', b'e']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let normalized = match get_bool(d, o, &[b'n', b'o', b'r', b'm', b'a', b'l', b'i', b'z', b'e', b'd']) { Ok(Some(b)) => b, Ok(None) => false, Err(()) => return Err(GltfError::Invalid) };
    let count = match req_uint(d, o, &[b'c', b'o', b'u', b'n', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let t = match get_string(d, o, &[b't', b'y', b'p', b'e']) { Ok(Some(t)) => t, _ => return Err(GltfError::Invalid) };
    let (components, is_matrix) = match type_components(&t) { Some(c) => c, None => return Err(GltfError::Unsupported) };
    let min_len = match get_number_array_len(d, o, &[b'm', b'i', b'n']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let max_len = match get_number_array_len(d, o, &[b'm', b'a', b'x']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    proof {
        lemma_lookup(d@, o@, seq![b's', b'p', b'a', b'r', b's', b'e']);
        lemma_ext_refl(ext@);
    }
    let sparse = match find_member(o, &[b's', b'p', b'a', b'r', b's', b'e']) {
        None => None,
        Some(i) => match read_sparse(d, o[i].value, ext) { Ok(s) => Some(s), Err(()) => return Err(GltfError::Invalid) },
    };
    Ok(Accessor { buffer_view, byte_offset, component_type, normalized, count, components, is_matrix, min_len, max_len, sparse })
}

pub open spec fn buffer_view_s(v: JsonS) -> Option<(BufferView, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let b = req_uint_s(o, seq![b'b', b'u', b'f', b'f', b'e', b'r']);
            let bo = uint_or_s(o, k_byte_offset(), 0);
            let bl = req_uint_s(o, seq![b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']);
            let bs = get_uint_s(o, seq![b'b', b'y', b't', b'e', b'S', b't', b'r', b'i', b'd', b'e']);
            let t = get_uint_s(o, seq![b't', b'a', b'r', b'g', b'e', b't']);
            if c is Some && b is Some && bo is Some && bl is Some && bs is Some && t is Some {
                Some((
                    BufferView {
                        buffer: b->Some_0,
                        byte_offset: bo->Some_0,
                        byte_length: bl->Some_0,
                        byte_stride: bs->Some_0,
                        target: t->Some_0,
                    },
                    c->Some_0,
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_buffer_view(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<BufferView, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(buffer_view_s(tree(d@, id as int)), x, old(ext)@, final(ext)@),
            Err(_) => buffer_view_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let buffer = match req_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let byte_offset = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    let byte_length = match req_uint(d, o, &[b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let byte_stride = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'S', b't', b'r', b'i', b'd', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let target = match get_uint(d, o, &[b't', b'a', b'r', b'g', b'e', b't']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(BufferView { buffer, byte_offset, byte_length, byte_stride, target })
}

pub open spec fn buffer_s(v: JsonS) -> Option<(BufferS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let bl = req_uint_s(o, seq![b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']);
            let uri = get_string_s(o, seq![b'u', b'r', b'i']);
            if c is Some && bl is Some && uri is Some {
                Some((BufferS { byte_length: bl->Some_0, uri: uri->Some_0 }, c->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_buffer(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Buffer, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(buffer_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => buffer_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let byte_length = match req_uint(d, o, &[b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let uri = match get_string(d, o, &[b'u', b'r', b'i']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Buffer { byte_length, uri })
}

pub open spec fn image_s(v: JsonS) -> Option<(ImageS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let uri = get_string_s(o, seq![b'u', b'r', b'i']);
            let bv = get_uint_s(o, k_buffer_view());
            let mt = get_string_s(o, seq![b'm', b'i', b'm', b'e', b'T', b'y', b'p', b'e']);
            if c is Some && uri is Some && bv is Some && mt is Some {
                Some((ImageS { uri: uri->Some_0, buffer_view: bv->Some_0, has_mime_type: mt->Some_0 is Some }, c->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_image(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Image, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(image_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => image_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let uri = match get_string(d, o, &[b'u', b'r', b'i']) { Ok(v) => v, Err(()) => return Err(()) };
    let buffer_view = match get_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let has_mime_type = match get_string(d, o, &[b'm', b'i', b'm', b'e', b'T', b'y', b'p', b'e']) { Ok(v) => v.is_some(), Err(()) => return Err(()) };
    Ok(Image { uri, buffer_view, has_mime_type })
}

pub open spec fn texture_s(v: JsonS) -> Option<(Texture, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let sm = get_uint_s(o, seq![b's', b'a', b'm', b'p', b'l', b'e', b'r']);
            let so = get_uint_s(o, seq![b's', b'o', b'u', b'r', b'c', b'e']);
            if c is Some && sm is Some && so is Some {
                Some((Texture { sampler: sm->Some_0, source: so->Some_0 }, c->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_texture(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Texture, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(texture_s(tree(d@, id as int)), x, old(ext)@, final(ext)@),
            Err(_) => texture_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let sampler = match get_uint(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let source = match get_uint(d, o, &[b's', b'o', b'u', b'r', b'c', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Texture { sampler, source })
}

// sampler: 個数だけを数える
pub open spec fn sampler_s(v: JsonS) -> Option<((), Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            if c is Some && get_uint_s(o, seq![b'm', b'a', b'g', b'F', b'i', b'l', b't', b'e', b'r']) is Some && get_uint_s(
                o,
                seq![b'm', b'i', b'n', b'F', b'i', b'l', b't', b'e', b'r'],
            ) is Some && get_uint_s(o, seq![b'w', b'r', b'a', b'p', b'S']) is Some && get_uint_s(o, seq![b'w', b'r', b'a', b'p', b'T'])
                is Some {
                Some(((), c->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub(crate) fn read_sampler(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<(), ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(sampler_s(tree(d@, id as int)), (), old(ext)@, final(ext)@),
            Err(_) => sampler_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    match get_uint(d, o, &[b'm', b'a', b'g', b'F', b'i', b'l', b't', b'e', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'm', b'i', b'n', b'F', b'i', b'l', b't', b'e', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'w', b'r', b'a', b'p', b'S']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'w', b'r', b'a', b'p', b'T']) { Err(()) => return Err(()), Ok(_) => {} }
    Ok(())
}

pub open spec fn k_zfar() -> Seq<u8> {
    seq![b'z', b'f', b'a', b'r']
}

pub open spec fn k_znear() -> Seq<u8> {
    seq![b'z', b'n', b'e', b'a', b'r']
}

pub open spec fn perspective_s(o: Ms) -> Option<(bool, Ext)> {
    match get_object_s(o, seq![b'p', b'e', b'r', b's', b'p', b'e', b'c', b't', b'i', b'v', b'e']) {
        None => None,
        Some(None) => Some((false, ISet::empty())),
        Some(Some(p)) => {
            let e = ext_s(p);
            if e is Some && check_number_s(p, seq![b'a', b's', b'p', b'e', b'c', b't', b'R', b'a', b't', b'i', b'o']) is Some
                && check_number_s(p, seq![b'y', b'f', b'o', b'v']) == Some(true) && check_number_s(p, k_zfar()) is Some
                && check_number_s(p, k_znear()) == Some(true) {
                Some((true, e->Some_0))
            } else {
                None
            }
        },
    }
}

fn check_perspective(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<bool, ()>)
    ensures
        ctx(d@, o@) ==> match r {
            Ok(b) => got(perspective_s(mt(d@, o@)), b, old(ext)@, final(ext)@),
            Err(_) => perspective_s(mt(d@, o@)) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_object(d, o, &[b'p', b'e', b'r', b's', b'p', b'e', b'c', b't', b'i', b'v', b'e']) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(p)) => {
            match check_extensions(d, p, ext) { Err(()) => return Err(()), Ok(()) => {} }
            match check_number(d, p, &[b'a', b's', b'p', b'e', b'c', b't', b'R', b'a', b't', b'i', b'o']) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'y', b'f', b'o', b'v']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'z', b'f', b'a', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
            match check_number(d, p, &[b'z', b'n', b'e', b'a', b'r']) { Ok(true) => {} _ => return Err(()) }
            Ok(true)
        }
    }
}

pub open spec fn orthographic_s(o: Ms) -> Option<(bool, Ext)> {
    match get_object_s(o, seq![b'o', b'r', b't', b'h', b'o', b'g', b'r', b'a', b'p', b'h', b'i', b'c']) {
        None => None,
        Some(None) => Some((false, ISet::empty())),
        Some(Some(p)) => {
            let e = ext_s(p);
            if e is Some && check_number_s(p, seq![b'x', b'm', b'a', b'g']) == Some(true) && check_number_s(p, seq![b'y', b'm', b'a', b'g'])
                == Some(true) && check_number_s(p, k_zfar()) == Some(true) && check_number_s(p, k_znear()) == Some(true) {
                Some((true, e->Some_0))
            } else {
                None
            }
        },
    }
}

fn check_orthographic(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<bool, ()>)
    ensures
        ctx(d@, o@) ==> match r {
            Ok(b) => got(orthographic_s(mt(d@, o@)), b, old(ext)@, final(ext)@),
            Err(_) => orthographic_s(mt(d@, o@)) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_object(d, o, &[b'o', b'r', b't', b'h', b'o', b'g', b'r', b'a', b'p', b'h', b'i', b'c']) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(p)) => {
            match check_extensions(d, p, ext) { Err(()) => return Err(()), Ok(()) => {} }
            match check_number(d, p, &[b'x', b'm', b'a', b'g']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'y', b'm', b'a', b'g']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'z', b'f', b'a', b'r']) { Ok(true) => {} _ => return Err(()) }
            match check_number(d, p, &[b'z', b'n', b'e', b'a', b'r']) { Ok(true) => {} _ => return Err(()) }
            Ok(true)
        }
    }
}

pub open spec fn camera_kind_s(t: Seq<u8>) -> u64 {
    if t == seq![b'p', b'e', b'r', b's', b'p', b'e', b'c', b't', b'i', b'v', b'e'] {
        CAMERA_PERSPECTIVE
    } else if t == seq![b'o', b'r', b't', b'h', b'o', b'g', b'r', b'a', b'p', b'h', b'i', b'c'] {
        CAMERA_ORTHOGRAPHIC
    } else {
        KIND_OTHER
    }
}

// MUST-132: camera.type が必要
pub open spec fn camera_s(v: JsonS) -> Option<(Camera, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let t = get_string_s(o, seq![b't', b'y', b'p', b'e']);
            let p = perspective_s(o);
            let q = orthographic_s(o);
            if c is Some && (t matches Some(Some(_))) && p is Some && q is Some {
                Some((
                    Camera { kind: camera_kind_s(t->Some_0->Some_0), has_perspective: p->Some_0.0, has_orthographic: q->Some_0.0 },
                    c->Some_0.union(p->Some_0.1).union(q->Some_0.1),
                ))
            } else {
                None
            }
        },
        _ => None,
    }
}

// MUST-132: camera.type が必要
pub(crate) fn read_camera(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Camera, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(camera_s(tree(d@, id as int)), x, old(ext)@, final(ext)@),
            Err(_) => camera_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let t = match get_string(d, o, &[b't', b'y', b'p', b'e']) { Ok(Some(t)) => t, _ => return Err(()) };
    let kind = if bytes_eq(&t, &[b'p', b'e', b'r', b's', b'p', b'e', b'c', b't', b'i', b'v', b'e']) {
        CAMERA_PERSPECTIVE
    } else if bytes_eq(&t, &[b'o', b'r', b't', b'h', b'o', b'g', b'r', b'a', b'p', b'h', b'i', b'c']) {
        CAMERA_ORTHOGRAPHIC
    } else {
        KIND_OTHER
    };
    let has_perspective = match check_perspective(d, o, ext) { Ok(b) => b, Err(()) => return Err(()) };
    let has_orthographic = match check_orthographic(d, o, ext) { Ok(b) => b, Err(()) => return Err(()) };
    Ok(Camera { kind, has_perspective, has_orthographic })
}

// MUST-095: skin.joints が必要
pub open spec fn skin_s(v: JsonS) -> Option<(SkinS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let j = get_uint_array_s(o, seq![b'j', b'o', b'i', b'n', b't', b's']);
            let sk = get_uint_s(o, seq![b's', b'k', b'e', b'l', b'e', b't', b'o', b'n']);
            let ibm = get_uint_s(o, seq![b'i', b'n', b'v', b'e', b'r', b's', b'e', b'B', b'i', b'n', b'd', b'M', b'a', b't', b'r', b'i', b'c', b'e', b's']);
            if c is Some && (j matches Some(Some(_))) && sk is Some && ibm is Some {
                Some((SkinS { joints: j->Some_0->Some_0, skeleton: sk->Some_0, inverse_bind_matrices: ibm->Some_0 }, c->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

// MUST-095: skin.joints が必要
pub(crate) fn read_skin(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Skin, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(skin_s(tree(d@, id as int)), x@, old(ext)@, final(ext)@),
            Err(_) => skin_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let joints = match get_uint_array(d, o, &[b'j', b'o', b'i', b'n', b't', b's']) { Ok(Some(c)) => c, _ => return Err(()) };
    let skeleton = match get_uint(d, o, &[b's', b'k', b'e', b'l', b'e', b't', b'o', b'n']) { Ok(v) => v, Err(()) => return Err(()) };
    let inverse_bind_matrices = match get_uint(d, o, &[b'i', b'n', b'v', b'e', b'r', b's', b'e', b'B', b'i', b'n', b'd', b'M', b'a', b't', b'r', b'i', b'c', b'e', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Skin { joints, skeleton, inverse_bind_matrices })
}

pub open spec fn path_s(p: Seq<u8>) -> u64 {
    if p == seq![b't', b'r', b'a', b'n', b's', b'l', b'a', b't', b'i', b'o', b'n'] {
        PATH_TRANSLATION
    } else if p == seq![b'r', b'o', b't', b'a', b't', b'i', b'o', b'n'] {
        PATH_ROTATION
    } else if p == seq![b's', b'c', b'a', b'l', b'e'] {
        PATH_SCALE
    } else if p == seq![b'w', b'e', b'i', b'g', b'h', b't', b's'] {
        PATH_WEIGHTS
    } else {
        KIND_OTHER
    }
}

pub open spec fn channel_s(v: JsonS) -> Option<(Channel, Ext)> {
    match v {
        JsonS::Object(o) => {
            let e = ext_s(o);
            let sm = req_uint_s(o, seq![b's', b'a', b'm', b'p', b'l', b'e', b'r']);
            match get_object_s(o, seq![b't', b'a', b'r', b'g', b'e', b't']) {
                Some(Some(t)) => {
                    let et = ext_s(t);
                    let nd = get_uint_s(t, seq![b'n', b'o', b'd', b'e']);
                    let p = get_string_s(t, seq![b'p', b'a', b't', b'h']);
                    if e is Some && sm is Some && et is Some && nd is Some && (p matches Some(Some(_))) {
                        Some((Channel { sampler: sm->Some_0, node: nd->Some_0, path: path_s(p->Some_0->Some_0) }, e->Some_0.union(et->Some_0)))
                    } else {
                        None
                    }
                },
                _ => None,
            }
        },
        _ => None,
    }
}

fn read_channel(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Channel, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(channel_s(tree(d@, id as int)), x, old(ext)@, final(ext)@),
            Err(_) => channel_s(tree(d@, id as int)) is None,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let sampler = match req_uint(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let t = match get_object(d, o, &[b't', b'a', b'r', b'g', b'e', b't']) { Ok(Some(t)) => t, _ => return Err(()) };
    match check_extensions(d, t, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let node = match get_uint(d, t, &[b'n', b'o', b'd', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let p = match get_string(d, t, &[b'p', b'a', b't', b'h']) { Ok(Some(p)) => p, _ => return Err(()) };
    let path = if bytes_eq(&p, &[b't', b'r', b'a', b'n', b's', b'l', b'a', b't', b'i', b'o', b'n']) {
        PATH_TRANSLATION
    } else if bytes_eq(&p, &[b'r', b'o', b't', b'a', b't', b'i', b'o', b'n']) {
        PATH_ROTATION
    } else if bytes_eq(&p, &[b's', b'c', b'a', b'l', b'e']) {
        PATH_SCALE
    } else if bytes_eq(&p, &[b'w', b'e', b'i', b'g', b'h', b't', b's']) {
        PATH_WEIGHTS
    } else {
        KIND_OTHER
    };
    Ok(Channel { sampler, node, path })
}

pub open spec fn interp_s(s: Seq<u8>) -> Option<u64> {
    if s == seq![b'L', b'I', b'N', b'E', b'A', b'R'] {
        Some(INTERP_LINEAR)
    } else if s == seq![b'S', b'T', b'E', b'P'] {
        Some(INTERP_STEP)
    } else if s == seq![b'C', b'U', b'B', b'I', b'C', b'S', b'P', b'L', b'I', b'N', b'E'] {
        Some(INTERP_CUBICSPLINE)
    } else {
        None
    }
}

pub open spec fn k_interpolation() -> Seq<u8> {
    seq![b'i', b'n', b't', b'e', b'r', b'p', b'o', b'l', b'a', b't', b'i', b'o', b'n']
}

// (U) 未知の補間方法
pub open spec fn u_sampler(v: JsonS) -> bool {
    v matches JsonS::Object(o) && (get_string_s(o, k_interpolation()) matches Some(Some(s)) && interp_s(s) is None)
}

pub open spec fn anim_sampler_s(v: JsonS, strict: bool) -> Option<(AnimationSampler, Ext)> {
    match v {
        JsonS::Object(o) => {
            let e = ext_s(o);
            let inp = req_uint_s(o, seq![b'i', b'n', b'p', b'u', b't']);
            let out = req_uint_s(o, seq![b'o', b'u', b't', b'p', b'u', b't']);
            let ip: Option<u64> = match get_string_s(o, k_interpolation()) {
                None => None,
                Some(None) => Some(INTERP_LINEAR),
                Some(Some(s)) => match interp_s(s) {
                    Some(x) => Some(x),
                    None => if strict {
                        None
                    } else {
                        Some(INTERP_LINEAR)
                    },
                },
            };
            if e is Some && inp is Some && out is Some && ip is Some {
                Some((AnimationSampler { input: inp->Some_0, output: out->Some_0, interpolation: ip->Some_0 }, e->Some_0))
            } else {
                None
            }
        },
        _ => None,
    }
}

fn read_animation_sampler(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<AnimationSampler, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(anim_sampler_s(tree(d@, id as int), true), x, old(ext)@, final(ext)@) && anim_sampler_s(tree(d@, id as int), false)
                == anim_sampler_s(tree(d@, id as int), true),
            Err(GltfError::Invalid) => anim_sampler_s(tree(d@, id as int), false) is None && anim_sampler_s(tree(d@, id as int), true) is None,
            Err(GltfError::Unsupported) => u_sampler(tree(d@, id as int)) && anim_sampler_s(tree(d@, id as int), true) is None,
            Err(_) => false,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_extensions(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let input = match req_uint(d, o, &[b'i', b'n', b'p', b'u', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let output = match req_uint(d, o, &[b'o', b'u', b't', b'p', b'u', b't']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let interpolation = match get_string(d, o, &[b'i', b'n', b't', b'e', b'r', b'p', b'o', b'l', b'a', b't', b'i', b'o', b'n']) {
        Err(()) => return Err(GltfError::Invalid),
        Ok(None) => INTERP_LINEAR,
        Ok(Some(s)) => {
            if bytes_eq(&s, &[b'L', b'I', b'N', b'E', b'A', b'R']) {
                INTERP_LINEAR
            } else if bytes_eq(&s, &[b'S', b'T', b'E', b'P']) {
                INTERP_STEP
            } else if bytes_eq(&s, &[b'C', b'U', b'B', b'I', b'C', b'S', b'P', b'L', b'I', b'N', b'E']) {
                INTERP_CUBICSPLINE
            } else {
                return Err(GltfError::Unsupported);
            }
        }
    };
    Ok(AnimationSampler { input, output, interpolation })
}

pub open spec fn channel_f() -> spec_fn(JsonS) -> Option<(Channel, Ext)> {
    |v: JsonS| channel_s(v)
}

fn read_channel_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Channel>, ()>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), channel_f()), v@, old(ext)@, final(ext)@),
            Err(e) => items_s(trees(d@, a@), channel_f()) is None,
        },
{
    let mut out: Vec<Channel> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), channel_f(), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), channel_f(), out@, i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), channel_f(), i as int);
            }
        }
        match read_channel(d, a[i], ext) {
            Ok(c) => out.push(c),
            Err(()) => return Err(()),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), channel_f(), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), channel_f(), out@, e0, ext@);
        }
    }
    Ok(out)
}

pub proof fn lemma_items_eq<T>(t: Seq<JsonS>, f: spec_fn(JsonS) -> Option<(T, Ext)>, g: spec_fn(JsonS) -> Option<(T, Ext)>)
    requires
        forall|k: int| 0 <= k < t.len() ==> #[trigger] f(t[k]) == g(t[k]),
    ensures
        items_s(t, f) == items_s(t, g),
{
    if items_s(t, g) is Some {
        assert(forall|k: int| 0 <= k < t.len() ==> (#[trigger] f(t[k])) is Some);
        assert(items_s(t, f)->Some_0.0 =~= items_s(t, g)->Some_0.0);
        assert forall|x: Seq<u8>| items_s(t, f)->Some_0.1.contains(x) == items_s(t, g)->Some_0.1.contains(x) by {
            if items_s(t, f)->Some_0.1.contains(x) {
                let k = choose|k: int| 0 <= k < t.len() && (#[trigger] f(t[k]))->Some_0.1.contains(x);
                assert(g(t[k])->Some_0.1.contains(x));
            }
            if items_s(t, g)->Some_0.1.contains(x) {
                let k = choose|k: int| 0 <= k < t.len() && (#[trigger] g(t[k]))->Some_0.1.contains(x);
                assert(f(t[k])->Some_0.1.contains(x));
            }
        }
        assert(items_s(t, f)->Some_0.1 =~= items_s(t, g)->Some_0.1);
    } else {
        let k = choose|k: int| 0 <= k < t.len() && !((#[trigger] g(t[k])) is Some);
        assert(f(t[k]) is None);
    }
}

pub open spec fn anim_sampler_f(strict: bool) -> spec_fn(JsonS) -> Option<(AnimationSampler, Ext)> {
    |v: JsonS| anim_sampler_s(v, strict)
}

fn read_animation_sampler_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<AnimationSampler>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), anim_sampler_f(true)), v@, old(ext)@, final(ext)@) && items_s(trees(d@, a@), anim_sampler_f(false))
                == items_s(trees(d@, a@), anim_sampler_f(true)),
            Err(GltfError::Invalid) => items_s(trees(d@, a@), anim_sampler_f(false)) is None && items_s(trees(d@, a@), anim_sampler_f(true)) is None,
            Err(GltfError::Unsupported) => (exists|k: int| 0 <= k < a.len() && u_sampler(#[trigger] trees(d@, a@)[k])) && items_s(
                trees(d@, a@),
                anim_sampler_f(true),
            ) is None,
            Err(_) => false,
        },
{
    let mut out: Vec<AnimationSampler> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), anim_sampler_f(true), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), anim_sampler_f(true), out@, i as int, e0, ext@),
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> #[trigger] anim_sampler_f(false)(trees(d@, a@)[k]) == anim_sampler_f(true)(trees(d@, a@)[k]),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), anim_sampler_f(false), i as int);
                lemma_items_fail(trees(d@, a@), anim_sampler_f(true), i as int);
            }
        }
        match read_animation_sampler(d, a[i], ext) {
            Ok(s) => out.push(s),
            Err(e) => return Err(e),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), anim_sampler_f(true), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), anim_sampler_f(true), out@, e0, ext@);
            lemma_items_eq(trees(d@, a@), anim_sampler_f(false), anim_sampler_f(true));
        }
    }
    Ok(out)
}

pub open spec fn animation_s(v: JsonS, strict: bool) -> Option<(AnimationS, Ext)> {
    match v {
        JsonS::Object(o) => {
            let c = child_s(o);
            let ch = match get_array_s(o, seq![b'c', b'h', b'a', b'n', b'n', b'e', b'l', b's']) {
                Some(Some(a)) => items_s(a, channel_f()),
                _ => None,
            };
            let sm = match get_array_s(o, seq![b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']) {
                Some(Some(a)) => items_s(a, anim_sampler_f(strict)),
                _ => None,
            };
            if c is Some && ch is Some && sm is Some {
                Some((AnimationS { channels: ch->Some_0.0, samplers: sm->Some_0.0 }, c->Some_0.union(ch->Some_0.1).union(sm->Some_0.1)))
            } else {
                None
            }
        },
        _ => None,
    }
}

pub open spec fn k_samplers() -> Seq<u8> {
    seq![b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']
}

// (U) を含むアニメーション（samplers の要素）
pub open spec fn u_animation(v: JsonS) -> bool {
    v matches JsonS::Object(ao) && (get_array_s(ao, k_samplers()) matches Some(Some(sa)) && exists|k: int|
        0 <= k < sa.len() && u_sampler(#[trigger] sa[k]))
}

pub(crate) fn read_animation(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> (r: Result<Animation, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) ==> match r {
            Ok(x) => got(animation_s(tree(d@, id as int), true), x@, old(ext)@, final(ext)@) && animation_s(tree(d@, id as int), false)
                == animation_s(tree(d@, id as int), true),
            Err(GltfError::Invalid) => animation_s(tree(d@, id as int), false) is None && animation_s(tree(d@, id as int), true) is None,
            Err(GltfError::Unsupported) => u_animation(tree(d@, id as int)) && animation_s(tree(d@, id as int), true) is None,
            Err(_) => false,
        },
{
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let channels = match get_array(d, o, &[b'c', b'h', b'a', b'n', b'n', b'e', b'l', b's']) {
        Ok(Some(a)) => match read_channel_items(d, a, ext) {
            Ok(c) => c,
            Err(()) => return Err(GltfError::Invalid),
        },
        _ => return Err(GltfError::Invalid),
    };
    let samplers = match get_array(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']) {
        Ok(Some(a)) => match read_animation_sampler_items(d, a, ext) {
            Ok(s) => s,
            Err(e) => return Err(e),
        },
        _ => return Err(GltfError::Invalid),
    };
    Ok(Animation { channels, samplers })
}

pub proof fn lemma_version_part(s: Seq<u8>, start: int, end: int)
    requires
        0 <= start <= end <= s.len(),
    ensures
        ({
            let p = s.subrange(start, end);
            &&& (forall|k: int| start <= k < end ==> digit(#[trigger] s[k])) == (forall|k: int| 0 <= k < p.len() ==> digit(#[trigger] p[k]))
            &&& (start < end ==> p[0] == s[start])
            &&& s.subrange(start, end) == p
        }),
{
    let p = s.subrange(start, end);
    if forall|k: int| start <= k < end ==> digit(#[trigger] s[k]) {
        assert forall|k: int| 0 <= k < p.len() implies digit(#[trigger] p[k]) by {
            assert(digit(s[start + k]));
        }
    }
    if forall|k: int| 0 <= k < p.len() ==> digit(#[trigger] p[k]) {
        assert forall|k: int| start <= k < end implies digit(#[trigger] s[k]) by {
            assert(digit(p[k - start]));
        }
    }
}

// asset.version / minVersion: ^(0|[1-9][0-9]{0,8})\.(0|[1-9][0-9]{0,8})$
pub open spec fn version_part(p: Seq<u8>) -> Option<u64> {
    if 1 <= p.len() <= 9 && (forall|k: int| 0 <= k < p.len() ==> digit(#[trigger] p[k])) && (p[0] != b'0' || p.len() == 1) {
        Some(digits_val(dec_digits(p)) as u64)
    } else {
        None
    }
}

fn parse_version_part(s: &Vec<u8>, start: usize, end: usize) -> (r: Option<u64>)
    requires
        start <= end <= s.len(),
    ensures
        r == version_part(s@.subrange(start as int, end as int)),
{
    if start >= end || end - start > 9 {
        return None;
    }
    proof {
        lemma_version_part(s@, start as int, end as int);
    }
    if s[start] == b'0' && end - start > 1 {
        return None;
    }
    let mut v: u64 = 0;
    let mut i = start;
    proof {
        assert(dec_digits(s@.subrange(start as int, start as int)) =~= Seq::<u8>::empty());
    }
    while i < end
        invariant
            start < end <= s.len(),
            end - start <= 9,
            start <= i <= end,
            forall|k: int| start <= k < i ==> digit(#[trigger] s@[k]),
            v as nat == digits_val(dec_digits(s@.subrange(start as int, i as int))),
            v < pow10((i - start) as nat),
        decreases end - i,
    {
        if s[i] < b'0' || s[i] > b'9' {
            proof {
                assert(s@.subrange(start as int, end as int)[i - start] == s@[i as int]);
            }
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
    proof {
        lemma_version_part(s@, start as int, end as int);
    }
    Some(v)
}

// MUST-010: version / minVersion の構文
pub open spec fn version_s(v: Seq<u8>) -> Option<(u64, u64)> {
    let dot = first_byte(v, 0, v.len() as int, b'.');
    if dot >= v.len() {
        None
    } else {
        match (version_part(v.subrange(0, dot)), version_part(v.subrange(dot + 1, v.len() as int))) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        }
    }
}

// MUST-010: version / minVersion の構文
pub(crate) fn parse_version(s: &Vec<u8>) -> (r: Option<(u64, u64)>)
    ensures
        r == version_s(s@),
{
    let mut dot = 0;
    while dot < s.len() && s[dot] != b'.'
        invariant
            0 <= dot <= s.len(),
            forall|k: int| 0 <= k < dot ==> #[trigger] s@[k] != b'.',
        decreases s.len() - dot,
    {
        dot += 1;
    }
    proof {
        lemma_first_byte_unique(s@, 0, s.len() as int, b'.', dot as int);
    }
    if dot >= s.len() {
        return None;
    }
    match parse_version_part(s, 0, dot) {
        None => None,
        Some(a) => match parse_version_part(s, dot + 1, s.len()) {
            None => None,
            Some(b) => Some((a, b)),
        },
    }
}

} // verus!
