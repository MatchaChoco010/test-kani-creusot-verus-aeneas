use creusot_std::prelude::*;
use crate::json::*;
use crate::json::number::*;
use crate::model::*;
use crate::read::access::*;
#[cfg(creusot)]
use crate::validate::mesh::*;

#[logic(open, inline)]
pub fn f_uint_req(o: JObj, k: Seq<u8>, x: u64) -> bool {
    pearlite! { p_uint(o, k) == Ok(Some(x@)) }
}

#[logic(open, inline)]
pub fn f_uint_def(o: JObj, k: Seq<u8>, def: Int, x: u64) -> bool {
    pearlite! { match p_uint(o, k) { Ok(None) => x@ == def, Ok(Some(v)) => x@ == v, Err(()) => false } }
}

#[logic(open, inline)]
pub fn rd_texture_info_o(o: JObj, extra: Int, x: TextureInfo) -> bool {
    pearlite! {
        ext_ok(o) && f_uint_req(o, key_index(), x.index) && f_uint_def(o, key_tex_coord(), 0, x.tex_coord)
                && (extra == 1 ==> p_number(o, key_scale()) != Err(()))
                && (extra == 2 ==> p_number(o, key_strength()) != Err(()))
    }
}

#[logic(open)]
pub fn key_index() -> Seq<u8> {
    pearlite! { seq![105u8, 110u8, 100u8, 101u8, 120u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 105u8 && s[1] == 110u8 && s[2] == 100u8 && s[3] == 101u8 && s[4] == 120u8 ==> seq_is(key_index(), s))]
pub fn lemma_key_index(s: Seq<u8>) {}

#[logic(open)]
pub fn key_scale() -> Seq<u8> {
    pearlite! { seq![115u8, 99u8, 97u8, 108u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 115u8 && s[1] == 99u8 && s[2] == 97u8 && s[3] == 108u8 && s[4] == 101u8 ==> seq_is(key_scale(), s))]
pub fn lemma_key_scale(s: Seq<u8>) {}

#[logic(open)]
pub fn key_strength() -> Seq<u8> {
    pearlite! { seq![115u8, 116u8, 114u8, 101u8, 110u8, 103u8, 116u8, 104u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 115u8 && s[1] == 116u8 && s[2] == 114u8 && s[3] == 101u8 && s[4] == 110u8 && s[5] == 103u8 && s[6] == 116u8 && s[7] == 104u8 ==> seq_is(key_strength(), s))]
pub fn lemma_key_strength(s: Seq<u8>) {}

#[logic(open)]
pub fn key_tex_coord() -> Seq<u8> {
    pearlite! { seq![116u8, 101u8, 120u8, 67u8, 111u8, 111u8, 114u8, 100u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 116u8 && s[1] == 101u8 && s[2] == 120u8 && s[3] == 67u8 && s[4] == 111u8 && s[5] == 111u8 && s[6] == 114u8 && s[7] == 100u8 ==> seq_is(key_tex_coord(), s))]
pub fn lemma_key_tex_coord(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_texture_info_o(obj_or_nil(tree(d@, id@)), extra@, x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: TextureInfo> !(is_object(tree(d@, id@)) && rd_texture_info_o(obj_or_nil(tree(d@, id@)), extra@, y)),
})]
#[check(terminates)]
fn read_texture_info(d: &Vec<JsonNode>, id: usize, extra: u64, ext: &mut Vec<Vec<u8>>) -> Result<TextureInfo, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_index(Seq::empty()));
    snapshot!(lemma_key_tex_coord(Seq::empty()));
    snapshot!(lemma_key_scale(Seq::empty()));
    snapshot!(lemma_key_strength(Seq::empty()));
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

// textureInfo（extra 1: normalTextureInfo の scale, extra 2: occlusionTextureInfo の strength）
#[logic(open)]
pub fn rd_texture_info(j: JsonS, extra: Int, x: TextureInfo) -> bool {
    pearlite! { is_object(j) && rd_texture_info_o(obj_or_nil(j), extra, x) }
}

#[logic(open)]
pub fn ext_obj(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_here(obj_or_nil(j), x) }
}

#[logic(open, inline)]
pub fn f_tex_opt(o: JObj, k: Seq<u8>, extra: Int, x: Option<TextureInfo>) -> bool {
    pearlite! {
        match lookup(o, k) {
            None => x == None,
            Some(v) => match x { Some(t) => rd_texture_info(v, extra, t), None => false },
        }
    }
}

#[logic(open, inline)]
pub fn ext_opt(o: JObj, k: Seq<u8>, x: Seq<u8>) -> bool {
    pearlite! { match lookup(o, k) { Some(v) => ext_obj(v, x), None => false } }
}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(forall<k: Seq<u8>> #[trigger(lookup(obj_of(d@, o@), k))] seq_is(k, key@) ==> match result {
    Ok(t) => f_tex_opt(obj_of(d@, o@), k, extra@, t) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_opt(obj_of(d@, o@), k, x))),
    Err(()) => forall<t: Option<TextureInfo>> !f_tex_opt(obj_of(d@, o@), k, extra@, t),
})]
#[check(terminates)]
fn opt_texture_info(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8], extra: u64, ext: &mut Vec<Vec<u8>>) -> Result<Option<TextureInfo>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    match find_member(o, key) {
        None => Ok(None),
        Some(i) => match read_texture_info(d, o[i].value, extra, ext) {
            Ok(t) => Ok(Some(t)),
            Err(()) => Err(()),
        },
    }
}

#[logic(open, inline)]
pub fn rd_pbr(o: JObj, b: Option<TextureInfo>, m: Option<TextureInfo>) -> bool {
    pearlite! {
        match p_object(o, key_pbr_metallic_roughness()) {
            Err(()) => false,
            Ok(None) => b == None && m == None,
            Ok(Some(p)) => ext_ok(p)
                && p_number_array(p, key_base_color_factor(), 4u64@) != Err(())
                && p_number(p, key_metallic_factor()) != Err(())
                && p_number(p, key_roughness_factor()) != Err(())
                && f_tex_opt(p, key_base_color_texture(), 0, b)
                && f_tex_opt(p, key_metallic_roughness_texture(), 0, m),
        }
    }
}

#[logic(open, inline)]
pub fn rd_material_o(o: JObj, x: Material) -> bool {
    pearlite! {
        cor_ok(o) && rd_pbr(o, x.base_color_texture, x.metallic_roughness_texture)
                && f_tex_opt(o, key_normal_texture(), 1, x.normal_texture)
                && f_tex_opt(o, key_occlusion_texture(), 2, x.occlusion_texture)
                && f_tex_opt(o, key_emissive_texture(), 0, x.emissive_texture)
                && p_number_array(o, key_emissive_factor(), 3u64@) != Err(())
                && p_string(o, key_alpha_mode()) != Err(())
                && p_number(o, key_alpha_cutoff()) != Err(())
                && p_bool(o, key_double_sided()) != Err(())
    }
}

#[logic(open, inline)]
pub fn ext_material_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x)
                || ext_pbr(o, x)
                || ext_opt(o, key_normal_texture(), x) || ext_opt(o, key_occlusion_texture(), x) || ext_opt(o, key_emissive_texture(), x)
    }
}

#[logic(open, inline)]
pub fn ext_pbr(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_object(o, key_pbr_metallic_roughness()) {
            Ok(Some(p)) => ext_here(p, x) || ext_opt(p, key_base_color_texture(), x) || ext_opt(p, key_metallic_roughness_texture(), x),
            _ => false,
        }
    }
}

#[logic(open)]
pub fn key_alpha_cutoff() -> Seq<u8> {
    pearlite! { seq![97u8, 108u8, 112u8, 104u8, 97u8, 67u8, 117u8, 116u8, 111u8, 102u8, 102u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 97u8 && s[1] == 108u8 && s[2] == 112u8 && s[3] == 104u8 && s[4] == 97u8 && s[5] == 67u8 && s[6] == 117u8 && s[7] == 116u8 && s[8] == 111u8 && s[9] == 102u8 && s[10] == 102u8 ==> seq_is(key_alpha_cutoff(), s))]
pub fn lemma_key_alpha_cutoff(s: Seq<u8>) {}

#[logic(open)]
pub fn key_alpha_mode() -> Seq<u8> {
    pearlite! { seq![97u8, 108u8, 112u8, 104u8, 97u8, 77u8, 111u8, 100u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 97u8 && s[1] == 108u8 && s[2] == 112u8 && s[3] == 104u8 && s[4] == 97u8 && s[5] == 77u8 && s[6] == 111u8 && s[7] == 100u8 && s[8] == 101u8 ==> seq_is(key_alpha_mode(), s))]
pub fn lemma_key_alpha_mode(s: Seq<u8>) {}

#[logic(open)]
pub fn key_base_color_factor() -> Seq<u8> {
    pearlite! { seq![98u8, 97u8, 115u8, 101u8, 67u8, 111u8, 108u8, 111u8, 114u8, 70u8, 97u8, 99u8, 116u8, 111u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 15 && s[0] == 98u8 && s[1] == 97u8 && s[2] == 115u8 && s[3] == 101u8 && s[4] == 67u8 && s[5] == 111u8 && s[6] == 108u8 && s[7] == 111u8 && s[8] == 114u8 && s[9] == 70u8 && s[10] == 97u8 && s[11] == 99u8 && s[12] == 116u8 && s[13] == 111u8 && s[14] == 114u8 ==> seq_is(key_base_color_factor(), s))]
pub fn lemma_key_base_color_factor(s: Seq<u8>) {}

#[logic(open)]
pub fn key_base_color_texture() -> Seq<u8> {
    pearlite! { seq![98u8, 97u8, 115u8, 101u8, 67u8, 111u8, 108u8, 111u8, 114u8, 84u8, 101u8, 120u8, 116u8, 117u8, 114u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 16 && s[0] == 98u8 && s[1] == 97u8 && s[2] == 115u8 && s[3] == 101u8 && s[4] == 67u8 && s[5] == 111u8 && s[6] == 108u8 && s[7] == 111u8 && s[8] == 114u8 && s[9] == 84u8 && s[10] == 101u8 && s[11] == 120u8 && s[12] == 116u8 && s[13] == 117u8 && s[14] == 114u8 && s[15] == 101u8 ==> seq_is(key_base_color_texture(), s))]
pub fn lemma_key_base_color_texture(s: Seq<u8>) {}

#[logic(open)]
pub fn key_double_sided() -> Seq<u8> {
    pearlite! { seq![100u8, 111u8, 117u8, 98u8, 108u8, 101u8, 83u8, 105u8, 100u8, 101u8, 100u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 100u8 && s[1] == 111u8 && s[2] == 117u8 && s[3] == 98u8 && s[4] == 108u8 && s[5] == 101u8 && s[6] == 83u8 && s[7] == 105u8 && s[8] == 100u8 && s[9] == 101u8 && s[10] == 100u8 ==> seq_is(key_double_sided(), s))]
pub fn lemma_key_double_sided(s: Seq<u8>) {}

#[logic(open)]
pub fn key_emissive_factor() -> Seq<u8> {
    pearlite! { seq![101u8, 109u8, 105u8, 115u8, 115u8, 105u8, 118u8, 101u8, 70u8, 97u8, 99u8, 116u8, 111u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 14 && s[0] == 101u8 && s[1] == 109u8 && s[2] == 105u8 && s[3] == 115u8 && s[4] == 115u8 && s[5] == 105u8 && s[6] == 118u8 && s[7] == 101u8 && s[8] == 70u8 && s[9] == 97u8 && s[10] == 99u8 && s[11] == 116u8 && s[12] == 111u8 && s[13] == 114u8 ==> seq_is(key_emissive_factor(), s))]
pub fn lemma_key_emissive_factor(s: Seq<u8>) {}

#[logic(open)]
pub fn key_emissive_texture() -> Seq<u8> {
    pearlite! { seq![101u8, 109u8, 105u8, 115u8, 115u8, 105u8, 118u8, 101u8, 84u8, 101u8, 120u8, 116u8, 117u8, 114u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 15 && s[0] == 101u8 && s[1] == 109u8 && s[2] == 105u8 && s[3] == 115u8 && s[4] == 115u8 && s[5] == 105u8 && s[6] == 118u8 && s[7] == 101u8 && s[8] == 84u8 && s[9] == 101u8 && s[10] == 120u8 && s[11] == 116u8 && s[12] == 117u8 && s[13] == 114u8 && s[14] == 101u8 ==> seq_is(key_emissive_texture(), s))]
pub fn lemma_key_emissive_texture(s: Seq<u8>) {}

#[logic(open)]
pub fn key_metallic_factor() -> Seq<u8> {
    pearlite! { seq![109u8, 101u8, 116u8, 97u8, 108u8, 108u8, 105u8, 99u8, 70u8, 97u8, 99u8, 116u8, 111u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 14 && s[0] == 109u8 && s[1] == 101u8 && s[2] == 116u8 && s[3] == 97u8 && s[4] == 108u8 && s[5] == 108u8 && s[6] == 105u8 && s[7] == 99u8 && s[8] == 70u8 && s[9] == 97u8 && s[10] == 99u8 && s[11] == 116u8 && s[12] == 111u8 && s[13] == 114u8 ==> seq_is(key_metallic_factor(), s))]
pub fn lemma_key_metallic_factor(s: Seq<u8>) {}

#[logic(open)]
pub fn key_metallic_roughness_texture() -> Seq<u8> {
    pearlite! { seq![109u8, 101u8, 116u8, 97u8, 108u8, 108u8, 105u8, 99u8, 82u8, 111u8, 117u8, 103u8, 104u8, 110u8, 101u8, 115u8, 115u8, 84u8, 101u8, 120u8, 116u8, 117u8, 114u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 24 && s[0] == 109u8 && s[1] == 101u8 && s[2] == 116u8 && s[3] == 97u8 && s[4] == 108u8 && s[5] == 108u8 && s[6] == 105u8 && s[7] == 99u8 && s[8] == 82u8 && s[9] == 111u8 && s[10] == 117u8 && s[11] == 103u8 && s[12] == 104u8 && s[13] == 110u8 && s[14] == 101u8 && s[15] == 115u8 && s[16] == 115u8 && s[17] == 84u8 && s[18] == 101u8 && s[19] == 120u8 && s[20] == 116u8 && s[21] == 117u8 && s[22] == 114u8 && s[23] == 101u8 ==> seq_is(key_metallic_roughness_texture(), s))]
pub fn lemma_key_metallic_roughness_texture(s: Seq<u8>) {}

#[logic(open)]
pub fn key_normal_texture() -> Seq<u8> {
    pearlite! { seq![110u8, 111u8, 114u8, 109u8, 97u8, 108u8, 84u8, 101u8, 120u8, 116u8, 117u8, 114u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 13 && s[0] == 110u8 && s[1] == 111u8 && s[2] == 114u8 && s[3] == 109u8 && s[4] == 97u8 && s[5] == 108u8 && s[6] == 84u8 && s[7] == 101u8 && s[8] == 120u8 && s[9] == 116u8 && s[10] == 117u8 && s[11] == 114u8 && s[12] == 101u8 ==> seq_is(key_normal_texture(), s))]
pub fn lemma_key_normal_texture(s: Seq<u8>) {}

#[logic(open)]
pub fn key_occlusion_texture() -> Seq<u8> {
    pearlite! { seq![111u8, 99u8, 99u8, 108u8, 117u8, 115u8, 105u8, 111u8, 110u8, 84u8, 101u8, 120u8, 116u8, 117u8, 114u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 16 && s[0] == 111u8 && s[1] == 99u8 && s[2] == 99u8 && s[3] == 108u8 && s[4] == 117u8 && s[5] == 115u8 && s[6] == 105u8 && s[7] == 111u8 && s[8] == 110u8 && s[9] == 84u8 && s[10] == 101u8 && s[11] == 120u8 && s[12] == 116u8 && s[13] == 117u8 && s[14] == 114u8 && s[15] == 101u8 ==> seq_is(key_occlusion_texture(), s))]
pub fn lemma_key_occlusion_texture(s: Seq<u8>) {}

#[logic(open)]
pub fn key_pbr_metallic_roughness() -> Seq<u8> {
    pearlite! { seq![112u8, 98u8, 114u8, 77u8, 101u8, 116u8, 97u8, 108u8, 108u8, 105u8, 99u8, 82u8, 111u8, 117u8, 103u8, 104u8, 110u8, 101u8, 115u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 20 && s[0] == 112u8 && s[1] == 98u8 && s[2] == 114u8 && s[3] == 77u8 && s[4] == 101u8 && s[5] == 116u8 && s[6] == 97u8 && s[7] == 108u8 && s[8] == 108u8 && s[9] == 105u8 && s[10] == 99u8 && s[11] == 82u8 && s[12] == 111u8 && s[13] == 117u8 && s[14] == 103u8 && s[15] == 104u8 && s[16] == 110u8 && s[17] == 101u8 && s[18] == 115u8 && s[19] == 115u8 ==> seq_is(key_pbr_metallic_roughness(), s))]
pub fn lemma_key_pbr_metallic_roughness(s: Seq<u8>) {}

#[logic(open)]
pub fn key_roughness_factor() -> Seq<u8> {
    pearlite! { seq![114u8, 111u8, 117u8, 103u8, 104u8, 110u8, 101u8, 115u8, 115u8, 70u8, 97u8, 99u8, 116u8, 111u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 15 && s[0] == 114u8 && s[1] == 111u8 && s[2] == 117u8 && s[3] == 103u8 && s[4] == 104u8 && s[5] == 110u8 && s[6] == 101u8 && s[7] == 115u8 && s[8] == 115u8 && s[9] == 70u8 && s[10] == 97u8 && s[11] == 99u8 && s[12] == 116u8 && s[13] == 111u8 && s[14] == 114u8 ==> seq_is(key_roughness_factor(), s))]
pub fn lemma_key_roughness_factor(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_material_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_material_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Material> !(is_object(tree(d@, id@)) && rd_material_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_material(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Material, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_pbr_metallic_roughness(Seq::empty()));
    snapshot!(lemma_key_base_color_factor(Seq::empty()));
    snapshot!(lemma_key_metallic_factor(Seq::empty()));
    snapshot!(lemma_key_roughness_factor(Seq::empty()));
    snapshot!(lemma_key_base_color_texture(Seq::empty()));
    snapshot!(lemma_key_metallic_roughness_texture(Seq::empty()));
    snapshot!(lemma_key_normal_texture(Seq::empty()));
    snapshot!(lemma_key_occlusion_texture(Seq::empty()));
    snapshot!(lemma_key_emissive_texture(Seq::empty()));
    snapshot!(lemma_key_emissive_factor(Seq::empty()));
    snapshot!(lemma_key_alpha_mode(Seq::empty()));
    snapshot!(lemma_key_alpha_cutoff(Seq::empty()));
    snapshot!(lemma_key_double_sided(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
        let _e1 = snapshot!(ext@);
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
    proof_assert!(rd_pbr(obj_of(d@, o@), base_color_texture, metallic_roughness_texture));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e1, x) || ext_pbr(obj_of(d@, o@), x)));
    let normal_texture = match opt_texture_info(d, o, &[b'n', b'o', b'r', b'm', b'a', b'l', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 1, ext) { Ok(t) => t, Err(()) => return Err(()) };
    let occlusion_texture = match opt_texture_info(d, o, &[b'o', b'c', b'c', b'l', b'u', b's', b'i', b'o', b'n', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 2, ext) { Ok(t) => t, Err(()) => return Err(()) };
    let emissive_texture = match opt_texture_info(d, o, &[b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'T', b'e', b'x', b't', b'u', b'r', b'e'], 0, ext) { Ok(t) => t, Err(()) => return Err(()) };
    match check_number_array(d, o, &[b'e', b'm', b'i', b's', b's', b'i', b'v', b'e', b'F', b'a', b'c', b't', b'o', b'r'], 3) { Err(()) => return Err(()), Ok(_) => {} }
    match get_string(d, o, &[b'a', b'l', b'p', b'h', b'a', b'M', b'o', b'd', b'e']) { Err(()) => return Err(()), Ok(_) => {} }
    match check_number(d, o, &[b'a', b'l', b'p', b'h', b'a', b'C', b'u', b't', b'o', b'f', b'f']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_bool(d, o, &[b'd', b'o', b'u', b'b', b'l', b'e', b'S', b'i', b'd', b'e', b'd']) { Err(()) => return Err(()), Ok(_) => {} }
    Ok(Material { base_color_texture, metallic_roughness_texture, normal_texture, occlusion_texture, emissive_texture })
}

// 上書きされていないメンバーの (キー, 値) の列（メンバーの順）のうち、位置 n より前の部分
#[logic(open)]
#[variant(n)]
pub fn live_upto(o: JObj, n: Int) -> Seq<(Seq<u8>, JsonS)> {
    pearlite! {
        if n <= 0 { Seq::empty() }
        else if is_last(o, n - 1) { live_upto(o, n - 1).push_back((okey(o, n - 1), oval(o, n - 1))) }
        else { live_upto(o, n - 1) }
    }
}

#[logic(open)]
pub fn live(o: JObj) -> Seq<(Seq<u8>, JsonS)> {
    pearlite! { live_upto(o, olen(o)) }
}

// attributes / targets: 上書きされていないメンバーを順に、値は uint
// MUST-058, MUST-082: attributes と targets の要素は平らな「名前 → アクセサー」
#[logic(open)]
pub fn attrs_is(o: JObj, v: Seq<Attribute>) -> bool {
    pearlite! {
        v.len() == live(o).len()
            && forall<t> 0 <= t && t < v.len() ==> v[t].name@ == live(o)[t].0 && uint_of(live(o)[t].1) == Some(v[t].accessor@)
    }
}

// 上書きされていないメンバーの列の前の部分は伸ばしても変わらない
#[logic(opaque)]
#[variant(n)]
#[requires(0 <= i && i <= n)]
#[ensures(live_upto(o, i).len() <= live_upto(o, n).len())]
#[ensures(forall<t> 0 <= t && t < live_upto(o, i).len() ==> live_upto(o, n)[t] == live_upto(o, i)[t])]
pub fn lemma_live_prefix(o: JObj, i: Int, n: Int) {
    if i < n {
        lemma_live_prefix(o, i, n - 1)
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result { Ok(v) => attrs_is(obj_of(d@, o@), v@), Err(()) => forall<v: Seq<Attribute>> !attrs_is(obj_of(d@, o@), v) })]
#[check(terminates)]
fn attribute_entries(d: &Vec<JsonNode>, o: &Vec<Member>) -> Result<Vec<Attribute>, ()> {
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_obj_index(d@, o@));
    snapshot!(lemma_live_prefix(obj_of(d@, o@), 0, 0));
    let mut out: Vec<Attribute> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= o@.len())]
    #[invariant(out@.len() == live_upto(obj_of(d@, o@), i@).len())]
    #[invariant(forall<t> 0 <= t && t < out@.len() ==> out@[t].name@ == live_upto(obj_of(d@, o@), i@)[t].0 && uint_of(live_upto(obj_of(d@, o@), i@)[t].1) == Some(out@[t].accessor@))]
    #[variant(o@.len() - i@)]
    while i < o.len() {
        if is_last_member(o, i) {
            snapshot!(lemma_live_prefix(obj_of(d@, o@), i@ + 1, o@.len()));
            proof_assert!(live_upto(obj_of(d@, o@), i@ + 1) == live_upto(obj_of(d@, o@), i@).push_back((okey(obj_of(d@, o@), i@), oval(obj_of(d@, o@), i@))));
            match node_at(d, o[i].value) {
                Some(JsonNode::Number(n)) => match number_to_u64(n) {
                    Some(v) => out.push(Attribute { name: copy_key(&o[i].key), accessor: v }),
                    None => return Err(()),
                },
                _ => return Err(()),
            }
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_attr_map(j: JsonS, allow_empty: bool, v: Seq<Attribute>) -> bool {
    pearlite! { is_object(j) && rd_attr_map_o(obj_or_nil(j), allow_empty, v) }
}

#[logic(open, inline)]
pub fn rd_attr_map_o(o: JObj, allow_empty: bool, v: Seq<Attribute>) -> bool {
    pearlite! {
        (allow_empty || olen(o) > 0) && attrs_is(o, v)
    }
}

// MUST-058, MUST-082: attributes と targets の要素は平らな「名前 → アクセサー」
#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result { Ok(v) => rd_attr_map(tree(d@, id@), allow_empty, v@), Err(()) => forall<v: Seq<Attribute>> !rd_attr_map(tree(d@, id@), allow_empty, v) })]
#[check(terminates)]
fn read_attribute_map(d: &Vec<JsonNode>, id: usize, allow_empty: bool) -> Result<Vec<Attribute>, ()> {
    snapshot!(lemma_obj_index(d@, Seq::empty()));
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

#[logic(open, inline)]
pub fn f_uint_opt(o: JObj, k: Seq<u8>, x: Option<u64>) -> bool {
    pearlite! { p_uint(o, k) == Ok(opt_int(x)) }
}

#[logic(open, inline)]
pub fn rd_targets(o: JObj, v: Seq<Vec<Attribute>>) -> bool {
    pearlite! {
        match p_array(o, key_targets()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_attr_map(nth(l, t), true, v[t]@),
        }
    }
}

#[logic(open, inline)]
pub fn rd_primitive_o(o: JObj, x: Primitive) -> bool {
    pearlite! {
        ext_ok(o)
                && (match lookup(o, key_attributes()) { Some(a) => rd_attr_map(a, false, x.attributes@), None => false })
                && f_uint_opt(o, key_indices(), x.indices)
                && f_uint_opt(o, key_material(), x.material)
                && f_uint_def(o, key_mode(), 4, x.mode)
                && rd_targets(o, x.targets@)
    }
}

#[logic(open)]
pub fn key_attributes() -> Seq<u8> {
    pearlite! { seq![97u8, 116u8, 116u8, 114u8, 105u8, 98u8, 117u8, 116u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 97u8 && s[1] == 116u8 && s[2] == 116u8 && s[3] == 114u8 && s[4] == 105u8 && s[5] == 98u8 && s[6] == 117u8 && s[7] == 116u8 && s[8] == 101u8 && s[9] == 115u8 ==> seq_is(key_attributes(), s))]
pub fn lemma_key_attributes(s: Seq<u8>) {}

#[logic(open)]
pub fn key_indices() -> Seq<u8> {
    pearlite! { seq![105u8, 110u8, 100u8, 105u8, 99u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 105u8 && s[1] == 110u8 && s[2] == 100u8 && s[3] == 105u8 && s[4] == 99u8 && s[5] == 101u8 && s[6] == 115u8 ==> seq_is(key_indices(), s))]
pub fn lemma_key_indices(s: Seq<u8>) {}

#[logic(open)]
pub fn key_material() -> Seq<u8> {
    pearlite! { seq![109u8, 97u8, 116u8, 101u8, 114u8, 105u8, 97u8, 108u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 109u8 && s[1] == 97u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 105u8 && s[6] == 97u8 && s[7] == 108u8 ==> seq_is(key_material(), s))]
pub fn lemma_key_material(s: Seq<u8>) {}

#[logic(open)]
pub fn key_mode() -> Seq<u8> {
    pearlite! { seq![109u8, 111u8, 100u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 109u8 && s[1] == 111u8 && s[2] == 100u8 && s[3] == 101u8 ==> seq_is(key_mode(), s))]
pub fn lemma_key_mode(s: Seq<u8>) {}

#[logic(open)]
pub fn key_targets() -> Seq<u8> {
    pearlite! { seq![116u8, 97u8, 114u8, 103u8, 101u8, 116u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 116u8 && s[1] == 97u8 && s[2] == 114u8 && s[3] == 103u8 && s[4] == 101u8 && s[5] == 116u8 && s[6] == 115u8 ==> seq_is(key_targets(), s))]
pub fn lemma_key_targets(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_primitive_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Primitive> !(is_object(tree(d@, id@)) && rd_primitive_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
fn read_primitive(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Primitive, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_attributes(Seq::empty()));
    snapshot!(lemma_key_indices(Seq::empty()));
    snapshot!(lemma_key_material(Seq::empty()));
    snapshot!(lemma_key_mode(Seq::empty()));
    snapshot!(lemma_key_targets(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_extensions(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
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
    Ok(Primitive { attributes, indices, material, mode, targets })
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && forall<t> 0 <= t && t < v@.len() ==> rd_attr_map(nth(list_of(d@, a@), t), true, v@[t]@),
    Err(()) => exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<w: Seq<Attribute>> !rd_attr_map(nth(list_of(d@, a@), t), true, w),
})]
#[check(terminates)]
fn read_target_items(d: &Vec<JsonNode>, a: &Vec<usize>) -> Result<Vec<Vec<Attribute>>, ()> {
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Vec<Attribute>> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_attr_map(tree(d@, a@[t]@), true, out@[t]@))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        match read_attribute_map(d, a[i], true) {
            Ok(t) => out.push(t),
            Err(()) => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_primitive(j: JsonS, x: Primitive) -> bool {
    pearlite! { is_object(j) && rd_primitive_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_primitive(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(()) => exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Primitive> !rd_primitive(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_primitive_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Primitive>, ()> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Primitive> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_primitive(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Primitive> rd_primitive(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_primitive_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_primitive(d, a[i], ext) {
            Ok(p) => out.push(p),
            Err(()) => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open, inline)]
pub fn f_number_array_len(o: JObj, k: Seq<u8>, x: Option<u64>) -> bool {
    pearlite! { p_number_array_len(o, k) == Ok(opt_int(x)) }
}

#[logic(open, inline)]
pub fn rd_mesh_o(o: JObj, x: Mesh) -> bool {
    pearlite! {
        cor_ok(o)
                && (match p_array(o, key_primitives()) {
                    Ok(Some(l)) => jlen(l) == x.primitives@.len() && forall<t> 0 <= t && t < jlen(l) ==> rd_primitive(nth(l, t), x.primitives@[t]),
                    _ => false,
                })
                && f_number_array_len(o, key_weights(), x.weights_len)
    }
}

#[logic(open, inline)]
pub fn ext_mesh_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x) || match p_array(o, key_primitives()) {
                Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x),
                _ => false,
            }
    }
}

#[logic(open)]
pub fn key_primitives() -> Seq<u8> {
    pearlite! { seq![112u8, 114u8, 105u8, 109u8, 105u8, 116u8, 105u8, 118u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 112u8 && s[1] == 114u8 && s[2] == 105u8 && s[3] == 109u8 && s[4] == 105u8 && s[5] == 116u8 && s[6] == 105u8 && s[7] == 118u8 && s[8] == 101u8 && s[9] == 115u8 ==> seq_is(key_primitives(), s))]
pub fn lemma_key_primitives(s: Seq<u8>) {}

#[logic(open)]
pub fn key_weights() -> Seq<u8> {
    pearlite! { seq![119u8, 101u8, 105u8, 103u8, 104u8, 116u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 119u8 && s[1] == 101u8 && s[2] == 105u8 && s[3] == 103u8 && s[4] == 104u8 && s[5] == 116u8 && s[6] == 115u8 ==> seq_is(key_weights(), s))]
pub fn lemma_key_weights(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_mesh_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_mesh_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Mesh> !(is_object(tree(d@, id@)) && rd_mesh_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_mesh(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Mesh, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_primitives(Seq::empty()));
    snapshot!(lemma_key_weights(Seq::empty()));
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

#[logic(open, inline)]
pub fn f_uint_array(o: JObj, k: Seq<u8>, v: Seq<u64>) -> bool {
    pearlite! { match p_array(o, k) { Err(()) => false, Ok(None) => v.len() == 0, Ok(Some(l)) => uints_is(l, v) } }
}

#[logic(open, inline)]
pub fn rd_node_o(o: JObj, x: Node) -> bool {
    pearlite! {
        cor_ok(o)
                && f_uint_array(o, key_children(), x.children@)
                && f_uint_opt(o, key_mesh(), x.mesh)
                && f_uint_opt(o, key_camera(), x.camera)
                && f_uint_opt(o, key_skin(), x.skin)
                && p_number_array(o, key_matrix(), 16u64@) == Ok(x.has_matrix)
                && p_number_array(o, key_translation(), 3u64@) != Err(())
                && p_number_array(o, key_rotation(), 4u64@) != Err(())
                && p_number_array(o, key_scale(), 3u64@) != Err(())
                && x.has_trs == (p_number_array(o, key_translation(), 3u64@) == Ok(true)
                    || p_number_array(o, key_rotation(), 4u64@) == Ok(true)
                    || p_number_array(o, key_scale(), 3u64@) == Ok(true))
                && f_number_array_len(o, key_weights(), x.weights_len)
    }
}

#[logic(open)]
pub fn key_camera() -> Seq<u8> {
    pearlite! { seq![99u8, 97u8, 109u8, 101u8, 114u8, 97u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 99u8 && s[1] == 97u8 && s[2] == 109u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 97u8 ==> seq_is(key_camera(), s))]
pub fn lemma_key_camera(s: Seq<u8>) {}

#[logic(open)]
pub fn key_children() -> Seq<u8> {
    pearlite! { seq![99u8, 104u8, 105u8, 108u8, 100u8, 114u8, 101u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 99u8 && s[1] == 104u8 && s[2] == 105u8 && s[3] == 108u8 && s[4] == 100u8 && s[5] == 114u8 && s[6] == 101u8 && s[7] == 110u8 ==> seq_is(key_children(), s))]
pub fn lemma_key_children(s: Seq<u8>) {}

#[logic(open)]
pub fn key_matrix() -> Seq<u8> {
    pearlite! { seq![109u8, 97u8, 116u8, 114u8, 105u8, 120u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 109u8 && s[1] == 97u8 && s[2] == 116u8 && s[3] == 114u8 && s[4] == 105u8 && s[5] == 120u8 ==> seq_is(key_matrix(), s))]
pub fn lemma_key_matrix(s: Seq<u8>) {}

#[logic(open)]
pub fn key_mesh() -> Seq<u8> {
    pearlite! { seq![109u8, 101u8, 115u8, 104u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 109u8 && s[1] == 101u8 && s[2] == 115u8 && s[3] == 104u8 ==> seq_is(key_mesh(), s))]
pub fn lemma_key_mesh(s: Seq<u8>) {}

#[logic(open)]
pub fn key_rotation() -> Seq<u8> {
    pearlite! { seq![114u8, 111u8, 116u8, 97u8, 116u8, 105u8, 111u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 114u8 && s[1] == 111u8 && s[2] == 116u8 && s[3] == 97u8 && s[4] == 116u8 && s[5] == 105u8 && s[6] == 111u8 && s[7] == 110u8 ==> seq_is(key_rotation(), s))]
pub fn lemma_key_rotation(s: Seq<u8>) {}

#[logic(open)]
pub fn key_skin() -> Seq<u8> {
    pearlite! { seq![115u8, 107u8, 105u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 115u8 && s[1] == 107u8 && s[2] == 105u8 && s[3] == 110u8 ==> seq_is(key_skin(), s))]
pub fn lemma_key_skin(s: Seq<u8>) {}

#[logic(open)]
pub fn key_translation() -> Seq<u8> {
    pearlite! { seq![116u8, 114u8, 97u8, 110u8, 115u8, 108u8, 97u8, 116u8, 105u8, 111u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 116u8 && s[1] == 114u8 && s[2] == 97u8 && s[3] == 110u8 && s[4] == 115u8 && s[5] == 108u8 && s[6] == 97u8 && s[7] == 116u8 && s[8] == 105u8 && s[9] == 111u8 && s[10] == 110u8 ==> seq_is(key_translation(), s))]
pub fn lemma_key_translation(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_node_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Node> !(is_object(tree(d@, id@)) && rd_node_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_node(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Node, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_children(Seq::empty()));
    snapshot!(lemma_key_mesh(Seq::empty()));
    snapshot!(lemma_key_camera(Seq::empty()));
    snapshot!(lemma_key_skin(Seq::empty()));
    snapshot!(lemma_key_matrix(Seq::empty()));
    snapshot!(lemma_key_translation(Seq::empty()));
    snapshot!(lemma_key_rotation(Seq::empty()));
    snapshot!(lemma_key_scale(Seq::empty()));
    snapshot!(lemma_key_weights(Seq::empty()));
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

#[logic(open, inline)]
pub fn rd_scene_o(o: JObj, x: Scene) -> bool {
    pearlite! {
        cor_ok(o) && f_uint_array(o, key_nodes(), x.nodes@)
    }
}

#[logic(open)]
pub fn key_nodes() -> Seq<u8> {
    pearlite! { seq![110u8, 111u8, 100u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 110u8 && s[1] == 111u8 && s[2] == 100u8 && s[3] == 101u8 && s[4] == 115u8 ==> seq_is(key_nodes(), s))]
pub fn lemma_key_nodes(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_scene_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Scene> !(is_object(tree(d@, id@)) && rd_scene_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_scene(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Scene, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_nodes(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let nodes = match get_uint_array(d, o, &[b'n', b'o', b'd', b'e', b's']) {
        Ok(Some(c)) => c,
        Ok(None) => Vec::new(),
        Err(()) => return Err(()),
    };
    Ok(Scene { nodes })
}

// accessor の type。SCALAR/VEC2/VEC3/VEC4/MAT2/MAT3/MAT4 → (components, is_matrix)
#[logic(open)]
pub fn type_spec(t: Seq<u8>) -> Option<(Int, bool)> {
    pearlite! {
        if seq_is(t, key_scalar()) { Some((1, false)) }
        else if seq_is(t, key_vec2()) { Some((2, false)) }
        else if seq_is(t, key_vec3()) { Some((3, false)) }
        else if seq_is(t, key_vec4()) { Some((4, false)) }
        else if seq_is(t, key_mat2()) { Some((4, true)) }
        else if seq_is(t, key_mat3()) { Some((9, true)) }
        else if seq_is(t, key_mat4()) { Some((16, true)) }
        else { None }
    }
}

#[logic(open)]
pub fn key_mat2() -> Seq<u8> {
    pearlite! { seq![77u8, 65u8, 84u8, 50u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 77u8 && s[1] == 65u8 && s[2] == 84u8 && s[3] == 50u8 ==> seq_is(key_mat2(), s))]
pub fn lemma_key_mat2(s: Seq<u8>) {}

#[logic(open)]
pub fn key_mat3() -> Seq<u8> {
    pearlite! { seq![77u8, 65u8, 84u8, 51u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 77u8 && s[1] == 65u8 && s[2] == 84u8 && s[3] == 51u8 ==> seq_is(key_mat3(), s))]
pub fn lemma_key_mat3(s: Seq<u8>) {}

#[logic(open)]
pub fn key_mat4() -> Seq<u8> {
    pearlite! { seq![77u8, 65u8, 84u8, 52u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 77u8 && s[1] == 65u8 && s[2] == 84u8 && s[3] == 52u8 ==> seq_is(key_mat4(), s))]
pub fn lemma_key_mat4(s: Seq<u8>) {}

#[logic(open)]
pub fn key_scalar() -> Seq<u8> {
    pearlite! { seq![83u8, 67u8, 65u8, 76u8, 65u8, 82u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 83u8 && s[1] == 67u8 && s[2] == 65u8 && s[3] == 76u8 && s[4] == 65u8 && s[5] == 82u8 ==> seq_is(key_scalar(), s))]
pub fn lemma_key_scalar(s: Seq<u8>) {}

#[logic(open)]
pub fn key_vec2() -> Seq<u8> {
    pearlite! { seq![86u8, 69u8, 67u8, 50u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 86u8 && s[1] == 69u8 && s[2] == 67u8 && s[3] == 50u8 ==> seq_is(key_vec2(), s))]
pub fn lemma_key_vec2(s: Seq<u8>) {}

#[logic(open)]
pub fn key_vec3() -> Seq<u8> {
    pearlite! { seq![86u8, 69u8, 67u8, 51u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 86u8 && s[1] == 69u8 && s[2] == 67u8 && s[3] == 51u8 ==> seq_is(key_vec3(), s))]
pub fn lemma_key_vec3(s: Seq<u8>) {}

#[logic(open)]
pub fn key_vec4() -> Seq<u8> {
    pearlite! { seq![86u8, 69u8, 67u8, 52u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 86u8 && s[1] == 69u8 && s[2] == 67u8 && s[3] == 52u8 ==> seq_is(key_vec4(), s))]
pub fn lemma_key_vec4(s: Seq<u8>) {}

#[ensures(match result { Some((c, m)) => type_spec(t@) == Some((c@, m)), None => type_spec(t@) == None })]
#[check(terminates)]
fn type_components(t: &Vec<u8>) -> Option<(u64, bool)> {
    snapshot!(lemma_key_scalar(Seq::empty()));
    snapshot!(lemma_key_vec2(Seq::empty()));
    snapshot!(lemma_key_vec3(Seq::empty()));
    snapshot!(lemma_key_vec4(Seq::empty()));
    snapshot!(lemma_key_mat2(Seq::empty()));
    snapshot!(lemma_key_mat3(Seq::empty()));
    snapshot!(lemma_key_mat4(Seq::empty()));
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

// MUST-043: sparse の必須プロパティ
#[logic(open, inline)]
pub fn rd_sparse_o(o: JObj, x: Sparse) -> bool {
    pearlite! {
        ext_ok(o) && f_uint_req(o, key_count(), x.count)
                && (match p_object(o, key_indices()) {
                    Ok(Some(i)) => ext_ok(i) && f_uint_req(i, key_buffer_view(), x.indices_buffer_view)
                        && f_uint_def(i, key_byte_offset(), 0, x.indices_byte_offset)
                        && f_uint_req(i, key_component_type(), x.indices_component_type),
                    _ => false,
                })
                && (match p_object(o, key_values()) {
                    Ok(Some(v)) => ext_ok(v) && f_uint_req(v, key_buffer_view(), x.values_buffer_view)
                        && f_uint_def(v, key_byte_offset(), 0, x.values_byte_offset),
                    _ => false,
                })
    }
}

#[logic(open, inline)]
pub fn ext_sparse_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x)
                || (match p_object(o, key_indices()) { Ok(Some(i)) => ext_here(i, x), _ => false })
                || (match p_object(o, key_values()) { Ok(Some(v)) => ext_here(v, x), _ => false })
    }
}

#[logic(open)]
pub fn key_buffer_view() -> Seq<u8> {
    pearlite! { seq![98u8, 117u8, 102u8, 102u8, 101u8, 114u8, 86u8, 105u8, 101u8, 119u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 98u8 && s[1] == 117u8 && s[2] == 102u8 && s[3] == 102u8 && s[4] == 101u8 && s[5] == 114u8 && s[6] == 86u8 && s[7] == 105u8 && s[8] == 101u8 && s[9] == 119u8 ==> seq_is(key_buffer_view(), s))]
pub fn lemma_key_buffer_view(s: Seq<u8>) {}

#[logic(open)]
pub fn key_byte_offset() -> Seq<u8> {
    pearlite! { seq![98u8, 121u8, 116u8, 101u8, 79u8, 102u8, 102u8, 115u8, 101u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 98u8 && s[1] == 121u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 79u8 && s[5] == 102u8 && s[6] == 102u8 && s[7] == 115u8 && s[8] == 101u8 && s[9] == 116u8 ==> seq_is(key_byte_offset(), s))]
pub fn lemma_key_byte_offset(s: Seq<u8>) {}

#[logic(open)]
pub fn key_component_type() -> Seq<u8> {
    pearlite! { seq![99u8, 111u8, 109u8, 112u8, 111u8, 110u8, 101u8, 110u8, 116u8, 84u8, 121u8, 112u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 13 && s[0] == 99u8 && s[1] == 111u8 && s[2] == 109u8 && s[3] == 112u8 && s[4] == 111u8 && s[5] == 110u8 && s[6] == 101u8 && s[7] == 110u8 && s[8] == 116u8 && s[9] == 84u8 && s[10] == 121u8 && s[11] == 112u8 && s[12] == 101u8 ==> seq_is(key_component_type(), s))]
pub fn lemma_key_component_type(s: Seq<u8>) {}

#[logic(open)]
pub fn key_count() -> Seq<u8> {
    pearlite! { seq![99u8, 111u8, 117u8, 110u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 99u8 && s[1] == 111u8 && s[2] == 117u8 && s[3] == 110u8 && s[4] == 116u8 ==> seq_is(key_count(), s))]
pub fn lemma_key_count(s: Seq<u8>) {}

#[logic(open)]
pub fn key_values() -> Seq<u8> {
    pearlite! { seq![118u8, 97u8, 108u8, 117u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 118u8 && s[1] == 97u8 && s[2] == 108u8 && s[3] == 117u8 && s[4] == 101u8 && s[5] == 115u8 ==> seq_is(key_values(), s))]
pub fn lemma_key_values(s: Seq<u8>) {}

// MUST-043: sparse の必須プロパティ
#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_sparse_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_sparse_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Sparse> !(is_object(tree(d@, id@)) && rd_sparse_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
fn read_sparse(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Sparse, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_count(Seq::empty()));
    snapshot!(lemma_key_indices(Seq::empty()));
    snapshot!(lemma_key_buffer_view(Seq::empty()));
    snapshot!(lemma_key_byte_offset(Seq::empty()));
    snapshot!(lemma_key_component_type(Seq::empty()));
    snapshot!(lemma_key_values(Seq::empty()));
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

#[logic(open, inline)]
pub fn f_bool_def(o: JObj, k: Seq<u8>, def: bool, x: bool) -> bool {
    pearlite! { match p_bool(o, k) { Ok(None) => x == def, Ok(Some(b)) => x == b, Err(()) => false } }
}

#[logic(open)]
pub fn rd_sparse(j: JsonS, x: Sparse) -> bool {
    pearlite! { is_object(j) && rd_sparse_o(obj_or_nil(j), x) }
}

#[logic(open)]
pub fn ext_sparse(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_sparse_o(obj_or_nil(j), x) }
}

#[logic(open, inline)]
pub fn rd_accessor_o(o: JObj, x: Accessor, strict: bool) -> bool {
    pearlite! {
        cor_ok(o)
                && f_uint_opt(o, key_buffer_view(), x.buffer_view)
                && f_uint_opt(o, key_byte_offset(), x.byte_offset)
                && f_uint_req(o, key_component_type(), x.component_type)
                && f_bool_def(o, key_normalized(), false, x.normalized)
                && f_uint_req(o, key_count(), x.count)
                && (match p_string(o, key_type()) {
                    Ok(Some(t)) => match type_spec(t) {
                        Some((c, m)) => x.components@ == c && x.is_matrix == m,
                        None => !strict,
                    },
                    _ => false,
                })
                && f_number_array_len(o, key_min(), x.min_len)
                && f_number_array_len(o, key_max(), x.max_len)
                && (match lookup(o, key_sparse()) {
                    None => x.sparse == None,
                    Some(sp) => match x.sparse { Some(y) => rd_sparse(sp, y), None => false },
                })
    }
}

// (U): accessor の type が既知の値でない
#[logic(open)]
pub fn unsup_accessor(j: JsonS) -> bool {
    pearlite! { is_object(j) && unsup_accessor_o(obj_or_nil(j)) }
}

#[logic(open, inline)]
pub fn unsup_accessor_o(o: JObj) -> bool {
    pearlite! {
        match p_string(o, key_type()) { Ok(Some(t)) => type_spec(t) == None, _ => false }
    }
}

#[logic(open, inline)]
pub fn ext_accessor_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x) || match lookup(o, key_sparse()) { Some(sp) => ext_sparse(sp, x), None => false }
    }
}

#[logic(open)]
pub fn key_max() -> Seq<u8> {
    pearlite! { seq![109u8, 97u8, 120u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 3 && s[0] == 109u8 && s[1] == 97u8 && s[2] == 120u8 ==> seq_is(key_max(), s))]
pub fn lemma_key_max(s: Seq<u8>) {}

#[logic(open)]
pub fn key_min() -> Seq<u8> {
    pearlite! { seq![109u8, 105u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 3 && s[0] == 109u8 && s[1] == 105u8 && s[2] == 110u8 ==> seq_is(key_min(), s))]
pub fn lemma_key_min(s: Seq<u8>) {}

#[logic(open)]
pub fn key_normalized() -> Seq<u8> {
    pearlite! { seq![110u8, 111u8, 114u8, 109u8, 97u8, 108u8, 105u8, 122u8, 101u8, 100u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 110u8 && s[1] == 111u8 && s[2] == 114u8 && s[3] == 109u8 && s[4] == 97u8 && s[5] == 108u8 && s[6] == 105u8 && s[7] == 122u8 && s[8] == 101u8 && s[9] == 100u8 ==> seq_is(key_normalized(), s))]
pub fn lemma_key_normalized(s: Seq<u8>) {}

#[logic(open)]
pub fn key_sparse() -> Seq<u8> {
    pearlite! { seq![115u8, 112u8, 97u8, 114u8, 115u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 115u8 && s[1] == 112u8 && s[2] == 97u8 && s[3] == 114u8 && s[4] == 115u8 && s[5] == 101u8 ==> seq_is(key_sparse(), s))]
pub fn lemma_key_sparse(s: Seq<u8>) {}

#[logic(open)]
pub fn key_type() -> Seq<u8> {
    pearlite! { seq![116u8, 121u8, 112u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 116u8 && s[1] == 121u8 && s[2] == 112u8 && s[3] == 101u8 ==> seq_is(key_type(), s))]
pub fn lemma_key_type(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_accessor_o(obj_or_nil(tree(d@, id@)), x, true)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_accessor_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(e) => (forall<y: Accessor> !(is_object(tree(d@, id@)) && rd_accessor_o(obj_or_nil(tree(d@, id@)), y, true)))
        && (e == GltfError::Invalid ==> forall<y: Accessor> !(is_object(tree(d@, id@)) && rd_accessor_o(obj_or_nil(tree(d@, id@)), y, false)))
        && (e == GltfError::Unsupported ==> unsup_accessor(tree(d@, id@)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
pub(crate) fn read_accessor(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Accessor, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_buffer_view(Seq::empty()));
    snapshot!(lemma_key_byte_offset(Seq::empty()));
    snapshot!(lemma_key_component_type(Seq::empty()));
    snapshot!(lemma_key_normalized(Seq::empty()));
    snapshot!(lemma_key_count(Seq::empty()));
    snapshot!(lemma_key_type(Seq::empty()));
    snapshot!(lemma_key_min(Seq::empty()));
    snapshot!(lemma_key_max(Seq::empty()));
    snapshot!(lemma_key_sparse(Seq::empty()));
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
    let sparse = match find_member(o, &[b's', b'p', b'a', b'r', b's', b'e']) {
        None => None,
        Some(i) => match read_sparse(d, o[i].value, ext) { Ok(s) => Some(s), Err(()) => return Err(GltfError::Invalid) },
    };
    Ok(Accessor { buffer_view, byte_offset, component_type, normalized, count, components, is_matrix, min_len, max_len, sparse })
}

#[logic(open, inline)]
pub fn rd_buffer_view_o(o: JObj, x: BufferView) -> bool {
    pearlite! {
        cor_ok(o)
                && f_uint_req(o, key_buffer(), x.buffer)
                && f_uint_def(o, key_byte_offset(), 0, x.byte_offset)
                && f_uint_req(o, key_byte_length(), x.byte_length)
                && f_uint_opt(o, key_byte_stride(), x.byte_stride)
                && f_uint_opt(o, key_target(), x.target)
    }
}

#[logic(open)]
pub fn key_buffer() -> Seq<u8> {
    pearlite! { seq![98u8, 117u8, 102u8, 102u8, 101u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 98u8 && s[1] == 117u8 && s[2] == 102u8 && s[3] == 102u8 && s[4] == 101u8 && s[5] == 114u8 ==> seq_is(key_buffer(), s))]
pub fn lemma_key_buffer(s: Seq<u8>) {}

#[logic(open)]
pub fn key_byte_length() -> Seq<u8> {
    pearlite! { seq![98u8, 121u8, 116u8, 101u8, 76u8, 101u8, 110u8, 103u8, 116u8, 104u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 98u8 && s[1] == 121u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 76u8 && s[5] == 101u8 && s[6] == 110u8 && s[7] == 103u8 && s[8] == 116u8 && s[9] == 104u8 ==> seq_is(key_byte_length(), s))]
pub fn lemma_key_byte_length(s: Seq<u8>) {}

#[logic(open)]
pub fn key_byte_stride() -> Seq<u8> {
    pearlite! { seq![98u8, 121u8, 116u8, 101u8, 83u8, 116u8, 114u8, 105u8, 100u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 98u8 && s[1] == 121u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 83u8 && s[5] == 116u8 && s[6] == 114u8 && s[7] == 105u8 && s[8] == 100u8 && s[9] == 101u8 ==> seq_is(key_byte_stride(), s))]
pub fn lemma_key_byte_stride(s: Seq<u8>) {}

#[logic(open)]
pub fn key_target() -> Seq<u8> {
    pearlite! { seq![116u8, 97u8, 114u8, 103u8, 101u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 116u8 && s[1] == 97u8 && s[2] == 114u8 && s[3] == 103u8 && s[4] == 101u8 && s[5] == 116u8 ==> seq_is(key_target(), s))]
pub fn lemma_key_target(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_buffer_view_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: BufferView> !(is_object(tree(d@, id@)) && rd_buffer_view_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_buffer_view(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<BufferView, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_buffer(Seq::empty()));
    snapshot!(lemma_key_byte_offset(Seq::empty()));
    snapshot!(lemma_key_byte_length(Seq::empty()));
    snapshot!(lemma_key_byte_stride(Seq::empty()));
    snapshot!(lemma_key_target(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let buffer = match req_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let byte_offset = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'O', b'f', b'f', b's', b'e', b't']) { Ok(Some(v)) => v, Ok(None) => 0, Err(()) => return Err(()) };
    let byte_length = match req_uint(d, o, &[b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let byte_stride = match get_uint(d, o, &[b'b', b'y', b't', b'e', b'S', b't', b'r', b'i', b'd', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    let target = match get_uint(d, o, &[b't', b'a', b'r', b'g', b'e', b't']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(BufferView { buffer, byte_offset, byte_length, byte_stride, target })
}

#[logic(open, inline)]
pub fn f_string_opt(o: JObj, k: Seq<u8>, x: Option<Vec<u8>>) -> bool {
    pearlite! {
        match p_string(o, k) {
            Ok(None) => x == None,
            Ok(Some(s)) => match x { Some(v) => v@ == s, None => false },
            Err(()) => false,
        }
    }
}

#[logic(open, inline)]
pub fn rd_buffer_o(o: JObj, x: Buffer) -> bool {
    pearlite! {
        cor_ok(o) && f_uint_req(o, key_byte_length(), x.byte_length) && f_string_opt(o, key_uri(), x.uri)
    }
}

#[logic(open)]
pub fn key_uri() -> Seq<u8> {
    pearlite! { seq![117u8, 114u8, 105u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 3 && s[0] == 117u8 && s[1] == 114u8 && s[2] == 105u8 ==> seq_is(key_uri(), s))]
pub fn lemma_key_uri(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_buffer_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Buffer> !(is_object(tree(d@, id@)) && rd_buffer_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_buffer(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Buffer, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_byte_length(Seq::empty()));
    snapshot!(lemma_key_uri(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let byte_length = match req_uint(d, o, &[b'b', b'y', b't', b'e', b'L', b'e', b'n', b'g', b't', b'h']) { Ok(v) => v, Err(()) => return Err(()) };
    let uri = match get_string(d, o, &[b'u', b'r', b'i']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Buffer { byte_length, uri })
}

#[logic(open, inline)]
pub fn rd_image_o(o: JObj, x: Image) -> bool {
    pearlite! {
        cor_ok(o) && f_string_opt(o, key_uri(), x.uri) && f_uint_opt(o, key_buffer_view(), x.buffer_view)
                && (match p_string(o, key_mime_type()) { Err(()) => false, Ok(m) => x.has_mime_type == (m != None) })
    }
}

#[logic(open)]
pub fn key_mime_type() -> Seq<u8> {
    pearlite! { seq![109u8, 105u8, 109u8, 101u8, 84u8, 121u8, 112u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 109u8 && s[1] == 105u8 && s[2] == 109u8 && s[3] == 101u8 && s[4] == 84u8 && s[5] == 121u8 && s[6] == 112u8 && s[7] == 101u8 ==> seq_is(key_mime_type(), s))]
pub fn lemma_key_mime_type(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_image_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Image> !(is_object(tree(d@, id@)) && rd_image_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_image(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Image, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_uri(Seq::empty()));
    snapshot!(lemma_key_buffer_view(Seq::empty()));
    snapshot!(lemma_key_mime_type(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let uri = match get_string(d, o, &[b'u', b'r', b'i']) { Ok(v) => v, Err(()) => return Err(()) };
    let buffer_view = match get_uint(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w']) { Ok(v) => v, Err(()) => return Err(()) };
    let has_mime_type = match get_string(d, o, &[b'm', b'i', b'm', b'e', b'T', b'y', b'p', b'e']) { Ok(v) => v.is_some(), Err(()) => return Err(()) };
    Ok(Image { uri, buffer_view, has_mime_type })
}

#[logic(open, inline)]
pub fn rd_texture_o(o: JObj, x: Texture) -> bool {
    pearlite! {
        cor_ok(o) && f_uint_opt(o, key_sampler(), x.sampler) && f_uint_opt(o, key_source(), x.source)
    }
}

#[logic(open)]
pub fn key_sampler() -> Seq<u8> {
    pearlite! { seq![115u8, 97u8, 109u8, 112u8, 108u8, 101u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 115u8 && s[1] == 97u8 && s[2] == 109u8 && s[3] == 112u8 && s[4] == 108u8 && s[5] == 101u8 && s[6] == 114u8 ==> seq_is(key_sampler(), s))]
pub fn lemma_key_sampler(s: Seq<u8>) {}

#[logic(open)]
pub fn key_source() -> Seq<u8> {
    pearlite! { seq![115u8, 111u8, 117u8, 114u8, 99u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 115u8 && s[1] == 111u8 && s[2] == 117u8 && s[3] == 114u8 && s[4] == 99u8 && s[5] == 101u8 ==> seq_is(key_source(), s))]
pub fn lemma_key_source(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_texture_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Texture> !(is_object(tree(d@, id@)) && rd_texture_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_texture(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Texture, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_sampler(Seq::empty()));
    snapshot!(lemma_key_source(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let sampler = match get_uint(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r']) { Ok(v) => v, Err(()) => return Err(()) };
    let source = match get_uint(d, o, &[b's', b'o', b'u', b'r', b'c', b'e']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Texture { sampler, source })
}

#[logic(open)]
pub fn rd_sampler(j: JsonS) -> bool {
    pearlite! { is_object(j) && rd_sampler_o(obj_or_nil(j)) }
}

#[logic(open, inline)]
pub fn rd_sampler_o(o: JObj) -> bool {
    pearlite! {
        cor_ok(o) && p_uint(o, key_mag_filter()) != Err(()) && p_uint(o, key_min_filter()) != Err(())
                && p_uint(o, key_wrap_s()) != Err(()) && p_uint(o, key_wrap_t()) != Err(())
    }
}

#[logic(open)]
pub fn key_mag_filter() -> Seq<u8> {
    pearlite! { seq![109u8, 97u8, 103u8, 70u8, 105u8, 108u8, 116u8, 101u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 109u8 && s[1] == 97u8 && s[2] == 103u8 && s[3] == 70u8 && s[4] == 105u8 && s[5] == 108u8 && s[6] == 116u8 && s[7] == 101u8 && s[8] == 114u8 ==> seq_is(key_mag_filter(), s))]
pub fn lemma_key_mag_filter(s: Seq<u8>) {}

#[logic(open)]
pub fn key_min_filter() -> Seq<u8> {
    pearlite! { seq![109u8, 105u8, 110u8, 70u8, 105u8, 108u8, 116u8, 101u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 109u8 && s[1] == 105u8 && s[2] == 110u8 && s[3] == 70u8 && s[4] == 105u8 && s[5] == 108u8 && s[6] == 116u8 && s[7] == 101u8 && s[8] == 114u8 ==> seq_is(key_min_filter(), s))]
pub fn lemma_key_min_filter(s: Seq<u8>) {}

#[logic(open)]
pub fn key_wrap_s() -> Seq<u8> {
    pearlite! { seq![119u8, 114u8, 97u8, 112u8, 83u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 119u8 && s[1] == 114u8 && s[2] == 97u8 && s[3] == 112u8 && s[4] == 83u8 ==> seq_is(key_wrap_s(), s))]
pub fn lemma_key_wrap_s(s: Seq<u8>) {}

#[logic(open)]
pub fn key_wrap_t() -> Seq<u8> {
    pearlite! { seq![119u8, 114u8, 97u8, 112u8, 84u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 119u8 && s[1] == 114u8 && s[2] == 97u8 && s[3] == 112u8 && s[4] == 84u8 ==> seq_is(key_wrap_t(), s))]
pub fn lemma_key_wrap_t(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result { Ok(()) => rd_sampler(tree(d@, id@)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_obj(tree(d@, id@), x))), Err(()) => !rd_sampler(tree(d@, id@)) })]
#[check(terminates)]
pub(crate) fn read_sampler(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    snapshot!(lemma_key_mag_filter(Seq::empty()));
    snapshot!(lemma_key_min_filter(Seq::empty()));
    snapshot!(lemma_key_wrap_s(Seq::empty()));
    snapshot!(lemma_key_wrap_t(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    match get_uint(d, o, &[b'm', b'a', b'g', b'F', b'i', b'l', b't', b'e', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'm', b'i', b'n', b'F', b'i', b'l', b't', b'e', b'r']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'w', b'r', b'a', b'p', b'S']) { Err(()) => return Err(()), Ok(_) => {} }
    match get_uint(d, o, &[b'w', b'r', b'a', b'p', b'T']) { Err(()) => return Err(()), Ok(_) => {} }
    Ok(())
}

#[logic(open, inline)]
pub fn rd_perspective(o: JObj, b: bool) -> bool {
    pearlite! {
        match p_object(o, key_perspective()) {
            Err(()) => false,
            Ok(None) => !b,
            Ok(Some(p)) => b && ext_ok(p) && p_number(p, key_aspect_ratio()) != Err(()) && p_number(p, key_yfov()) == Ok(true)
                && p_number(p, key_zfar()) != Err(()) && p_number(p, key_znear()) == Ok(true),
        }
    }
}

#[logic(open)]
pub fn key_aspect_ratio() -> Seq<u8> {
    pearlite! { seq![97u8, 115u8, 112u8, 101u8, 99u8, 116u8, 82u8, 97u8, 116u8, 105u8, 111u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 97u8 && s[1] == 115u8 && s[2] == 112u8 && s[3] == 101u8 && s[4] == 99u8 && s[5] == 116u8 && s[6] == 82u8 && s[7] == 97u8 && s[8] == 116u8 && s[9] == 105u8 && s[10] == 111u8 ==> seq_is(key_aspect_ratio(), s))]
pub fn lemma_key_aspect_ratio(s: Seq<u8>) {}

#[logic(open)]
pub fn key_perspective() -> Seq<u8> {
    pearlite! { seq![112u8, 101u8, 114u8, 115u8, 112u8, 101u8, 99u8, 116u8, 105u8, 118u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 112u8 && s[1] == 101u8 && s[2] == 114u8 && s[3] == 115u8 && s[4] == 112u8 && s[5] == 101u8 && s[6] == 99u8 && s[7] == 116u8 && s[8] == 105u8 && s[9] == 118u8 && s[10] == 101u8 ==> seq_is(key_perspective(), s))]
pub fn lemma_key_perspective(s: Seq<u8>) {}

#[logic(open)]
pub fn key_yfov() -> Seq<u8> {
    pearlite! { seq![121u8, 102u8, 111u8, 118u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 121u8 && s[1] == 102u8 && s[2] == 111u8 && s[3] == 118u8 ==> seq_is(key_yfov(), s))]
pub fn lemma_key_yfov(s: Seq<u8>) {}

#[logic(open)]
pub fn key_zfar() -> Seq<u8> {
    pearlite! { seq![122u8, 102u8, 97u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 122u8 && s[1] == 102u8 && s[2] == 97u8 && s[3] == 114u8 ==> seq_is(key_zfar(), s))]
pub fn lemma_key_zfar(s: Seq<u8>) {}

#[logic(open)]
pub fn key_znear() -> Seq<u8> {
    pearlite! { seq![122u8, 110u8, 101u8, 97u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 122u8 && s[1] == 110u8 && s[2] == 101u8 && s[3] == 97u8 && s[4] == 114u8 ==> seq_is(key_znear(), s))]
pub fn lemma_key_znear(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(b) => rd_perspective(obj_of(d@, o@), b) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || match p_object(obj_of(d@, o@), key_perspective()) { Ok(Some(p)) => ext_here(p, x), _ => false })),
    Err(()) => forall<b: bool> !rd_perspective(obj_of(d@, o@), b),
})]
#[check(terminates)]
fn check_perspective(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<bool, ()> {
    snapshot!(lemma_key_perspective(Seq::empty()));
    snapshot!(lemma_key_aspect_ratio(Seq::empty()));
    snapshot!(lemma_key_yfov(Seq::empty()));
    snapshot!(lemma_key_zfar(Seq::empty()));
    snapshot!(lemma_key_znear(Seq::empty()));
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

#[logic(open, inline)]
pub fn rd_orthographic(o: JObj, b: bool) -> bool {
    pearlite! {
        match p_object(o, key_orthographic()) {
            Err(()) => false,
            Ok(None) => !b,
            Ok(Some(p)) => b && ext_ok(p) && p_number(p, key_xmag()) == Ok(true) && p_number(p, key_ymag()) == Ok(true)
                && p_number(p, key_zfar()) == Ok(true) && p_number(p, key_znear()) == Ok(true),
        }
    }
}

#[logic(open)]
pub fn key_orthographic() -> Seq<u8> {
    pearlite! { seq![111u8, 114u8, 116u8, 104u8, 111u8, 103u8, 114u8, 97u8, 112u8, 104u8, 105u8, 99u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 12 && s[0] == 111u8 && s[1] == 114u8 && s[2] == 116u8 && s[3] == 104u8 && s[4] == 111u8 && s[5] == 103u8 && s[6] == 114u8 && s[7] == 97u8 && s[8] == 112u8 && s[9] == 104u8 && s[10] == 105u8 && s[11] == 99u8 ==> seq_is(key_orthographic(), s))]
pub fn lemma_key_orthographic(s: Seq<u8>) {}

#[logic(open)]
pub fn key_xmag() -> Seq<u8> {
    pearlite! { seq![120u8, 109u8, 97u8, 103u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 120u8 && s[1] == 109u8 && s[2] == 97u8 && s[3] == 103u8 ==> seq_is(key_xmag(), s))]
pub fn lemma_key_xmag(s: Seq<u8>) {}

#[logic(open)]
pub fn key_ymag() -> Seq<u8> {
    pearlite! { seq![121u8, 109u8, 97u8, 103u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 121u8 && s[1] == 109u8 && s[2] == 97u8 && s[3] == 103u8 ==> seq_is(key_ymag(), s))]
pub fn lemma_key_ymag(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(b) => rd_orthographic(obj_of(d@, o@), b) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || match p_object(obj_of(d@, o@), key_orthographic()) { Ok(Some(p)) => ext_here(p, x), _ => false })),
    Err(()) => forall<b: bool> !rd_orthographic(obj_of(d@, o@), b),
})]
#[check(terminates)]
fn check_orthographic(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<bool, ()> {
    snapshot!(lemma_key_orthographic(Seq::empty()));
    snapshot!(lemma_key_xmag(Seq::empty()));
    snapshot!(lemma_key_ymag(Seq::empty()));
    snapshot!(lemma_key_zfar(Seq::empty()));
    snapshot!(lemma_key_znear(Seq::empty()));
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

#[logic(open)]
pub fn camera_kind(t: Seq<u8>) -> Int {
    pearlite! {
        if seq_is(t, key_perspective()) { CAMERA_PERSPECTIVE@ }
        else if seq_is(t, key_orthographic()) { CAMERA_ORTHOGRAPHIC@ }
        else { KIND_OTHER@ }
    }
}

// MUST-132: camera.type が必要
#[logic(open, inline)]
pub fn rd_camera_o(o: JObj, x: Camera) -> bool {
    pearlite! {
        cor_ok(o)
                && (match p_string(o, key_type()) { Ok(Some(t)) => x.kind@ == camera_kind(t), _ => false })
                && rd_perspective(o, x.has_perspective) && rd_orthographic(o, x.has_orthographic)
    }
}

#[logic(open, inline)]
pub fn ext_camera_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x)
                || (match p_object(o, key_perspective()) { Ok(Some(p)) => ext_here(p, x), _ => false })
                || (match p_object(o, key_orthographic()) { Ok(Some(p)) => ext_here(p, x), _ => false })
    }
}

// MUST-132: camera.type が必要
#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_camera_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_camera_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Camera> !(is_object(tree(d@, id@)) && rd_camera_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_camera(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Camera, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_type(Seq::empty()));
    snapshot!(lemma_key_perspective(Seq::empty()));
    snapshot!(lemma_key_orthographic(Seq::empty()));
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

#[logic(open, inline)]
pub fn f_uint_array_req(o: JObj, k: Seq<u8>, v: Seq<u64>) -> bool {
    pearlite! { match p_array(o, k) { Ok(Some(l)) => uints_is(l, v), _ => false } }
}

// MUST-095: skin.joints が必要
#[logic(open, inline)]
pub fn rd_skin_o(o: JObj, x: Skin) -> bool {
    pearlite! {
        cor_ok(o) && f_uint_array_req(o, key_joints(), x.joints@)
                && f_uint_opt(o, key_skeleton(), x.skeleton)
                && f_uint_opt(o, key_inverse_bind_matrices(), x.inverse_bind_matrices)
    }
}

#[logic(open)]
pub fn key_inverse_bind_matrices() -> Seq<u8> {
    pearlite! { seq![105u8, 110u8, 118u8, 101u8, 114u8, 115u8, 101u8, 66u8, 105u8, 110u8, 100u8, 77u8, 97u8, 116u8, 114u8, 105u8, 99u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 19 && s[0] == 105u8 && s[1] == 110u8 && s[2] == 118u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 115u8 && s[6] == 101u8 && s[7] == 66u8 && s[8] == 105u8 && s[9] == 110u8 && s[10] == 100u8 && s[11] == 77u8 && s[12] == 97u8 && s[13] == 116u8 && s[14] == 114u8 && s[15] == 105u8 && s[16] == 99u8 && s[17] == 101u8 && s[18] == 115u8 ==> seq_is(key_inverse_bind_matrices(), s))]
pub fn lemma_key_inverse_bind_matrices(s: Seq<u8>) {}

#[logic(open)]
pub fn key_joints() -> Seq<u8> {
    pearlite! { seq![106u8, 111u8, 105u8, 110u8, 116u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 106u8 && s[1] == 111u8 && s[2] == 105u8 && s[3] == 110u8 && s[4] == 116u8 && s[5] == 115u8 ==> seq_is(key_joints(), s))]
pub fn lemma_key_joints(s: Seq<u8>) {}

#[logic(open)]
pub fn key_skeleton() -> Seq<u8> {
    pearlite! { seq![115u8, 107u8, 101u8, 108u8, 101u8, 116u8, 111u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 115u8 && s[1] == 107u8 && s[2] == 101u8 && s[3] == 108u8 && s[4] == 101u8 && s[5] == 116u8 && s[6] == 111u8 && s[7] == 110u8 ==> seq_is(key_skeleton(), s))]
pub fn lemma_key_skeleton(s: Seq<u8>) {}

// MUST-095: skin.joints が必要
#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_skin_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Skin> !(is_object(tree(d@, id@)) && rd_skin_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
pub(crate) fn read_skin(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Skin, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_joints(Seq::empty()));
    snapshot!(lemma_key_skeleton(Seq::empty()));
    snapshot!(lemma_key_inverse_bind_matrices(Seq::empty()));
    let o = match as_object(d, id) { Ok(o) => o, Err(()) => return Err(()) };
    match check_child_of_root(d, o, ext) { Err(()) => return Err(()), Ok(()) => {} }
    let joints = match get_uint_array(d, o, &[b'j', b'o', b'i', b'n', b't', b's']) { Ok(Some(c)) => c, _ => return Err(()) };
    let skeleton = match get_uint(d, o, &[b's', b'k', b'e', b'l', b'e', b't', b'o', b'n']) { Ok(v) => v, Err(()) => return Err(()) };
    let inverse_bind_matrices = match get_uint(d, o, &[b'i', b'n', b'v', b'e', b'r', b's', b'e', b'B', b'i', b'n', b'd', b'M', b'a', b't', b'r', b'i', b'c', b'e', b's']) { Ok(v) => v, Err(()) => return Err(()) };
    Ok(Skin { joints, skeleton, inverse_bind_matrices })
}

#[logic(open)]
pub fn path_kind(p: Seq<u8>) -> Int {
    pearlite! {
        if seq_is(p, key_translation()) { PATH_TRANSLATION@ }
        else if seq_is(p, key_rotation()) { PATH_ROTATION@ }
        else if seq_is(p, key_scale()) { PATH_SCALE@ }
        else if seq_is(p, key_weights()) { PATH_WEIGHTS@ }
        else { KIND_OTHER@ }
    }
}

#[logic(open, inline)]
pub fn rd_channel_o(o: JObj, x: Channel) -> bool {
    pearlite! {
        ext_ok(o) && f_uint_req(o, key_sampler(), x.sampler)
                && match p_object(o, key_target()) {
                    Ok(Some(t)) => ext_ok(t) && f_uint_opt(t, key_node(), x.node)
                        && (match p_string(t, key_path()) { Ok(Some(p)) => x.path@ == path_kind(p), _ => false }),
                    _ => false,
                }
    }
}

#[logic(open, inline)]
pub fn ext_channel_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x) || match p_object(o, key_target()) { Ok(Some(t)) => ext_here(t, x), _ => false }
    }
}

#[logic(open)]
pub fn key_node() -> Seq<u8> {
    pearlite! { seq![110u8, 111u8, 100u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 110u8 && s[1] == 111u8 && s[2] == 100u8 && s[3] == 101u8 ==> seq_is(key_node(), s))]
pub fn lemma_key_node(s: Seq<u8>) {}

#[logic(open)]
pub fn key_path() -> Seq<u8> {
    pearlite! { seq![112u8, 97u8, 116u8, 104u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 112u8 && s[1] == 97u8 && s[2] == 116u8 && s[3] == 104u8 ==> seq_is(key_path(), s))]
pub fn lemma_key_path(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_channel_o(obj_or_nil(tree(d@, id@)), x)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_channel_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(()) => forall<y: Channel> !(is_object(tree(d@, id@)) && rd_channel_o(obj_or_nil(tree(d@, id@)), y)),
})]
#[check(terminates)]
fn read_channel(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Channel, ()> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_sampler(Seq::empty()));
    snapshot!(lemma_key_target(Seq::empty()));
    snapshot!(lemma_key_node(Seq::empty()));
    snapshot!(lemma_key_path(Seq::empty()));
    snapshot!(lemma_key_translation(Seq::empty()));
    snapshot!(lemma_key_rotation(Seq::empty()));
    snapshot!(lemma_key_scale(Seq::empty()));
    snapshot!(lemma_key_weights(Seq::empty()));
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

#[logic(open)]
pub fn interp_kind(s: Seq<u8>) -> Option<Int> {
    pearlite! {
        if seq_is(s, key_linear()) { Some(INTERP_LINEAR@) }
        else if seq_is(s, key_step()) { Some(INTERP_STEP@) }
        else if seq_is(s, key_cubicspline()) { Some(INTERP_CUBICSPLINE@) }
        else { None }
    }
}

#[logic(open, inline)]
pub fn rd_anim_sampler_o(o: JObj, x: AnimationSampler, strict: bool) -> bool {
    pearlite! {
        ext_ok(o) && f_uint_req(o, key_input(), x.input) && f_uint_req(o, key_output(), x.output)
                && match p_string(o, key_interpolation()) {
                    Err(()) => false,
                    Ok(None) => x.interpolation@ == INTERP_LINEAR@,
                    Ok(Some(s)) => match interp_kind(s) { Some(k) => x.interpolation@ == k, None => !strict },
                }
    }
}

// (U): animation sampler の interpolation が既知の値でない
#[logic(open)]
pub fn unsup_anim_sampler(j: JsonS) -> bool {
    pearlite! { is_object(j) && unsup_anim_sampler_o(obj_or_nil(j)) }
}

#[logic(open, inline)]
pub fn unsup_anim_sampler_o(o: JObj) -> bool {
    pearlite! {
        match p_string(o, key_interpolation()) { Ok(Some(s)) => interp_kind(s) == None, _ => false }
    }
}

// キーの文字列
#[logic(open)]
pub fn key_cubicspline() -> Seq<u8> {
    pearlite! { seq![67u8, 85u8, 66u8, 73u8, 67u8, 83u8, 80u8, 76u8, 73u8, 78u8, 69u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 67u8 && s[1] == 85u8 && s[2] == 66u8 && s[3] == 73u8 && s[4] == 67u8 && s[5] == 83u8 && s[6] == 80u8 && s[7] == 76u8 && s[8] == 73u8 && s[9] == 78u8 && s[10] == 69u8 ==> seq_is(key_cubicspline(), s))]
pub fn lemma_key_cubicspline(s: Seq<u8>) {}

#[logic(open)]
pub fn key_linear() -> Seq<u8> {
    pearlite! { seq![76u8, 73u8, 78u8, 69u8, 65u8, 82u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 76u8 && s[1] == 73u8 && s[2] == 78u8 && s[3] == 69u8 && s[4] == 65u8 && s[5] == 82u8 ==> seq_is(key_linear(), s))]
pub fn lemma_key_linear(s: Seq<u8>) {}

#[logic(open)]
pub fn key_step() -> Seq<u8> {
    pearlite! { seq![83u8, 84u8, 69u8, 80u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 83u8 && s[1] == 84u8 && s[2] == 69u8 && s[3] == 80u8 ==> seq_is(key_step(), s))]
pub fn lemma_key_step(s: Seq<u8>) {}

#[logic(open)]
pub fn key_input() -> Seq<u8> {
    pearlite! { seq![105u8, 110u8, 112u8, 117u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 105u8 && s[1] == 110u8 && s[2] == 112u8 && s[3] == 117u8 && s[4] == 116u8 ==> seq_is(key_input(), s))]
pub fn lemma_key_input(s: Seq<u8>) {}

#[logic(open)]
pub fn key_interpolation() -> Seq<u8> {
    pearlite! { seq![105u8, 110u8, 116u8, 101u8, 114u8, 112u8, 111u8, 108u8, 97u8, 116u8, 105u8, 111u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 13 && s[0] == 105u8 && s[1] == 110u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 112u8 && s[6] == 111u8 && s[7] == 108u8 && s[8] == 97u8 && s[9] == 116u8 && s[10] == 105u8 && s[11] == 111u8 && s[12] == 110u8 ==> seq_is(key_interpolation(), s))]
pub fn lemma_key_interpolation(s: Seq<u8>) {}

#[logic(open)]
pub fn key_output() -> Seq<u8> {
    pearlite! { seq![111u8, 117u8, 116u8, 112u8, 117u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 111u8 && s[1] == 117u8 && s[2] == 116u8 && s[3] == 112u8 && s[4] == 117u8 && s[5] == 116u8 ==> seq_is(key_output(), s))]
pub fn lemma_key_output(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_anim_sampler_o(obj_or_nil(tree(d@, id@)), x, true)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_here(obj_or_nil(tree(d@, id@)), x)))),
    Err(e) => (forall<y: AnimationSampler> !(is_object(tree(d@, id@)) && rd_anim_sampler_o(obj_or_nil(tree(d@, id@)), y, true)))
        && (e == GltfError::Invalid ==> forall<y: AnimationSampler> !(is_object(tree(d@, id@)) && rd_anim_sampler_o(obj_or_nil(tree(d@, id@)), y, false)))
        && (e == GltfError::Unsupported ==> unsup_anim_sampler(tree(d@, id@)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
fn read_animation_sampler(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<AnimationSampler, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_input(Seq::empty()));
    snapshot!(lemma_key_output(Seq::empty()));
    snapshot!(lemma_key_interpolation(Seq::empty()));
    snapshot!(lemma_key_linear(Seq::empty()));
    snapshot!(lemma_key_step(Seq::empty()));
    snapshot!(lemma_key_cubicspline(Seq::empty()));
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

#[logic(open)]
pub fn rd_channel(j: JsonS, x: Channel) -> bool {
    pearlite! { is_object(j) && rd_channel_o(obj_or_nil(j), x) }
}

#[logic(open)]
pub fn ext_channel(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_channel_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_channel(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_channel(nth(list_of(d@, a@), t), x))),
    Err(()) => exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Channel> !rd_channel(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_channel_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Channel>, ()> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Channel> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_channel(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_channel(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Channel> rd_channel(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_channel_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_channel(d, a[i], ext) {
            Ok(c) => out.push(c),
            Err(()) => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

// strict = false のときは (U) の場合（未知の interpolation）を受け入れる
#[logic(open)]
pub fn rd_anim_sampler(j: JsonS, x: AnimationSampler, strict: bool) -> bool {
    pearlite! { is_object(j) && rd_anim_sampler_o(obj_or_nil(j), x, strict) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_anim_sampler(nth(list_of(d@, a@), t), v@[t], true))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => (exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: AnimationSampler> !rd_anim_sampler(nth(list_of(d@, a@), t), y, true))
        && (e == GltfError::Invalid ==> exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: AnimationSampler> !rd_anim_sampler(nth(list_of(d@, a@), t), y, false))
        && (e == GltfError::Unsupported ==> exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && unsup_anim_sampler(nth(list_of(d@, a@), t)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
fn read_animation_sampler_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<AnimationSampler>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<AnimationSampler> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_anim_sampler(tree(d@, a@[t]@), out@[t], true))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: AnimationSampler> rd_anim_sampler(tree(d@, a@[i@]@), y, true) == (is_object(tree(d@, a@[i@]@)) && rd_anim_sampler_o(obj_or_nil(tree(d@, a@[i@]@)), y, true)));
        match read_animation_sampler(d, a[i], ext) {
            Ok(s) => out.push(s),
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open, inline)]
pub fn rd_animation_o(o: JObj, x: Animation, strict: bool) -> bool {
    pearlite! {
        cor_ok(o)
                && (match p_array(o, key_channels()) {
                    Ok(Some(l)) => jlen(l) == x.channels@.len() && forall<t> 0 <= t && t < jlen(l) ==> rd_channel(nth(l, t), x.channels@[t]),
                    _ => false,
                })
                && match p_array(o, key_samplers()) {
                    Ok(Some(l)) => jlen(l) == x.samplers@.len() && forall<t> 0 <= t && t < jlen(l) ==> rd_anim_sampler(nth(l, t), x.samplers@[t], strict),
                    _ => false,
                }
    }
}

#[logic(open)]
pub fn unsup_animation(j: JsonS) -> bool {
    pearlite! { is_object(j) && unsup_animation_o(obj_or_nil(j)) }
}

#[logic(open, inline)]
pub fn unsup_animation_o(o: JObj) -> bool {
    pearlite! {
        match p_array(o, key_samplers()) {
                Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && unsup_anim_sampler(nth(l, t)),
                _ => false,
            }
    }
}

#[logic(open, inline)]
pub fn ext_animation_o(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x)
                || (match p_array(o, key_channels()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_channel(nth(l, t), x), _ => false })
                || (match p_array(o, key_samplers()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false })
    }
}

#[logic(open)]
pub fn key_channels() -> Seq<u8> {
    pearlite! { seq![99u8, 104u8, 97u8, 110u8, 110u8, 101u8, 108u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 99u8 && s[1] == 104u8 && s[2] == 97u8 && s[3] == 110u8 && s[4] == 110u8 && s[5] == 101u8 && s[6] == 108u8 && s[7] == 115u8 ==> seq_is(key_channels(), s))]
pub fn lemma_key_channels(s: Seq<u8>) {}

#[logic(open)]
pub fn key_samplers() -> Seq<u8> {
    pearlite! { seq![115u8, 97u8, 109u8, 112u8, 108u8, 101u8, 114u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 115u8 && s[1] == 97u8 && s[2] == 109u8 && s[3] == 112u8 && s[4] == 108u8 && s[5] == 101u8 && s[6] == 114u8 && s[7] == 115u8 ==> seq_is(key_samplers(), s))]
pub fn lemma_key_samplers(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && id@ < d@.len())]
#[ensures(match result {
    Ok(x) => (is_object(tree(d@, id@)) && rd_animation_o(obj_or_nil(tree(d@, id@)), x, true)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || (is_object(tree(d@, id@)) && ext_animation_o(obj_or_nil(tree(d@, id@)), x)))),
    Err(e) => (forall<y: Animation> !(is_object(tree(d@, id@)) && rd_animation_o(obj_or_nil(tree(d@, id@)), y, true)))
        && (e == GltfError::Invalid ==> forall<y: Animation> !(is_object(tree(d@, id@)) && rd_animation_o(obj_or_nil(tree(d@, id@)), y, false)))
        && (e == GltfError::Unsupported ==> unsup_animation(tree(d@, id@)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
pub(crate) fn read_animation(d: &Vec<JsonNode>, id: usize, ext: &mut Vec<Vec<u8>>) -> Result<Animation, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_channels(Seq::empty()));
    snapshot!(lemma_key_samplers(Seq::empty()));
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

#[requires(start@ <= end@ && end@ <= s@.len())]
#[ensures(opt_int(result) == set_index(s@[start@..end@]))]
#[check(terminates)]
fn parse_version_part(s: &Vec<u8>, start: usize, end: usize) -> Option<u64> {
    if start >= end || end - start > 9 {
        return None;
    }
    if s[start] == b'0' && end - start > 1 {
        return None;
    }
    let mut v: u64 = 0;
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= end@)]
    #[invariant(forall<t> start@ <= t && t < i@ ==> is_dec(s@[t]))]
    #[invariant(v@ == dec_val(s@[start@..i@]))]
    #[invariant(v@ < pow10(i@ - start@))]
    #[variant(end@ - i@)]
    while i < end {
        if s[i] < b'0' || s[i] > b'9' {
            return None;
        }
        v = v * 10 + (s[i] - b'0') as u64;
        i += 1;
    }
    Some(v)
}

// asset の version の構文 ^(0|[1-9][0-9]{0,8})\.(0|[1-9][0-9]{0,8})$
// MUST-010: version / minVersion の構文
#[logic(open)]
pub fn version_is(s: Seq<u8>, a: Int, b: Int) -> bool {
    pearlite! {
        exists<p> 0 <= p && p < s.len() && s[p]@ == 46 && set_index(s[..p]) == Some(a) && set_index(s[p + 1..]) == Some(b)
    }
}

#[logic(open)]
pub fn version_ok(s: Seq<u8>) -> bool {
    pearlite! { exists<a, b> version_is(s, a, b) }
}

// version の構文で、区切りの '.' は最初の '.'
#[logic(opaque)]
#[requires(0 <= p && p <= s.len() && (p == s.len() || s[p]@ == 46) && forall<t> 0 <= t && t < p ==> s[t]@ != 46)]
#[ensures(p == s.len() ==> !version_ok(s))]
#[ensures(p < s.len() ==> forall<a: Int, b: Int> version_is(s, a, b) == (set_index(s[..p]) == Some(a) && set_index(s[p + 1..]) == Some(b)))]
pub fn lemma_version_first_dot(s: Seq<u8>, p: Int) {
    proof_assert!(forall<q> p < q && q <= s.len() ==> s[..q][p] == s[p] && !is_dec(s[..q][p]) && set_index(s[..q]) == None);
    proof_assert!(forall<q> 0 <= q && q < p ==> s[q]@ != 46);
}

// MUST-010: version / minVersion の構文
#[ensures(match result { Some((a, b)) => version_is(s@, a@, b@), None => !version_ok(s@) })]
#[check(terminates)]
pub(crate) fn parse_version(s: &Vec<u8>) -> Option<(u64, u64)> {
    let mut dot = 0;
    #[invariant(dot@ <= s@.len())]
    #[invariant(forall<t> 0 <= t && t < dot@ ==> s@[t]@ != 46)]
    #[variant(s@.len() - dot@)]
    while dot < s.len() && s[dot] != b'.' {
        dot += 1;
    }
    snapshot!(lemma_version_first_dot(s@, dot@));
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
