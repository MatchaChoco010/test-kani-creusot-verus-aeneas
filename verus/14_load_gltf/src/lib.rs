#![cfg_attr(not(verus_only), allow(unused_braces))]

pub mod glb;
pub mod json;
pub mod model;
pub mod read;
pub mod validate;

use crate::glb::*;
use crate::json::*;
use crate::model::*;
use crate::read::*;
use crate::validate::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::validate::refs::*;
#[cfg(verus_only)]
use crate::validate::support::*;

verus! {

// 対象は 64 ビット環境（usize = u64）
global size_of usize == 8;

// JSON 値まで（GLB と JSON の段階）
pub open spec fn stage_json(s: Seq<u8>) -> Option<(JsonS, bool, Option<u64>)> {
    if is_glb_s(s) {
        match glb_spec(s) {
            Some((js, bin)) => match json_text(js) {
                Some(j) => Some((j, true, bin)),
                None => None,
            },
            None => None,
        }
    } else {
        match json_text(s) {
            Some(j) => Some((j, false, None)),
            None => None,
        }
    }
}

pub open spec fn glb_fails(s: Seq<u8>) -> bool {
    is_glb_s(s) && glb_spec(s) is None
}

pub open spec fn json_fails(s: Seq<u8>) -> bool {
    if is_glb_s(s) {
        glb_spec(s) matches Some((js, _)) && json_text(js) is None
    } else {
        json_text(s) is None
    }
}

// T1
pub open spec fn parse_post(s: Seq<u8>, r: Result<Gltf, GltfError>) -> bool {
    &&& (r matches Err(GltfError::Glb)) == glb_fails(s)
    &&& (r matches Err(GltfError::Json)) == json_fails(s)
    &&& (stage_json(s) matches Some((j, glb, bin)) ==> match r {
        Ok(g) => read_spec(j, glb, bin) == Some(g@),
        Err(GltfError::Unsupported) => contains_u(j) && read_spec(j, glb, bin) is None,
        Err(GltfError::Invalid) => violates_rule(j) && read_spec(j, glb, bin) is None,
        Err(_) => false,
    })
}

// T1
pub fn parse_gltf(bytes: &[u8]) -> (r: Result<Gltf, GltfError>)
    ensures
        parse_post(bytes@, r),
{
    if is_glb(bytes) {
        match parse_glb(bytes) {
            None => Err(GltfError::Glb),
            Some(c) => match parse_json(&c.json) {
                None => Err(GltfError::Json),
                Some(j) => read_gltf(&j, true, c.bin_len),
            },
        }
    } else {
        match parse_json(bytes) {
            None => Err(GltfError::Json),
            Some(j) => read_gltf(&j, false, None),
        }
    }
}

// parse_gltf の仕様上の結果（成功時のモデル）
pub open spec fn parsed(s: Seq<u8>) -> Option<GltfS> {
    match stage_json(s) {
        Some((j, glb, bin)) => read_spec(j, glb, bin),
        None => None,
    }
}

// T3 / T5 のエラーの分類
pub open spec fn load_err(s: Seq<u8>, e: GltfError) -> bool {
    match e {
        GltfError::Glb => glb_fails(s),
        GltfError::Json => json_fails(s),
        GltfError::Unsupported => stage_json(s) matches Some((j, glb, bin)) && ((contains_u(j) && read_spec(j, glb, bin) is None)
            || (read_spec(j, glb, bin) matches Some(g) && refs_ok(g) && !supported_s(g))),
        GltfError::Invalid => stage_json(s) matches Some((j, glb, bin)) && ((violates_rule(j) && read_spec(j, glb, bin) is None)
            || (read_spec(j, glb, bin) matches Some(g) && (!refs_ok(g) || (supported_s(g) && !rules_ok_s(g))))),
    }
}

// T3
pub open spec fn load_post(s: Seq<u8>, r: Result<Gltf, GltfError>) -> bool {
    &&& r is Ok == (parsed(s) matches Some(g) && valid(g))
    &&& match r {
        Ok(g) => parsed(s) == Some(g@) && valid(g@),
        Err(e) => load_err(s, e),
    }
    &&& (r matches Err(GltfError::Glb)) == glb_fails(s)
    &&& (r matches Err(GltfError::Json)) == json_fails(s)
}

// T3
pub fn load_gltf(bytes: &[u8]) -> (r: Result<Gltf, GltfError>)
    ensures
        load_post(bytes@, r),
{
    match parse_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => match validate(&g) {
            Err(e) => Err(e),
            Ok(()) => Ok(g),
        },
    }
}

// T4
pub fn process(_gltf: &Gltf)
    requires
        valid(_gltf@),
{
    // ジオメトリ処理を行う想定。参照がすべて範囲内で、仕様の規則を満たすことを前提にする
}

// T5
pub open spec fn render_post(s: Seq<u8>, r: Result<(), GltfError>) -> bool {
    &&& r is Ok == (parsed(s) matches Some(g) && valid(g))
    &&& (r matches Err(e) ==> load_err(s, e))
    &&& (r matches Err(GltfError::Glb)) == glb_fails(s)
    &&& (r matches Err(GltfError::Json)) == json_fails(s)
}

// T5
pub fn render(bytes: &[u8]) -> (r: Result<(), GltfError>)
    ensures
        render_post(bytes@, r),
{
    match load_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => {
            process(&g);
            Ok(())
        }
    }
}

// T6
// 検証失敗: parse_gltf の事後条件からは process の事前条件 valid(g) が導けない
// pub fn render_unvalidated(bytes: &[u8]) -> Result<(), GltfError> {
//     match parse_gltf(bytes) {
//         Err(e) => Err(e),
//         Ok(g) => {
//             process(&g);
//             Ok(())
//         }
//     }
// }

} // verus!
