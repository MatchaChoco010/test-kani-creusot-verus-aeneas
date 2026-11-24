pub mod glb;
pub mod json;
pub mod model;
pub mod read;
pub mod validate;

use creusot_std::prelude::*;
use crate::glb::*;
use crate::json::*;
use crate::model::*;
use crate::read::*;
use crate::validate::*;

// T1: parse_gltf(bytes) の結果
#[logic(open)]
pub fn parse_res(s: Seq<u8>, r: Result<Gltf, GltfError>) -> bool {
    pearlite! {
        if is_glb_spec(s) {
            match glb_spec(s) {
                None => r == Err(GltfError::Glb),
                Some(c) => match json_text_spec(c.json) {
                    None => r == Err(GltfError::Json),
                    Some(j) => read_res(j, true, c.bin_len, r),
                },
            }
        } else {
            match json_text_spec(s) {
                None => r == Err(GltfError::Json),
                Some(j) => read_res(j, false, None, r),
            }
        }
    }
}

#[ensures(parse_res(bytes@, result))]
#[check(terminates)]
pub fn parse_gltf(bytes: &[u8]) -> Result<Gltf, GltfError> {
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

// T3: load_gltf(bytes) の結果。Ok(g) は parse_gltf の仕様が Ok(g) で valid(g)、誤りは T1・T2 のとおり伝わる
#[logic(open)]
pub fn load_res(s: Seq<u8>, r: Result<Gltf, GltfError>) -> bool {
    pearlite! {
        match r {
            Ok(g) => parse_res(s, Ok(g)) && valid(g),
            Err(e) => parse_res(s, Err(e)) || exists<g: Gltf> parse_res(s, Ok(g)) && validate_res(g, Err(e)),
        }
    }
}

#[ensures(load_res(bytes@, result))]
#[check(terminates)]
pub fn load_gltf(bytes: &[u8]) -> Result<Gltf, GltfError> {
    match parse_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => match validate(&g) {
            Err(e) => Err(e),
            Ok(()) => Ok(g),
        },
    }
}

#[requires(valid(*_gltf))]
#[check(terminates)]
pub fn process(_gltf: &Gltf) {
    // ジオメトリ処理を行う想定。参照がすべて範囲内で、仕様の規則を満たすことを前提にする
}

#[ensures(match result { Ok(()) => exists<g: Gltf> load_res(bytes@, Ok(g)), Err(e) => load_res(bytes@, Err(e)) })]
#[check(terminates)]
pub fn render(bytes: &[u8]) -> Result<(), GltfError> {
    match load_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => {
            process(&g);
            Ok(())
        }
    }
}

// 検証失敗: parse_gltf は valid(g) を保証しないので、process の事前条件 valid(g) を示せない
// pub fn render_unvalidated(bytes: &[u8]) -> Result<(), GltfError> {
//     match parse_gltf(bytes) {
//         Err(e) => Err(e),
//         Ok(g) => {
//             process(&g);
//             Ok(())
//         }
//     }
// }
