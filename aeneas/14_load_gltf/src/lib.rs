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

pub fn load_gltf(bytes: &[u8]) -> Result<Gltf, GltfError> {
    match parse_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => match validate(&g) {
            Err(e) => Err(e),
            Ok(()) => Ok(g),
        },
    }
}

pub fn process(gltf: &Gltf) {
    debug_assert!(matches!(validate(gltf), Ok(())));
    // ジオメトリ処理を行う想定。参照がすべて範囲内で、仕様の規則を満たすことを前提にする
}

pub fn render(bytes: &[u8]) -> Result<(), GltfError> {
    match load_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => {
            process(&g);
            Ok(())
        }
    }
}

pub fn render_unvalidated(bytes: &[u8]) -> Result<(), GltfError> {
    match parse_gltf(bytes) {
        Err(e) => Err(e),
        Ok(g) => {
            process(&g);
            Ok(())
        }
    }
}
