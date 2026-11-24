use vstd::prelude::*;

verus! {

pub fn add_f32(a: f32, b: f32) -> f32 {
    a + b
}

// 検証失敗: vstd は f32 の加算結果を未解釈関数 add_ensures でしか表さず、意味を与えていない
// use vstd::float::FloatBitsProperties;
//
// pub fn add_f32(a: f32, b: f32) -> (r: f32)
//     requires
//         a.is_finite_spec(),
//         b.is_finite_spec(),
//     ensures
//         !r.is_nan_spec(),
// {
//     a + b
// }

} // verus!
