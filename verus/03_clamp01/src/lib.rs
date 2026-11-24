use vstd::prelude::*;

verus! {

pub fn clamp01(x: f32) -> f32 {
    if x < 0.0 {
        0.0
    } else if x > 1.0 {
        1.0
    } else {
        x
    }
}

// 検証失敗: vstd は f32 の比較結果を未解釈関数 lt_ensures / gt_ensures でしか表さず、意味を与えていない
// use vstd::std_specs::cmp::{gt_ensures, lt_ensures};
//
// pub fn clamp01(x: f32) -> (r: f32)
//     ensures
//         lt_ensures(x, 0.0f32, true) ==> r == 0.0f32,
//         gt_ensures(x, 1.0f32, true) ==> r == 1.0f32,
//         lt_ensures(x, 0.0f32, false) && gt_ensures(x, 1.0f32, false) ==> r == x,
// {
//     if x < 0.0 {
//         0.0
//     } else if x > 1.0 {
//         1.0
//     } else {
//         x
//     }
// }

} // verus!
