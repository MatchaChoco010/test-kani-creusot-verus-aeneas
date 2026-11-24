pub fn add_f32(a: f32, b: f32) -> f32 {
    a + b
}

#[cfg(kani)]
#[kani::proof]
fn check_nan() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    let opposite_infinities = a.is_infinite() && b.is_infinite() && a.is_sign_positive() != b.is_sign_positive();
    assert_eq!(add_f32(a, b).is_nan(), a.is_nan() || b.is_nan() || opposite_infinities);
}

// 検証失敗: 実数の足し算は結合的だが、f32 の足し算は丸めのため結合的でない
// #[cfg(kani)]
// #[kani::proof]
// fn check_associative() {
//     let a: f32 = kani::any();
//     let b: f32 = kani::any();
//     let c: f32 = kani::any();
//     kani::assume(a.is_finite() && b.is_finite() && c.is_finite());
//     let left = add_f32(add_f32(a, b), c);
//     let right = add_f32(a, add_f32(b, c));
//     kani::assume(left.is_finite() && right.is_finite());
//     assert!(left == right);
// }
