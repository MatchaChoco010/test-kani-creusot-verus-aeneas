pub fn clamp01(x: f32) -> f32 {
    if x < 0.0 {
        0.0
    } else if x > 1.0 {
        1.0
    } else {
        x
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_clamp01() {
    let x: f32 = kani::any();
    let r = clamp01(x);
    if x < 0.0 {
        assert!(r == 0.0);
    } else if x > 1.0 {
        assert!(r == 1.0);
    } else {
        assert_eq!(r.to_bits(), x.to_bits());
    }
}
