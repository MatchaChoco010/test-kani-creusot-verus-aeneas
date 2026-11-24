pub fn add_saturate(a: u32, b: u32) -> u32 {
    if a > u32::MAX - b { u32::MAX } else { a + b }
}

#[cfg(kani)]
#[kani::proof]
fn check_add_saturate() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let r = add_saturate(a, b);
    assert_eq!(r as u64, (a as u64 + b as u64).min(u32::MAX as u64));
}
