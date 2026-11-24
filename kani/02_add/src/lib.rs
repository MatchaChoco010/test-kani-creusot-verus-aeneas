pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

pub fn double(a: u32) -> u32 {
    add(a, a)
}

pub fn double_checked(a: u32) -> Option<u32> {
    if a <= u32::MAX / 2 { Some(add(a, a)) } else { None }
}

#[cfg(kani)]
#[kani::proof]
fn check_add() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a as u64 + b as u64 <= u32::MAX as u64);
    assert_eq!(add(a, b) as u64, a as u64 + b as u64);
}

// 検証失敗: a + a がオーバーフローし得る
// #[cfg(kani)]
// #[kani::proof]
// fn check_double() {
//     double(kani::any());
// }

#[cfg(kani)]
#[kani::proof]
fn check_double_checked() {
    let a: u32 = kani::any();
    let r = double_checked(a);
    if a <= u32::MAX / 2 {
        assert_eq!(r, Some(a * 2));
    } else {
        assert_eq!(r, None);
    }
}
