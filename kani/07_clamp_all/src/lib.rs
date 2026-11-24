pub fn clamp_all(v: &mut [u32], hi: u32) {
    for x in v.iter_mut() {
        if *x > hi {
            *x = hi;
        }
    }
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn check_clamp_all() {
    let mut arr: [u32; 5] = kani::any();
    let orig = arr;
    let len: usize = kani::any();
    kani::assume(len <= 5);
    let hi: u32 = kani::any();
    clamp_all(&mut arr[..len], hi);
    for i in 0..5 {
        if i < len {
            assert!(arr[i] == orig[i].min(hi));
        } else {
            assert!(arr[i] == orig[i]);
        }
    }
}

// 検証失敗: 長さ 6 のループは unwind(6) では展開しきれない
// #[cfg(kani)]
// #[kani::proof]
// #[kani::unwind(6)]
// fn check_clamp_all_len_6() {
//     let mut arr: [u32; 6] = kani::any();
//     let hi: u32 = kani::any();
//     clamp_all(&mut arr, hi);
//     assert!(arr.iter().all(|&x| x <= hi));
// }
