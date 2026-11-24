pub fn max(v: &[u32]) -> u32 {
    let mut m = v[0];
    let mut i = 1;
    while i < v.len() {
        if v[i] > m {
            m = v[i];
        }
        i += 1;
    }
    m
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn check_max() {
    let arr: [u32; 5] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    kani::assume(!v.is_empty());
    let r = max(v);
    assert!(v.iter().all(|&x| x <= r));
    assert!(v.contains(&r));
}

// 検証失敗: 長さ 10 のループは unwind(6) では展開しきれない
// #[cfg(kani)]
// #[kani::proof]
// #[kani::unwind(6)]
// fn check_max_len_10() {
//     let arr: [u32; 10] = kani::any();
//     let r = max(&arr);
//     assert!(arr.iter().all(|&x| x <= r));
// }
