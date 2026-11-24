pub fn get_or<T: Copy>(v: &[T], i: usize, default: T) -> T {
    if i < v.len() { v[i] } else { default }
}

#[cfg(kani)]
fn check_get_or<T: kani::Arbitrary + Copy + PartialEq>() {
    let arr: [T; 3] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let i: usize = kani::any();
    let d: T = kani::any();
    let r = get_or(v, i, d);
    if i < v.len() {
        assert!(r == v[i]);
    } else {
        assert!(r == d);
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_get_or_u8() {
    check_get_or::<u8>();
}

#[cfg(kani)]
#[kani::proof]
fn check_get_or_char() {
    check_get_or::<char>();
}

// コンパイルエラー: #[kani::proof] はジェネリック関数に付けられない
// #[cfg(kani)]
// #[kani::proof]
// fn check_get_or_generic<T: kani::Arbitrary + Copy + PartialEq>() {
//     check_get_or::<T>();
// }
