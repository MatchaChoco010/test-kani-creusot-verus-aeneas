pub fn count_eq(v: &[u32], x: u32) -> usize {
    let mut c = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i] == x {
            c += 1;
        }
        i += 1;
    }
    c
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn check_count_eq() {
    let arr: [u32; 5] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let x: u32 = kani::any();
    assert_eq!(count_eq(v, x), v.iter().filter(|&&y| y == x).count());
}
