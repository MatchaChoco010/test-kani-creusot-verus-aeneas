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
