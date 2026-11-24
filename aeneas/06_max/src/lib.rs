pub fn max(v: &[u32]) -> u32 {
    debug_assert!(!v.is_empty());
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
