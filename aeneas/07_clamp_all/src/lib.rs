pub fn clamp_all(v: &mut [u32], hi: u32) {
    for x in v.iter_mut() {
        if *x > hi {
            *x = hi;
        }
    }
}
