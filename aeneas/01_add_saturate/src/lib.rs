pub fn add_saturate(a: u32, b: u32) -> u32 {
    if a > u32::MAX - b { u32::MAX } else { a + b }
}
