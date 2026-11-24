pub fn add(a: u32, b: u32) -> u32 {
    debug_assert!(a <= u32::MAX - b);
    a + b
}

pub fn double(a: u32) -> u32 {
    add(a, a)
}

pub fn double_checked(a: u32) -> Option<u32> {
    if a <= u32::MAX / 2 { Some(add(a, a)) } else { None }
}
