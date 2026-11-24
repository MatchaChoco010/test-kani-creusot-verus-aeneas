pub fn incr_on_heap(v: u64) -> u64 {
    let p: *mut u64 = Box::into_raw(Box::new(v));
    unsafe {
        *p += 1;
        let r = *p;
        drop(Box::from_raw(p));
        r
    }
}
