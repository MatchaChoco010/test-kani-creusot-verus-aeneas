pub fn incr_on_heap(v: u64) -> u64 {
    let p: *mut u64 = Box::into_raw(Box::new(v));
    unsafe {
        *p += 1;
        let r = *p;
        drop(Box::from_raw(p));
        r
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_incr_on_heap() {
    let v: u64 = kani::any();
    kani::assume(v < u64::MAX);
    assert_eq!(incr_on_heap(v), v + 1);
}
