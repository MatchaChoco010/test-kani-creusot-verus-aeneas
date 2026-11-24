use creusot_std::{ghost::perm::Perm, prelude::*};

#[requires(v@ < u64::MAX@)]
#[ensures(result@ == v@ + 1)]
pub fn incr_on_heap(v: u64) -> u64 {
    let (p, mut perm) = Perm::new(v);
    unsafe {
        *Perm::as_mut(p, perm.borrow_mut()) += 1;
        let r = *Perm::as_ref(p, perm.borrow());
        Perm::drop(p, perm);
        r
    }
}
