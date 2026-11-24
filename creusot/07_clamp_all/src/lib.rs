use creusot_std::prelude::*;

#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> (^v)@[i] == if v@[i] > hi { hi } else { v@[i] })]
pub fn clamp_all(v: &mut [u32], hi: u32) {
    #[invariant(forall<i> 0 <= i && i < produced.len() ==>
        ^produced[i] == if *produced[i] > hi { hi } else { *produced[i] })]
    for x in v.iter_mut() {
        if *x > hi {
            *x = hi;
        }
    }
}
