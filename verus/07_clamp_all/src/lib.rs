use vstd::prelude::*;

verus! {

pub fn clamp_all(v: &mut [u32], hi: u32)
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|i: int| #![auto] 0 <= i < old(v)@.len() ==>
            final(v)@[i] == if old(v)@[i] > hi { hi } else { old(v)@[i] },
{
    for x in it: v.iter_mut()
        invariant
            forall|i: int| #![auto] 0 <= i < it.index() ==>
                *final(it.seq()[i]) == if *it.seq()[i] > hi { hi } else { *it.seq()[i] },
    {
        if *x > hi {
            *x = hi;
        }
    }
}

} // verus!
