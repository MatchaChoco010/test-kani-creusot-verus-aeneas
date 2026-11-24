use vstd::prelude::*;
use vstd::simple_pptr::PPtr;

verus! {

pub fn incr_on_heap(v: u64) -> (r: u64)
    requires
        v < u64::MAX,
    ensures
        r == v + 1,
{
    let (p, Tracked(mut perm)) = PPtr::<u64>::new(v);
    let x = p.read(Tracked(&perm));
    p.write(Tracked(&mut perm), x + 1);
    p.into_inner(Tracked(perm))
}

} // verus!
