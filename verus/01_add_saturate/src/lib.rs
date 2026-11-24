use vstd::prelude::*;

verus! {

pub fn add_saturate(a: u32, b: u32) -> u32
    returns
        (if a + b > u32::MAX { u32::MAX } else { (a + b) as u32 }),
{
    if a > u32::MAX - b { u32::MAX } else { a + b }
}

} // verus!
