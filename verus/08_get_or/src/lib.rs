use vstd::prelude::*;

verus! {

pub fn get_or<T: Copy>(v: &[T], i: usize, default: T) -> T
    returns
        (if i < v.len() { v[i as int] } else { default }),
{
    if i < v.len() { v[i] } else { default }
}

} // verus!
