use creusot_std::prelude::*;

#[ensures(i@ < v@.len() ==> result == v@[i@])]
#[ensures(i@ >= v@.len() ==> result == default)]
pub fn get_or<T: Copy>(v: &[T], i: usize, default: T) -> T {
    if i < v.len() { v[i] } else { default }
}
