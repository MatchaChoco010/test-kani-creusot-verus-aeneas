pub fn get_or<T: Copy>(v: &[T], i: usize, default: T) -> T {
    if i < v.len() { v[i] } else { default }
}
