use rayon::prelude::*;

pub trait Monoid: Copy + Send + Sync {
    fn id() -> Self;
    fn op(a: Self, b: Self) -> Self;
}

pub fn par_sum<T: Monoid>(v: &[T]) -> T {
    v.par_iter().copied().reduce(T::id, T::op)
}

impl Monoid for u64 {
    fn id() -> u64 {
        0
    }

    fn op(a: u64, b: u64) -> u64 {
        a.saturating_add(b)
    }
}

#[derive(Clone, Copy)]
pub struct Diff(pub u64);

impl Monoid for Diff {
    fn id() -> Diff {
        Diff(0)
    }

    fn op(a: Diff, b: Diff) -> Diff {
        if a.0 >= b.0 { Diff(a.0 - b.0) } else { Diff(b.0 - a.0) }
    }
}

pub fn diff_sum(v: &[Diff]) -> Diff {
    par_sum(v)
}

fn sum_fits_u64(v: &[u64]) -> bool {
    let mut s: u64 = 0;
    let mut i = 0;
    while i < v.len() {
        match s.checked_add(v[i]) {
            Some(t) => s = t,
            None => return false,
        }
        i += 1;
    }
    true
}

pub fn mean(v: &[u64]) -> u64 {
    debug_assert!(!v.is_empty() && sum_fits_u64(v));
    let (left, right) = v.split_at(v.len() / 2);
    let (a, b) = rayon::join(|| par_sum(left), || par_sum(right));
    (a + b) / v.len() as u64
}
