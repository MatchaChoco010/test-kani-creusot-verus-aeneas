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

pub fn mean(v: &[u64]) -> u64 {
    let (left, right) = v.split_at(v.len() / 2);
    let (a, b) = rayon::join(|| par_sum(left), || par_sum(right));
    (a + b) / v.len() as u64
}

// rayon はスレッドを使うので検証できない。par_sum と rayon::join を逐次版に差し替え、その振る舞いを信用する
#[cfg(kani)]
fn seq_sum<T: Monoid>(v: &[T]) -> T {
    let mut acc = T::id();
    for &x in v {
        acc = T::op(acc, x);
    }
    acc
}

#[cfg(kani)]
fn seq_join<A, B, RA, RB>(oper_a: A, oper_b: B) -> (RA, RB)
where
    A: FnOnce() -> RA + Send,
    B: FnOnce() -> RB + Send,
    RA: Send,
    RB: Send,
{
    (oper_a(), oper_b())
}

#[cfg(kani)]
#[kani::proof]
#[kani::stub(par_sum, seq_sum)]
#[kani::stub(rayon::join, seq_join)]
#[kani::unwind(5)]
fn check_mean() {
    let arr: [u64; 4] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    kani::assume(!v.is_empty());
    let total = v.iter().try_fold(0u64, |s, &x| s.checked_add(x));
    kani::assume(total.is_some());
    assert_eq!(mean(v), total.unwrap() / v.len() as u64);
}

// Kani が内部エラーで停止する: rayon が内部で立てるスレッドに対応していない
// #[cfg(kani)]
// #[kani::proof]
// #[kani::unwind(5)]
// fn check_mean_without_stub() {
//     let arr: [u64; 4] = kani::any();
//     let v = kani::slice::any_slice_of_array(&arr);
//     kani::assume(!v.is_empty());
//     let total = v.iter().try_fold(0u64, |s, &x| s.checked_add(x));
//     kani::assume(total.is_some());
//     assert_eq!(mean(v), total.unwrap() / v.len() as u64);
// }
