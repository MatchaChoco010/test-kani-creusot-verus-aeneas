pub trait Monoid: Copy {
    fn id() -> Self;
    fn op(a: Self, b: Self) -> Self;
}

pub fn fold<T: Monoid>(v: &[T]) -> T {
    let mut acc = T::id();
    let mut i = 0;
    while i < v.len() {
        acc = T::op(acc, v[i]);
        i += 1;
    }
    acc
}

pub fn fold_halves<T: Monoid>(v: &[T]) -> T {
    let (left, right) = v.split_at(v.len() / 2);
    T::op(fold(left), fold(right))
}

#[derive(Clone, Copy)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Max(pub u32);

impl Monoid for Max {
    fn id() -> Max {
        Max(0)
    }

    fn op(a: Max, b: Max) -> Max {
        if a.0 >= b.0 { a } else { b }
    }
}

pub fn max_halves(v: &[Max]) -> Max {
    fold_halves(v)
}

#[derive(Clone, Copy)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Diff(pub u32);

impl Monoid for Diff {
    fn id() -> Diff {
        Diff(0)
    }

    fn op(a: Diff, b: Diff) -> Diff {
        if a.0 >= b.0 { Diff(a.0 - b.0) } else { Diff(b.0 - a.0) }
    }
}

pub fn diff_halves(v: &[Diff]) -> Diff {
    fold_halves(v)
}

#[cfg(kani)]
#[kani::proof]
fn check_max_laws() {
    let a: Max = kani::any();
    let b: Max = kani::any();
    let c: Max = kani::any();
    assert_eq!(Max::op(Max::op(a, b), c).0, Max::op(a, Max::op(b, c)).0);
    assert_eq!(Max::op(Max::id(), a).0, a.0);
    assert_eq!(Max::op(a, Max::id()).0, a.0);
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn check_max_halves() {
    let arr: [Max; 4] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    assert_eq!(max_halves(v).0, fold(v).0);
}

// 検証失敗: Diff は結合律を満たさない
// #[cfg(kani)]
// #[kani::proof]
// fn check_diff_laws() {
//     let a: Diff = kani::any();
//     let b: Diff = kani::any();
//     let c: Diff = kani::any();
//     assert_eq!(Diff::op(Diff::op(a, b), c).0, Diff::op(a, Diff::op(b, c)).0);
// }
