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
