#[cfg(creusot)]
use creusot_std::logic::Seq;
use creusot_std::prelude::*;

pub trait Monoid: Sized + Copy {
    #[logic]
    fn id_spec() -> Self;

    #[logic]
    fn op_spec(a: Self, b: Self) -> Self;

    #[logic(law)]
    #[ensures(Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)))]
    fn assoc(a: Self, b: Self, c: Self);

    #[logic(law)]
    #[ensures(Self::op_spec(Self::id_spec(), a) == a)]
    #[ensures(Self::op_spec(a, Self::id_spec()) == a)]
    fn identity(a: Self);

    #[ensures(result == Self::id_spec())]
    fn id() -> Self;

    #[ensures(result == Self::op_spec(a, b))]
    fn op(a: Self, b: Self) -> Self;
}

#[logic(open)]
#[variant(s.len())]
pub fn fold_spec<T: Monoid>(s: Seq<T>) -> T {
    pearlite! {
        if s.len() == 0 {
            T::id_spec()
        } else {
            T::op_spec(fold_spec(s.subsequence(0, s.len() - 1)), s[s.len() - 1])
        }
    }
}

#[logic]
#[variant(t.len())]
#[ensures(fold_spec(s.concat(t)) == T::op_spec(fold_spec(s), fold_spec(t)))]
pub fn lemma_fold_concat<T: Monoid>(s: Seq<T>, t: Seq<T>) {
    if t.len() == 0 {
        proof_assert!(s.concat(t).ext_eq(s));
    } else {
        proof_assert!(s.concat(t).subsequence(0, s.len() + t.len() - 1).ext_eq(s.concat(t.subsequence(0, t.len() - 1))));
        lemma_fold_concat(s, t.subsequence(0, t.len() - 1))
    }
}

#[ensures(result == fold_spec(v@))]
pub fn fold<T: Monoid>(v: &[T]) -> T {
    let mut acc = T::id();
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(acc == fold_spec(v@.subsequence(0, i@)))]
    while i < v.len() {
        proof_assert!(v@.subsequence(0, i@ + 1).subsequence(0, i@).ext_eq(v@.subsequence(0, i@)));
        acc = T::op(acc, v[i]);
        i += 1;
    }
    proof_assert!(v@.subsequence(0, v@.len()).ext_eq(v@));
    acc
}

#[ensures(result == fold_spec(v@))]
pub fn fold_halves<T: Monoid>(v: &[T]) -> T {
    let (left, right) = v.split_at(v.len() / 2);
    proof_assert!(v@.ext_eq(left@.concat(right@)));
    snapshot!(lemma_fold_concat(left@, right@));
    T::op(fold(left), fold(right))
}

#[derive(core::clone::Clone, Copy)]
pub struct Max(pub u32);

impl Monoid for Max {
    #[logic(open)]
    fn id_spec() -> Max {
        Max(0u32)
    }

    #[logic(open)]
    fn op_spec(a: Max, b: Max) -> Max {
        pearlite! { if a.0@ >= b.0@ { a } else { b } }
    }

    #[logic]
    #[ensures(Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)))]
    fn assoc(a: Max, b: Max, c: Max) {}

    #[logic]
    #[ensures(Self::op_spec(Self::id_spec(), a) == a)]
    #[ensures(Self::op_spec(a, Self::id_spec()) == a)]
    fn identity(a: Max) {}

    #[ensures(result == Self::id_spec())]
    fn id() -> Max {
        Max(0)
    }

    #[ensures(result == Self::op_spec(a, b))]
    fn op(a: Max, b: Max) -> Max {
        if a.0 >= b.0 { a } else { b }
    }
}

#[ensures(result == fold_spec(v@))]
pub fn max_halves(v: &[Max]) -> Max {
    fold_halves(v)
}

// 検証失敗: Diff は結合律を満たさないので、Monoid の法則 assoc を証明できない
// #[derive(core::clone::Clone, Copy)]
// pub struct Diff(pub u32);
//
// impl Monoid for Diff {
//     #[logic(open)]
//     fn id_spec() -> Diff {
//         Diff(0u32)
//     }
//
//     #[logic(open)]
//     fn op_spec(a: Diff, b: Diff) -> Diff {
//         pearlite! { if a.0@ >= b.0@ { Diff(a.0 - b.0) } else { Diff(b.0 - a.0) } }
//     }
//
//     #[logic]
//     #[ensures(Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)))]
//     fn assoc(a: Diff, b: Diff, c: Diff) {}
//
//     #[logic]
//     #[ensures(Self::op_spec(Self::id_spec(), a) == a)]
//     #[ensures(Self::op_spec(a, Self::id_spec()) == a)]
//     fn identity(a: Diff) {}
//
//     #[ensures(result == Self::id_spec())]
//     fn id() -> Diff {
//         Diff(0)
//     }
//
//     #[ensures(result == Self::op_spec(a, b))]
//     fn op(a: Diff, b: Diff) -> Diff {
//         if a.0 >= b.0 { Diff(a.0 - b.0) } else { Diff(b.0 - a.0) }
//     }
// }
