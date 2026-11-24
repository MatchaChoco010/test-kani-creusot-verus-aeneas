#[cfg(creusot)]
use creusot_std::logic::Seq;
use creusot_std::prelude::*;
use rayon::prelude::*;

pub trait Monoid: Sized + Copy + Send + Sync {
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

// 本体は検証しない。T がモノイドなら、rayon の並列の畳み込みが順の畳み込みと等しいことを信用する
#[trusted]
#[ensures(result == fold_spec(v@))]
pub fn par_sum<T: Monoid>(v: &[T]) -> T {
    v.par_iter().copied().reduce(T::id, T::op)
}

// 本体は検証しない。rayon::join が両クロージャを実行して結果を返すことを信用する
#[trusted]
#[requires(a.precondition(()) && b.precondition(()))]
#[ensures(a.postcondition_once((), result.0) && b.postcondition_once((), result.1))]
pub fn join<A, B, RA, RB>(a: A, b: B) -> (RA, RB)
where
    A: FnOnce() -> RA + Send,
    B: FnOnce() -> RB + Send,
    RA: Send,
    RB: Send,
{
    rayon::join(a, b)
}

impl Monoid for u64 {
    #[logic(open)]
    fn id_spec() -> u64 {
        0u64
    }

    #[logic(open)]
    fn op_spec(a: u64, b: u64) -> u64 {
        pearlite! { if a@ + b@ > u64::MAX@ { u64::MAX } else { a + b } }
    }

    #[logic]
    #[ensures(Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)))]
    fn assoc(a: u64, b: u64, c: u64) {}

    #[logic]
    #[ensures(Self::op_spec(Self::id_spec(), a) == a)]
    #[ensures(Self::op_spec(a, Self::id_spec()) == a)]
    fn identity(a: u64) {}

    #[ensures(result == Self::id_spec())]
    fn id() -> u64 {
        0
    }

    #[ensures(result == Self::op_spec(a, b))]
    fn op(a: u64, b: u64) -> u64 {
        a.saturating_add(b)
    }
}

#[logic(open)]
#[variant(s.len())]
pub fn sum(s: Seq<u64>) -> Int {
    pearlite! { if s.len() == 0 { 0 } else { sum(s.subsequence(0, s.len() - 1)) + s[s.len() - 1]@ } }
}

#[logic]
#[variant(t.len())]
#[ensures(sum(s.concat(t)) == sum(s) + sum(t))]
pub fn lemma_sum_concat(s: Seq<u64>, t: Seq<u64>) {
    if t.len() == 0 {
        proof_assert!(s.concat(t).ext_eq(s));
    } else {
        proof_assert!(s.concat(t).subsequence(0, s.len() + t.len() - 1).ext_eq(s.concat(t.subsequence(0, t.len() - 1))));
        lemma_sum_concat(s, t.subsequence(0, t.len() - 1))
    }
}

#[logic]
#[variant(s.len())]
#[ensures(0 <= sum(s))]
#[ensures(sum(s) <= u64::MAX@ ==> fold_spec(s)@ == sum(s))]
#[ensures(sum(s) > u64::MAX@ ==> fold_spec(s) == u64::MAX)]
pub fn lemma_fold_sum(s: Seq<u64>) {
    if s.len() > 0 {
        lemma_fold_sum(s.subsequence(0, s.len() - 1))
    }
}

#[requires(0 < v@.len() && sum(v@) <= u64::MAX@)]
#[ensures(result@ == sum(v@) / v@.len())]
pub fn mean(v: &[u64]) -> u64 {
    let (left, right) = v.split_at(v.len() / 2);
    proof_assert!(v@.ext_eq(left@.concat(right@)));
    snapshot!(lemma_sum_concat(left@, right@));
    snapshot!(lemma_fold_sum(left@));
    snapshot!(lemma_fold_sum(right@));
    let (a, b) = join(move || par_sum(left), move || par_sum(right));
    (a + b) / v.len() as u64
}

// 検証失敗: Diff は結合律を満たさないので、Monoid の法則 assoc を証明できない
// #[derive(core::clone::Clone, Copy)]
// pub struct Diff(pub u64);
//
// impl Monoid for Diff {
//     #[logic(open)]
//     fn id_spec() -> Diff {
//         Diff(0u64)
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
//
// pub fn diff_sum(v: &[Diff]) -> Diff {
//     par_sum(v)
// }
