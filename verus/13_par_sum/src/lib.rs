use rayon::prelude::*;
use vstd::prelude::*;

verus! {

pub trait Monoid: Sized + Copy + Send + Sync {
    spec fn id_spec() -> Self;

    spec fn op_spec(a: Self, b: Self) -> Self;

    proof fn lemma_assoc(a: Self, b: Self, c: Self)
        ensures
            Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)),
    ;

    proof fn lemma_id(a: Self)
        ensures
            Self::op_spec(Self::id_spec(), a) == a,
            Self::op_spec(a, Self::id_spec()) == a,
    ;

    fn id() -> (r: Self)
        ensures
            r == Self::id_spec(),
    ;

    fn op(a: Self, b: Self) -> (r: Self)
        ensures
            r == Self::op_spec(a, b),
    ;
}

pub open spec fn fold_spec<T: Monoid>(s: Seq<T>) -> T
    decreases s.len(),
{
    if s.len() == 0 {
        T::id_spec()
    } else {
        T::op_spec(fold_spec(s.drop_last()), s.last())
    }
}

// 本体は検証しない。T がモノイドなら、rayon の並列の畳み込みが順の畳み込みと等しいことを信用する
#[verifier::external_body]
pub fn par_sum<T: Monoid>(v: &[T]) -> (r: T)
    ensures
        r == fold_spec(v@),
{
    v.par_iter().copied().reduce(T::id, T::op)
}

// 本体は検証しない。rayon::join が両クロージャを実行して結果を返すことを信用する
#[verifier::external_body]
pub fn join<A, B, RA, RB>(a: A, b: B) -> (r: (RA, RB))
    where
        A: FnOnce() -> RA + Send,
        B: FnOnce() -> RB + Send,
        RA: Send,
        RB: Send,
    requires
        a.requires(()),
        b.requires(()),
    ensures
        a.ensures((), r.0),
        b.ensures((), r.1),
{
    rayon::join(a, b)
}

impl Monoid for u64 {
    open spec fn id_spec() -> u64 {
        0
    }

    open spec fn op_spec(a: u64, b: u64) -> u64 {
        if a + b > u64::MAX { u64::MAX } else { (a + b) as u64 }
    }

    proof fn lemma_assoc(a: u64, b: u64, c: u64) {
    }

    proof fn lemma_id(a: u64) {
    }

    fn id() -> (r: u64) {
        0
    }

    fn op(a: u64, b: u64) -> (r: u64) {
        a.saturating_add(b)
    }
}

pub open spec fn sum(s: Seq<u64>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum(s.drop_last()) + s.last()
    }
}

pub proof fn lemma_sum_concat(s: Seq<u64>, t: Seq<u64>)
    ensures
        sum(s + t) == sum(s) + sum(t),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t =~= s);
    } else {
        assert((s + t).drop_last() =~= s + t.drop_last());
        lemma_sum_concat(s, t.drop_last());
    }
}

pub proof fn lemma_fold_sum(s: Seq<u64>)
    ensures
        0 <= sum(s),
        sum(s) <= u64::MAX ==> fold_spec(s) == sum(s),
        sum(s) > u64::MAX ==> fold_spec(s) == u64::MAX,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_fold_sum(s.drop_last());
    }
}

pub fn mean(v: &[u64]) -> (r: u64)
    requires
        0 < v.len(),
        sum(v@) <= u64::MAX,
    ensures
        r == sum(v@) / v.len() as int,
{
    let (left, right) = v.split_at(v.len() / 2);
    proof {
        assert(v@ =~= left@ + right@);
        lemma_sum_concat(left@, right@);
        lemma_fold_sum(left@);
        lemma_fold_sum(right@);
    }
    let (a, b) = join(
        move || -> (s: u64)
            ensures
                s == fold_spec(left@),
            { par_sum(left) },
        move || -> (s: u64)
            ensures
                s == fold_spec(right@),
            { par_sum(right) },
    );
    (a + b) / v.len() as u64
}

// 検証失敗: Diff は結合律を満たさないので、Monoid の lemma_assoc を証明できない
// #[derive(Clone, Copy)]
// pub struct Diff(pub u64);
//
// impl Monoid for Diff {
//     open spec fn id_spec() -> Diff {
//         Diff(0)
//     }
//
//     open spec fn op_spec(a: Diff, b: Diff) -> Diff {
//         if a.0 >= b.0 { Diff((a.0 - b.0) as u64) } else { Diff((b.0 - a.0) as u64) }
//     }
//
//     proof fn lemma_assoc(a: Diff, b: Diff, c: Diff) {
//     }
//
//     proof fn lemma_id(a: Diff) {
//     }
//
//     fn id() -> (r: Diff) {
//         Diff(0)
//     }
//
//     fn op(a: Diff, b: Diff) -> (r: Diff) {
//         if a.0 >= b.0 { Diff(a.0 - b.0) } else { Diff(b.0 - a.0) }
//     }
// }
//
// pub fn diff_sum(v: &[Diff]) -> Diff {
//     par_sum(v)
// }

} // verus!
