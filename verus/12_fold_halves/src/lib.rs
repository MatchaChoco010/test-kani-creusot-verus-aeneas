use vstd::prelude::*;

verus! {

pub trait Monoid: Sized + Copy {
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

pub proof fn lemma_fold_concat<T: Monoid>(s: Seq<T>, t: Seq<T>)
    ensures
        fold_spec(s + t) == T::op_spec(fold_spec(s), fold_spec(t)),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(s + t =~= s);
        T::lemma_id(fold_spec(s));
    } else {
        assert((s + t).drop_last() =~= s + t.drop_last());
        lemma_fold_concat(s, t.drop_last());
        T::lemma_assoc(fold_spec(s), fold_spec(t.drop_last()), t.last());
    }
}

pub fn fold<T: Monoid>(v: &[T]) -> (r: T)
    ensures
        r == fold_spec(v@),
{
    let mut acc = T::id();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            acc == fold_spec(v@.subrange(0, i as int)),
        decreases v.len() - i,
    {
        assert(v@.subrange(0, i + 1).drop_last() =~= v@.subrange(0, i as int));
        acc = T::op(acc, v[i]);
        i += 1;
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    acc
}

pub fn fold_halves<T: Monoid>(v: &[T]) -> (r: T)
    ensures
        r == fold_spec(v@),
{
    let (left, right) = v.split_at(v.len() / 2);
    proof {
        assert(v@ =~= left@ + right@);
        lemma_fold_concat(left@, right@);
    }
    T::op(fold(left), fold(right))
}

#[derive(Clone, Copy)]
pub struct Max(pub u32);

impl Monoid for Max {
    open spec fn id_spec() -> Max {
        Max(0)
    }

    open spec fn op_spec(a: Max, b: Max) -> Max {
        if a.0 >= b.0 { a } else { b }
    }

    proof fn lemma_assoc(a: Max, b: Max, c: Max) {
    }

    proof fn lemma_id(a: Max) {
    }

    fn id() -> (r: Max) {
        Max(0)
    }

    fn op(a: Max, b: Max) -> (r: Max) {
        if a.0 >= b.0 { a } else { b }
    }
}

pub fn max_halves(v: &[Max]) -> (r: Max)
    ensures
        r == fold_spec(v@),
{
    fold_halves(v)
}

// 検証失敗: Diff は結合律を満たさないので、Monoid の lemma_assoc を証明できない
// #[derive(Clone, Copy)]
// pub struct Diff(pub u32);
//
// impl Monoid for Diff {
//     open spec fn id_spec() -> Diff {
//         Diff(0)
//     }
//
//     open spec fn op_spec(a: Diff, b: Diff) -> Diff {
//         if a.0 >= b.0 { Diff((a.0 - b.0) as u32) } else { Diff((b.0 - a.0) as u32) }
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

} // verus!
