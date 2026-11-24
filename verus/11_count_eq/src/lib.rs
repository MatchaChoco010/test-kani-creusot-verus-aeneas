use vstd::prelude::*;

verus! {

pub open spec fn count(s: Seq<u32>, x: u32) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == x { 1nat } else { 0nat }) + count(s.drop_first(), x)
    }
}

pub proof fn lemma_count_push(s: Seq<u32>, y: u32, x: u32)
    ensures
        count(s.push(y), x) == count(s, x) + (if y == x { 1nat } else { 0nat }),
    decreases s.len(),
{
    // 列の等しさはソルバーが自分では導かないので =~= で明示する
    if s.len() == 0 {
        assert(s.push(y).drop_first() =~= s);
    } else {
        assert(s.push(y).drop_first() =~= s.drop_first().push(y));
        // 再帰呼び出しが帰納法の仮定にあたる
        lemma_count_push(s.drop_first(), y, x);
    }
}

pub fn count_eq(v: &[u32], x: u32) -> (c: usize)
    ensures
        c == count(v@, x),
{
    let mut c: usize = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            c <= i,
            c == count(v@.subrange(0, i as int), x),
        decreases v.len() - i,
    {
        // 列の等しさはソルバーが自分では導かないので =~= で明示する
        assert(v@.subrange(0, i + 1) =~= v@.subrange(0, i as int).push(v[i as int]));
        // 補題を呼び出す
        proof {
            lemma_count_push(v@.subrange(0, i as int), v[i as int], x);
        }
        if v[i] == x {
            c += 1;
        }
        i += 1;
    }
    // 列の等しさはソルバーが自分では導かないので =~= で明示する
    assert(v@.subrange(0, v.len() as int) =~= v@);
    c
}

} // verus!
