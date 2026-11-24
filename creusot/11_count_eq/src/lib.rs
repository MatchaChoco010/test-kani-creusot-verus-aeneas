use creusot_std::prelude::*;
#[cfg(creusot)]
use creusot_std::logic::Seq;

#[logic(open)]
#[variant(s.len())]
pub fn count(s: Seq<u32>, x: u32) -> Int {
    if s.len() == 0 { 0 } else { (if s[0] == x { 1 } else { 0 }) + count(s.tail(), x) }
}

#[logic]
#[variant(s.len())]
#[ensures(count(s.push_back(y), x) == count(s, x) + if y == x { 1 } else { 0 })]
pub fn lemma_count_push_back(s: Seq<u32>, y: u32, x: u32) {
    if s.len() > 0 {
        // 列の等しさはソルバーが自分では導かないので明示する
        proof_assert!(s.push_back(y).tail().ext_eq(s.tail().push_back(y)));
        // 再帰呼び出しが帰納法の仮定にあたる
        lemma_count_push_back(s.tail(), y, x)
    }
}

#[ensures(result@ == count(v@, x))]
pub fn count_eq(v: &[u32], x: u32) -> usize {
    let mut c = 0;
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(c@ <= i@)]
    #[invariant(c@ == count(v@.subsequence(0, i@), x))]
    while i < v.len() {
        // 列の等しさはソルバーが自分では導かないので明示する
        proof_assert!(v@.subsequence(0, i@ + 1).ext_eq(v@.subsequence(0, i@).push_back(v@[i@])));
        // 補題を取り込む
        snapshot!(lemma_count_push_back(v@.subsequence(0, i@), v@[i@], x));
        if v[i] == x {
            c += 1;
        }
        i += 1;
    }
    c
}
