use creusot_std::prelude::*;

#[requires(v@.len() > 0)]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> v@[i] <= result)]
#[ensures(exists<i> 0 <= i && i < v@.len() && v@[i] == result)]
pub fn max(v: &[u32]) -> u32 {
    let mut m = v[0];
    let mut i = 1;
    #[invariant(1 <= i@ && i@ <= v@.len())]
    #[invariant(forall<j> 0 <= j && j < i@ ==> v@[j] <= m)]
    #[invariant(exists<j> 0 <= j && j < i@ && v@[j] == m)]
    while i < v.len() {
        if v[i] > m {
            m = v[i];
        }
        i += 1;
    }
    m
}
