use creusot_std::prelude::*;
use crate::model::*;

#[requires(i@ < v@.len())]
#[ensures(result == forall<j> i@ < j && j < v@.len() ==> v@[i@] != v@[j])]
#[check(terminates)]
fn not_in_rest(v: &Vec<u64>, i: usize) -> bool {
    let mut j = i + 1;
    #[invariant(i@ < j@ && j@ <= v@.len())]
    #[invariant(forall<k> i@ < k && k < j@ ==> v@[i@] != v@[k])]
    #[variant(v@.len() - j@)]
    while j < v.len() {
        if v[i] == v[j] {
            return false;
        }
        j += 1;
    }
    true
}

#[logic(open)]
pub fn unique_seq(v: Seq<u64>) -> bool {
    pearlite! { forall<i, j> 0 <= i && i < j && j < v.len() ==> v[i] != v[j] }
}

#[ensures(result == unique_seq(v@))]
#[check(terminates)]
pub(crate) fn unique(v: &Vec<u64>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(forall<a, b> 0 <= a && a < i@ && a < b && b < v@.len() ==> v@[a] != v@[b])]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        if !not_in_rest(v, i) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(open)]
pub fn all_lt(v: Seq<u64>, n: Int) -> bool {
    pearlite! { forall<k> 0 <= k && k < v.len() ==> v[k]@ < n }
}

#[ensures(result == all_lt(v@, n@))]
#[check(terminates)]
pub(crate) fn all_less(v: &Vec<u64>, n: usize) -> bool {
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> v@[k]@ < n@)]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        if v[i] >= n as u64 {
            return false;
        }
        i += 1;
    }
    true
}

// opt_lt(o, n) := o = None ∨ o < n
#[logic(open)]
pub fn opt_lt(o: Option<u64>, n: Int) -> bool {
    pearlite! {
        match o {
            None => true,
            Some(v) => v@ < n,
        }
    }
}

#[ensures(result == opt_lt(o, n@))]
#[check(terminates)]
pub(crate) fn opt_less(o: Option<u64>, n: usize) -> bool {
    match o {
        None => true,
        Some(v) => v < n as u64,
    }
}

#[ensures(result == opt_lt(o, n@))]
#[check(terminates)]
pub(crate) fn opt_less_u64(o: Option<u64>, n: u64) -> bool {
    match o {
        None => true,
        Some(v) => v < n,
    }
}

#[requires(i@ < v@.len())]
#[ensures(result == forall<j> i@ < j && j < v@.len() ==> v@[i@]@ != v@[j]@)]
#[check(terminates)]
fn string_not_in_rest(v: &Vec<Vec<u8>>, i: usize) -> bool {
    let mut j = i + 1;
    #[invariant(i@ < j@ && j@ <= v@.len())]
    #[invariant(forall<k> i@ < k && k < j@ ==> v@[i@]@ != v@[k]@)]
    #[variant(v@.len() - j@)]
    while j < v.len() {
        if bytes_eq(&v[i], &v[j]) {
            return false;
        }
        j += 1;
    }
    true
}

#[logic(open)]
pub fn str_unique(v: Seq<Vec<u8>>) -> bool {
    pearlite! { forall<i, j> 0 <= i && i < j && j < v.len() ==> v[i]@ != v[j]@ }
}

#[ensures(result == str_unique(v@))]
#[check(terminates)]
pub(crate) fn strings_unique(v: &Vec<Vec<u8>>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(forall<a, b> 0 <= a && a < i@ && a < b && b < v@.len() ==> v@[a]@ != v@[b]@)]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        if !string_not_in_rest(v, i) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(open)]
pub fn str_in(v: Seq<Vec<u8>>, s: Seq<u8>) -> bool {
    pearlite! { exists<k> 0 <= k && k < v.len() && v[k]@ == s }
}

#[ensures(result == str_in(v@, s@))]
#[check(terminates)]
fn strings_contains(v: &Vec<Vec<u8>>, s: &Vec<u8>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> v@[k]@ != s@)]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        if bytes_eq(&v[i], s) {
            return true;
        }
        i += 1;
    }
    false
}

#[logic(open)]
pub fn str_subset(a: Seq<Vec<u8>>, b: Seq<Vec<u8>>) -> bool {
    pearlite! { forall<i> 0 <= i && i < a.len() ==> str_in(b, a[i]@) }
}

#[ensures(result == str_subset(a@, b@))]
#[check(terminates)]
pub(crate) fn strings_subset(a: &Vec<Vec<u8>>, b: &Vec<Vec<u8>>) -> bool {
    let mut i = 0;
    #[invariant(i@ <= a@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> str_in(b@, a@[k]@))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        if !strings_contains(b, &a[i]) {
            return false;
        }
        i += 1;
    }
    true
}

// float32 = 5126、unorm8/16 = normalized の 5121/5123、snorm8/16 = normalized の 5120/5122、uint8/16 = 正規化なしの 5121/5123
#[logic(open)]
pub fn f32_ty(a: Accessor) -> bool {
    pearlite! { a.component_type@ == 5126 }
}

#[ensures(result == (a.component_type@ == 5126))]
#[ensures(result == f32_ty(*a))]
#[check(terminates)]
pub(crate) fn float32(a: &Accessor) -> bool {
    a.component_type == 5126
}

#[logic(open)]
pub fn unorm_ty(a: Accessor) -> bool {
    pearlite! { a.normalized && (a.component_type@ == 5121 || a.component_type@ == 5123) }
}

#[ensures(result == unorm_ty(*a))]
#[check(terminates)]
pub(crate) fn unorm8_16(a: &Accessor) -> bool {
    a.normalized && (a.component_type == 5121 || a.component_type == 5123)
}

#[logic(open)]
pub fn snorm_ty(a: Accessor) -> bool {
    pearlite! { a.normalized && (a.component_type@ == 5120 || a.component_type@ == 5122) }
}

#[ensures(result == snorm_ty(*a))]
#[check(terminates)]
pub(crate) fn snorm8_16(a: &Accessor) -> bool {
    a.normalized && (a.component_type == 5120 || a.component_type == 5122)
}

#[ensures(result == exists<k> 0 <= k && k < v@.len() && v@[k] == x)]
#[check(terminates)]
pub(crate) fn contains(v: &Vec<u64>, x: u64) -> bool {
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> v@[k] != x)]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}
