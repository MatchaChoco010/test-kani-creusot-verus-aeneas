use creusot_std::prelude::*;
#[cfg(creusot)]
use crate::model::*;

pub struct Number {
    pub negative: bool,
    pub int_digits: Vec<u8>,
    pub frac_digits: Vec<u8>,
    pub exp_negative: bool,
    pub exp_digits: Vec<u8>,
}

#[logic(open)]
pub fn is_dec(b: u8) -> bool {
    pearlite! { 48 <= b@ && b@ <= 57 }
}

#[ensures(result == is_dec(b))]
#[check(terminates)]
pub(crate) fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

// i 以上で、|s| に等しいか数字でない最小の位置
#[logic(open)]
#[variant(s.len() - i)]
#[ensures(0 <= i && i <= s.len() ==> i <= result && result <= s.len())]
#[ensures(0 <= i && i <= s.len() ==> (forall<k> i <= k && k < result ==> is_dec(s[k])) && (result == s.len() || !is_dec(s[result])))]
pub fn digits_end(s: Seq<u8>, i: Int) -> Int {
    pearlite! { if i < 0 || i >= s.len() { i } else if is_dec(s[i]) { digits_end(s, i + 1) } else { i } }
}

// s[a..b] の数字の値（0〜9）の列
#[logic(open)]
pub fn digit_seq(s: Seq<u8>, a: Int, b: Int) -> Seq<u8> {
    pearlite! { Seq::create(b - a, |t: Int| byte(s[a + t]@ - 48)) }
}

#[logic(opaque)]
#[requires(0 <= a && a <= b && b <= s.len() && o.len() == o0.len() + (b - a))]
#[requires(forall<t> 0 <= t && t < o0.len() ==> o[t] == o0[t])]
#[requires(forall<t> o0.len() <= t && t < o.len() ==> o[t]@ == s[a + (t - o0.len())]@ - 48)]
#[ensures(o == o0.concat(digit_seq(s, a, b)))]
pub fn lemma_concat_digits(o: Seq<u8>, o0: Seq<u8>, s: Seq<u8>, a: Int, b: Int) {
    proof_assert!(forall<t> 0 <= t && t < b - a ==> digit_seq(s, a, b)[t] == byte(s[a + t]@ - 48));
    proof_assert!(o.ext_eq(o0.concat(digit_seq(s, a, b))));
}

#[requires(i@ <= s@.len())]
#[ensures(result@ == digits_end(s@, i@))]
#[ensures((^out)@ == (*out)@.concat(digit_seq(s@, i@, result@)))]
#[check(terminates)]
fn parse_digits(s: &[u8], i: usize, out: &mut Vec<u8>) -> usize {
    let mut j = i;
    let _o0 = snapshot!(out@);
    #[invariant(i@ <= j@ && j@ <= s@.len())]
    #[invariant(digits_end(s@, i@) == digits_end(s@, j@))]
    #[invariant(forall<t> i@ <= t && t < j@ ==> is_dec(s@[t]))]
    #[invariant(out@.len() == _o0.len() + (j@ - i@))]
    #[invariant(forall<t> 0 <= t && t < _o0.len() ==> out@[t] == _o0[t])]
    #[invariant(forall<t> _o0.len() <= t && t < out@.len() ==> out@[t]@ == s@[i@ + (t - _o0.len())]@ - 48)]
    #[variant(s@.len() - j@)]
    while j < s.len() && is_digit(s[j]) {
        out.push(s[j] - b'0');
        j += 1;
    }
    snapshot!(lemma_concat_digits(out@, *_o0, s@, i@, j@));
    j
}

// JSON の数値の抽象値（桁は 0〜9 の値）
#[cfg(creusot)]
pub struct NumS {
    pub neg: bool,
    pub int: Seq<u8>,
    pub frac: Seq<u8>,
    pub eneg: bool,
    pub exp: Seq<u8>,
}

#[logic(open)]
pub fn num_view(n: Number) -> NumS {
    pearlite! {
        NumS { neg: n.negative, int: n.int_digits@, frac: n.frac_digits@, eneg: n.exp_negative, exp: n.exp_digits@ }
    }
}

#[logic(open)]
#[ensures(0 <= p && p <= s.len() ==> match result { Some((_, e)) => p <= e && e <= s.len(), None => true })]
pub fn exp_part(s: Seq<u8>, ss: Int, neg: bool, ie: Int, fs: Int, fe: Int, p: Int) -> Option<(NumS, Int)> {
    pearlite! {
        if p < s.len() && (s[p]@ == 101 || s[p]@ == 69) {
            let sign = p + 1 < s.len() && (s[p + 1]@ == 43 || s[p + 1]@ == 45);
            let eneg = sign && s[p + 1]@ == 45;
            let es = if sign { p + 2 } else { p + 1 };
            let ee = digits_end(s, es);
            if ee == es {
                None
            } else {
                Some((NumS { neg: neg, int: digit_seq(s, ss, ie), frac: digit_seq(s, fs, fe), eneg: eneg, exp: digit_seq(s, es, ee) }, ee))
            }
        } else {
            Some((NumS { neg: neg, int: digit_seq(s, ss, ie), frac: digit_seq(s, fs, fe), eneg: false, exp: Seq::empty() }, p))
        }
    }
}

// number(s, i): -? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?
// RFC 8259 §6: 数値
#[logic(open)]
#[ensures(0 <= i && i < s.len() ==> match result { Some((_, e)) => i < e && e <= s.len(), None => true })]
pub fn number_spec(s: Seq<u8>, i: Int) -> Option<(NumS, Int)> {
    pearlite! {
        let neg = s[i]@ == 45;
        let ss = if neg { i + 1 } else { i };
        if ss >= s.len() || !is_dec(s[ss]) {
            None
        } else {
            let ie = if s[ss]@ == 48 { ss + 1 } else { digits_end(s, ss) };
            if ie < s.len() && s[ie]@ == 46 {
                let fe = digits_end(s, ie + 1);
                if fe == ie + 1 { None } else { exp_part(s, ss, neg, ie, ie + 1, fe, fe) }
            } else {
                exp_part(s, ss, neg, ie, ie, ie, ie)
            }
        }
    }
}

// 数値の表現の不変条件（number_spec の num_ok）
#[logic(open)]
pub fn num_repr_ok(n: NumS) -> bool {
    pearlite! { num_ok(n) }
}

#[logic(opaque)]
#[requires(0 <= a && a <= b && b <= s.len())]
#[requires(forall<t> a <= t && t < b ==> is_dec(s[t]))]
#[ensures(forall<t> 0 <= t && t < digit_seq(s, a, b).len() ==> digit_seq(s, a, b)[t]@ <= 9)]
#[ensures(digit_seq(s, a, b).len() == b - a)]
pub fn lemma_digit_seq_ok(s: Seq<u8>, a: Int, b: Int) {}

#[logic(open)]
pub fn digits_le9(s: Seq<u8>) -> bool {
    pearlite! { forall<k> 0 <= k && k < s.len() ==> s[k]@ <= 9 }
}

// Number の表現の不変条件: 各桁が 9 以下で、3 つの桁列の長さの和が usize に収まる
#[logic(open)]
pub fn num_ok(ns: NumS) -> bool {
    pearlite! {
        digits_le9(ns.int) && digits_le9(ns.frac) && digits_le9(ns.exp)
            && ns.int.len() + ns.frac.len() + ns.exp.len() <= usize::MAX@
    }
}

// RFC 8259 §6: 数値
#[requires(i@ < s@.len())]
#[ensures(match result {
    None => number_spec(s@, i@) == None,
    Some((n, j)) => number_spec(s@, i@) == Some((num_view(n), j@)) && num_repr_ok(num_view(n)),
})]
#[check(terminates)]
pub(crate) fn parse_number(s: &[u8], i: usize) -> Option<(Number, usize)> {
    let mut j = i;
    let mut negative = false;
    if s[j] == b'-' {
        negative = true;
        j += 1;
    }
    let mut int_digits: Vec<u8> = Vec::new();
    proof_assert!(int_digits@.ext_eq(Seq::empty()));
    if j >= s.len() || !is_digit(s[j]) {
        return None;
    }
    snapshot!(lemma_snoc_cat(Seq::empty(), 0u8));
    let _ss = snapshot!(j@);
    if s[j] == b'0' {
        int_digits.push(0);
        j += 1;
        proof_assert!(int_digits@.ext_eq(digit_seq(s@, *_ss, *_ss + 1)));
    } else {
        j = parse_digits(s, j, &mut int_digits);
    }
    snapshot!(lemma_digit_seq_ok(s@, *_ss, j@));
    proof_assert!(int_digits@.len() == j@ - *_ss && j@ <= s@.len());
    let _ie = snapshot!(j@);
    proof_assert!(*_ss == if negative { i@ + 1 } else { i@ } && negative == (s@[i@]@ == 45));
    proof_assert!(*_ie == if s@[*_ss]@ == 48 { *_ss + 1 } else { digits_end(s@, *_ss) });
    proof_assert!(int_digits@ == digit_seq(s@, *_ss, *_ie));
    let mut frac_digits: Vec<u8> = Vec::new();
    proof_assert!(frac_digits@.ext_eq(Seq::empty()));
    if j < s.len() && s[j] == b'.' {
        let k = parse_digits(s, j + 1, &mut frac_digits);
        if k == j + 1 {
            return None;
        }
        snapshot!(lemma_digit_seq_ok(s@, j@ + 1, k@));
        j = k;
    }
    proof_assert!(int_digits@.len() + frac_digits@.len() <= j@ - *_ss && j@ <= s@.len());
    let _fs = snapshot!(if *_ie < j@ { *_ie + 1 } else { *_ie });
    proof_assert!(frac_digits@ == digit_seq(s@, *_fs, j@));
    proof_assert!(number_spec(s@, i@) == exp_part(s@, *_ss, negative, *_ie, *_fs, j@, j@));
    let _p = snapshot!(j@);
    let mut exp_negative = false;
    let mut exp_digits: Vec<u8> = Vec::new();
    proof_assert!(exp_digits@.ext_eq(Seq::empty()));
    if j < s.len() && (s[j] == b'e' || s[j] == b'E') {
        j += 1;
        if j < s.len() && (s[j] == b'+' || s[j] == b'-') {
            exp_negative = s[j] == b'-';
            j += 1;
        }
        let k = parse_digits(s, j, &mut exp_digits);
        if k == j {
            return None;
        }
        snapshot!(lemma_digit_seq_ok(s@, j@, k@));
        j = k;
    }
    proof_assert!(int_digits@.len() + frac_digits@.len() + exp_digits@.len() <= j@ - *_ss && j@ <= s@.len() && s@.len() <= usize::MAX@);
    proof_assert!(exp_part(s@, *_ss, negative, *_ie, *_fs, *_p, *_p) == Some((NumS { neg: negative, int: int_digits@, frac: frac_digits@, eneg: exp_negative, exp: exp_digits@ }, j@)));
    Some((Number { negative, int_digits, frac_digits, exp_negative, exp_digits }, j))
}

// I ++ F
#[logic(open)]
pub fn mantissa(ns: NumS) -> Seq<u8> {
    pearlite! { ns.int.concat(ns.frac) }
}

#[requires(k@ < n.int_digits@.len() + n.frac_digits@.len())]
#[ensures(result == mantissa(num_view(*n))[k@])]
#[check(terminates)]
fn digit_at(n: &Number, k: usize) -> u8 {
    if k < n.int_digits.len() { n.int_digits[k] } else { n.frac_digits[k - n.int_digits.len()] }
}

#[requires(n.int_digits@.len() + n.frac_digits@.len() <= usize::MAX@)]
#[ensures(result == forall<k> 0 <= k && k < mantissa(num_view(*n)).len() ==> mantissa(num_view(*n))[k]@ == 0)]
#[check(terminates)]
fn all_digits_zero(n: &Number) -> bool {
    let total = n.int_digits.len() + n.frac_digits.len();
    let mut k = 0;
    #[invariant(k@ <= total@)]
    #[invariant(forall<j> 0 <= j && j < k@ ==> mantissa(num_view(*n))[j]@ == 0)]
    #[variant(total@ - k@)]
    while k < total {
        if digit_at(n, k) != 0 {
            return false;
        }
        k += 1;
    }
    true
}

#[logic(open)]
#[variant(n)]
pub fn pow10(n: Int) -> Int {
    pearlite! { if n <= 0 { 1 } else { 10 * pow10(n - 1) } }
}

#[logic(opaque)]
#[variant(n)]
#[requires(0 <= n)]
#[ensures(1 <= pow10(n))]
pub fn lemma_pow10_pos(n: Int) {
    if n > 0 {
        lemma_pow10_pos(n - 1)
    }
}

#[logic(opaque)]
#[variant(b)]
#[requires(0 <= a && a <= b)]
#[ensures(pow10(a) <= pow10(b))]
#[ensures(1 <= pow10(a))]
pub fn lemma_pow10_le(a: Int, b: Int) {
    lemma_pow10_pos(a);
    if a < b {
        lemma_pow10_le(a, b - 1)
    }
}

// 10 進の数字列の値
#[logic(open)]
#[variant(s.len())]
pub fn dec_val(s: Seq<u8>) -> Int {
    pearlite! { if s.len() <= 0 { 0 } else { dec_val(s[..s.len() - 1]) * 10 + (s[s.len() - 1]@ - 48) } }
}

#[logic(opaque)]
#[requires(0 <= i && i < s.len())]
#[ensures(dec_val(s[..i + 1]) == dec_val(s[..i]) * 10 + (s[i]@ - 48))]
pub fn lemma_dec_val_snoc(s: Seq<u8>, i: Int) {
    proof_assert!(s[..i + 1][..i].ext_eq(s[..i]));
}

#[cfg(creusot)]
pub use opaque::*;

#[cfg(creusot)]
mod opaque {
    use super::*;

    // 桁の値の列（各桁は 0〜9 の値）の 10 進の値
    #[logic]
    #[variant(s.len())]
    pub fn dval(s: Seq<u8>) -> Int {
        pearlite! { if s.len() <= 0 { 0 } else { dval(s[..s.len() - 1]) * 10 + s[s.len() - 1]@ } }
    }

    #[logic(opaque)]
    #[requires(0 <= i && i < s.len())]
    #[ensures(dval(s[..i + 1]) == dval(s[..i]) * 10 + s[i]@)]
    pub fn lemma_dval_snoc(s: Seq<u8>, i: Int) {
        proof_assert!(s[..i + 1][..i].ext_eq(s[..i]));
    }

    #[logic(opaque)]
    #[variant(s.len())]
    #[ensures(0 <= dval(s))]
    #[ensures(digits_le9(s) ==> dval(s) < pow10(s.len()))]
    #[ensures((dval(s) == 0) == (forall<k> 0 <= k && k < s.len() ==> s[k]@ == 0))]
    pub fn lemma_dval_bound(s: Seq<u8>) {
        if s.len() > 0 {
            lemma_dval_bound(s[..s.len() - 1]);
            proof_assert!(forall<k> 0 <= k && k < s.len() - 1 ==> s[..s.len() - 1][k] == s[k]);
        }
    }

    // dval(s) = dval(s[..k]) · 10^(|s|-k) + dval(s[k..])
    #[logic(opaque)]
    #[variant(s.len())]
    #[requires(0 <= k && k <= s.len())]
    #[ensures(dval(s) == dval(s[..k]) * pow10(s.len() - k) + dval(s[k..]))]
    pub fn lemma_dval_split(s: Seq<u8>, k: Int) {
        if k < s.len() {
            let t = s[..s.len() - 1];
            lemma_dval_split(t, k);
            proof_assert!(t[..k].ext_eq(s[..k]));
            proof_assert!(s[k..][..s.len() - 1 - k].ext_eq(t[k..]));
            proof_assert!(s[k..][s.len() - 1 - k] == s[s.len() - 1]);
        } else {
            proof_assert!(s[..k].ext_eq(s));
            proof_assert!(s[k..].len() == 0);
        }
    }

    // 先頭部分の値は全体の値以下
    #[logic(opaque)]
    #[requires(0 <= k && k <= s.len())]
    #[ensures(dval(s[..k]) <= dval(s))]
    pub fn lemma_dval_prefix(s: Seq<u8>, k: Int) {
        lemma_dval_split(s, k);
        lemma_dval_bound(s[k..]);
        lemma_pow10_pos(s.len() - k);
        lemma_dval_bound(s[..k]);
        proof_assert!(dval(s[..k]) * (pow10(s.len() - k) - 1) >= 0);
        proof_assert!(dval(s[..k]) * pow10(s.len() - k) == dval(s[..k]) * (pow10(s.len() - k) - 1) + dval(s[..k]));
    }

    // 仮数が 0 なら値は 0
    #[logic(opaque)]
    #[requires(num_ok(ns) && dval(mantissa(ns)) == 0)]
    #[ensures(num_u64_spec(ns) == Some(0))]
    pub fn lemma_n1_zero(ns: NumS) {
        if scale(ns) < 0 {
            lemma_pow10_pos(-scale(ns));
            lemma_divmod(0, 0, pow10(-scale(ns)), 0);
        }
    }

    // 仮数が正で負号付きなら None
    #[logic(opaque)]
    #[requires(num_ok(ns) && dval(mantissa(ns)) > 0 && ns.neg)]
    #[ensures(num_u64_spec(ns) == None)]
    pub fn lemma_n1_negative(ns: NumS) {
        if scale(ns) >= 0 {
            lemma_pow10_pos(scale(ns));
            proof_assert!(dval(mantissa(ns)) * pow10(scale(ns)) >= 1);
        } else {
            let p = pow10(-scale(ns));
            lemma_pow10_pos(-scale(ns));
            let m = dval(mantissa(ns));
            lemma_divmod(m, m.div_euclid(p), p, m.rem_euclid(p));
            proof_assert!(m.rem_euclid(p) == 0 ==> m.div_euclid(p) >= 1);
        }
    }

    // 指数が正で |F| 以上（飽和を含む）の場合
    #[logic(opaque)]
    #[requires(num_ok(ns) && dval(mantissa(ns)) > 0 && !ns.neg && !ns.eneg && exp_sat(ns) >= ns.frac.len())]
    #[ensures(dval(mantissa(ns)) > u64::MAX@ ==> num_u64_spec(ns) == None)]
    #[ensures(num_u64_spec(ns) == if dval(mantissa(ns)) * pow10(exp_sat(ns) - ns.frac.len()) <= u64::MAX@ {
        Some(dval(mantissa(ns)) * pow10(exp_sat(ns) - ns.frac.len()))
    } else {
        None
    })]
    pub fn lemma_n1_exp(ns: NumS) {
        let m = dval(mantissa(ns));
        lemma_pow10_pos(scale(ns));
        proof_assert!(m * pow10(scale(ns)) >= m);
        if dval(ns.exp) > u64_max() {
            // 指数が u64::MAX を超えるには 20 桁以上が要るので、|F| ≤ usize::MAX − 20
            lemma_dval_bound(ns.exp);
            lemma_pow10_20();
            if ns.exp.len() < 20 {
                lemma_pow10_le(ns.exp.len(), 19);
                lemma_pow10_19();
            }
            lemma_pow10_le(20, exp_sat(ns) - ns.frac.len());
            lemma_pow10_le(20, scale(ns));
            proof_assert!(m * pow10(exp_sat(ns) - ns.frac.len()) >= pow10(exp_sat(ns) - ns.frac.len()));
            proof_assert!(m * pow10(scale(ns)) >= pow10(scale(ns)));
        }
    }

    // 小数点を左へ drop 桁ずらす場合
    #[logic(opaque)]
    #[requires(num_ok(ns) && dval(mantissa(ns)) > 0 && !ns.neg && (ns.eneg || exp_sat(ns) < ns.frac.len()))]
    #[ensures(drop_count(ns) >= mantissa(ns).len() ==> num_u64_spec(ns) == None)]
    #[ensures(drop_count(ns) < mantissa(ns).len() ==> num_u64_spec(ns) == {
        let keep = mantissa(ns).len() - drop_count(ns);
        if forall<k> keep <= k && k < mantissa(ns).len() ==> mantissa(ns)[k]@ == 0 {
            if dval(mantissa(ns)[..keep]) <= u64_max() { Some(dval(mantissa(ns)[..keep])) } else { None }
        } else {
            None
        }
    })]
    pub fn lemma_n1_drop(ns: NumS) {
        let d = mantissa(ns);
        let m = dval(d);
        lemma_mantissa_le9(ns);
        lemma_dval_bound(d);
        proof_assert!(-scale(ns) >= drop_count(ns));
        proof_assert!(drop_count(ns) < u64::MAX@ ==> -scale(ns) == drop_count(ns));
        if drop_count(ns) >= d.len() {
            lemma_pow10_le(d.len(), -scale(ns));
            lemma_divmod(m, 0, pow10(-scale(ns)), m);
        } else {
            let keep = d.len() - drop_count(ns);
            lemma_dval_split(d, keep);
            lemma_dval_bound(d[keep..]);
            lemma_dval_bound(d[..keep]);
            proof_assert!(forall<k> 0 <= k && k < d.len() - keep ==> d[keep..][k] == d[keep + k]);
            proof_assert!(forall<k> keep <= k && k < d.len() ==> d[keep..][k - keep] == d[k]);
            lemma_pow10_pos(-scale(ns));
            lemma_divmod(m, dval(d[..keep]), pow10(-scale(ns)), dval(d[keep..]));
            proof_assert!((dval(d[keep..]) == 0) == (forall<k> keep <= k && k < d.len() ==> d[k]@ == 0));
            if scale(ns) == 0 {
                proof_assert!(d[..keep].ext_eq(d));
                proof_assert!(magnitude(ns) == dval(d[..keep]));
            } else {
                proof_assert!(is_integer(ns) == (dval(d[keep..]) == 0));
                proof_assert!(magnitude(ns) == dval(d[..keep]));
            }
        }
    }
}

#[ensures(result@ == if dval(n.exp_digits@) <= u64::MAX@ { dval(n.exp_digits@) } else { u64::MAX@ })]
#[check(terminates)]
fn exponent_value(n: &Number) -> u64 {
    let mut e: u64 = 0;
    let mut k = 0;
    snapshot!(lemma_dval_bound(n.exp_digits@[..0]));
    #[invariant(k@ <= n.exp_digits@.len())]
    #[invariant(e@ == if dval(n.exp_digits@[..k@]) <= u64::MAX@ { dval(n.exp_digits@[..k@]) } else { u64::MAX@ })]
    #[variant(n.exp_digits@.len() - k@)]
    while k < n.exp_digits.len() {
        e = match e.checked_mul(10) {
            Some(t) => match t.checked_add(n.exp_digits[k] as u64) {
                Some(u) => u,
                None => u64::MAX,
            },
            None => u64::MAX,
        };
        snapshot!(lemma_dval_snoc(n.exp_digits@, k@));
        snapshot!(lemma_dval_bound(n.exp_digits@[..k@]));
        k += 1;
    }
    proof_assert!(n.exp_digits@[..k@].ext_eq(n.exp_digits@));
    e
}

#[requires(n.int_digits@.len() + n.frac_digits@.len() <= usize::MAX@)]
#[requires(from@ <= n.int_digits@.len() + n.frac_digits@.len())]
#[ensures(result == forall<k> from@ <= k && k < mantissa(num_view(*n)).len() ==> mantissa(num_view(*n))[k]@ == 0)]
#[check(terminates)]
fn digits_zero_from(n: &Number, from: usize) -> bool {
    let total = n.int_digits.len() + n.frac_digits.len();
    let mut k = from;
    #[invariant(from@ <= k@ && k@ <= total@)]
    #[invariant(forall<j> from@ <= j && j < k@ ==> mantissa(num_view(*n))[j]@ == 0)]
    #[variant(total@ - k@)]
    while k < total {
        if digit_at(n, k) != 0 {
            return false;
        }
        k += 1;
    }
    true
}

#[requires(keep@ <= n.int_digits@.len() + n.frac_digits@.len())]
#[ensures(match result {
    None => dval(mantissa(num_view(*n))[..keep@]) > u64::MAX@,
    Some(v) => v@ == dval(mantissa(num_view(*n))[..keep@]),
})]
#[check(terminates)]
fn digits_value(n: &Number, keep: usize) -> Option<u64> {
    let mut v: u64 = 0;
    let mut k = 0;
    snapshot!(lemma_dval_bound(mantissa(num_view(*n))[..0]));
    #[invariant(k@ <= keep@)]
    #[invariant(v@ == dval(mantissa(num_view(*n))[..k@]))]
    #[variant(keep@ - k@)]
    while k < keep {
        snapshot!(lemma_dval_snoc(mantissa(num_view(*n))[..keep@], k@));
        proof_assert!(mantissa(num_view(*n))[..keep@][..k@].ext_eq(mantissa(num_view(*n))[..k@]));
        proof_assert!(mantissa(num_view(*n))[..keep@][..k@ + 1].ext_eq(mantissa(num_view(*n))[..k@ + 1]));
        snapshot!(lemma_dval_prefix(mantissa(num_view(*n))[..keep@], k@ + 1));
        v = match v.checked_mul(10) {
            Some(t) => match t.checked_add(digit_at(n, k) as u64) {
                Some(u) => u,
                None => return None,
            },
            None => return None,
        };
        k += 1;
    }
    Some(v)
}

#[ensures(match result {
    None => v@ * pow10(shift@) > u64::MAX@,
    Some(r) => r@ == v@ * pow10(shift@),
})]
#[check(terminates)]
fn mul_pow10(v: u64, shift: u64) -> Option<u64> {
    let mut r = v;
    let mut s: u64 = 0;
    #[invariant(s@ <= shift@)]
    #[invariant(r@ == v@ * pow10(s@))]
    #[variant(shift@ - s@)]
    while s < shift {
        snapshot!(lemma_pow10_le(s@ + 1, shift@));
        proof_assert!(v@ * pow10(s@ + 1) <= v@ * pow10(shift@));
        r = match r.checked_mul(10) {
            Some(t) => t,
            None => return None,
        };
        s += 1;
    }
    Some(r)
}

// q = (-1)^neg · val(I ++ F) · 10^(e − |F|) の指数 e − |F|
#[logic(open)]
pub fn scale(ns: NumS) -> Int {
    pearlite! { (if ns.eneg { -dval(ns.exp) } else { dval(ns.exp) }) - ns.frac.len() }
}

// q が整数のとき、その絶対値
#[logic(open)]
pub fn magnitude(ns: NumS) -> Int {
    pearlite! {
        if scale(ns) >= 0 { dval(mantissa(ns)) * pow10(scale(ns)) }
        else { dval(mantissa(ns)).div_euclid(pow10(-scale(ns))) }
    }
}

#[logic(open)]
pub fn is_integer(ns: NumS) -> bool {
    pearlite! { scale(ns) >= 0 || dval(mantissa(ns)).rem_euclid(pow10(-scale(ns))) == 0 }
}

// N1: q が整数で 0 ≤ q ≤ u64::MAX なら Some(q)、そうでなければ None
// MUST-006, MUST-013: 整数は小数部が 0 で、インデックスは 0 以上
#[logic(open)]
pub fn num_u64_spec(ns: NumS) -> Option<Int> {
    pearlite! {
        if is_integer(ns) {
            let q = if ns.neg { -magnitude(ns) } else { magnitude(ns) };
            if 0 <= q && q <= u64::MAX@ { Some(q) } else { None }
        } else {
            None
        }
    }
}

#[logic(opaque)]
#[ensures(pow10(20) > u64::MAX@)]
pub fn lemma_pow10_20() {}

#[logic(opaque)]
#[ensures(pow10(19) <= u64::MAX@)]
pub fn lemma_pow10_19() {}

// m = a·p + r, 0 ≤ r < p ならば商は a、余りは r
#[logic(opaque)]
#[requires(0 < p && 0 <= r && r < p && m == a * p + r)]
#[ensures(m.div_euclid(p) == a && m.rem_euclid(p) == r)]
pub fn lemma_divmod(m: Int, a: Int, p: Int, r: Int) {}

#[logic(open)]
pub fn u64_max() -> Int {
    pearlite! { u64::MAX@ }
}

// 指数の値を u64::MAX で飽和させたもの（実装の exponent_value の値）
#[logic(open)]
pub fn exp_sat(ns: NumS) -> Int {
    pearlite! { if dval(ns.exp) <= u64::MAX@ { dval(ns.exp) } else { u64::MAX@ } }
}

#[logic(opaque)]
#[requires(digits_le9(ns.int) && digits_le9(ns.frac))]
#[ensures(digits_le9(mantissa(ns)))]
pub fn lemma_mantissa_le9(ns: NumS) {}

#[logic(open)]
pub fn drop_count(ns: NumS) -> Int {
    pearlite! {
        if ns.eneg {
            if exp_sat(ns) + ns.frac.len() <= u64_max() { exp_sat(ns) + ns.frac.len() } else { u64_max() }
        } else {
            ns.frac.len() - exp_sat(ns)
        }
    }
}

// MUST-006, MUST-013: 整数は小数部が 0 で、インデックスは 0 以上
#[requires(num_ok(num_view(*n)))]
#[ensures(opt_int(result) == num_u64_spec(num_view(*n)))]
#[check(terminates)]
pub fn number_to_u64(n: &Number) -> Option<u64> {
    snapshot!(lemma_mantissa_le9(num_view(*n)));
    snapshot!(lemma_dval_bound(mantissa(num_view(*n))));
    snapshot!(lemma_dval_bound(n.exp_digits@));
    if all_digits_zero(n) {
        snapshot!(lemma_n1_zero(num_view(*n)));
        return Some(0);
    }
    if n.negative {
        snapshot!(lemma_n1_negative(num_view(*n)));
        return None;
    }
    let total = n.int_digits.len() + n.frac_digits.len();
    proof_assert!(mantissa(num_view(*n))[..total@].ext_eq(mantissa(num_view(*n))));
    proof_assert!(dval(mantissa(num_view(*n))[..total@]) == dval(mantissa(num_view(*n))));
    let e = exponent_value(n);
    let f = n.frac_digits.len() as u64;
    if !n.exp_negative && e >= f {
        snapshot!(lemma_n1_exp(num_view(*n)));
        proof_assert!(e@ - f@ == exp_sat(num_view(*n)) - num_view(*n).frac.len());
        match digits_value(n, total) {
            None => None,
            Some(v) => mul_pow10(v, e - f),
        }
    } else {
        let drop = if n.exp_negative { e.saturating_add(f) } else { f - e };
        snapshot!(lemma_n1_drop(num_view(*n)));
        proof_assert!(drop@ == drop_count(num_view(*n)));
        if drop >= total as u64 {
            return None;
        }
        let keep = total - drop as usize;
        if !digits_zero_from(n, keep) {
            return None;
        }
        digits_value(n, keep)
    }
}

#[logic(opaque)]
#[variant(b)]
#[requires(0 <= a && 0 <= b)]
#[ensures(pow10(a + b) == pow10(a) * pow10(b))]
pub fn lemma_pow10_add(a: Int, b: Int) {
    if b > 0 {
        lemma_pow10_add(a, b - 1)
    }
}
