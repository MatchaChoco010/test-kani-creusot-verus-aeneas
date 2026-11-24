use vstd::prelude::*;

verus! {

pub struct Number {
    pub negative: bool,
    pub int_digits: Vec<u8>,
    pub frac_digits: Vec<u8>,
    pub exp_negative: bool,
    pub exp_digits: Vec<u8>,
}

pub open spec fn digit(b: u8) -> bool {
    b'0' <= b <= b'9'
}

pub(crate) fn is_digit(b: u8) -> (r: bool)
    ensures
        r == digit(b),
{
    b >= b'0' && b <= b'9'
}

// 数字の並びの終わり（最小の非数字位置）
pub open spec fn digits_end_at(s: Seq<u8>, i: int, j: int) -> bool {
    &&& i <= j <= s.len()
    &&& (j == s.len() || !digit(s[j]))
    &&& forall|k: int| i <= k < j ==> digit(#[trigger] s[k])
}

pub open spec fn digits_end(s: Seq<u8>, i: int) -> int {
    choose|j: int| digits_end_at(s, i, j)
}

pub open spec fn digit_vals(s: Seq<u8>, i: int, j: int) -> Seq<u8> {
    Seq::new((j - i) as nat, |k: int| (s[i + k] - b'0') as u8)
}

pub proof fn lemma_digits_end_unique(s: Seq<u8>, i: int, j: int)
    requires
        digits_end_at(s, i, j),
    ensures
        digits_end(s, i) == j,
{
    let j2 = digits_end(s, i);
    assert(digits_end_at(s, i, j2));
    if j2 < j {
        assert(digit(s[j2]));
    } else if j < j2 {
        assert(digit(s[j]));
    }
}

fn parse_digits(s: &[u8], i: usize, out: &mut Vec<u8>) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == digits_end(s@, i as int),
        i <= r <= s.len(),
        final(out)@ == old(out)@ + digit_vals(s@, i as int, r as int),
{
    let ghost o = out@;
    let mut j = i;
    while j < s.len() && is_digit(s[j])
        invariant
            i <= j <= s.len(),
            forall|k: int| i <= k < j ==> digit(#[trigger] s@[k]),
            out@ == o + digit_vals(s@, i as int, j as int),
        decreases s.len() - j,
    {
        out.push(s[j] - b'0');
        j += 1;
        assert(out@ =~= o + digit_vals(s@, i as int, j as int));
    }
    proof {
        lemma_digits_end_unique(s@, i as int, j as int);
    }
    j
}

// number(s, i): -? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?
// RFC 8259 §6: 数値
pub open spec fn number_spec(s: Seq<u8>, i: int) -> Option<(NumberS, int)> {
    let neg = s[i] == b'-';
    let a = if neg { i + 1 } else { i };
    if i < 0 || i >= s.len() || a >= s.len() || !digit(s[a]) {
        None
    } else {
        let b = if s[a] == b'0' { a + 1 } else { digits_end(s, a) };
        let has_frac = b < s.len() && s[b] == b'.';
        let c = if has_frac { digits_end(s, b + 1) } else { b };
        if has_frac && c == b + 1 {
            None
        } else {
            let has_exp = c < s.len() && (s[c] == b'e' || s[c] == b'E');
            let has_sign = has_exp && c + 1 < s.len() && (s[c + 1] == b'+' || s[c + 1] == b'-');
            let d0 = if has_sign { c + 2 } else if has_exp { c + 1 } else { c };
            let e = if has_exp { digits_end(s, d0) } else { c };
            if has_exp && e == d0 {
                None
            } else {
                Some((
                    NumberS {
                        negative: neg,
                        int_digits: digit_vals(s, a, b),
                        frac_digits: if has_frac { digit_vals(s, b + 1, c) } else { seq![] },
                        exp_negative: has_sign && s[c + 1] == b'-',
                        exp_digits: if has_exp { digit_vals(s, d0, e) } else { seq![] },
                    },
                    e,
                ))
            }
        }
    }
}

pub proof fn lemma_digits_end_le(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= digits_end(s, i) <= s.len(),
        digits_end_at(s, i, digits_end(s, i)),
    decreases s.len() - i,
{
    if i < s.len() && digit(s[i]) {
        lemma_digits_end_le(s, i + 1);
        let j = digits_end(s, i + 1);
        assert(digits_end_at(s, i, j));
        lemma_digits_end_unique(s, i, j);
    } else {
        assert(digits_end_at(s, i, i));
        lemma_digits_end_unique(s, i, i);
    }
}

pub proof fn lemma_number_spec_wf(s: Seq<u8>, i: int)
    requires
        number_spec(s, i) is Some,
        s.len() <= usize::MAX,
    ensures
        number_wf(number_spec(s, i)->Some_0.0),
        i < number_spec(s, i)->Some_0.1 <= s.len(),
{
    let neg = s[i] == b'-';
    let a = if neg { i + 1 } else { i };
    let b = if s[a] == b'0' { a + 1 } else { digits_end(s, a) };
    if s[a] != b'0' {
        lemma_digits_end_le(s, a);
    }
    let has_frac = b < s.len() && s[b] == b'.';
    let c = if has_frac { digits_end(s, b + 1) } else { b };
    if has_frac {
        lemma_digits_end_le(s, b + 1);
    }
    let has_exp = c < s.len() && (s[c] == b'e' || s[c] == b'E');
    let has_sign = has_exp && c + 1 < s.len() && (s[c + 1] == b'+' || s[c + 1] == b'-');
    let d0 = if has_sign { c + 2 } else if has_exp { c + 1 } else { c };
    let e = if has_exp { digits_end(s, d0) } else { c };
    if has_exp {
        lemma_digits_end_le(s, d0);
    }
    let n = number_spec(s, i)->Some_0.0;
    assert(all_le9(n.int_digits)) by {
        assert forall|k: int| 0 <= k < n.int_digits.len() implies n.int_digits[k] <= 9 by {
            assert(digit(s[a + k]));
        }
    }
    assert(all_le9(n.frac_digits)) by {
        assert forall|k: int| 0 <= k < n.frac_digits.len() implies n.frac_digits[k] <= 9 by {
            assert(digit(s[b + 1 + k]));
        }
    }
    assert(all_le9(n.exp_digits)) by {
        assert forall|k: int| 0 <= k < n.exp_digits.len() implies n.exp_digits[k] <= 9 by {
            assert(digit(s[d0 + k]));
        }
    }
}

// N: JSON 数値 Number(neg, I, F, eneg, E) の値 q = (-1)^neg · val(I ++ F) · 10^(e − |F|)
pub struct NumberS {
    pub negative: bool,
    pub int_digits: Seq<u8>,
    pub frac_digits: Seq<u8>,
    pub exp_negative: bool,
    pub exp_digits: Seq<u8>,
}

// Number の表現不変条件: 数字は 0..9、数字列の長さの合計は usize::MAX 以下（parse_number が入力長で保証する）
pub open spec fn number_wf(n: NumberS) -> bool {
    &&& all_le9(n.int_digits)
    &&& all_le9(n.frac_digits)
    &&& all_le9(n.exp_digits)
    &&& n.int_digits.len() + n.frac_digits.len() + n.exp_digits.len() <= usize::MAX
}

pub open spec fn all_le9(ds: Seq<u8>) -> bool {
    forall|k: int| 0 <= k < ds.len() ==> ds[k] <= 9
}

pub(crate) fn parse_number(s: &[u8], i: usize) -> (r: Option<(Number, usize)>)
    requires
        i < s.len(),
    ensures
        match r {
            Some((n, k)) => number_spec(s@, i as int) == Some((n@, k as int)) && number_wf(n@) && i < k
                <= s.len(),
            None => number_spec(s@, i as int) is None,
        },
{
    let mut j = i;
    let mut negative = false;
    if s[j] == b'-' {
        negative = true;
        j += 1;
    }
    let mut int_digits: Vec<u8> = Vec::new();
    if j >= s.len() || !is_digit(s[j]) {
        return None;
    }
    let ghost a = j as int;
    if s[j] == b'0' {
        int_digits.push(0);
        j += 1;
        assert(int_digits@ =~= digit_vals(s@, a, a + 1));
    } else {
        j = parse_digits(s, j, &mut int_digits);
        assert(int_digits@ =~= digit_vals(s@, a, j as int));
    }
    let ghost b = j as int;
    let mut frac_digits: Vec<u8> = Vec::new();
    if j < s.len() && s[j] == b'.' {
        let k = parse_digits(s, j + 1, &mut frac_digits);
        if k == j + 1 {
            return None;
        }
        j = k;
        assert(frac_digits@ =~= digit_vals(s@, b + 1, j as int));
    }
    let ghost c = j as int;
    proof {
        if c == b {
            assert(frac_digits@ =~= seq![]);
        }
    }
    let mut exp_negative = false;
    let mut exp_digits: Vec<u8> = Vec::new();
    if j < s.len() && (s[j] == b'e' || s[j] == b'E') {
        j += 1;
        if j < s.len() && (s[j] == b'+' || s[j] == b'-') {
            exp_negative = s[j] == b'-';
            j += 1;
        }
        let ghost d0 = j as int;
        let k = parse_digits(s, j, &mut exp_digits);
        if k == j {
            return None;
        }
        j = k;
        assert(exp_digits@ =~= digit_vals(s@, d0, j as int));
    }
    proof {
        if j as int == c {
            assert(exp_digits@ =~= seq![]);
        }
    }
    proof {
        lemma_number_spec_wf(s@, i as int);
    }
    Some((Number { negative, int_digits, frac_digits, exp_negative, exp_digits }, j))
}

pub open spec fn number_mantissa(n: &Number) -> Seq<u8> {
    n.int_digits@ + n.frac_digits@
}

fn digit_at(n: &Number, k: usize) -> (r: u8)
    requires
        k < n.int_digits.len() + n.frac_digits.len(),
    ensures
        r == number_mantissa(n)[k as int],
{
    if k < n.int_digits.len() { n.int_digits[k] } else { n.frac_digits[k - n.int_digits.len()] }
}

fn all_digits_zero(n: &Number) -> (r: bool)
    requires
        n.int_digits.len() + n.frac_digits.len() <= usize::MAX,
    ensures
        r == (forall|k: int| 0 <= k < number_mantissa(n).len() ==> number_mantissa(n)[k] == 0),
{
    let total = n.int_digits.len() + n.frac_digits.len();
    let mut k = 0;
    while k < total
        invariant
            total == number_mantissa(n).len(),
            0 <= k <= total,
            forall|m: int| 0 <= m < k ==> number_mantissa(n)[m] == 0,
        decreases total - k,
    {
        if digit_at(n, k) != 0 {
            return false;
        }
        k += 1;
    }
    true
}

// 数字列の 10 進値 val
pub open spec fn digits_val(ds: Seq<u8>) -> nat
    decreases ds.len(),
{
    if ds.len() == 0 {
        0
    } else {
        digits_val(ds.drop_last()) * 10 + ds.last() as nat
    }
}

pub open spec fn min_u64(x: nat) -> u64 {
    if x <= u64::MAX {
        x as u64
    } else {
        u64::MAX
    }
}

fn exponent_value(n: &Number) -> (r: u64)
    ensures
        r == min_u64(digits_val(n.exp_digits@)),
{
    let mut e: u64 = 0;
    let mut k = 0;
    while k < n.exp_digits.len()
        invariant
            0 <= k <= n.exp_digits.len(),
            e == min_u64(digits_val(n.exp_digits@.subrange(0, k as int))),
        decreases n.exp_digits.len() - k,
    {
        let ghost a = digits_val(n.exp_digits@.subrange(0, k as int));
        let ghost d = n.exp_digits@[k as int] as nat;
        let ghost e0 = e;
        assert(n.exp_digits@.subrange(0, k + 1).drop_last() =~= n.exp_digits@.subrange(0, k as int));
        assert(digits_val(n.exp_digits@.subrange(0, k + 1)) == a * 10 + d);
        e = match e.checked_mul(10) {
            Some(t) => match t.checked_add(n.exp_digits[k] as u64) {
                Some(u) => u,
                None => u64::MAX,
            },
            None => u64::MAX,
        };
        assert(e == min_u64(a * 10 + d)) by {
            if a > u64::MAX {
                assert(e0 == u64::MAX);
            } else {
                assert(e0 == a);
            }
        }
        k += 1;
    }
    assert(n.exp_digits@.subrange(0, n.exp_digits.len() as int) =~= n.exp_digits@);
    e
}

fn digits_zero_from(n: &Number, from: usize) -> (r: bool)
    requires
        n.int_digits.len() + n.frac_digits.len() <= usize::MAX,
        from <= n.int_digits.len() + n.frac_digits.len(),
    ensures
        r == (forall|k: int| from <= k < number_mantissa(n).len() ==> number_mantissa(n)[k] == 0),
{
    let total = n.int_digits.len() + n.frac_digits.len();
    let mut k = from;
    while k < total
        invariant
            total == number_mantissa(n).len(),
            from <= k <= total,
            forall|m: int| from <= m < k ==> number_mantissa(n)[m] == 0,
        decreases total - k,
    {
        if digit_at(n, k) != 0 {
            return false;
        }
        k += 1;
    }
    true
}

pub open spec fn pow10(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        10 * pow10((k - 1) as nat)
    }
}

pub open spec fn dec_digits(s: Seq<u8>) -> Seq<u8> {
    Seq::new(s.len(), |k: int| (s[k] - b'0') as u8)
}

pub proof fn lemma_pow10_le_1e9(k: nat)
    requires
        k <= 9,
    ensures
        pow10(k) <= 1000000000,
{
    lemma_pow10_mono(k, 9);
    reveal_with_fuel(pow10, 10);
}

pub proof fn lemma_pow10_pos(k: nat)
    ensures
        pow10(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow10_pos((k - 1) as nat);
    }
}

pub proof fn lemma_val_append(a: Seq<u8>, b: Seq<u8>)
    ensures
        digits_val(a + b) == digits_val(a) * pow10(b.len()) + digits_val(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(pow10(0) == 1);
        assert(digits_val(b) == 0);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        assert(digits_val(a + b) == digits_val((a + b).drop_last()) * 10 + ((a + b).last() as nat));
        assert(digits_val(b) == digits_val(b.drop_last()) * 10 + (b.last() as nat));
        lemma_val_append(a, b.drop_last());
        assert(pow10(b.len()) == 10 * pow10((b.len() - 1) as nat));
        let p = pow10((b.len() - 1) as nat);
        let va = digits_val(a);
        let vb = digits_val(b.drop_last());
        assert((va * p + vb) * 10 + b.last() as nat == va * (10 * p) + (vb * 10 + b.last() as nat))
            by (nonlinear_arith);
    }
}

pub proof fn lemma_val_prefix_mono(ds: Seq<u8>, k: int, m: int)
    requires
        0 <= k <= m <= ds.len(),
    ensures
        digits_val(ds.subrange(0, k)) <= digits_val(ds.subrange(0, m)),
{
    assert(ds.subrange(0, m) =~= ds.subrange(0, k) + ds.subrange(k, m));
    lemma_val_append(ds.subrange(0, k), ds.subrange(k, m));
    lemma_pow10_pos((m - k) as nat);
    let a = digits_val(ds.subrange(0, k));
    let p = pow10((m - k) as nat);
    assert(a <= a * p) by (nonlinear_arith)
        requires
            p >= 1,
    ;
}

fn digits_value(n: &Number, keep: usize) -> (r: Option<u64>)
    requires
        keep <= n.int_digits.len() + n.frac_digits.len(),
    ensures
        r == (if digits_val(number_mantissa(n).subrange(0, keep as int)) <= u64::MAX {
            Some(digits_val(number_mantissa(n).subrange(0, keep as int)) as u64)
        } else {
            None::<u64>
        }),
{
    let ghost ds = number_mantissa(n);
    let mut v: u64 = 0;
    let mut k = 0;
    while k < keep
        invariant
            ds == number_mantissa(n),
            keep <= ds.len(),
            0 <= k <= keep,
            v == digits_val(ds.subrange(0, k as int)),
        decreases keep - k,
    {
        assert(ds.subrange(0, k + 1).drop_last() =~= ds.subrange(0, k as int));
        let ghost next = digits_val(ds.subrange(0, k + 1));
        assert(next == v * 10 + ds[k as int] as nat);
        proof {
            lemma_val_prefix_mono(ds, k + 1, keep as int);
        }
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

pub proof fn lemma_pow10_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow10(a) <= pow10(b),
    decreases b,
{
    if a < b {
        lemma_pow10_mono(a, (b - 1) as nat);
        lemma_pow10_pos((b - 1) as nat);
    }
}

pub proof fn lemma_mul_pow10_mono(v: nat, a: nat, b: nat)
    requires
        a <= b,
    ensures
        v * pow10(a) <= v * pow10(b),
{
    lemma_pow10_mono(a, b);
    let pa = pow10(a);
    let pb = pow10(b);
    assert(v * pa <= v * pb) by (nonlinear_arith)
        requires
            pa <= pb,
    ;
}

fn mul_pow10(v: u64, shift: u64) -> (r: Option<u64>)
    ensures
        r == (if v * pow10(shift as nat) <= u64::MAX {
            Some((v * pow10(shift as nat)) as u64)
        } else {
            None::<u64>
        }),
{
    let mut r = v;
    let mut s: u64 = 0;
    assert(pow10(0) == 1);
    while s < shift
        invariant
            0 <= s <= shift,
            r == v * pow10(s as nat),
        decreases shift - s,
    {
        proof {
            lemma_mul_pow10_mono(v as nat, (s + 1) as nat, shift as nat);
            assert(v * pow10((s + 1) as nat) == r * 10) by (nonlinear_arith)
                requires
                    r == v * pow10(s as nat),
                    pow10((s + 1) as nat) == 10 * pow10(s as nat),
            ;
        }
        r = match r.checked_mul(10) {
            Some(t) => t,
            None => return None,
        };
        s += 1;
    }
    Some(r)
}

pub open spec fn exp_val(n: NumberS) -> int {
    if n.exp_negative {
        -(digits_val(n.exp_digits) as int)
    } else {
        digits_val(n.exp_digits) as int
    }
}

// q == z（有理数の等式を整数で表したもの）
// MUST-006: 整数値は小数部が 0 の数で表す
pub open spec fn number_denotes(n: NumberS, z: int) -> bool {
    let d: int = if n.negative {
        -(digits_val(n.int_digits + n.frac_digits) as int)
    } else {
        digits_val(n.int_digits + n.frac_digits) as int
    };
    let x: int = exp_val(n) - n.frac_digits.len();
    if x >= 0 {
        z == d * pow10(x as nat)
    } else {
        z * pow10((-x) as nat) == d
    }
}

pub proof fn lemma_pow10_20()
    ensures
        pow10(20) == 100000000000000000000nat,
        pow10(19) == 10000000000000000000nat,
{
    reveal_with_fuel(pow10, 21);
}

pub proof fn lemma_val_bound(ds: Seq<u8>)
    requires
        all_le9(ds),
    ensures
        digits_val(ds) < pow10(ds.len()),
    decreases ds.len(),
{
    if ds.len() > 0 {
        lemma_val_bound(ds.drop_last());
        let p = pow10((ds.len() - 1) as nat);
        let v = digits_val(ds.drop_last());
        assert(v * 10 + (ds.last() as nat) < 10 * p) by (nonlinear_arith)
            requires
                v < p,
                ds.last() <= 9,
        ;
    }
}

pub proof fn lemma_val_zero(ds: Seq<u8>)
    ensures
        (digits_val(ds) == 0) == (forall|k: int| 0 <= k < ds.len() ==> ds[k] == 0),
    decreases ds.len(),
{
    if ds.len() > 0 {
        lemma_val_zero(ds.drop_last());
        if digits_val(ds) == 0 {
            assert forall|k: int| 0 <= k < ds.len() implies ds[k] == 0 by {
                if k < ds.len() - 1 {
                    assert(ds.drop_last()[k] == ds[k]);
                }
            }
        }
        if forall|k: int| 0 <= k < ds.len() ==> ds[k] == 0 {
            assert forall|k: int| 0 <= k < ds.drop_last().len() implies ds.drop_last()[k] == 0 by {
                assert(ds[k] == 0);
            }
            assert(ds[ds.len() - 1] == 0);
        }
    }
}

pub proof fn lemma_neg_not_denotes(n: NumberS, z: int)
    requires
        n.negative,
        digits_val(n.int_digits + n.frac_digits) != 0,
        z >= 0,
    ensures
        !number_denotes(n, z),
{
    let dv = digits_val(n.int_digits + n.frac_digits) as int;
    let x: int = exp_val(n) - n.frac_digits.len();
    if x >= 0 {
        lemma_pow10_pos(x as nat);
        let p = pow10(x as nat) as int;
        assert(-dv * p < 0) by (nonlinear_arith)
            requires
                dv > 0,
                p >= 1,
        ;
    } else {
        lemma_pow10_pos((-x) as nat);
        let p = pow10((-x) as nat) as int;
        assert(z * p >= 0) by (nonlinear_arith)
            requires
                z >= 0,
                p >= 1,
        ;
    }
}

// 指数が非負方向（!exp_negative かつ e >= |F|）の場合
pub proof fn lemma_branch_pos(n: NumberS, e: u64, f: nat)
    requires
        number_wf(n),
        !n.negative,
        !n.exp_negative,
        digits_val(n.int_digits + n.frac_digits) != 0,
        e == min_u64(digits_val(n.exp_digits)),
        f == n.frac_digits.len(),
        e >= f,
    ensures
        ({
            let dv = digits_val(n.int_digits + n.frac_digits);
            let ev = digits_val(n.exp_digits);
            &&& ev >= f
            &&& forall|z: int| number_denotes(n, z) == (z == dv * pow10((ev - f) as nat))
            &&& dv * pow10((ev - f) as nat) >= dv * pow10((e - f) as nat)
            &&& dv * pow10((e - f) as nat) >= dv
            &&& (e < ev ==> dv * pow10((e - f) as nat) > u64::MAX)
        }),
{
    let dv = digits_val(n.int_digits + n.frac_digits);
    let ev = digits_val(n.exp_digits);
    assert(e <= ev);
    lemma_mul_pow10_mono(dv, (e - f) as nat, (ev - f) as nat);
    lemma_mul_pow10_mono(dv, 0, (e - f) as nat);
    assert(pow10(0) == 1);
    if e < ev {
        assert(e == u64::MAX);
        if n.exp_digits.len() < 20 {
            lemma_val_bound(n.exp_digits);
            lemma_pow10_mono(n.exp_digits.len(), 19);
            lemma_pow10_20();
        }
        assert(e - f >= 20);
        lemma_pow10_20();
        lemma_mul_pow10_mono(dv, 20, (e - f) as nat);
        let p = pow10(20);
        assert(dv * p >= p) by (nonlinear_arith)
            requires
                dv >= 1,
        ;
    }
}

pub open spec fn drop_true(n: NumberS) -> int {
    if n.exp_negative {
        (digits_val(n.exp_digits) + n.frac_digits.len()) as int
    } else {
        n.frac_digits.len() - digits_val(n.exp_digits)
    }
}

pub open spec fn drop_code(e: u64, f: nat, exp_negative: bool) -> int {
    if exp_negative {
        if e + f > u64::MAX {
            u64::MAX as int
        } else {
            e + f
        }
    } else {
        f - e
    }
}

pub proof fn lemma_drop_rel(n: NumberS, e: u64, f: nat)
    requires
        e == min_u64(digits_val(n.exp_digits)),
        f == n.frac_digits.len(),
        f <= u64::MAX,
        n.exp_negative || e < f,
    ensures
        drop_code(e, f, n.exp_negative) <= drop_true(n),
        drop_code(e, f, n.exp_negative) < u64::MAX ==> drop_code(e, f, n.exp_negative) == drop_true(n),
        exp_val(n) - f == -drop_true(n),
{
}

pub proof fn lemma_branch_drop_all(n: NumberS, e: u64, f: nat, drop: u64, z: int)
    requires
        number_wf(n),
        !n.negative,
        digits_val(n.int_digits + n.frac_digits) != 0,
        e == min_u64(digits_val(n.exp_digits)),
        f == n.frac_digits.len(),
        n.exp_negative || e < f,
        drop == drop_code(e, f, n.exp_negative),
        drop >= (n.int_digits + n.frac_digits).len(),
        z >= 0,
    ensures
        !number_denotes(n, z),
{
    let ds = n.int_digits + n.frac_digits;
    let dv = digits_val(ds);
    lemma_drop_rel(n, e, f);
    let dt = drop_true(n);
    assert(all_le9(ds)) by {
        assert forall|k: int| 0 <= k < ds.len() implies ds[k] <= 9 by {
            if k < n.int_digits.len() {
                assert(ds[k] == n.int_digits[k]);
            } else {
                assert(ds[k] == n.frac_digits[k - n.int_digits.len()]);
            }
        }
    }
    lemma_val_bound(ds);
    lemma_pow10_mono(ds.len(), dt as nat);
    assert(exp_val(n) - n.frac_digits.len() == -dt);
    if dt == 0 {
        assert(ds.len() == 0);
        assert(ds =~= Seq::<u8>::empty());
        assert(dv == 0);
    } else {
        let p = pow10(dt as nat) as int;
        assert(dv < p);
        assert(number_denotes(n, z) == (z * p == dv));
        if z >= 1 {
            assert(z * p >= p) by (nonlinear_arith)
                requires
                    z >= 1,
                    p >= 1,
            ;
        } else {
            assert(z == 0);
            assert(z * p == 0);
        }
    }
}

pub proof fn lemma_branch_drop(n: NumberS, e: u64, f: nat, drop: u64, keep: nat)
    requires
        number_wf(n),
        !n.negative,
        e == min_u64(digits_val(n.exp_digits)),
        f == n.frac_digits.len(),
        n.exp_negative || e < f,
        drop == drop_code(e, f, n.exp_negative),
        drop < (n.int_digits + n.frac_digits).len(),
        keep == (n.int_digits + n.frac_digits).len() - drop,
    ensures
        ({
            let ds = n.int_digits + n.frac_digits;
            let pre = ds.subrange(0, keep as int);
            forall|z: int|
                number_denotes(n, z) == ((forall|k: int| keep <= k < ds.len() ==> ds[k] == 0) && z
                    == digits_val(pre))
        }),
{
    let ds = n.int_digits + n.frac_digits;
    let pre = ds.subrange(0, keep as int);
    let suf = ds.subrange(keep as int, ds.len() as int);
    lemma_drop_rel(n, e, f);
    assert(drop == drop_true(n));
    assert(ds =~= pre + suf);
    lemma_val_append(pre, suf);
    assert(all_le9(suf)) by {
        assert forall|k: int| 0 <= k < suf.len() implies suf[k] <= 9 by {
            let m = k + keep;
            if m < n.int_digits.len() {
                assert(ds[m] == n.int_digits[m]);
            } else {
                assert(ds[m] == n.frac_digits[m - n.int_digits.len()]);
            }
        }
    }
    lemma_val_bound(suf);
    lemma_val_zero(suf);
    assert((forall|k: int| keep <= k < ds.len() ==> ds[k] == 0) == (forall|k: int|
        0 <= k < suf.len() ==> suf[k] == 0)) by {
        if forall|k: int| keep <= k < ds.len() ==> ds[k] == 0 {
            assert forall|k: int| 0 <= k < suf.len() implies suf[k] == 0 by {
                assert(suf[k] == ds[k + keep]);
            }
        }
        if forall|k: int| 0 <= k < suf.len() ==> suf[k] == 0 {
            assert forall|k: int| keep <= k < ds.len() implies ds[k] == 0 by {
                assert(suf[k - keep] == ds[k]);
            }
        }
    }
    let a = digits_val(pre) as int;
    let b = digits_val(suf) as int;
    let p = pow10(suf.len()) as int;
    lemma_pow10_pos(suf.len());
    assert(suf.len() == drop);
    assert forall|z: int| number_denotes(n, z) == (b == 0 && z == a) by {
        if drop == 0 {
            assert(suf.len() == 0);
            assert(p == 1);
            assert(a * 1 + b == a + b);
        } else {
            assert(z * p == a * p + b <==> (b == 0 && z == a)) by (nonlinear_arith)
                requires
                    0 <= b < p,
                    p >= 1,
            {
                if z * p == a * p + b {
                    assert((z - a) * p == b);
                    if z - a >= 1 {
                        assert((z - a) * p >= p);
                    } else if z - a <= -1 {
                        assert((z - a) * p <= -p);
                    }
                }
            }
        }
    }
}

// N1
// MUST-006, MUST-013: 小数部が 0 の 0 以上の整数だけを値にする
pub fn number_to_u64(n: &Number) -> (r: Option<u64>)
    requires
        number_wf(n@),
    ensures
        match r {
            Some(v) => number_denotes(n@, v as int),
            None => forall|z: int| 0 <= z <= u64::MAX ==> !number_denotes(n@, z),
        },
{
    let ghost ds = number_mantissa(n);
    let ghost dv = digits_val(ds);
    let ghost ev = digits_val(n.exp_digits@);
    proof {
        lemma_val_zero(ds);
        assert(ds == n@.int_digits + n@.frac_digits);
    }
    if all_digits_zero(n) {
        proof {
            let x: int = exp_val(n@) - n@.frac_digits.len();
            assert(dv == 0);
            if x >= 0 {
                assert(0 * pow10(x as nat) == 0);
            } else {
                assert(0 * pow10((-x) as nat) == 0);
            }
        }
        return Some(0);
    }
    if n.negative {
        proof {
            assert forall|z: int| 0 <= z <= u64::MAX implies !number_denotes(n@, z) by {
                lemma_neg_not_denotes(n@, z);
            }
        }
        return None;
    }
    let total = n.int_digits.len() + n.frac_digits.len();
    let e = exponent_value(n);
    let f = n.frac_digits.len() as u64;
    assert(ds.subrange(0, total as int) =~= ds);
    if !n.exp_negative && e >= f {
        proof {
            lemma_branch_pos(n@, e, f as nat);
        }
        match digits_value(n, total) {
            None => None,
            Some(v) => mul_pow10(v, e - f),
        }
    } else {
        let drop = if n.exp_negative { e.saturating_add(f) } else { f - e };
        if drop >= total as u64 {
            proof {
                assert forall|z: int| 0 <= z <= u64::MAX implies !number_denotes(n@, z) by {
                    lemma_branch_drop_all(n@, e, f as nat, drop, z);
                }
            }
            return None;
        }
        let keep = total - drop as usize;
        proof {
            lemma_branch_drop(n@, e, f as nat, drop, keep as nat);
        }
        if !digits_zero_from(n, keep) {
            return None;
        }
        digits_value(n, keep)
    }
}

impl View for Number {
    type V = NumberS;

    open spec fn view(&self) -> NumberS {
        NumberS {
            negative: self.negative,
            int_digits: self.int_digits@,
            frac_digits: self.frac_digits@,
            exp_negative: self.exp_negative,
            exp_digits: self.exp_digits@,
        }
    }
}

// "uint": number_to_u64 が Some を返す数（N 節）
// MUST-013: インデックスは 0 以上の整数
pub open spec fn num_u64(n: NumberS) -> Option<u64> {
    if exists|z: int| 0 <= z <= u64::MAX && number_denotes(n, z) {
        Some((choose|z: int| 0 <= z <= u64::MAX && number_denotes(n, z)) as u64)
    } else {
        None
    }
}

pub proof fn lemma_num_u64(n: NumberS, r: Option<u64>)
    requires
        match r {
            Some(v) => number_denotes(n, v as int),
            None => forall|z: int| 0 <= z <= u64::MAX ==> !number_denotes(n, z),
        },
    ensures
        num_u64(n) == r,
{
    if let Some(v) = r {
        let z = choose|z: int| 0 <= z <= u64::MAX && number_denotes(n, z);
        lemma_denotes_unique(n, z, v as int);
    }
}

// number_to_u64 の事後条件から num_u64 を得る
pub proof fn lemma_num_u64_all()
    ensures
        forall|n: NumberS, v: u64| #[trigger] number_denotes(n, v as int) ==> num_u64(n) == Some(v),
        forall|n: NumberS|
            (forall|z: int| 0 <= z <= u64::MAX ==> !number_denotes(n, z)) ==> #[trigger] num_u64(n) is None,
{
    assert forall|n: NumberS, v: u64| #[trigger] number_denotes(n, v as int) implies num_u64(n) == Some(v) by {
        lemma_num_u64(n, Some(v));
    }
    assert forall|n: NumberS| (forall|z: int| 0 <= z <= u64::MAX ==> !number_denotes(n, z)) implies #[trigger] num_u64(
        n,
    ) is None by {
        lemma_num_u64(n, None);
    }
}

pub proof fn lemma_denotes_unique(n: NumberS, z1: int, z2: int)
    requires
        number_denotes(n, z1),
        number_denotes(n, z2),
    ensures
        z1 == z2,
{
    let x: int = exp_val(n) - n.frac_digits.len();
    if x < 0 {
        lemma_pow10_pos((-x) as nat);
        let p = pow10((-x) as nat) as int;
        assert(z1 == z2) by (nonlinear_arith)
            requires
                z1 * p == z2 * p,
                p >= 1,
        ;
    }
}

} // verus!
