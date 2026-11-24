use creusot_std::prelude::*;
#[cfg(creusot)]
use creusot_std::logic::{FSet, Mapping};

const MULTIPLIER: u128 = 0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645;

pub struct Pcg64 {
    state: u128,
    increment: u128,
}

// 増分は常に奇数
impl Invariant for Pcg64 {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.increment@ % 2 == 1 }
    }
}

// f(s) = A s + c (mod 2^128)。MULTIPLIER は非公開なので値を書く
#[logic(open)]
pub fn lcg(s: u128, c: u128) -> u128 {
    s * 0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645u128 + c
}

// output_xsl_rr
#[logic(open)]
pub fn out(x: u128) -> u64 {
    pearlite! {
        let rot = (x >> 122u32) as u32;
        let xsl = ((x >> 64u32) as u64) ^ (x as u64);
        (xsl >> rot) | (xsl << ((64u32 - rot) & 63u32))
    }
}

impl Pcg64 {
    #[bitwise_proof]
    #[ensures(result.increment == (stream << 1u32) | 1u128)]
    #[ensures(result.state == lcg(state + result.increment, result.increment))]
    #[check(terminates)]
    pub fn new(state: u128, stream: u128) -> Pcg64 {
        let increment = (stream << 1) | 1;
        let mut pcg = Pcg64 { state: state.wrapping_add(increment), increment };
        pcg.step();
        pcg
    }

    #[ensures((^self).state == lcg(self.state, self.increment))]
    #[ensures((^self).increment == self.increment)]
    #[check(terminates)]
    fn step(&mut self) {
        self.state = self.state.wrapping_mul(MULTIPLIER).wrapping_add(self.increment);
    }

    #[ensures((^self).state == lcg(self.state, self.increment))]
    #[ensures((^self).increment == self.increment)]
    #[ensures(result == out((^self).state))]
    #[check(terminates)]
    pub fn next_u64(&mut self) -> u64 {
        self.step();
        output_xsl_rr(self.state)
    }

    // int -> f32 のキャストを Creusot が翻訳できないので検証対象から外す
    #[cfg(not(creusot))]
    pub fn next_f32_mul(&mut self) -> f32 {
        u64_to_f32_mul(self.next_u64())
    }

    // u64_to_f32_dense を Creusot が扱えないので検証対象から外す
    #[cfg(not(creusot))]
    pub fn next_f32_dense(&mut self) -> f32 {
        u64_to_f32_dense(self.next_u64())
    }
}

#[bitwise_proof]
#[ensures(result == out(state))]
#[check(terminates)]
fn output_xsl_rr(state: u128) -> u64 {
    let rot = (state >> 122) as u32;
    let xsl = ((state >> 64) as u64) ^ (state as u64);
    (xsl >> rot) | (xsl << ((64 - rot) & 63))
}

#[cfg(not(creusot))]
const SCALE: f32 = 1.0 / 16777216.0;

// int -> f32 のキャストを Creusot が翻訳できないので検証対象から外す
#[cfg(not(creusot))]
pub fn u64_to_f32_mul(x: u64) -> f32 {
    ((x >> 40) as f32) * SCALE
}

#[cfg(not(creusot))]
const SCALE_TINY: f32 = 1.0 / 18446744073709551616.0;

// f32::from_bits に仕様がなく、int -> f32 のキャストも Creusot が翻訳できないので検証対象から外す
#[cfg(not(creusot))]
pub fn u64_to_f32_dense(x: u64) -> f32 {
    let z = x.leading_zeros();
    if z <= 40 {
        f32::from_bits(((126 - z) << 23) | ((x as u32) & 0x7F_FFFF))
    } else {
        ((x as u32) as f32) * SCALE_TINY
    }
}

// ---- P2・P3: 周期の証明 ----

// 法 2^128 と乗数 A
#[logic(open)]
pub fn m128() -> Int {
    pearlite! { u128::MAX@ + 1 }
}

#[logic]
pub fn mult() -> Int {
    pearlite! { MULTIPLIER@ }
}

#[logic]
pub fn p2(k: Int) -> Int {
    pearlite! { 2.pow(k) }
}

// A^n
#[logic]
pub fn ap(n: Int) -> Int {
    pearlite! { mult().pow(n) }
}

// S_n = 1 + A + ... + A^(n-1)
#[logic]
#[variant(n)]
pub fn gs(n: Int) -> Int {
    pearlite! { if n <= 0 { 0 } else { gs(n - 1) + ap(n - 1) } }
}

// (A-1)s + c
#[logic]
pub fn wv(s: Int, c: Int) -> Int {
    pearlite! { (mult() - 1) * s + c }
}

// f^[n](s)
#[logic(open)]
#[variant(n)]
pub fn lcg_n(n: Int, s: u128, c: u128) -> u128 {
    pearlite! { if n <= 0 { s } else { lcg(lcg_n(n - 1, s, c), c) } }
}

// k 回目 (k = 0, 1, ...) の next_u64 の出力
#[logic(open)]
pub fn out_k(k: Int, s: u128, c: u128) -> u64 {
    pearlite! { out(lcg_n(k + 1, s, c)) }
}

#[logic(opaque)]
#[ensures(p2(128) == m128())]
#[ensures(p2(127) * 2 == m128())]
pub fn lem_p2_128() {
    pearlite! {
        proof_assert!(p2(1) == 2);
        proof_assert!(p2(2) == p2(1) * p2(1));
        proof_assert!(p2(4) == p2(2) * p2(2));
        proof_assert!(p2(8) == p2(4) * p2(4));
        proof_assert!(p2(16) == p2(8) * p2(8));
        proof_assert!(p2(32) == p2(16) * p2(16));
        proof_assert!(p2(64) == p2(32) * p2(32));
        proof_assert!(p2(128) == p2(64) * p2(64));
        proof_assert!(p2(128) == p2(127) * 2);
    }
}

// (x + m q) mod m = x mod m
#[logic(opaque)]
#[requires(x >= 0 && q >= 0)]
#[ensures((x + m128() * q) % m128() == x % m128())]
pub fn lem_mod_add(x: Int, q: Int) {}

// (A (y mod m) + c) mod m = (A y + c) mod m
#[logic(opaque)]
#[requires(y >= 0 && c >= 0)]
#[ensures((mult() * (y % m128()) + c) % m128() == (mult() * y + c) % m128())]
pub fn lem_mod_affine(y: Int, c: Int) {
    pearlite! {
        proof_assert!(y == m128() * (y / m128()) + y % m128());
        proof_assert!(mult() * y + c == (mult() * (y % m128()) + c) + m128() * (mult() * (y / m128())));
        lem_mod_add(mult() * (y % m128()) + c, mult() * (y / m128()))
    }
}

#[logic(opaque)]
#[ensures(lcg(s, c)@ == (mult() * s@ + c@) % m128())]
pub fn lem_lcg(s: u128, c: u128) {}

#[logic(opaque)]
#[ensures((x + 0x8000_0000_0000_0000_0000_0000_0000_0000u128)@ == (x@ + p2(127)) % m128())]
pub fn lem_add_half(x: u128) {
    lem_p2_128()
}

#[logic(opaque)]
#[variant(n)]
#[requires(n >= 0)]
#[ensures(gs(n + 1) == 1 + mult() * gs(n))]
#[ensures(ap(n) == 1 + (mult() - 1) * gs(n))]
#[ensures(gs(n) >= 0 && ap(n) >= 1)]
pub fn lem_gs_succ(n: Int) {
    if n > 0 {
        lem_gs_succ(n - 1)
    }
}

#[logic(opaque)]
#[variant(k)]
#[requires(n >= 0 && k >= 0)]
#[ensures(gs(n + k) == gs(n) + ap(n) * gs(k))]
pub fn lem_gs_add(n: Int, k: Int) {
    pearlite! {
        if k > 0 {
            lem_gs_add(n, k - 1);
            proof_assert!(ap(n + (k - 1)) == ap(n) * ap(k - 1));
            proof_assert!(gs(n + k) == gs(n + (k - 1)) + ap(n + (k - 1)));
            proof_assert!(gs(k) == gs(k - 1) + ap(k - 1));
            proof_assert!(gs(n + k) == gs(n) + ap(n) * gs(k - 1) + ap(n) * ap(k - 1))
        }
    }
}

#[logic(opaque)]
#[variant(n)]
#[requires(n >= 0)]
#[ensures(ap(n) % 4 == 1)]
pub fn lem_ap_mod4(n: Int) {
    pearlite! {
        if n > 0 {
            lem_ap_mod4(n - 1);
            proof_assert!(ap(n) == mult() * ap(n - 1));
            proof_assert!(ap(n - 1) == 4 * (ap(n - 1) / 4) + 1);
            proof_assert!(ap(n) == 4 * (mult() * (ap(n - 1) / 4)) + mult());
            lem_gs_succ(n - 1)
        }
    }
}

#[logic(opaque)]
#[variant(n)]
#[requires(n >= 0)]
#[ensures(gs(n) % 2 == n % 2)]
pub fn lem_gs_parity(n: Int) {
    pearlite! {
        if n > 0 {
            lem_gs_parity(n - 1);
            lem_ap_mod4(n - 1);
            lem_gs_succ(n - 1)
        }
    }
}

// 奇数の積は奇数
#[logic(opaque)]
#[requires(x >= 1 && y >= 1 && x % 2 == 1 && y % 2 == 1)]
#[ensures((x * y) % 2 == 1 && x * y >= 1)]
pub fn lem_odd_mul(x: Int, y: Int) {
    pearlite! {
        proof_assert!(x == 2 * (x / 2) + 1);
        proof_assert!(y == 2 * (y / 2) + 1);
        proof_assert!(x * y == 2 * (2 * (x / 2) * (y / 2) + x / 2 + y / 2) + 1)
    }
}

#[logic(opaque)]
#[requires(s >= 0 && c >= 1 && c % 2 == 1)]
#[ensures(wv(s, c) >= 1 && wv(s, c) % 2 == 1)]
pub fn lem_w_odd(s: Int, c: Int) {
    pearlite! {
        proof_assert!(wv(s, c) == 2 * (((mult() - 1) / 2) * s) + c)
    }
}

// S_(2^j t) = 2^j * (奇数)
#[logic]
#[variant(j)]
pub fn os(j: Int, t: Int) -> Int {
    pearlite! { if j <= 0 { gs(t) } else { os(j - 1, t) * ((1 + ap(p2(j - 1) * t)) / 2) } }
}

#[logic(opaque)]
#[variant(j)]
#[requires(j >= 0 && t >= 1 && t % 2 == 1)]
#[ensures(gs(p2(j) * t) == p2(j) * os(j, t))]
#[ensures(os(j, t) >= 1 && os(j, t) % 2 == 1)]
pub fn lem_gs_pow2(j: Int, t: Int) {
    pearlite! {
        if j > 0 {
            let n = p2(j - 1) * t;
            let h = (1 + ap(n)) / 2;
            lem_gs_pow2(j - 1, t);
            proof_assert!(p2(j) == 2 * p2(j - 1));
            proof_assert!(n >= 1);
            proof_assert!(p2(j) * t == n + n);
            lem_gs_add(n, n);
            lem_ap_mod4(n);
            proof_assert!(ap(n) == 4 * (ap(n) / 4) + 1);
            proof_assert!(1 + ap(n) == 2 * h);
            proof_assert!(h == 2 * (ap(n) / 4) + 1);
            lem_odd_mul(os(j - 1, t), h);
            proof_assert!(gs(n + n) == gs(n) * (1 + ap(n)));
            proof_assert!(gs(n + n) == p2(j - 1) * os(j - 1, t) * 2 * h);
            proof_assert!(p2(j - 1) * os(j - 1, t) * 2 * h == p2(j) * (os(j - 1, t) * h));
            proof_assert!(gs(p2(j) * t) == gs(n + n));
            proof_assert!(os(j, t) == os(j - 1, t) * h)
        } else {
            lem_gs_parity(t)
        }
    }
}

// f^[n](s) = (s + S_n w) mod 2^128
#[logic(opaque)]
#[variant(n)]
#[requires(n >= 0)]
#[ensures(lcg_n(n, s, c)@ == (s@ + gs(n) * wv(s@, c@)) % m128())]
pub fn lem_lcg_n(n: Int, s: u128, c: u128) {
    pearlite! {
        if n > 0 {
            let y = s@ + gs(n - 1) * wv(s@, c@);
            lem_lcg_n(n - 1, s, c);
            lem_lcg(lcg_n(n - 1, s, c), c);
            lem_gs_succ(n - 1);
            proof_assert!(y >= 0);
            lem_mod_affine(y, c@);
            proof_assert!(mult() * y + c@ == s@ + gs(n) * wv(s@, c@))
        } else {
            proof_assert!(s@ % m128() == s@)
        }
    }
}

// n = 2^v2(n) * (奇数)
#[logic]
#[variant(n)]
pub fn v2(n: Int) -> Int {
    pearlite! { if n <= 0 || n % 2 == 1 { 0 } else { 1 + v2(n / 2) } }
}

#[logic]
#[variant(n)]
pub fn odd_part(n: Int) -> Int {
    pearlite! { if n <= 0 || n % 2 == 1 { n } else { odd_part(n / 2) } }
}

#[logic(opaque)]
#[variant(n)]
#[requires(n >= 1)]
#[ensures(v2(n) >= 0 && odd_part(n) >= 1 && odd_part(n) % 2 == 1)]
#[ensures(n == p2(v2(n)) * odd_part(n))]
pub fn lem_v2(n: Int) {
    pearlite! {
        if n % 2 == 0 {
            lem_v2(n / 2);
            proof_assert!(p2(v2(n)) == 2 * p2(v2(n / 2)))
        }
    }
}

#[logic(opaque)]
#[requires(1 <= n && n < m128())]
#[ensures(v2(n) <= 127)]
pub fn lem_v2_bound(n: Int) {
    pearlite! {
        lem_v2(n);
        lem_p2_128();
        if v2(n) >= 128 {
            proof_assert!(p2(v2(n)) >= p2(128));
            proof_assert!(n >= p2(v2(n)))
        }
    }
}

// 0 <= v <= 127 で t が奇数なら、x + 2^v t は法 2^128 で x と異なる
#[logic(opaque)]
#[requires(0 <= x && x < m128() && 0 <= v && v <= 127 && t >= 1 && t % 2 == 1)]
#[ensures((x + p2(v) * t) % m128() != x)]
pub fn lem_no_zero(x: Int, v: Int, t: Int) {
    pearlite! {
        let y = p2(v) * t;
        let q = (x + y) / m128();
        lem_p2_128();
        proof_assert!(p2(128) == p2(v) * p2(128 - v));
        proof_assert!(p2(128 - v) == 2 * p2(127 - v));
        proof_assert!((x + y) % m128() == x ==> y == m128() * q);
        proof_assert!((x + y) % m128() == x ==> p2(v) * (t - p2(128 - v) * q) == 0);
        proof_assert!((x + y) % m128() == x ==> t == 2 * (p2(127 - v) * q))
    }
}

// x + 2^127 t (t 奇数) は法 2^128 で x + 2^127
#[logic(opaque)]
#[requires(0 <= x && t >= 1 && t % 2 == 1)]
#[ensures((x + p2(127) * t) % m128() == (x + p2(127)) % m128())]
pub fn lem_half(x: Int, t: Int) {
    pearlite! {
        lem_p2_128();
        proof_assert!(p2(127) * t == p2(127) + m128() * (t / 2));
        lem_mod_add(x + p2(127), t / 2)
    }
}

#[logic(opaque)]
#[variant(a)]
#[requires(a >= 0 && b >= 0)]
#[ensures(lcg_n(a + b, s, c) == lcg_n(a, lcg_n(b, s, c), c))]
pub fn lem_lcg_n_add(a: Int, b: Int, s: u128, c: u128) {
    if a > 0 {
        lem_lcg_n_add(a - 1, b, s, c)
    }
}

// P2: 状態の周期は 2^128
#[logic(opaque)]
#[requires(c@ % 2 == 1)]
#[ensures(lcg_n(m128(), s, c) == s)]
#[ensures(0 < n && n < m128() ==> lcg_n(n, s, c) != s)]
pub fn p2_state_period(s: u128, c: u128, n: Int) {
    pearlite! {
        lem_w_odd(s@, c@);
        lem_p2_128();
        lem_lcg_n(m128(), s, c);
        lem_gs_pow2(128, 1);
        proof_assert!(gs(m128()) * wv(s@, c@) == m128() * (os(128, 1) * wv(s@, c@)));
        lem_mod_add(s@, os(128, 1) * wv(s@, c@));
        if 0 < n && n < m128() {
            lem_v2(n);
            lem_v2_bound(n);
            lem_gs_pow2(v2(n), odd_part(n));
            lem_lcg_n(n, s, c);
            lem_odd_mul(os(v2(n), odd_part(n)), wv(s@, c@));
            proof_assert!(gs(n) * wv(s@, c@) == p2(v2(n)) * (os(v2(n), odd_part(n)) * wv(s@, c@)));
            lem_no_zero(s@, v2(n), os(v2(n), odd_part(n)) * wv(s@, c@))
        }
    }
}

// n が出力の周期なら q n も周期
#[logic(opaque)]
#[variant(q)]
#[requires(n >= 0 && q >= 0 && j >= 0)]
#[ensures((forall<i> i >= 0 ==> out_k(i + n, s, c) == out_k(i, s, c)) ==> out_k(j + q * n, s, c) == out_k(j, s, c))]
pub fn lem_period_mul(s: u128, c: u128, n: Int, q: Int, j: Int) {
    pearlite! {
        if q > 0 {
            lem_period_mul(s, c, n, q - 1, j);
            proof_assert!((q - 1) * n >= 0);
            proof_assert!(j + q * n == (j + (q - 1) * n) + n);
            proof_assert!((forall<i> i >= 0 ==> out_k(i + n, s, c) == out_k(i, s, c))
                ==> out_k((j + (q - 1) * n) + n, s, c) == out_k(j + (q - 1) * n, s, c))
        }
    }
}

// P3: 出力の周期は 2^128
#[logic(opaque)]
#[requires(c@ % 2 == 1)]
#[ensures(k >= 0 ==> out_k(k + m128(), s, c) == out_k(k, s, c))]
#[ensures(0 < n && n < m128() ==> exists<j> j >= 0 && out_k(j + n, s, c) != out_k(j, s, c))]
pub fn p3_output_period(s: u128, c: u128, k: Int, n: Int) {
    pearlite! {
        p2_state_period(s, c, 0);
        if k >= 0 {
            lem_lcg_n_add(k + 1, m128(), s, c)
        };
        if 0 < n && n < m128() {
            let x = lcg_n(1, s, c);
            let v = v2(n);
            let t = odd_part(n);
            let q = p2(127 - v);
            lem_v2(n);
            lem_v2_bound(n);
            proof_assert!(p2(127) == q * p2(v));
            proof_assert!(q * n == p2(127) * t);
            lem_period_mul(s, c, n, q, 0);
            lem_lcg_n_add(q * n, 1, s, c);
            lem_w_odd(x@, c@);
            lem_lcg_n(q * n, x, c);
            lem_gs_pow2(127, t);
            lem_odd_mul(os(127, t), wv(x@, c@));
            proof_assert!(gs(q * n) * wv(x@, c@) == p2(127) * (os(127, t) * wv(x@, c@)));
            lem_half(x@, os(127, t) * wv(x@, c@));
            lem_add_half(x);
            proof_assert!(lcg_n(q * n, x, c) == x + 0x8000_0000_0000_0000_0000_0000_0000_0000u128);
            lem_out_flip(x)
        }
    }
}

// 最上位ビットだけが異なる 2 つの状態の出力は異なる
#[logic(opaque)]
#[bitwise_proof]
#[ensures(out(x + 0x8000_0000_0000_0000_0000_0000_0000_0000u128) != out(x))]
pub fn lem_out_flip(x: u128) {}

// ---- P4: 1 周期の中で各 u64 の値はちょうど 2^64 回出る ----

// Int から u128・u64 へ
#[logic]
#[variant(x)]
#[ensures(0 <= x && x <= u128::MAX@ ==> result@ == x)]
pub fn u128_of(x: Int) -> u128 {
    pearlite! { if x <= 0 { 0u128 } else { u128_of(x - 1) + 1u128 } }
}

#[logic]
#[variant(x)]
#[ensures(0 <= x && x <= u64::MAX@ ==> result@ == x)]
pub fn u64_of(x: Int) -> u64 {
    pearlite! { if x <= 0 { 0u64 } else { u64_of(x - 1) + 1u64 } }
}

#[logic(opaque)]
#[ensures(forall<x: u128> u128_of(x@) == x)]
pub fn lem_u128_of() {}

// 上位 64 ビットが h の状態で out(h:lo) == v となる lo
#[logic(open)]
pub fn out_inv(h: u64, v: u64) -> u64 {
    pearlite! {
        let rot = (h >> 58u32) as u32;
        ((v << rot) | (v >> ((64u32 - rot) & 63u32))) ^ h
    }
}

#[logic(opaque)]
#[bitwise_proof]
#[ensures((out(x) == v) == ((x as u64) == out_inv((x >> 64u32) as u64, v)))]
pub fn bv_out_inv(x: u128, v: u64) {}

#[logic(opaque)]
#[bitwise_proof]
#[ensures((x as u64) == (x - ((x >> 64u32) << 64u32)) as u64)]
pub fn bv_trunc_split64(x: u128) {}

#[logic(opaque)]
#[bitwise_proof]
#[requires(x@ <= u64::MAX@)]
#[ensures((x as u64)@ == x@)]
pub fn bv_cast128_64(x: u128) {}

// (x as u64)@ = x@ mod 2^64、((x >> 64) as u64)@ = x@ / 2^64
#[logic(opaque)]
#[ensures((x as u64)@ == x@ % pw(64))]
#[ensures(((x >> 64u32) as u64)@ == x@ / pw(64))]
pub fn lem_split64(x: u128) {
    pearlite! {
        let y = (x >> 64u32) << 64u32;
        lem_pw_mono(64, 128);
        bv_shr128(x, 64u32);
        bv_shl128(x >> 64u32, 64u32);
        proof_assert!(x@ == pw(64) * (x@ / pw(64)) + x@ % pw(64) && 0 <= x@ % pw(64) && x@ % pw(64) < pw(64));
        proof_assert!((x@ / pw(64)) * pw(64) <= x@);
        lem_div_unique((x@ / pw(64)) * pw(64), u128::MAX@ + 1, 0);
        proof_assert!(y@ == (x@ / pw(64)) * pw(64));
        bv_sub128(x, y);
        bv_cast128_64(x - y);
        bv_trunc_split64(x);
        lem_div_lt(x@, pw(64), pw(64));
        bv_cast128_64(x >> 64u32)
    }
}

// 状態 X (Int) の出力
#[logic(open)]
pub fn out_i(x: Int) -> u64 {
    pearlite! { out(u128_of(x)) }
}

#[logic(open)]
pub fn lo_i(h: Int, v: u64) -> Int {
    pearlite! { out_inv(u64_of(h), v)@ }
}

// out(X) == v は「下位 64 ビットが lo_i(上位 64 ビット)」と同じ
#[logic(opaque)]
#[requires(0 <= x && x < m128())]
#[ensures((out_i(x) == v) == (x % pw(64) == lo_i(x / pw(64), v)))]
pub fn lem_out_char(x: Int, v: u64) {
    pearlite! {
        let y = u128_of(x);
        lem_p2_128();
        lem_pw_mono(64, 128);
        proof_assert!(y@ == x);
        bv_out_inv(y, v);
        lem_split64(y);
        lem_div_lt(x, pw(64), pw(64));
        proof_assert!(u64_of(x / pw(64))@ == x / pw(64));
        proof_assert!((y >> 64u32) as u64 == u64_of(x / pw(64)))
    }
}

// 単射な写像で集合の要素数は変わらない
#[logic(opaque)]
#[variant(s.len())]
#[requires(forall<x: Int, y: Int> s.contains(x) && s.contains(y) && f.get(x) == f.get(y) ==> x == y)]
#[ensures(s.map(f).len() == s.len())]
pub fn lem_map_inj(s: FSet<Int>, f: Mapping<Int, Int>) {
    pearlite! {
        if s.len() > 0 {
            let x = s.peek();
            lem_map_inj(s.remove(x), f);
            proof_assert!(s.map(f).ext_eq(s.remove(x).map(f).insert(f.get(x))));
            proof_assert!(!s.remove(x).map(f).contains(f.get(x)))
        } else {
            proof_assert!(s.map(f).ext_eq(FSet::empty()))
        }
    }
}

// out(X) == v となる状態 X の集合
#[logic(open)]
pub fn bset(v: u64) -> FSet<Int> {
    pearlite! { FSet::interval(0, m128()).filter(|x: Int| out_i(x) == v) }
}

#[logic]
pub fn mk(v: u64) -> Mapping<Int, Int> {
    pearlite! { |h: Int| h * pw(64) + lo_i(h, v) }
}

#[logic(opaque)]
#[requires(0 <= h && h < pw(64))]
#[ensures(0 <= lo_i(h, v) && lo_i(h, v) < pw(64))]
#[ensures(0 <= mk(v).get(h) && mk(v).get(h) < m128())]
#[ensures(mk(v).get(h) / pw(64) == h && mk(v).get(h) % pw(64) == lo_i(h, v))]
pub fn lem_mk(h: Int, v: u64) {
    pearlite! {
        lem_p2_128();
        lem_pw_mono(64, 128);
        proof_assert!(lo_i(h, v) <= u64::MAX@ && pw(64) == u64::MAX@ + 1);
        lem_div_unique(mk(v).get(h), pw(64), h);
        proof_assert!((h + 1) * pw(64) <= pw(64) * pw(64))
    }
}

// 各 v について out(X) == v となる状態はちょうど 2^64 個
#[logic(opaque)]
#[ensures(bset(v).len() == pw(64))]
pub fn lem_bset_len(v: u64) {
    pearlite! {
        let hs = FSet::interval(0, pw(64));
        lem_p2_128();
        lem_pw_mono(64, 128);
        proof_assert!(forall<h: Int> hs.contains(h) ==>
            lem_mk(h, v) == () && lem_out_char(mk(v).get(h), v) == () && bset(v).contains(mk(v).get(h)));
        proof_assert!(forall<x: Int> bset(v).contains(x) ==>
            lem_out_char(x, v) == () && lem_div_lt(x, pw(64), pw(64)) == ()
            && hs.contains(x / pw(64)) && mk(v).get(x / pw(64)) == x);
        proof_assert!(bset(v).ext_eq(hs.map(mk(v))));
        proof_assert!(forall<h1: Int, h2: Int> hs.contains(h1) && hs.contains(h2) && mk(v).get(h1) == mk(v).get(h2) ==>
            lem_mk(h1, v) == () && lem_mk(h2, v) == () && h1 == h2);
        lem_map_inj(hs, mk(v))
    }
}

// k 回目の状態 (Int)
#[logic]
pub fn st(s: u128, c: u128) -> Mapping<Int, Int> {
    pearlite! { |k: Int| lcg_n(k + 1, s, c)@ }
}

#[logic(opaque)]
#[requires(c@ % 2 == 1 && 0 <= k1 && k1 < k2 && k2 < m128())]
#[ensures(st(s, c).get(k1) != st(s, c).get(k2))]
pub fn lem_st_ne(s: u128, c: u128, k1: Int, k2: Int) {
    pearlite! {
        lem_lcg_n_add(k2 - k1, k1 + 1, s, c);
        proof_assert!(k2 - k1 + (k1 + 1) == k2 + 1);
        p2_state_period(lcg_n(k1 + 1, s, c), c, k2 - k1);
        proof_assert!(lcg_n(k2 + 1, s, c) != lcg_n(k1 + 1, s, c))
    }
}

// P2 より 1 周期の状態は互いに異なり、すべての状態を 1 回ずつ通る
#[logic(opaque)]
#[requires(c@ % 2 == 1)]
#[ensures(forall<k1: Int, k2: Int> 0 <= k1 && k1 < m128() && 0 <= k2 && k2 < m128()
    && st(s, c).get(k1) == st(s, c).get(k2) ==> k1 == k2)]
#[ensures(FSet::interval(0, m128()).map(st(s, c)) == FSet::interval(0, m128()))]
pub fn lem_states(s: u128, c: u128) {
    pearlite! {
        let ks = FSet::interval(0, m128());
        proof_assert!(forall<k1: Int, k2: Int> 0 <= k1 && k1 < k2 && k2 < m128() ==>
            lem_st_ne(s, c, k1, k2) == () && st(s, c).get(k1) != st(s, c).get(k2));
        lem_map_inj(ks, st(s, c));
        proof_assert!(ks.map(st(s, c)).is_subset(ks))
    }
}

// k < 2^128 のうち out_k(k) == v となる k の集合
#[logic(open)]
pub fn hits(s: u128, c: u128, v: u64) -> FSet<Int> {
    pearlite! { FSet::interval(0, m128()).filter(|k: Int| out_k(k, s, c) == v) }
}

// P4: 1 周期 (2^128 回) の出力の中で、各 u64 の値はちょうど 2^64 回出る
#[logic(opaque)]
#[requires(c@ % 2 == 1)]
#[ensures(hits(s, c, v).len() == pw(64))]
pub fn p4_uniform(s: u128, c: u128, v: u64) {
    pearlite! {
        let ks = FSet::interval(0, m128());
        let g = st(s, c);
        lem_states(s, c);
        lem_u128_of();
        lem_bset_len(v);
        proof_assert!(forall<k: Int> hits(s, c, v).contains(k) ==> bset(v).contains(g.get(k)));
        proof_assert!(forall<x: Int> bset(v).contains(x) ==> ks.map(g).contains(x));
        proof_assert!(forall<x: Int> bset(v).contains(x) ==> hits(s, c, v).map(g).contains(x));
        proof_assert!(bset(v).ext_eq(hits(s, c, v).map(g)));
        lem_map_inj(hits(s, c, v), g)
    }
}

// ---- P4 で使うビット演算と整数の補題 ----

#[logic(open)]
pub fn pw(k: Int) -> Int {
    pearlite! { k.pow2() }
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(k@ < 128)]
#[ensures((x >> k)@ == x@ / pw(k@))]
pub fn bv_shr128_0(x: u128, k: u128) {}

#[logic(opaque)]
#[requires(k@ < 128)]
#[ensures((x >> k)@ == x@ / pw(k@))]
pub fn bv_shr128(x: u128, k: u32) {
    bv_shr128_0(x, k as u128)
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(k@ < 128)]
#[ensures((x << k)@ == (x@ * pw(k@)) % (u128::MAX@ + 1))]
pub fn bv_shl128_0(x: u128, k: u128) {}

#[logic(opaque)]
#[requires(k@ < 128)]
#[ensures((x << k)@ == (x@ * pw(k@)) % (u128::MAX@ + 1))]
pub fn bv_shl128(x: u128, k: u32) {
    bv_shl128_0(x, k as u128)
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(y <= x)]
#[ensures((x - y)@ == x@ - y@)]
pub fn bv_sub128(x: u128, y: u128) {}

#[logic(opaque)]
#[requires(d > 0 && q >= 0 && q * d <= x && x < q * d + d)]
#[ensures(x / d == q && x % d == x - q * d)]
pub fn lem_div_unique(x: Int, d: Int, q: Int) {
    pearlite! {
        proof_assert!(x == d * (x / d) + x % d);
        proof_assert!(0 <= x % d && x % d < d);
        proof_assert!(x / d >= q + 1 ==> d * (x / d) >= d * (q + 1));
        proof_assert!(x / d <= q - 1 ==> d * (x / d) <= d * (q - 1))
    }
}

#[logic(opaque)]
#[requires(x >= 0 && d > 0 && x < d * q)]
#[ensures(x / d < q)]
pub fn lem_div_lt(x: Int, d: Int, q: Int) {
    pearlite! {
        proof_assert!(x == d * (x / d) + x % d && x % d >= 0);
        proof_assert!(x / d >= q ==> d * (x / d) >= d * q)
    }
}

#[logic(opaque)]
#[variant(j - i)]
#[requires(0 <= i && i <= j)]
#[ensures(pw(i) <= pw(j) && pw(j) == pw(i) * pw(j - i) && pw(i) >= 1)]
pub fn lem_pw_mono(i: Int, j: Int) {
    pearlite! {
        if i < j {
            lem_pw_mono(i, j - 1)
        }
    }
}
