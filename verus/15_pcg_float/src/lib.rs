use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::arithmetic::div_mod::*;
#[cfg(verus_only)]
use vstd::arithmetic::power::*;
#[cfg(verus_only)]
use vstd::arithmetic::power2::*;
#[cfg(verus_only)]
use vstd::set::*;
#[cfg(verus_only)]
use vstd::set_lib::*;

verus! {

const MULTIPLIER: u128 = 0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645;

pub struct Pcg64 {
    state: u128,
    increment: u128,
}

impl Pcg64 {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        self.increment % 2 == 1
    }

    pub closed spec fn st(self) -> u128 {
        self.state
    }

    pub closed spec fn inc(self) -> u128 {
        self.increment
    }

    pub fn new(state: u128, stream: u128) -> (r: Pcg64)
        ensures
            r.inc() == (2 * stream + 1) % m128(),
            r.inc() % 2 == 1,
            r.st() == lcg((state + r.inc()) % m128(), r.inc() as int),
    {
        proof {
            lemma_odd_inc(stream);
        }
        let increment = (stream << 1) | 1;
        let mut pcg = Pcg64 { state: state.wrapping_add(increment), increment };
        proof {
            lemma_wrap_add(state, increment);
        }
        pcg.step();
        pcg
    }

    fn step(&mut self)
        ensures
            final(self).inc() == old(self).inc(),
            final(self).st() == lcg(old(self).st() as int, old(self).inc() as int),
    {
        proof {
            use_type_invariant(&*self);
            lemma_wrap_lcg(self.state, self.increment);
        }
        self.state = self.state.wrapping_mul(MULTIPLIER).wrapping_add(self.increment);
    }

    // P1
    pub fn next_u64(&mut self) -> (r: u64)
        ensures
            final(self).inc() == old(self).inc(),
            final(self).inc() % 2 == 1,
            final(self).st() == lcg(old(self).st() as int, old(self).inc() as int),
            r == out(final(self).st()),
    {
        self.step();
        proof {
            use_type_invariant(&*self);
        }
        output_xsl_rr(self.state)
    }

    pub fn next_f32_mul(&mut self) -> f32 {
        u64_to_f32_mul(self.next_u64())
    }
}

proof fn lemma_odd_inc(stream: u128)
    ensures
        ((stream << 1) | 1) == (2 * stream + 1) % m128(),
        ((stream << 1) | 1) % 2 == 1,
{
    assert(((stream << 1) | 1) % 2 == 1) by (bit_vector);
    if stream < 0x8000_0000_0000_0000_0000_0000_0000_0000u128 {
        assert(((stream << 1) | 1) == 2 * stream + 1) by (bit_vector)
            requires
                stream < 0x8000_0000_0000_0000_0000_0000_0000_0000u128,
        ;
        lemma_small_mod((2 * stream + 1) as nat, m128() as nat);
    } else {
        assert(((stream << 1) | 1) == 2 * (stream - 0x8000_0000_0000_0000_0000_0000_0000_0000u128) + 1) by (bit_vector)
            requires
                stream >= 0x8000_0000_0000_0000_0000_0000_0000_0000u128,
        ;
        lemma_fundamental_div_mod_converse(2 * stream + 1, m128(), 1, 2 * (stream - 0x8000_0000_0000_0000_0000_0000_0000_0000u128) + 1);
    }
}

proof fn lemma_wrap_lcg(s: u128, c: u128)
    ensures
        s.wrapping_mul(0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645u128).wrapping_add(c) == lcg(
            s as int,
            c as int,
        ),
{
    let m = s as int * mul_a();
    let p = m % m128();
    lemma_add_mod_noop(m, c as int, m128());
    lemma_small_mod(c as nat, m128() as nat);
    lemma_mod_bound(m, m128());
    if p + c >= m128() {
        lemma_fundamental_div_mod_converse(p + c, m128(), 1, p + c - m128());
    } else {
        lemma_small_mod((p + c) as nat, m128() as nat);
    }
}

proof fn lemma_wrap_add(s: u128, c: u128)
    ensures
        s.wrapping_add(c) == (s + c) % m128(),
{
    if s + c >= m128() {
        lemma_fundamental_div_mod_converse(s + c, m128(), 1, s + c - m128());
    } else {
        lemma_small_mod((s + c) as nat, m128() as nat);
    }
}

proof fn lemma_mod_bound(x: int, m: int)
    requires
        m > 0,
    ensures
        0 <= x % m < m,
{
}

fn output_xsl_rr(state: u128) -> (r: u64)
    ensures
        r == out(state),
{
    proof {
        assert(state >> 122 < 64) by (bit_vector);
        assert(forall|x: u32| #[trigger] (x & 63u32) < 64) by (bit_vector);
    }
    let rot = (state >> 122) as u32;
    let xsl = ((state >> 64) as u64) ^ (state as u64);
    proof {
        assert((xsl >> rot) | (xsl << (sub(64u32, rot) & 63u32)) == out(state)) by (bit_vector)
            requires
                rot == (state >> 122) as u32,
                xsl == ((state >> 64) as u64) ^ (state as u64),
        ;
    }
    (xsl >> rot) | (xsl << ((64 - rot) & 63))
}

// f32 の除算は spec 式にできないため exec const にする
exec const SCALE: f32 = 1.0 / 16777216.0;

pub fn u64_to_f32_mul(x: u64) -> f32 {
    ((x >> 40) as f32) * SCALE
}

// ---- 仕様 ----

pub open spec fn m128() -> int {
    u128::MAX + 1
}

pub open spec fn mul_a() -> int {
    0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645
}

// f(s) = (A s + c) mod 2^128
pub open spec fn lcg(s: int, c: int) -> int {
    (mul_a() * s + c) % m128()
}

// f^[n](s)
pub open spec fn iter(n: nat, s: int, c: int) -> int
    decreases n,
{
    if n == 0 {
        s
    } else {
        lcg(iter((n - 1) as nat, s, c), c)
    }
}

pub open spec fn rotr64(x: u64, r: u64) -> u64 {
    if r == 0 {
        x
    } else {
        (x >> r) | (x << (64 - r) as u64)
    }
}

// XSL RR
pub open spec fn out(s: u128) -> u64 {
    rotr64(((s >> 64u128) as u64) ^ (s as u64), (s >> 122u128) as u64)
}

// o_k = out(f^[k+1](s))
pub open spec fn output(s: int, c: int, k: nat) -> u64 {
    out(iter(k + 1, s, c) as u128)
}

// ---- P2: 状態の周期 ----

// S_n = 1 + A + ... + A^(n-1)
pub open spec fn geo(n: nat) -> int
    decreases n,
{
    if n == 0 {
        0
    } else {
        1 + mul_a() * geo((n - 1) as nat)
    }
}

proof fn lemma_pow2_128()
    ensures
        pow2(128) == m128(),
        pow2(127) * 2 == m128(),
{
    lemma2_to64();
    lemma_pow2_adds(64, 64);
    lemma_pow2_unfold(128);
}

// f^[n](s) = s + S_n((A-1)s + c) mod 2^128
proof fn lemma_iter_closed(n: nat, s: int, c: int)
    requires
        0 <= s < m128(),
    ensures
        iter(n, s, c) == (s + geo(n) * ((mul_a() - 1) * s + c)) % m128(),
    decreases n,
{
    let d = (mul_a() - 1) * s + c;
    if n == 0 {
        lemma_small_mod(s as nat, m128() as nat);
    } else {
        let n1 = (n - 1) as nat;
        lemma_iter_closed(n1, s, c);
        let x = s + geo(n1) * d;
        let r = x % m128();
        let q = x / m128();
        lemma_fundamental_div_mod(x, m128());
        assert(mul_a() * r + c == mul_a() * x + c - (mul_a() * q) * m128()) by (nonlinear_arith)
            requires
                x == m128() * q + r,
        ;
        lemma_mod_multiples_vanish(-(mul_a() * q), mul_a() * x + c, m128());
        assert(mul_a() * x + c == s + geo(n) * d) by (nonlinear_arith)
            requires
                x == s + geo(n1) * d,
                d == (mul_a() - 1) * s + c,
                geo(n) == 1 + mul_a() * geo(n1),
        ;
    }
}

proof fn lemma_geo_nonneg(n: nat)
    ensures
        geo(n) >= 1 || n == 0,
        geo(n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_geo_nonneg((n - 1) as nat);
        assert(mul_a() * geo((n - 1) as nat) >= 0) by (nonlinear_arith)
            requires
                geo((n - 1) as nat) >= 0,
        ;
    }
}

proof fn lemma_geo_parity(n: nat)
    ensures
        geo(n) % 2 == n % 2,
    decreases n,
{
    hide(geo);
    if n > 0 {
        let n1 = (n - 1) as nat;
        lemma_geo_parity(n1);
        lemma_geo_step(n1);
        assert(n1 + 1 == n);
    } else {
        reveal(geo);
    }
}

// A は奇数なので S_(n+1) = 1 + A S_n ≡ 1 + S_n (mod 2)
proof fn lemma_geo_step(n: nat)
    ensures
        geo(n + 1) % 2 == (1 + geo(n)) % 2,
{
    let g = geo(n);
    let h = 0x11b0_7682_8fe3_2ed2_21c2_efb2_4fe6_7b22int;
    assert(geo(n + 1) == 1 + mul_a() * g);
    assert(1 + mul_a() * g == 2 * (h * g) + (1 + g)) by (nonlinear_arith)
        requires
            mul_a() == 2 * h + 1,
    ;
    lemma_mod_multiples_vanish(h * g, 1 + g, 2);
}

// S_(a+b) = S_b + A^b S_a
proof fn lemma_geo_add(a: nat, b: nat)
    ensures
        geo(a + b) == geo(b) + pow(mul_a(), b) * geo(a),
    decreases b,
{
    reveal(pow);
    if b > 0 {
        let b1 = (b - 1) as nat;
        lemma_geo_add(a, b1);
        assert(geo(a + b) == 1 + mul_a() * geo(a + b1));
        assert(1 + mul_a() * (geo(b1) + pow(mul_a(), b1) * geo(a)) == geo(b) + (mul_a() * pow(
            mul_a(),
            b1,
        )) * geo(a)) by (nonlinear_arith)
            requires
                geo(b) == 1 + mul_a() * geo(b1),
        ;
    }
}

proof fn lemma_pow_mod4(m: nat)
    ensures
        pow(mul_a(), m) % 4 == 1,
    decreases m,
{
    reveal(pow);
    if m > 0 {
        lemma_pow_mod4((m - 1) as nat);
        lemma_mul_mod_noop(mul_a(), pow(mul_a(), (m - 1) as nat), 4);
    }
}

// y % 2^(k+1) == 0 <==> y 偶数かつ (y/2) % 2^k == 0
proof fn lemma_div_pow2_step(k: nat, y: int)
    requires
        y >= 0,
    ensures
        (y % (pow2(k + 1) as int) == 0) == (y % 2 == 0 && (y / 2) % (pow2(k) as int) == 0),
{
    lemma_pow2_unfold(k + 1);
    lemma_pow2_pos(k);
    lemma_mod_breakdown(y, 2, pow2(k) as int);
    lemma_mod_bound(y / 2, pow2(k) as int);
}

// u が奇数なら 2^k | x u <==> 2^k | x
proof fn lemma_odd_factor(k: nat, x: int, u: int)
    requires
        x >= 0,
        u > 0,
        u % 2 == 1,
    ensures
        ((x * u) % (pow2(k) as int) == 0) == (x % (pow2(k) as int) == 0),
    decreases k,
{
    if k == 0 {
        lemma2_to64();
    } else {
        let k1 = (k - 1) as nat;
        assert(x * u >= 0) by (nonlinear_arith)
            requires
                x >= 0,
                u > 0,
        ;
        lemma_div_pow2_step(k1, x * u);
        lemma_div_pow2_step(k1, x);
        lemma_mul_mod_noop(x, u, 2);
        if x % 2 == 0 {
            let x2 = x / 2;
            assert(x * u == 2 * (x2 * u)) by (nonlinear_arith)
                requires
                    x == 2 * x2,
            ;
            assert((x * u) / 2 == x2 * u);
            lemma_odd_factor(k1, x2, u);
        }
    }
}

// 2^k | S_n <==> 2^k | n
proof fn lemma_geo_v2(k: nat, n: nat)
    ensures
        (geo(n) % (pow2(k) as int) == 0) == (n as int % (pow2(k) as int) == 0),
    decreases k,
{
    hide(geo);
    if k == 0 {
        lemma2_to64();
    } else {
        let k1 = (k - 1) as nat;
        lemma_geo_nonneg(n);
        lemma_geo_parity(n);
        lemma_div_pow2_step(k1, geo(n));
        lemma_div_pow2_step(k1, n as int);
        if n % 2 == 0 {
            let m = (n / 2) as nat;
            let u = lemma_geo_double(m);
            assert(geo(n) / 2 == geo(m) * u);
            lemma_geo_nonneg(m);
            lemma_odd_factor(k1, geo(m), u);
            lemma_geo_v2(k1, m);
        } else {
            assert(geo(n) % 2 == 1);
        }
    }
}

// S_2m = 2 S_m u（u は奇数）
proof fn lemma_geo_double(m: nat) -> (u: int)
    ensures
        geo(2 * m) == 2 * (geo(m) * u),
        u > 0,
        u % 2 == 1,
{
    hide(geo);
    lemma_geo_add(m, m);
    lemma_pow_mod4(m);
    lemma_pow_positive(mul_a(), m);
    let p = pow(mul_a(), m);
    let u = (1 + p) / 2;
    assert(1 + p == 2 * u && u % 2 == 1);
    assert(m + m == 2 * m);
    assert(geo(2 * m) == 2 * (geo(m) * u)) by (nonlinear_arith)
        requires
            geo(2 * m) == geo(m) + p * geo(m),
            1 + p == 2 * u,
    ;
    u
}

// (s + X) mod 2^128 == s <==> 2^128 | X
proof fn lemma_shift_fixed(s: int, x: int)
    requires
        0 <= s < m128(),
    ensures
        ((s + x) % m128() == s) == (x % m128() == 0),
{
    lemma_add_mod_noop(s, x, m128());
    lemma_small_mod(s as nat, m128() as nat);
    let r = x % m128();
    lemma_mod_bound(x, m128());
    if s + r < m128() {
        lemma_small_mod((s + r) as nat, m128() as nat);
    } else {
        lemma_fundamental_div_mod_converse(s + r, m128(), 1, s + r - m128());
    }
}

// (A-1)s + c は正の奇数
proof fn lemma_d_odd(s: int, c: int)
    requires
        0 <= s,
        0 <= c,
        c % 2 == 1,
    ensures
        ((mul_a() - 1) * s + c) % 2 == 1,
        (mul_a() - 1) * s + c > 0,
{
    let h = 0x11b0_7682_8fe3_2ed2_21c2_efb2_4fe6_7b22int;
    assert((mul_a() - 1) * s + c == 2 * (h * s) + c) by (nonlinear_arith)
        requires
            mul_a() - 1 == 2 * h,
    ;
    lemma_mod_multiples_vanish(h * s, c, 2);
    assert(h * s >= 0) by (nonlinear_arith)
        requires
            h > 0,
            s >= 0,
    ;
}

// f^[n](s) == s <==> 2^128 | n
pub proof fn lemma_fixed_iff(n: nat, s: int, c: int)
    requires
        0 <= s < m128(),
        0 <= c < m128(),
        c % 2 == 1,
    ensures
        (iter(n, s, c) == s) == (n as int % m128() == 0),
{
    hide(geo);
    let d = (mul_a() - 1) * s + c;
    lemma_d_odd(s, c);
    lemma_iter_closed(n, s, c);
    lemma_shift_fixed(s, geo(n) * d);
    lemma_pow2_128();
    lemma_geo_nonneg(n);
    lemma_odd_factor(128, geo(n), d);
    lemma_geo_v2(128, n);
}

// P2
pub proof fn lemma_state_period(s: int, c: int)
    requires
        0 <= s < m128(),
        0 <= c < m128(),
        c % 2 == 1,
    ensures
        iter(m128() as nat, s, c) == s,
        forall|n: nat| 0 < n < m128() ==> #[trigger] iter(n, s, c) != s,
{
    lemma_fixed_iff(m128() as nat, s, c);
    assert forall|n: nat| 0 < n < m128() implies #[trigger] iter(n, s, c) != s by {
        lemma_fixed_iff(n, s, c);
        lemma_small_mod(n, m128() as nat);
    }
}

// ---- P3: 出力の周期 ----

proof fn lemma_iter_compose(a: nat, b: nat, s: int, c: int)
    ensures
        iter(a + b, s, c) == iter(a, iter(b, s, c), c),
    decreases a,
{
    if a > 0 {
        lemma_iter_compose((a - 1) as nat, b, s, c);
        assert((a + b - 1) as nat == (a - 1) as nat + b);
    }
}

proof fn lemma_iter_range(n: nat, s: int, c: int)
    requires
        0 <= s < m128(),
    ensures
        0 <= iter(n, s, c) < m128(),
{
    if n > 0 {
        lemma_mod_bound(mul_a() * iter((n - 1) as nat, s, c) + c, m128());
    }
}

// 最上位ビットが反転すると出力は必ず変わる
proof fn lemma_out_flip(x: u128)
    ensures
        out(x ^ 0x8000_0000_0000_0000_0000_0000_0000_0000u128) != out(x),
{
    assert(out(x ^ 0x8000_0000_0000_0000_0000_0000_0000_0000u128) != out(x)) by (bit_vector);
}

proof fn lemma_add_half(x: u128)
    ensures
        (x + pow2(127)) % m128() == (x ^ 0x8000_0000_0000_0000_0000_0000_0000_0000u128) as int,
{
    lemma_pow2_128();
    if x < 0x8000_0000_0000_0000_0000_0000_0000_0000u128 {
        assert(x ^ 0x8000_0000_0000_0000_0000_0000_0000_0000u128 == x
            + 0x8000_0000_0000_0000_0000_0000_0000_0000u128) by (bit_vector)
            requires
                x < 0x8000_0000_0000_0000_0000_0000_0000_0000u128,
        ;
        lemma_small_mod((x + pow2(127)) as nat, m128() as nat);
    } else {
        assert(x ^ 0x8000_0000_0000_0000_0000_0000_0000_0000u128 == x
            - 0x8000_0000_0000_0000_0000_0000_0000_0000u128) by (bit_vector)
            requires
                x >= 0x8000_0000_0000_0000_0000_0000_0000_0000u128,
        ;
        lemma_fundamental_div_mod_converse(x + pow2(127), m128(), 1, x - pow2(127));
    }
}

// 2^127 | n かつ 2^128 ∤ n なら f^[n](x) = x + 2^127 mod 2^128
proof fn lemma_iter_half(n: nat, x: int, c: int)
    requires
        0 <= x < m128(),
        0 <= c < m128(),
        c % 2 == 1,
        n as int % (pow2(127) as int) == 0,
        n as int % m128() != 0,
    ensures
        iter(n, x, c) == (x + pow2(127)) % m128(),
{
    hide(geo);
    lemma_pow2_128();
    let d = (mul_a() - 1) * x + c;
    lemma_d_odd(x, c);
    lemma_iter_closed(n, x, c);
    lemma_geo_v2(127, n);
    lemma_geo_v2(128, n);
    let g = geo(n);
    let p = pow2(127) as int;
    lemma_fundamental_div_mod(g, p);
    let w = g / p;
    assert(g == p * w);
    if w % 2 == 0 {
        assert(g == m128() * (w / 2)) by (nonlinear_arith)
            requires
                g == p * w,
                w % 2 == 0,
                p * 2 == m128(),
        ;
        lemma_mod_multiples_basic(w / 2, m128());
        assert(false);
    }
    assert(w % 2 == 1);
    lemma_mul_mod_noop(w, d, 2);
    assert((w * d) % 2 == 1);
    let t = (w * d) / 2;
    assert(g * d == m128() * t + p) by (nonlinear_arith)
        requires
            g == p * w,
            (w * d) % 2 == 1,
            t == (w * d) / 2,
            p * 2 == m128(),
    ;
    assert(x + g * d == m128() * t + (x + p));
    lemma_mod_multiples_vanish(t, x + p, m128());
}

// 2 進付値
spec fn v2(n: nat) -> nat
    decreases n,
{
    if n == 0 || n % 2 == 1 {
        0
    } else {
        1 + v2(n / 2)
    }
}

proof fn lemma_v2(n: nat) -> (u: nat)
    requires
        n > 0,
    ensures
        n == pow2(v2(n)) * u,
        u % 2 == 1,
    decreases n,
{
    lemma2_to64();
    if n % 2 == 1 {
        assert(pow2(v2(n)) == 1);
        assert(n == pow2(v2(n)) * n) by (nonlinear_arith)
            requires
                pow2(v2(n)) == 1,
        ;
        n
    } else {
        let u = lemma_v2(n / 2);
        lemma_pow2_unfold(v2(n));
        assert(n == pow2(v2(n)) * u) by (nonlinear_arith)
            requires
                n / 2 == pow2(v2((n / 2) as nat)) * u,
                pow2(v2(n)) == 2 * pow2(v2((n / 2) as nat)),
                n % 2 == 0,
        ;
        u
    }
}

proof fn lemma_period_mult(s: int, c: int, n: nat, q: nat, k: nat)
    requires
        forall|j: nat| #[trigger] output(s, c, (j + n) as nat) == output(s, c, j),
    ensures
        output(s, c, (k + q * n) as nat) == output(s, c, k),
    decreases q,
{
    if q > 0 {
        let q1 = (q - 1) as nat;
        lemma_period_mult(s, c, n, q1, k);
        assert(q * n == q1 * n + n) by (nonlinear_arith)
            requires
                q1 == q - 1,
        ;
        assert(q1 * n >= 0) by (nonlinear_arith);
        assert(output(s, c, ((k + q1 * n) as nat + n) as nat) == output(s, c, (k + q1 * n) as nat));
        assert(((k + q1 * n) as nat + n) as nat == (k + q * n) as nat);
    } else {
        assert(q * n == 0) by (nonlinear_arith)
            requires
                q == 0,
        ;
    }
}

// n が出力列の周期: ∀k, o_(k+n) = o_k
pub open spec fn has_period(s: int, c: int, n: nat) -> bool {
    forall|k: nat| #[trigger] output(s, c, (k + n) as nat) == output(s, c, k)
}

// P3
pub proof fn lemma_output_period(s: int, c: int)
    requires
        0 <= s < m128(),
        0 <= c < m128(),
        c % 2 == 1,
    ensures
        has_period(s, c, m128() as nat),
        forall|n: nat| 0 < n < m128() ==> !#[trigger] has_period(s, c, n),
{
    lemma_state_period(s, c);
    assert forall|k: nat| #[trigger] output(s, c, (k + m128()) as nat) == output(s, c, k) by {
        lemma_iter_compose(k + 1, m128() as nat, s, c);
        assert((k + m128()) as nat + 1 == k + 1 + m128() as nat);
    }
    assert forall|n: nat| 0 < n < m128() implies !#[trigger] has_period(s, c, n) by {
        if has_period(s, c, n) {
            lemma_pow2_128();
            let u = lemma_v2(n);
            let j = v2(n);
            if j >= 128 {
                if j > 128 {
                    lemma_pow2_strictly_increases(128, j);
                }
                assert(pow2(j) * u >= pow2(j)) by (nonlinear_arith)
                    requires
                        u >= 1,
                ;
                assert(false);
            }
            let q = pow2((127 - j) as nat);
            lemma_pow2_adds((127 - j) as nat, j);
            let big_n = q * n;
            assert(big_n == pow2(127) * u) by (nonlinear_arith)
                requires
                    big_n == q * n,
                    n == pow2(j) * u,
                    pow2(127) == q * pow2(j),
            ;
            lemma_mod_multiples_basic(u as int, pow2(127) as int);
            assert(big_n == (u / 2) as int * m128() + pow2(127)) by (nonlinear_arith)
                requires
                    big_n == pow2(127) * u,
                    u % 2 == 1,
                    pow2(127) * 2 == m128(),
            ;
            lemma_fundamental_div_mod_converse(big_n as int, m128(), (u / 2) as int, pow2(127) as int);
            lemma_period_mult(s, c, n, q, 0);
            let x = iter(1, s, c);
            lemma_iter_range(1, s, c);
            lemma_iter_compose(big_n, 1, s, c);
            lemma_iter_half(big_n, x, c);
            lemma_add_half(x as u128);
            lemma_out_flip(x as u128);
            assert(false);
        }
    }
}

// ---- P4: 一様性 ----

// #{k < 2^128 | o_k = v}
pub open spec fn occ(s: int, c: int, v: u64) -> Set<int> {
    set_int_range(0, m128()).filter(|k: int| output(s, c, k as nat) == v)
}

spec fn preimage(v: u64) -> Set<int> {
    set_int_range(0, m128()).filter(|x: int| out(x as u128) == v)
}

spec fn rotl64(x: u64, r: u64) -> u64 {
    if r == 0 {
        x
    } else {
        (x << r) | (x >> (64 - r) as u64)
    }
}

// 上位 64 ビット h を固定すると下位 64 ビットは一つに決まる
spec fn join(v: u64, h: int) -> int {
    (((h as u64) as u128) << 64u128 | ((rotl64(v, (h as u64) >> 58u64) ^ (h as u64)) as u128)) as int
}

proof fn lemma_out_split(x: u128, v: u64)
    ensures
        (out(x) == v) == (x == ((((x >> 64u128) as u64) as u128) << 64u128 | ((rotl64(
            v,
            ((x >> 64u128) as u64) >> 58u64,
        ) ^ ((x >> 64u128) as u64)) as u128))),
{
    assert((out(x) == v) == (x == ((((x >> 64u128) as u64) as u128) << 64u128 | ((rotl64(
        v,
        ((x >> 64u128) as u64) >> 58u64,
    ) ^ ((x >> 64u128) as u64)) as u128)))) by (bit_vector);
}

proof fn lemma_join_top(h: u64, l: u64)
    ensures
        ((h as u128) << 64u128 | (l as u128)) >> 64u128 == h as u128,
{
    assert(((h as u128) << 64u128 | (l as u128)) >> 64u128 == h as u128) by (bit_vector);
}

proof fn lemma_preimage_len(v: u64)
    ensures
        preimage(v).len() == pow2(64),
{
    lemma_pow2_consts();
    let w = u64::MAX + 1;
    let r = set_int_range(0, w);
    lemma_int_range(0, w);
    lemma_int_range(0, m128());
    let f = |h: int| join(v, h);
    assert(r.injective_on(f)) by {
        assert forall|h1: int, h2: int|
            r.contains(h1) && r.contains(h2) && #[trigger] f(h1) == #[trigger] f(h2) implies h1
            == h2 by {
            let l1 = rotl64(v, (h1 as u64) >> 58u64) ^ (h1 as u64);
            let l2 = rotl64(v, (h2 as u64) >> 58u64) ^ (h2 as u64);
            lemma_join_top(h1 as u64, l1);
            lemma_join_top(h2 as u64, l2);
        }
    }
    assert(r.map(f) =~= preimage(v)) by {
        broadcast use Set::lemma_map_contains, lemma_set_filter;

        assert forall|x: int| r.map(f).contains(x) implies #[trigger] preimage(v).contains(x) by {
            let h = choose|h: int| r.contains(h) && f(h) == x;
            let hu = h as u64;
            let l = rotl64(v, hu >> 58u64) ^ hu;
            let xu = ((hu as u128) << 64u128 | (l as u128));
            lemma_join_top(hu, l);
            lemma_out_split(xu, v);
        }
        assert forall|x: int| #[trigger] preimage(v).contains(x) implies r.map(f).contains(x) by {
            let xu = x as u128;
            let h = ((xu >> 64u128) as u64) as int;
            lemma_out_split(xu, v);
            assert(f(h) == x);
            assert(r.contains(h));
        }
    }
    lemma_map_size(r, preimage(v), f);
}

proof fn lemma_occ_len(s: int, c: int, v: u64)
    requires
        0 <= s < m128(),
        0 <= c < m128(),
        c % 2 == 1,
    ensures
        occ(s, c, v).len() == pow2(64),
{
    broadcast use Set::lemma_map_contains, lemma_set_filter;

    let full = set_int_range(0, m128());
    lemma_int_range(0, m128());
    let phi = |k: int| iter((k + 1) as nat, s, c);
    // k ↦ f^[k+1](s) は [0, 2^128) 上で単射
    assert(full.injective_on(phi)) by {
        assert forall|i: int, j: int|
            full.contains(i) && full.contains(j) && #[trigger] phi(i) == #[trigger] phi(j) implies i
            == j by {
            if i != j {
                let (a, b) = if i < j {
                    (i, j)
                } else {
                    (j, i)
                };
                lemma_iter_compose((b - a) as nat, (a + 1) as nat, s, c);
                assert((b - a) as nat + (a + 1) as nat == (b + 1) as nat);
                lemma_iter_range((a + 1) as nat, s, c);
                lemma_fixed_iff((b - a) as nat, iter((a + 1) as nat, s, c), c);
                lemma_small_mod((b - a) as nat, m128() as nat);
            }
        }
    }
    let img = full.map(phi);
    assert(img.subset_of(full)) by {
        assert forall|x: int| img.contains(x) implies full.contains(x) by {
            let k = choose|k: int| full.contains(k) && phi(k) == x;
            lemma_iter_range((k + 1) as nat, s, c);
        }
    }
    lemma_map_size(full, img, phi);
    lemma_subset_equality(img, full);
    let o = occ(s, c, v);
    lemma_injective_on_filter(full, o, phi);
    assert(o.map(phi) =~= preimage(v)) by {
        assert forall|x: int| o.map(phi).contains(x) implies #[trigger] preimage(v).contains(x) by {
            let k = choose|k: int| o.contains(k) && phi(k) == x;
            lemma_iter_range((k + 1) as nat, s, c);
        }
        assert forall|x: int| #[trigger] preimage(v).contains(x) implies o.map(phi).contains(x) by {
            assert(img.contains(x));
            let k = choose|k: int| full.contains(k) && phi(k) == x;
            assert(o.contains(k));
        }
    }
    lemma_map_size(o, preimage(v), phi);
    lemma_preimage_len(v);
}

proof fn lemma_injective_on_filter(full: Set<int>, o: Set<int>, phi: spec_fn(int) -> int)
    requires
        full.injective_on(phi),
        o.subset_of(full),
    ensures
        o.injective_on(phi),
{
}

// P4
pub proof fn lemma_uniform(s: int, c: int)
    requires
        0 <= s < m128(),
        0 <= c < m128(),
        c % 2 == 1,
    ensures
        forall|v: u64| #[trigger] occ(s, c, v).len() == pow2(64),
{
    assert forall|v: u64| #[trigger] occ(s, c, v).len() == pow2(64) by {
        lemma_occ_len(s, c, v);
    }
}

proof fn lemma_pow2_consts()
    ensures
        pow2(64) == u64::MAX + 1,
        pow2(128) == m128(),
{
    lemma2_to64();
    lemma_pow2_128();
}

} // verus!

impl Pcg64 {
    pub fn next_f32_dense(&mut self) -> f32 {
        u64_to_f32_dense(self.next_u64())
    }
}

const SCALE_TINY: f32 = 1.0 / 18446744073709551616.0;

pub fn u64_to_f32_dense(x: u64) -> f32 {
    let z = x.leading_zeros();
    if z <= 40 {
        f32::from_bits(((126 - z) << 23) | ((x as u32) & 0x7F_FFFF))
    } else {
        ((x as u32) as f32) * SCALE_TINY
    }
}
