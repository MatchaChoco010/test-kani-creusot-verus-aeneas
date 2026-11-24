const MULTIPLIER: u128 = 0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645;

pub struct Pcg64 {
    state: u128,
    increment: u128,
}

impl Pcg64 {
    pub fn new(state: u128, stream: u128) -> Pcg64 {
        let increment = (stream << 1) | 1;
        let mut pcg = Pcg64 { state: state.wrapping_add(increment), increment };
        pcg.step();
        pcg
    }

    fn step(&mut self) {
        self.state = self.state.wrapping_mul(MULTIPLIER).wrapping_add(self.increment);
    }

    pub fn next_u64(&mut self) -> u64 {
        self.step();
        output_xsl_rr(self.state)
    }

    pub fn next_f32_mul(&mut self) -> f32 {
        u64_to_f32_mul(self.next_u64())
    }

    pub fn next_f32_dense(&mut self) -> f32 {
        u64_to_f32_dense(self.next_u64())
    }
}

fn output_xsl_rr(state: u128) -> u64 {
    let rot = (state >> 122) as u32;
    let xsl = ((state >> 64) as u64) ^ (state as u64);
    (xsl >> rot) | (xsl << ((64 - rot) & 63))
}

const SCALE: f32 = 1.0 / 16777216.0;

pub fn u64_to_f32_mul(x: u64) -> f32 {
    ((x >> 40) as f32) * SCALE
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

#[cfg(kani)]
#[kani::proof]
fn check_new() {
    let g = Pcg64::new(kani::any(), kani::any());
    assert!(g.increment % 2 == 1);
}

#[cfg(kani)]
#[kani::proof]
fn check_next_u64() {
    let mut g = Pcg64 { state: kani::any(), increment: kani::any() };
    let inc = g.increment;
    let r = g.next_u64();
    let x = g.state;
    assert!(g.increment == inc);
    assert!(r == (((x >> 64) as u64) ^ (x as u64)).rotate_right((x >> 122) as u32));
}

// 終わらない: 新しい状態 = A·s + c を確かめると 128 ビットの乗算 2 つを比べることになり、58 分たっても終わらなかった
// #[cfg(kani)]
// #[kani::proof]
// fn check_next_u64_state() {
//     let mut g = Pcg64 { state: kani::any(), increment: kani::any() };
//     let (s, inc) = (g.state, g.increment);
//     g.next_u64();
//     assert!(g.state == s.wrapping_mul(MULTIPLIER).wrapping_add(inc));
// }

#[cfg(kani)]
#[kani::proof]
fn check_mul_range() {
    let r = u64_to_f32_mul(kani::any());
    assert!(r.is_finite());
    assert!(0.0 <= r && r < 1.0);
}

#[cfg(kani)]
#[kani::proof]
fn check_dense_range() {
    let r = u64_to_f32_dense(kani::any());
    assert!(r.is_finite());
    assert!(0.0 <= r && r < 1.0);
}

#[cfg(kani)]
#[kani::proof]
fn check_next_f32_mul_range() {
    let mut g = Pcg64 { state: kani::any(), increment: kani::any() };
    let r = g.next_f32_mul();
    assert!(r.is_finite());
    assert!(0.0 <= r && r < 1.0);
}

#[cfg(kani)]
#[kani::proof]
fn check_next_f32_dense_range() {
    let mut g = Pcg64 { state: kani::any(), increment: kani::any() };
    let r = g.next_f32_dense();
    assert!(r.is_finite());
    assert!(0.0 <= r && r < 1.0);
}

#[cfg(kani)]
#[kani::proof]
fn check_mul_grid() {
    let x: u64 = kani::any();
    let r = u64_to_f32_mul(x);
    // r は丸めなしで (x >> 40)·2^-24。2^-24 の倍数でない f32（2^-25 など）は返らない
    assert!(r as f64 == (x >> 40) as f64 / 16777216.0);
}
