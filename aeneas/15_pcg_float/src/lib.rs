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
