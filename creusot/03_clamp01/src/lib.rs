use creusot_std::prelude::*;

// pearlite は f32 リテラルを翻訳できない (Unsupported literal)。定数は const 評価を経て翻訳されるので定数で参照する
const ZERO: f32 = 0.0;
const ONE: f32 = 1.0;

#[ensures(x < ZERO ==> result == ZERO)]
#[ensures(x > ONE ==> result == ONE)]
#[ensures(!(x < ZERO) && !(x > ONE) ==> result == x)]
pub fn clamp01(x: f32) -> f32 {
    if x < ZERO {
        ZERO
    } else if x > ONE {
        ONE
    } else {
        x
    }
}
