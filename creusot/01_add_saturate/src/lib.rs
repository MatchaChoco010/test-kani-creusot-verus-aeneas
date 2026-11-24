use creusot_std::prelude::*;

#[ensures(a@ + b@ <= u32::MAX@ ==> result@ == a@ + b@)]
#[ensures(a@ + b@ > u32::MAX@ ==> result@ == u32::MAX@)]
pub fn add_saturate(a: u32, b: u32) -> u32 {
    if a > u32::MAX - b { u32::MAX } else { a + b }
}
