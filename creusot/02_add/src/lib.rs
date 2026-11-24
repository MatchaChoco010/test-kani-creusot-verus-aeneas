use creusot_std::prelude::*;

#[requires(a@ + b@ <= u32::MAX@)]
#[ensures(result@ == a@ + b@)]
pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

// 検証失敗: a に制約が無いので add の requires を満たせない
// pub fn double(a: u32) -> u32 {
//     add(a, a)
// }

#[ensures(a@ <= u32::MAX@ / 2 ==> match result { Some(r) => r@ == 2 * a@, None => false })]
#[ensures(a@ > u32::MAX@ / 2 ==> result == None)]
pub fn double_checked(a: u32) -> Option<u32> {
    if a <= u32::MAX / 2 { Some(add(a, a)) } else { None }
}
