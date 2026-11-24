use vstd::prelude::*;

verus! {

pub fn add(a: u32, b: u32) -> (r: u32)
    requires
        a + b <= u32::MAX,
    ensures
        r == a + b,
{
    a + b
}

// 検証失敗: a に制約が無いので add の requires を満たせない
// pub fn double(a: u32) -> u32 {
//     add(a, a)
// }

pub fn double_checked(a: u32) -> Option<u32>
    returns
        (if a <= u32::MAX / 2 { Some((2 * a) as u32) } else { None }),
{
    if a <= u32::MAX / 2 { Some(add(a, a)) } else { None }
}

} // verus!
