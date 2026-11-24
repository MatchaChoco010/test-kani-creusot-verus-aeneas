pub fn contains<T: PartialEq>(v: &[T], x: &T) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] == *x {
            return true;
        }
        i += 1;
    }
    false
}

#[derive(PartialEq, Clone, Copy)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Vertex {
    pub x: i32,
    pub y: i32,
}

pub fn contains_vertex(v: &[Vertex], x: &Vertex) -> bool {
    contains(v, x)
}

pub fn contains_f32(v: &[f32], x: f32) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] == x || (v[i] != v[i] && x != x) {
            return true;
        }
        i += 1;
    }
    false
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(4)]
fn check_contains_vertex() {
    let arr: [Vertex; 3] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let x: Vertex = kani::any();
    let expected = v.iter().any(|y| y.x == x.x && y.y == x.y);
    assert_eq!(contains_vertex(v, &x), expected);
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(4)]
fn check_contains_f32() {
    let arr: [f32; 3] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let x: f32 = kani::any();
    let expected = v.iter().any(|&y| y == x || (y.is_nan() && x.is_nan()));
    assert_eq!(contains_f32(v, x), expected);
}

// 検証失敗: NaN == NaN は偽なので、ジェネリックな contains では配列にある NaN が見つからない
// #[cfg(kani)]
// #[kani::proof]
// #[kani::unwind(4)]
// fn check_contains_generic_f32() {
//     let arr: [f32; 3] = kani::any();
//     let i: usize = kani::any();
//     kani::assume(i < 3);
//     assert!(contains(&arr, &arr[i]));
// }
