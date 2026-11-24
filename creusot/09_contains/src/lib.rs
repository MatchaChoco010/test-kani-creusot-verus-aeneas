use creusot_std::{prelude::*, std::cmp::PartialEq};

#[ensures(result == exists<i> 0 <= i && i < v@.len() && v@[i].deep_model() == x.deep_model())]
pub fn contains<T: PartialEq + DeepModel>(v: &[T], x: &T) -> bool {
    let mut i = 0;
    #[invariant(forall<j> 0 <= j && j < i@ ==> v@[j].deep_model() != x.deep_model())]
    while i < v.len() {
        if v[i] == *x {
            return true;
        }
        i += 1;
    }
    false
}

#[derive(PartialEq)]
pub struct Vertex {
    pub x: i32,
    pub y: i32,
}

// == の仕様は deep_model の等しさで与えられる。#[derive(DeepModel)] は通常ビルドで impl を生成しないため手で書く
impl DeepModel for Vertex {
    type DeepModelTy = (i32, i32);

    #[logic(open)]
    fn deep_model(self) -> Self::DeepModelTy {
        (self.x, self.y)
    }
}

#[ensures(result == exists<i> 0 <= i && i < v@.len() && v@[i].x == x.x && v@[i].y == x.y)]
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

// 書けない: NaN の特殊処理の振る舞いを仕様に書くには f32::is_nan と f32 の IEEE の == が要るが、creusot-std はこれらを仕様に提供しておらず、
// "called program function `core::f32::<impl f32>::is_nan` in logic context" でコンパイルできない (仕様の == は論理的な等しさで IEEE の == ではない)
// #[ensures(result == exists<i> 0 <= i && i < v@.len() && (v@[i] == x || (v@[i].is_nan() && x.is_nan())))]
// pub fn contains_f32_spec(v: &[f32], x: f32) -> bool {
//     let mut i = 0;
//     #[invariant(forall<j> 0 <= j && j < i@ ==> !(v@[j] == x || (v@[j].is_nan() && x.is_nan())))]
//     while i < v.len() {
//         if v[i] == x || (v[i] != v[i] && x != x) {
//             return true;
//         }
//         i += 1;
//     }
//     false
// }
