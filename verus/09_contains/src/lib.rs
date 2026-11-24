use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {

pub fn contains<T: PartialEq>(v: &[T], x: &T) -> (r: bool)
    requires
        T::obeys_eq_spec(),
    ensures
        r == exists|i: int| 0 <= i < v.len() && v[i].eq_spec(x),
{
    let mut i = 0;
    while i < v.len()
        invariant
            T::obeys_eq_spec(),
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> !v[j].eq_spec(x),
        decreases v.len() - i,
    {
        if v[i] == *x {
            return true;
        }
        i += 1;
    }
    false
}

pub struct Vertex {
    pub x: i32,
    pub y: i32,
}

impl PartialEq for Vertex {
    fn eq(&self, other: &Vertex) -> (r: bool)
        ensures
            r == (self == other),
    {
        self.x == other.x && self.y == other.y
    }
}

// Vertex の == が eq_spec に従うことを vstd に伝える
impl vstd::std_specs::cmp::PartialEqSpecImpl for Vertex {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Vertex) -> bool {
        self == other
    }
}

pub fn contains_vertex(v: &[Vertex], x: &Vertex) -> (r: bool)
    ensures
        r == exists|i: int| #![auto] 0 <= i < v.len() && v[i].x == x.x && v[i].y == x.y,
{
    contains(v, x)
}

pub fn contains_f32(v: &[f32], x: f32) -> bool {
    let mut i = 0;
    while i < v.len()
        decreases v.len() - i,
    {
        if v[i] == x || (v[i] != v[i] && x != x) {
            return true;
        }
        i += 1;
    }
    false
}

// 検証失敗: vstd は f32 の == の結果に意味を与えないため、見つかったかどうかを仕様で表せない
// pub fn contains_f32(v: &[f32], x: f32) -> (r: bool)
//     ensures
//         (exists|i: int| 0 <= i < v.len() && v[i] == x) ==> r,
// {
//     let mut i = 0;
//     while i < v.len()
//         invariant
//             0 <= i <= v.len(),
//             forall|j: int| 0 <= j < i ==> v[j] != x,
//         decreases v.len() - i,
//     {
//         if v[i] == x || (v[i] != v[i] && x != x) {
//             return true;
//         }
//         i += 1;
//     }
//     false
// }

} // verus!
