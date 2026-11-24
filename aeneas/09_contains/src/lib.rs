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

#[derive(PartialEq)]
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
