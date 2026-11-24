use crate::model::*;

fn not_in_rest(v: &Vec<u64>, i: usize) -> bool {
    let mut j = i + 1;
    while j < v.len() {
        if v[i] == v[j] {
            return false;
        }
        j += 1;
    }
    true
}

pub(crate) fn unique(v: &Vec<u64>) -> bool {
    let mut i = 0;
    while i < v.len() {
        if !not_in_rest(v, i) {
            return false;
        }
        i += 1;
    }
    true
}

pub(crate) fn all_less(v: &Vec<u64>, n: usize) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] >= n as u64 {
            return false;
        }
        i += 1;
    }
    true
}

pub(crate) fn opt_less(o: Option<u64>, n: usize) -> bool {
    match o {
        None => true,
        Some(v) => v < n as u64,
    }
}

pub(crate) fn opt_less_u64(o: Option<u64>, n: u64) -> bool {
    match o {
        None => true,
        Some(v) => v < n,
    }
}

fn string_not_in_rest(v: &Vec<Vec<u8>>, i: usize) -> bool {
    let mut j = i + 1;
    while j < v.len() {
        if bytes_eq(&v[i], &v[j]) {
            return false;
        }
        j += 1;
    }
    true
}

pub(crate) fn strings_unique(v: &Vec<Vec<u8>>) -> bool {
    let mut i = 0;
    while i < v.len() {
        if !string_not_in_rest(v, i) {
            return false;
        }
        i += 1;
    }
    true
}

fn strings_contains(v: &Vec<Vec<u8>>, s: &Vec<u8>) -> bool {
    let mut i = 0;
    while i < v.len() {
        if bytes_eq(&v[i], s) {
            return true;
        }
        i += 1;
    }
    false
}

pub(crate) fn strings_subset(a: &Vec<Vec<u8>>, b: &Vec<Vec<u8>>) -> bool {
    let mut i = 0;
    while i < a.len() {
        if !strings_contains(b, &a[i]) {
            return false;
        }
        i += 1;
    }
    true
}

pub(crate) fn float32(a: &Accessor) -> bool {
    a.component_type == 5126
}

pub(crate) fn unorm8_16(a: &Accessor) -> bool {
    a.normalized && (a.component_type == 5121 || a.component_type == 5123)
}

pub(crate) fn snorm8_16(a: &Accessor) -> bool {
    a.normalized && (a.component_type == 5120 || a.component_type == 5122)
}

pub(crate) fn contains(v: &Vec<u64>, x: u64) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}
