use crate::model::*;
use vstd::prelude::*;

verus! {

fn not_in_rest(v: &Vec<u64>, i: usize) -> (r: bool)
    requires
        i < v.len(),
    ensures
        r == (forall|j: int| i < j < v.len() ==> v@[i as int] != #[trigger] v@[j]),
{
    let mut j = i + 1;
    while j < v.len()
        invariant
            i < j <= v.len(),
            forall|k: int| i < k < j ==> v@[i as int] != #[trigger] v@[k],
        decreases v.len() - j,
    {
        if v[i] == v[j] {
            return false;
        }
        j += 1;
    }
    true
}

pub open spec fn seq_unique<T>(v: Seq<T>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j]
}

pub(crate) fn unique(v: &Vec<u64>) -> (r: bool)
    ensures
        r == seq_unique(v@),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|a: int, b: int| 0 <= a < i && a < b < v.len() ==> v@[a] != v@[b],
        decreases v.len() - i,
    {
        if !not_in_rest(v, i) {
            return false;
        }
        i += 1;
    }
    true
}

pub(crate) fn all_less(v: &Vec<u64>, n: usize) -> (r: bool)
    ensures
        r == (forall|k: int| 0 <= k < v.len() ==> #[trigger] v@[k] < n),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] v@[k] < n,
        decreases v.len() - i,
    {
        if v[i] >= n as u64 {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn prim(g: GltfS, m: int, p: int) -> PrimitiveS {
    g.meshes[m].primitives[p]
}

pub open spec fn opt_lt(o: Option<u64>, n: int) -> bool {
    match o {
        Some(x) => x < n,
        None => true,
    }
}

pub(crate) fn opt_less(o: Option<u64>, n: usize) -> (r: bool)
    ensures
        r == opt_lt(o, n as int),
{
    match o {
        None => true,
        Some(v) => v < n as u64,
    }
}

pub(crate) fn opt_less_u64(o: Option<u64>, n: u64) -> (r: bool)
    ensures
        r == opt_lt(o, n as int),
{
    match o {
        None => true,
        Some(v) => v < n,
    }
}

fn string_not_in_rest(v: &Vec<Vec<u8>>, i: usize) -> (r: bool)
    requires
        i < v.len(),
    ensures
        r == (forall|j: int| i < j < v.len() ==> strings_view(v@)[i as int] != #[trigger] strings_view(v@)[j]),
{
    let mut j = i + 1;
    while j < v.len()
        invariant
            i < j <= v.len(),
            forall|k: int| i < k < j ==> strings_view(v@)[i as int] != #[trigger] strings_view(v@)[k],
        decreases v.len() - j,
    {
        proof {
            assert(strings_view(v@)[j as int] == v@[j as int]@);
            assert(strings_view(v@)[i as int] == v@[i as int]@);
        }
        if bytes_eq(&v[i], &v[j]) {
            return false;
        }
        j += 1;
    }
    true
}

pub(crate) fn strings_unique(v: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == seq_unique(strings_view(v@)),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|a: int, b: int| 0 <= a < i && a < b < v.len() ==> strings_view(v@)[a] != strings_view(v@)[b],
        decreases v.len() - i,
    {
        if !string_not_in_rest(v, i) {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn seq_contains<T>(v: Seq<T>, x: T) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == x
}

fn strings_contains(v: &Vec<Vec<u8>>, s: &Vec<u8>) -> (r: bool)
    ensures
        r == seq_contains(strings_view(v@), s@),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] strings_view(v@)[k] != s@,
        decreases v.len() - i,
    {
        proof {
            assert(strings_view(v@)[i as int] == v@[i as int]@);
        }
        if bytes_eq(&v[i], s) {
            return true;
        }
        i += 1;
    }
    false
}

pub(crate) fn strings_subset(a: &Vec<Vec<u8>>, b: &Vec<Vec<u8>>) -> (r: bool)
    ensures
        r == (forall|k: int| 0 <= k < a.len() ==> seq_contains(strings_view(b@), #[trigger] strings_view(a@)[k])),
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> seq_contains(strings_view(b@), #[trigger] strings_view(a@)[k]),
        decreases a.len() - i,
    {
        proof {
            assert(strings_view(a@)[i as int] == a@[i as int]@);
        }
        if !strings_contains(b, &a[i]) {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn f32_s(a: Accessor) -> bool {
    a.component_type == 5126
}

pub(crate) fn float32(a: &Accessor) -> (r: bool)
    ensures
        r == f32_s(*a),
{
    a.component_type == 5126
}

pub open spec fn unorm_s(a: Accessor) -> bool {
    a.normalized && (a.component_type == 5121 || a.component_type == 5123)
}

pub(crate) fn unorm8_16(a: &Accessor) -> (r: bool)
    ensures
        r == unorm_s(*a),
{
    a.normalized && (a.component_type == 5121 || a.component_type == 5123)
}

pub open spec fn snorm_s(a: Accessor) -> bool {
    a.normalized && (a.component_type == 5120 || a.component_type == 5122)
}

pub(crate) fn snorm8_16(a: &Accessor) -> (r: bool)
    ensures
        r == snorm_s(*a),
{
    a.normalized && (a.component_type == 5120 || a.component_type == 5122)
}

pub(crate) fn contains(v: &Vec<u64>, x: u64) -> (r: bool)
    ensures
        r == seq_contains(v@, x),
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v@[k] != x,
        decreases v.len() - i,
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

} // verus!
