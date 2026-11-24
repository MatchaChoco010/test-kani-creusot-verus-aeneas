use crate::json::*;
use crate::json::number::*;
use crate::model::*;
use vstd::prelude::*;

verus! {

// ---- JSON アリーナの取得関数（R 節の lookup などに対応） ----
pub open spec fn key_last(o: Seq<Member>, k: Seq<u8>, i: int) -> bool {
    0 <= i < o.len() && o[i].key@ == k && forall|j: int| i < j < o.len() ==> #[trigger] o[j].key@ != k
}

pub fn is_last_member(obj: &Vec<Member>, i: usize) -> (r: bool)
    requires
        i < obj.len(),
    ensures
        r == key_last(obj@, obj@[i as int].key@, i as int),
{
    match find_member(obj, &obj[i].key) {
        None => false,
        Some(k) => k == i,
    }
}

pub fn find_member(obj: &Vec<Member>, key: &[u8]) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => key_last(obj@, key@, i as int),
            None => forall|j: int| 0 <= j < obj.len() ==> #[trigger] obj@[j].key@ != key@,
        },
{
    let mut found: Option<usize> = None;
    let mut i = 0;
    while i < obj.len()
        invariant
            0 <= i <= obj.len(),
            match found {
                Some(f) => f < i && obj@[f as int].key@ == key@ && forall|j: int| f < j < i ==> #[trigger] obj@[j].key@ != key@,
                None => forall|j: int| 0 <= j < i ==> #[trigger] obj@[j].key@ != key@,
            },
        decreases obj.len() - i,
    {
        if bytes_eq(&obj[i].key, key) {
            found = Some(i);
        }
        i += 1;
    }
    found
}

// obj の値の添字がすべて d の範囲内
pub open spec fn obj_in(d: Seq<JsonNode>, o: Seq<Member>) -> bool {
    forall|k: int| 0 <= k < o.len() ==> #[trigger] o[k].value < d.len()
}

pub open spec fn arr_in(d: Seq<JsonNode>, a: Seq<usize>) -> bool {
    forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k] < d.len()
}

// ノードの中身から見た木（子の添字が親より小さい文書では tree(d, x) と一致）
pub open spec fn node_tree(d: Seq<JsonNode>, n: JsonNode) -> JsonS {
    match n {
        JsonNode::Array(a) => JsonS::Array(trees(d, a@)),
        JsonNode::Object(m) => JsonS::Object(member_trees(d, m@)),
        _ => node_scalar(n),
    }
}

pub open spec fn node_in(d: Seq<JsonNode>, n: JsonNode) -> bool {
    match n {
        JsonNode::Array(a) => arr_in(d, a@),
        JsonNode::Object(m) => obj_in(d, m@),
        _ => true,
    }
}

pub proof fn lemma_node_tree(d: Seq<JsonNode>, x: int)
    requires
        children_lt(d),
        0 <= x < d.len(),
    ensures
        tree(d, x) == node_tree(d, d[x]),
        node_in(d, d[x]),
{
    match d[x] {
        JsonNode::Array(a) => {
            assert(tree(d, x)->Array_0 =~= trees(d, a@));
        },
        JsonNode::Object(m) => {
            assert(tree(d, x)->Object_0 =~= member_trees(d, m@));
        },
        _ => {},
    }
}

pub fn node_at(d: &Vec<JsonNode>, id: usize) -> (r: Option<&JsonNode>)
    ensures
        match r {
            Some(n) => id < d.len() && *n == d@[id as int],
            None => id >= d.len(),
        },
        r matches Some(n) ==> (children_lt(d@) ==> tree(d@, id as int) == node_tree(d@, *n) && node_in(d@, *n)) && (
        numbers_wf(d@) ==> scalar_wf(*n)),
{
    if id < d.len() {
        proof {
            if children_lt(d@) {
                lemma_node_tree(d@, id as int);
            }
            if numbers_wf(d@) {
                assert(match d@[id as int] {
                    JsonNode::Number(x) => number_wf(x@),
                    _ => true,
                });
            }
        }
        Some(&d[id])
    } else {
        None
    }
}

pub open spec fn mt(d: Seq<JsonNode>, o: Seq<Member>) -> Ms {
    member_trees(d, o)
}

pub proof fn lemma_lookup(d: Seq<JsonNode>, o: Seq<Member>, k: Seq<u8>)
    ensures
        (forall|j: int| 0 <= j < o.len() ==> #[trigger] o[j].key@ != k) ==> lookup(mt(d, o), k) is None,
        forall|i: int| #[trigger] key_last(o, k, i) ==> lookup(mt(d, o), k) == Some(tree(d, o[i].value as int)),
{
    let m = mt(d, o);
    assert forall|i: int| #[trigger] key_last(o, k, i) implies lookup(mt(d, o), k) == Some(tree(d, o[i].value as int)) by {
        assert(m[i].0 == k);
        assert(last_key_at(m, k, i));
        let i2 = choose|i2: int| last_key_at(m, k, i2);
        if i2 < i {
            assert(m[i].0 == o[i].key@);
        } else if i < i2 {
            assert(m[i2].0 == o[i2].key@);
            assert(o[i2].key@ == k);
        }
    }
    if forall|j: int| 0 <= j < o.len() ==> #[trigger] o[j].key@ != k {
        assert forall|j: int| 0 <= j < m.len() implies m[j].0 != k by {
            assert(m[j].0 == o[j].key@);
        }
    }
}

// 取得関数の前提: 子の添字が親より小さく、obj の値が範囲内
pub open spec fn ctx(d: Seq<JsonNode>, o: Seq<Member>) -> bool {
    children_lt(d) && obj_in(d, o)
}

pub type Ms = Seq<(Seq<u8>, JsonS)>;

// lookup(o, k): キー k を持つ最後のメンバーの値
pub open spec fn last_key_at(o: Ms, k: Seq<u8>, i: int) -> bool {
    0 <= i < o.len() && o[i].0 == k && forall|j: int| i < j < o.len() ==> o[j].0 != k
}

pub open spec fn lookup(o: Ms, k: Seq<u8>) -> Option<JsonS> {
    if exists|i: int| 0 <= i < o.len() && o[i].0 == k {
        Some(o[choose|i: int| last_key_at(o, k, i)].1)
    } else {
        None
    }
}

fn member_node<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<&'a JsonNode>, ()>)
    ensures
        r matches Ok(Some(n)) ==> (numbers_wf(d@) ==> scalar_wf(*n)),
        ctx(d@, obj@) ==> match r {
            Ok(None) => lookup(mt(d@, obj@), key@) is None,
            Ok(Some(n)) => lookup(mt(d@, obj@), key@) == Some(node_tree(d@, *n)) && node_in(d@, *n),
            Err(_) => false,
        },
{
    proof {
        lemma_lookup(d@, obj@, key@);
    }
    match find_member(obj, key) {
        None => Ok(None),
        Some(i) => match node_at(d, obj[i].value) {
            None => Err(()),
            Some(n) => Ok(Some(n)),
        },
    }
}

pub open spec fn uint_val(v: JsonS) -> Option<u64> {
    match v {
        JsonS::Number(n) => num_u64(n),
        _ => None,
    }
}

// 以下の取得関数は外側の None がエラー、Some(None) が省略
// MUST-013: インデックスは 0 以上の整数
pub open spec fn get_uint_s(o: Ms, k: Seq<u8>) -> Option<Option<u64>> {
    match lookup(o, k) {
        None => Some(None),
        Some(v) => match uint_val(v) {
            Some(x) => Some(Some(x)),
            None => None,
        },
    }
}

// MUST-013: インデックスは 0 以上の整数
pub fn get_uint(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<u64>, ()>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(v) => get_uint_s(mt(d@, obj@), key@) == Some(v),
            Err(_) => get_uint_s(mt(d@, obj@), key@) is None,
        },
{
    proof {
        lemma_num_u64_all();
    }
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Number(n))) => match number_to_u64(n) {
            Some(v) => Ok(Some(v)),
            None => Err(()),
        },
        Ok(Some(_)) => Err(()),
    }
}

pub open spec fn get_bool_s(o: Ms, k: Seq<u8>) -> Option<Option<bool>> {
    match lookup(o, k) {
        None => Some(None),
        Some(JsonS::Bool(b)) => Some(Some(b)),
        Some(_) => None,
    }
}

pub fn get_bool(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<bool>, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(v) => get_bool_s(mt(d@, obj@), key@) == Some(v),
            Err(_) => get_bool_s(mt(d@, obj@), key@) is None,
        },
{
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Bool(b))) => Ok(Some(*b)),
        Ok(Some(_)) => Err(()),
    }
}

fn copy_bytes(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            out@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        out.push(v[i]);
        i += 1;
        assert(out@ =~= v@.subrange(0, i as int));
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    out
}

pub open spec fn get_string_s(o: Ms, k: Seq<u8>) -> Option<Option<Seq<u8>>> {
    match lookup(o, k) {
        None => Some(None),
        Some(JsonS::String(s)) => Some(Some(s)),
        Some(_) => None,
    }
}

pub fn get_string(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<Vec<u8>>, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(v) => get_string_s(mt(d@, obj@), key@) == Some(bytes_opt_view(v)),
            Err(_) => get_string_s(mt(d@, obj@), key@) is None,
        },
{
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::String(s))) => Ok(Some(copy_bytes(s))),
        Ok(Some(_)) => Err(()),
    }
}

pub open spec fn get_object_s(o: Ms, k: Seq<u8>) -> Option<Option<Ms>> {
    match lookup(o, k) {
        None => Some(None),
        Some(JsonS::Object(m)) => Some(Some(m)),
        Some(_) => None,
    }
}

pub fn get_object<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<&'a Vec<Member>>, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(None) => get_object_s(mt(d@, obj@), key@) == Some(None::<Ms>),
            Ok(Some(m)) => get_object_s(mt(d@, obj@), key@) == Some(Some(mt(d@, m@))) && obj_in(d@, m@),
            Err(_) => get_object_s(mt(d@, obj@), key@) is None,
        },
{
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Object(m))) => Ok(Some(m)),
        Ok(Some(_)) => Err(()),
    }
}

// "array" は 1 要素以上
pub open spec fn get_array_s(o: Ms, k: Seq<u8>) -> Option<Option<Seq<JsonS>>> {
    match lookup(o, k) {
        None => Some(None),
        Some(JsonS::Array(a)) => if a.len() > 0 {
            Some(Some(a))
        } else {
            None
        },
        Some(_) => None,
    }
}

pub fn get_array<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<&'a Vec<usize>>, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(None) => get_array_s(mt(d@, obj@), key@) == Some(None::<Seq<JsonS>>),
            Ok(Some(a)) => get_array_s(mt(d@, obj@), key@) == Some(Some(trees(d@, a@))) && arr_in(d@, a@),
            Err(_) => get_array_s(mt(d@, obj@), key@) is None,
        },
{
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Array(a))) => {
            if a.len() == 0 {
                Err(())
            } else {
                Ok(Some(a))
            }
        }
        Ok(Some(_)) => Err(()),
    }
}

pub proof fn lemma_trees_index(d: Seq<JsonNode>, a: Seq<usize>, i: int)
    requires
        children_lt(d),
        arr_in(d, a),
        0 <= i < a.len(),
    ensures
        trees(d, a)[i] == node_tree(d, d[a[i] as int]),
        node_in(d, d[a[i] as int]),
{
    lemma_node_tree(d, a[i] as int);
}

pub open spec fn uints_s(a: Seq<JsonS>) -> Option<Seq<u64>> {
    if forall|i: int| 0 <= i < a.len() ==> (#[trigger] uint_val(a[i])) is Some {
        Some(Seq::new(a.len(), |i: int| uint_val(a[i])->Some_0))
    } else {
        None
    }
}

fn uints_of(d: &Vec<JsonNode>, a: &Vec<usize>) -> (r: Option<Vec<u64>>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Some(v) => uints_s(trees(d@, a@)) == Some(v@),
            None => uints_s(trees(d@, a@)) is None,
        },
{
    let ghost t = trees(d@, a@);
    let mut out: Vec<u64> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            numbers_wf(d@),
            t == trees(d@, a@),
            0 <= i <= a.len(),
            out@.len() == i,
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> (#[trigger] uint_val(t[k])) == Some(out@[k]),
        decreases a.len() - i,
    {
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_trees_index(d@, a@, i as int);
            }
        }
        proof {
            lemma_num_u64_all();
            if children_lt(d@) && arr_in(d@, a@) {
                assert(uint_val(t[i as int]) == uint_val(node_tree(d@, d@[a@[i as int] as int])));
            }
        }
        match node_at(d, a[i]) {
            Some(JsonNode::Number(n)) => match number_to_u64(n) {
                Some(v) => out.push(v),
                None => return None,
            },
            _ => return None,
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            assert(Seq::new(t.len(), |k: int| uint_val(t[k])->Some_0) =~= out@);
        }
    }
    Some(out)
}

pub open spec fn get_uint_array_s(o: Ms, k: Seq<u8>) -> Option<Option<Seq<u64>>> {
    match get_array_s(o, k) {
        None => None,
        Some(None) => Some(None),
        Some(Some(a)) => match uints_s(a) {
            Some(v) => Some(Some(v)),
            None => None,
        },
    }
}

pub fn get_uint_array(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<Vec<u64>>, ()>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(None) => get_uint_array_s(mt(d@, obj@), key@) == Some(None::<Seq<u64>>),
            Ok(Some(v)) => get_uint_array_s(mt(d@, obj@), key@) == Some(Some(v@)),
            Err(_) => get_uint_array_s(mt(d@, obj@), key@) is None,
        },
{
    match get_array(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(a)) => match uints_of(d, a) {
            None => Err(()),
            Some(v) => Ok(Some(v)),
        },
    }
}

fn all_numbers(d: &Vec<JsonNode>, a: &Vec<usize>) -> (r: bool)
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> r == (forall|i: int| 0 <= i < a.len() ==> (#[trigger] trees(d@, a@)[i]) is Number),
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> (#[trigger] trees(d@, a@)[k]) is Number,
        decreases a.len() - i,
    {
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_trees_index(d@, a@, i as int);
            }
        }
        match node_at(d, a[i]) {
            Some(JsonNode::Number(_)) => {}
            _ => return false,
        }
        i += 1;
    }
    true
}

pub open spec fn get_number_array_len_s(o: Ms, k: Seq<u8>) -> Option<Option<u64>> {
    match get_array_s(o, k) {
        None => None,
        Some(None) => Some(None),
        Some(Some(a)) => if forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]) is Number {
            Some(Some(a.len() as u64))
        } else {
            None
        },
    }
}

pub fn get_number_array_len(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<Option<u64>, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(v) => get_number_array_len_s(mt(d@, obj@), key@) == Some(v),
            Err(_) => get_number_array_len_s(mt(d@, obj@), key@) is None,
        },
{
    match get_array(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(a)) => {
            if all_numbers(d, a) {
                Ok(Some(a.len() as u64))
            } else {
                Err(())
            }
        }
    }
}

// "number"（値は解釈しない）
pub open spec fn check_number_s(o: Ms, k: Seq<u8>) -> Option<bool> {
    match lookup(o, k) {
        None => Some(false),
        Some(JsonS::Number(_)) => Some(true),
        Some(_) => None,
    }
}

pub fn check_number(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> (r: Result<bool, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(b) => check_number_s(mt(d@, obj@), key@) == Some(b),
            Err(_) => check_number_s(mt(d@, obj@), key@) is None,
        },
{
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(JsonNode::Number(_))) => Ok(true),
        Ok(Some(_)) => Err(()),
    }
}

// ちょうど n 個の数の配列
pub open spec fn check_number_array_s(o: Ms, k: Seq<u8>, n: u64) -> Option<bool> {
    match get_number_array_len_s(o, k) {
        None => None,
        Some(None) => Some(false),
        Some(Some(m)) => if m == n {
            Some(true)
        } else {
            None
        },
    }
}

pub fn check_number_array(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8], len: u64) -> (r: Result<bool, ()>)
    ensures
        ctx(d@, obj@) ==> match r {
            Ok(b) => check_number_array_s(mt(d@, obj@), key@, len) == Some(b),
            Err(_) => check_number_array_s(mt(d@, obj@), key@, len) is None,
        },
{
    match get_number_array_len(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(n)) => {
            if n == len {
                Ok(true)
            } else {
                Err(())
            }
        }
    }
}

pub fn as_object(d: &Vec<JsonNode>, id: usize) -> (r: Result<&Vec<Member>, ()>)
    ensures
        children_lt(d@) ==> match r {
            Ok(m) => tree(d@, id as int) == JsonS::Object(mt(d@, m@)) && obj_in(d@, m@),
            Err(_) => !(tree(d@, id as int) is Object),
        },
{
    proof {
        if children_lt(d@) && id < d.len() {
            lemma_node_tree(d@, id as int);
        }
    }
    match node_at(d, id) {
        Some(JsonNode::Object(m)) => Ok(m),
        _ => Err(()),
    }
}

// ext の内容（集合）
pub open spec fn ext_set(v: Seq<Vec<u8>>) -> ISet<Seq<u8>> {
    seq_iset(strings_view(v))
}

pub open spec fn ext_grow(a: Seq<Vec<u8>>, b: Seq<Vec<u8>>, e: Ext) -> bool {
    forall|x: Seq<u8>| #[trigger] ext_set(b).contains(x) == (ext_set(a).contains(x) || e.contains(x))
}

pub type Ext = ISet<Seq<u8>>;

// 後のメンバーに上書きされないメンバー
pub open spec fn not_overridden(o: Ms, i: int) -> bool {
    last_key_at(o, o[i].0, i)
}

pub open spec fn k_extensions() -> Seq<u8> {
    seq![b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's']
}

// extensions: オブジェクトで、上書きされないメンバーの値はすべてオブジェクト。そのキーの集合
pub open spec fn ext_s(o: Ms) -> Option<Ext> {
    match get_object_s(o, k_extensions()) {
        None => None,
        Some(None) => Some(ISet::empty()),
        Some(Some(e)) => if forall|i: int| 0 <= i < e.len() && #[trigger] not_overridden(e, i) ==> e[i].1 is Object {
            Some(ISet::new(|x: Seq<u8>| exists|i: int| 0 <= i < e.len() && #[trigger] not_overridden(e, i) && e[i].0 == x))
        } else {
            None
        },
    }
}

pub(crate) fn check_extensions(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<(), ()>)
    ensures
        ctx(d@, o@) ==> match r {
            Ok(_) => (ext_s(mt(d@, o@)) matches Some(e) && ext_grow(old(ext)@, final(ext)@, e)),
            Err(_) => ext_s(mt(d@, o@)) is None,
        },
{
    match get_object(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's']) {
        Err(()) => Err(()),
        Ok(None) => Ok(()),
        Ok(Some(e)) => collect_extension_names(d, e, ext),
    }
}

pub proof fn lemma_last_key(d: Seq<JsonNode>, o: Seq<Member>, i: int)
    requires
        0 <= i < o.len(),
    ensures
        key_last(o, o[i].key@, i) == not_overridden(mt(d, o), i),
{
    let m = mt(d, o);
    let k = o[i].key@;
    assert(m[i].0 == k);
    if key_last(o, k, i) {
        assert forall|j: int| i < j < m.len() implies m[j].0 != k by {
            assert(m[j].0 == o[j].key@);
        }
    }
    if not_overridden(m, i) {
        assert forall|j: int| i < j < o.len() implies #[trigger] o[j].key@ != k by {
            assert(m[j].0 == o[j].key@);
        }
    }
}

pub proof fn lemma_ext_push(eb: Seq<Vec<u8>>, ea: Seq<Vec<u8>>, key: Seq<u8>)
    requires
        ea.len() == eb.len() + 1,
        forall|k: int| 0 <= k < eb.len() ==> #[trigger] ea[k] == eb[k],
        ea[eb.len() as int]@ == key,
    ensures
        forall|x: Seq<u8>| #[trigger] ext_set(ea).contains(x) == (ext_set(eb).contains(x) || x == key),
{
    let sa = strings_view(ea);
    let sb = strings_view(eb);
    assert forall|x: Seq<u8>| #[trigger] ext_set(ea).contains(x) == (ext_set(eb).contains(x) || x == key) by {
        assert(ext_set(ea).contains(x) == sa.contains(x));
        assert(ext_set(eb).contains(x) == sb.contains(x));
        if sa.contains(x) {
            let k = sa.index_of(x);
            if k < sb.len() {
                assert(sa[k] == ea[k]@);
                assert(sb[k] == x);
            } else {
                assert(sa[k] == ea[k]@);
            }
        }
        if sb.contains(x) {
            let k = sb.index_of(x);
            assert(sa[k] == ea[k]@);
            assert(sa[k] == x);
        }
        if x == key {
            assert(sa[sb.len() as int] == x);
        }
    }
}

pub proof fn lemma_ext_push_step(d: Seq<JsonNode>, e: Seq<Member>, i: int, e0: Seq<Vec<u8>>, eb: Seq<Vec<u8>>, ea: Seq<Vec<u8>>)
    requires
        ctx(d, e),
        0 <= i < e.len(),
        forall|x: Seq<u8>| #[trigger] ext_set(eb).contains(x) == (ext_set(e0).contains(x) || exists|k: int| 0 <= k < i && #[trigger] not_overridden(mt(d, e), k) && mt(d, e)[k].0 == x),
        (ea == eb && !not_overridden(mt(d, e), i)) || (not_overridden(mt(d, e), i) && ea.len() == eb.len() + 1 && (forall|k: int| 0 <= k < eb.len() ==> #[trigger] ea[k] == eb[k]) && ea[eb.len() as int]@ == mt(d, e)[i].0),
    ensures
        forall|x: Seq<u8>| #[trigger] ext_set(ea).contains(x) == (ext_set(e0).contains(x) || exists|k: int| 0 <= k < i + 1 && #[trigger] not_overridden(mt(d, e), k) && mt(d, e)[k].0 == x),
{
    let m = mt(d, e);
    if ea != eb {
        lemma_ext_push(eb, ea, m[i].0);
    }
    assert forall|x: Seq<u8>| #[trigger] ext_set(ea).contains(x) == (ext_set(e0).contains(x) || exists|k: int| 0 <= k < i + 1 && #[trigger] not_overridden(m, k) && m[k].0 == x) by {
        let p0 = exists|k: int| 0 <= k < i && #[trigger] not_overridden(m, k) && m[k].0 == x;
        let p1 = exists|k: int| 0 <= k < i + 1 && #[trigger] not_overridden(m, k) && m[k].0 == x;
        if p1 {
            let k = choose|k: int| 0 <= k < i + 1 && #[trigger] not_overridden(m, k) && m[k].0 == x;
            if k < i {
                assert(p0);
            }
        }
        if p0 {
            let k = choose|k: int| 0 <= k < i && #[trigger] not_overridden(m, k) && m[k].0 == x;
            assert(0 <= k < i + 1);
        }
        if not_overridden(m, i) && m[i].0 == x {
            assert(p1);
        }
    }
}

fn collect_extension_names(d: &Vec<JsonNode>, e: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<(), ()>)
    ensures
        ctx(d@, e@) ==> match r {
            Ok(_) => (forall|i: int| 0 <= i < e.len() && #[trigger] not_overridden(mt(d@, e@), i) ==> mt(d@, e@)[i].1 is Object)
                && forall|x: Seq<u8>| #[trigger] ext_set(final(ext)@).contains(x) == (ext_set(old(ext)@).contains(x) || exists|i: int|
                0 <= i < e.len() && #[trigger] not_overridden(mt(d@, e@), i) && mt(d@, e@)[i].0 == x),
            Err(_) => !(forall|i: int| 0 <= i < e.len() && #[trigger] not_overridden(mt(d@, e@), i) ==> mt(d@, e@)[i].1 is Object),
        },
{
    let ghost e0 = ext@;
    let mut i = 0;
    while i < e.len()
        invariant
            e0 == old(ext)@,
            0 <= i <= e.len(),
            ctx(d@, e@) ==> forall|k: int| 0 <= k < i && #[trigger] not_overridden(mt(d@, e@), k) ==> mt(d@, e@)[k].1 is Object,
            ctx(d@, e@) ==> forall|x: Seq<u8>| #[trigger] ext_set(ext@).contains(x) == (ext_set(e0).contains(x) || exists|k: int| 0 <= k < i && #[trigger] not_overridden(mt(d@, e@), k) && mt(d@, e@)[k].0 == x),
        decreases e.len() - i,
    {
        let ghost eb = ext@;
        proof {
            lemma_last_key(d@, e@, i as int);
            if ctx(d@, e@) {
                lemma_node_tree(d@, e@[i as int].value as int);
            }
        }
        if is_last_member(e, i) {
            match node_at(d, e[i].value) {
                Some(JsonNode::Object(_)) => ext.push(copy_key(&e[i].key)),
                _ => return Err(()),
            }
        }
        proof {
            if ctx(d@, e@) {
                lemma_ext_push_step(d@, e@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    Ok(())
}

// glTFChildOfRootProperty: name は文字列
pub open spec fn child_s(o: Ms) -> Option<Ext> {
    if get_string_s(o, seq![b'n', b'a', b'm', b'e']) is Some {
        ext_s(o)
    } else {
        None
    }
}

pub(crate) fn check_child_of_root(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<(), ()>)
    ensures
        ctx(d@, o@) ==> match r {
            Ok(_) => (child_s(mt(d@, o@)) matches Some(e) && ext_grow(old(ext)@, final(ext)@, e)),
            Err(_) => child_s(mt(d@, o@)) is None,
        },
{
    match get_string(d, o, &[b'n', b'a', b'm', b'e']) {
        Err(()) => return Err(()),
        Ok(_) => {}
    }
    check_extensions(d, o, ext)
}

pub open spec fn req_uint_s(o: Ms, k: Seq<u8>) -> Option<u64> {
    match get_uint_s(o, k) {
        Some(Some(x)) => Some(x),
        _ => None,
    }
}

pub(crate) fn req_uint(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8]) -> (r: Result<u64, ()>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => req_uint_s(mt(d@, o@), key@) == Some(v),
            Err(_) => req_uint_s(mt(d@, o@), key@) is None,
        },
{
    match get_uint(d, o, key) {
        Ok(Some(v)) => Ok(v),
        _ => Err(()),
    }
}

pub(crate) fn copy_key(v: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == v@,
{
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            out@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        out.push(v[i]);
        i += 1;
        assert(out@ =~= v@.subrange(0, i as int));
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    out
}

} // verus!
