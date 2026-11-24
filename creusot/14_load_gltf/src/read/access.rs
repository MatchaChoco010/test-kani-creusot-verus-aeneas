use creusot_std::prelude::*;
use crate::json::*;
use crate::json::number::*;
use crate::model::*;

#[requires(i@ < obj@.len())]
#[ensures(result == forall<t> i@ < t && t < obj@.len() ==> obj@[t].key@ != obj@[i@].key@)]
#[check(terminates)]
pub fn is_last_member(obj: &Vec<Member>, i: usize) -> bool {
    match find_member(obj, &obj[i].key) {
        None => false,
        Some(k) => k == i,
    }
}

// n 番目より前で、キーが k である最後のメンバーの位置
#[logic(open)]
#[variant(n)]
pub fn last_key(o: JObj, k: Seq<u8>, n: Int) -> Option<Int> {
    pearlite! {
        if n <= 0 { None } else if okey(o, n - 1) == k { Some(n - 1) } else { last_key(o, k, n - 1) }
    }
}

// lookup(o, k): キーが k である最後のメンバーの値
#[logic(open)]
pub fn lookup(o: JObj, k: Seq<u8>) -> Option<JsonS> {
    pearlite! {
        match last_key(o, k, olen(o)) {
            None => None,
            Some(i) => Some(oval(o, i)),
        }
    }
}

// i 番目のメンバーは、後のメンバーに上書きされていない
#[logic(open)]
pub fn is_last(o: JObj, i: Int) -> bool {
    pearlite! { forall<t> i < t && t < olen(o) ==> okey(o, t) != okey(o, i) }
}

// i はキー k の最後のメンバー
#[logic(open)]
pub fn last_of(ms: Seq<Member>, i: Int, k: Seq<u8>) -> bool {
    pearlite! { 0 <= i && i < ms.len() && ms[i].key@ == k && forall<t> i < t && t < ms.len() ==> ms[t].key@ != k }
}

#[logic(open)]
pub fn no_key(ms: Seq<Member>, k: Seq<u8>) -> bool {
    pearlite! { forall<t> 0 <= t && t < ms.len() ==> ms[t].key@ != k }
}

#[logic(opaque)]
#[variant(n)]
#[requires(0 <= n)]
#[ensures(match last_key(o, k, n) {
    None => forall<t> 0 <= t && t < n ==> okey(o, t) != k,
    Some(i) => 0 <= i && i < n && okey(o, i) == k && forall<t> i < t && t < n ==> okey(o, t) != k,
})]
pub fn lemma_last_key(o: JObj, k: Seq<u8>, n: Int) {
    if n > 0 {
        lemma_last_key(o, k, n - 1)
    }
}

// lookup の特徴づけ
#[logic(opaque)]
#[ensures(lookup(o, k) == None ==> forall<t> 0 <= t && t < olen(o) ==> okey(o, t) != k)]
#[ensures((forall<t> 0 <= t && t < olen(o) ==> okey(o, t) != k) ==> lookup(o, k) == None)]
#[ensures(forall<i> 0 <= i && i < olen(o) && okey(o, i) == k && is_last(o, i) ==> lookup(o, k) == Some(oval(o, i)))]
#[ensures(lookup(o, k) != None ==> exists<i> 0 <= i && i < olen(o) && okey(o, i) == k && is_last(o, i))]
pub fn lemma_lookup_char(o: JObj, k: Seq<u8>) {
    lemma_last_key(o, k, olen(o));
    lemma_olen_nonneg(o)
}

#[logic(opaque)]
#[ensures(olen(o) >= 0)]
pub fn lemma_olen_nonneg(o: JObj) {
    pearlite! { match o { JObj::Nil => (), JObj::Cons(_, _, r) => lemma_olen_nonneg(*r) } }
}

// メンバーの列 ms の obj_of での lookup
#[logic(opaque)]
#[ensures(no_key(ms, k) ==> lookup(obj_of(nodes, ms), k) == None)]
#[ensures(forall<i> last_of(ms, i, k) ==> lookup(obj_of(nodes, ms), k) == Some(tree(nodes, ms[i].value@)))]
pub fn lemma_lookup_ms(nodes: Seq<JsonNode>, ms: Seq<Member>, k: Seq<u8>) {
    lemma_obj_index(nodes, ms);
    lemma_lookup_char(obj_of(nodes, ms), k)
}

#[logic(opaque)]
#[requires(seq_is(a, b))]
#[ensures(a == b)]
pub fn lemma_seq_is_eq(a: Seq<u8>, b: Seq<u8>) {
    proof_assert!(a.ext_eq(b));
}

#[ensures(match result { None => no_key(obj@, key@), Some(i) => last_of(obj@, i@, key@) })]
#[ensures(forall<nodes: Seq<JsonNode>, k: Seq<u8>> #[trigger(lookup(obj_of(nodes, obj@), k))] seq_is(k, key@) ==>
    lookup(obj_of(nodes, obj@), k) == match result { None => None, Some(i) => Some(tree(nodes, obj@[i@].value@)) })]
#[check(terminates)]
pub fn find_member(obj: &Vec<Member>, key: &[u8]) -> Option<usize> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_lookup_ms(Seq::empty(), obj@, key@));
    let mut found: Option<usize> = None;
    let mut i = 0;
    #[invariant(i@ <= obj@.len())]
    #[invariant(match found { None => forall<t> 0 <= t && t < i@ ==> obj@[t].key@ != key@, Some(f) => f@ < i@ && obj@[f@].key@ == key@ && forall<t> f@ < t && t < i@ ==> obj@[t].key@ != key@ })]
    #[variant(obj@.len() - i@)]
    while i < obj.len() {
        if bytes_eq(&obj[i].key, key) {
            found = Some(i);
        }
        i += 1;
    }
    found
}

#[ensures(match result { None => d@.len() <= id@, Some(n) => id@ < d@.len() && *n == d@[id@] })]
#[check(terminates)]
pub fn node_at(d: &Vec<JsonNode>, id: usize) -> Option<&JsonNode> {
    if id < d.len() {
        Some(&d[id])
    } else {
        None
    }
}

// ノードのメンバーの値（子の添字）は文書の範囲内
#[logic(open)]
pub fn ms_in(d: Seq<JsonNode>, ms: Seq<Member>) -> bool {
    pearlite! { forall<t> 0 <= t && t < ms.len() ==> ms[t].value@ < d.len() }
}

#[logic(open)]
pub fn ids_in(d: Seq<JsonNode>, ids: Seq<usize>) -> bool {
    pearlite! { forall<t> 0 <= t && t < ids.len() ==> ids[t]@ < d.len() }
}

#[logic(open)]
pub fn nodes_wf(d: Seq<JsonNode>) -> bool {
    pearlite! { wf_range(d, 0, d.len()) }
}

// ノード id の値（文書が整形式のとき）
#[logic(opaque)]
#[requires(nodes_wf(d))]
#[ensures(0 <= id && id < d.len() ==> tree(d, id) == node_val(d, d[id]) && node_in(d, d[id]))]
#[ensures(!(0 <= id && id < d.len()) ==> tree(d, id) == JsonS::Null)]
pub fn lemma_tree_node(d: Seq<JsonNode>, id: Int) {
    pearlite! {
        if 0 <= id && id < d.len() {
            match d[id] {
                JsonNode::Object(ms) => lemma_tree_object0(d, id, ms),
                JsonNode::Array(v) => lemma_tree_array0(d, id, v),
                _ => lemma_tree_scalar(d, id),
            }
        } else {
            lemma_tree_out(d, id)
        }
    }
}

// ノード値
#[logic(open)]
pub fn node_val(d: Seq<JsonNode>, n: JsonNode) -> JsonS {
    pearlite! {
        match n {
            JsonNode::Object(ms) => JsonS::Object(obj_of(d, ms@)),
            JsonNode::Array(v) => JsonS::Array(list_of(d, v@)),
            _ => scalar_view(n),
        }
    }
}

#[logic(open)]
pub fn node_in(d: Seq<JsonNode>, n: JsonNode) -> bool {
    pearlite! {
        match n {
            JsonNode::Object(ms) => ms_in(d, ms@),
            JsonNode::Array(v) => ids_in(d, v@),
            JsonNode::Number(x) => num_ok(num_view(x)),
            _ => true,
        }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result {
    Err(()) => false,
    Ok(None) => lookup(obj_of(d@, obj@), key@) == None,
    Ok(Some(n)) => lookup(obj_of(d@, obj@), key@) == Some(node_val(d@, *n)) && node_in(d@, *n),
})]
#[check(terminates)]
fn member_node<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<&'a JsonNode>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    match find_member(obj, key) {
        None => Ok(None),
        Some(i) => match node_at(d, obj[i].value) {
            None => Err(()),
            Some(n) => Ok(Some(n)),
        },
    }
}

// "uint": number_to_u64 が値を持つ数値
#[logic(open)]
pub fn uint_of(j: JsonS) -> Option<Int> {
    pearlite! { match j { JsonS::Number(n) => num_u64_spec(n), _ => None } }
}

// MUST-013: インデックスは 0 以上の整数
#[logic(open)]
pub fn p_uint(o: JObj, k: Seq<u8>) -> Result<Option<Int>, ()> {
    pearlite! {
        match lookup(o, k) {
            None => Ok(None),
            Some(v) => match uint_of(v) { Some(n) => Ok(Some(n)), None => Err(()) },
        }
    }
}

// MUST-013: インデックスは 0 以上の整数
#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(v) => p_uint(obj_of(d@, obj@), key@) == Ok(opt_int(v)), Err(()) => p_uint(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_uint(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(v) => p_uint(obj_of(d@, obj@), k) == Ok(opt_int(v)), Err(()) => p_uint(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn get_uint(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<u64>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
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

#[logic(open)]
pub fn p_bool(o: JObj, k: Seq<u8>) -> Result<Option<bool>, ()> {
    pearlite! { match lookup(o, k) { None => Ok(None), Some(JsonS::Bool(b)) => Ok(Some(b)), Some(_) => Err(()) } }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(v) => p_bool(obj_of(d@, obj@), key@) == Ok(v), Err(()) => p_bool(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_bool(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(v) => p_bool(obj_of(d@, obj@), k) == Ok(v), Err(()) => p_bool(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn get_bool(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<bool>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Bool(b))) => Ok(Some(*b)),
        Ok(Some(_)) => Err(()),
    }
}

#[ensures(result@ == v@)]
#[check(terminates)]
fn copy_bytes(v: &Vec<u8>) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(out@ == v@[..i@])]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        out.push(v[i]);
        i += 1;
    }
    out
}

#[logic(open)]
pub fn p_string(o: JObj, k: Seq<u8>) -> Result<Option<Seq<u8>>, ()> {
    pearlite! { match lookup(o, k) { None => Ok(None), Some(JsonS::Str(s)) => Ok(Some(s)), Some(_) => Err(()) } }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(None) => p_string(obj_of(d@, obj@), key@) == Ok(None), Ok(Some(v)) => p_string(obj_of(d@, obj@), key@) == Ok(Some(v@)), Err(()) => p_string(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_string(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(None) => p_string(obj_of(d@, obj@), k) == Ok(None), Ok(Some(v)) => p_string(obj_of(d@, obj@), k) == Ok(Some(v@)), Err(()) => p_string(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn get_string(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<Vec<u8>>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::String(s))) => Ok(Some(copy_bytes(s))),
        Ok(Some(_)) => Err(()),
    }
}

#[logic(open)]
pub fn p_object(o: JObj, k: Seq<u8>) -> Result<Option<JObj>, ()> {
    pearlite! { match lookup(o, k) { None => Ok(None), Some(JsonS::Object(m)) => Ok(Some(m)), Some(_) => Err(()) } }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(None) => p_object(obj_of(d@, obj@), key@) == Ok(None), Ok(Some(m)) => p_object(obj_of(d@, obj@), key@) == Ok(Some(obj_of(d@, m@))) && ms_in(d@, m@), Err(()) => p_object(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(match result { Ok(Some(m)) => ms_in(d@, m@), _ => true })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_object(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(None) => p_object(obj_of(d@, obj@), k) == Ok(None), Ok(Some(m)) => p_object(obj_of(d@, obj@), k) == Ok(Some(obj_of(d@, m@))) && ms_in(d@, m@), Err(()) => p_object(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn get_object<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<&'a Vec<Member>>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Object(m))) => Ok(Some(m)),
        Ok(Some(_)) => Err(()),
    }
}

// "array": 要素が 1 つ以上の配列 (minItems: 1)
#[logic(open)]
pub fn p_array(o: JObj, k: Seq<u8>) -> Result<Option<JList>, ()> {
    pearlite! {
        match lookup(o, k) {
            None => Ok(None),
            Some(JsonS::Array(l)) => if jlen(l) > 0 { Ok(Some(l)) } else { Err(()) },
            Some(_) => Err(()),
        }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(None) => p_array(obj_of(d@, obj@), key@) == Ok(None), Ok(Some(a)) => p_array(obj_of(d@, obj@), key@) == Ok(Some(list_of(d@, a@))) && ids_in(d@, a@), Err(()) => p_array(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(match result { Ok(Some(a)) => ids_in(d@, a@), _ => true })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_array(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(None) => p_array(obj_of(d@, obj@), k) == Ok(None), Ok(Some(a)) => p_array(obj_of(d@, obj@), k) == Ok(Some(list_of(d@, a@))) && ids_in(d@, a@), Err(()) => p_array(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn get_array<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<&'a Vec<usize>>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
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

#[logic(open)]
pub fn uints_is(l: JList, v: Seq<u64>) -> bool {
    pearlite! { jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> uint_of(nth(l, t)) == Some(v[t]@) }
}

#[logic(open)]
pub fn all_uints(l: JList) -> bool {
    pearlite! { forall<t> 0 <= t && t < jlen(l) ==> uint_of(nth(l, t)) != None }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result { Some(v) => uints_is(list_of(d@, a@), v@), None => !all_uints(list_of(d@, a@)) })]
#[check(terminates)]
fn uints_of(d: &Vec<JsonNode>, a: &Vec<usize>) -> Option<Vec<u64>> {
    snapshot!(lemma_list_index(d@, a@));
    snapshot!(lemma_tree_node(d@, 0));
    let mut out: Vec<u64> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> uint_of(tree(d@, a@[t]@)) == Some(out@[t]@))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        match node_at(d, a[i]) {
            Some(JsonNode::Number(n)) => match number_to_u64(n) {
                Some(v) => out.push(v),
                None => return None,
            },
            _ => return None,
        }
        i += 1;
    }
    Some(out)
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(None) => p_array(obj_of(d@, obj@), key@) == Ok(None), Ok(Some(v)) => match p_array(obj_of(d@, obj@), key@) { Ok(Some(l)) => uints_is(l, v@), _ => false }, Err(()) => match p_array(obj_of(d@, obj@), key@) { Err(()) => true, Ok(None) => false, Ok(Some(l)) => !all_uints(l) } })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_array(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(None) => p_array(obj_of(d@, obj@), k) == Ok(None), Ok(Some(v)) => match p_array(obj_of(d@, obj@), k) { Ok(Some(l)) => uints_is(l, v@), _ => false }, Err(()) => match p_array(obj_of(d@, obj@), k) { Err(()) => true, Ok(None) => false, Ok(Some(l)) => !all_uints(l) } })]
#[check(terminates)]
pub fn get_uint_array(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<Vec<u64>>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
    match get_array(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(a)) => match uints_of(d, a) {
            None => Err(()),
            Some(v) => Ok(Some(v)),
        },
    }
}

#[logic(open)]
pub fn is_number(j: JsonS) -> bool {
    pearlite! { match j { JsonS::Number(_) => true, _ => false } }
}

#[logic(open)]
pub fn all_numbers_l(l: JList) -> bool {
    pearlite! { forall<t> 0 <= t && t < jlen(l) ==> is_number(nth(l, t)) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(result == all_numbers_l(list_of(d@, a@)))]
#[check(terminates)]
fn all_numbers(d: &Vec<JsonNode>, a: &Vec<usize>) -> bool {
    snapshot!(lemma_list_index(d@, a@));
    snapshot!(lemma_tree_node(d@, 0));
    let mut i = 0;
    #[invariant(i@ <= a@.len())]
    #[invariant(forall<t> 0 <= t && t < i@ ==> is_number(tree(d@, a@[t]@)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        match node_at(d, a[i]) {
            Some(JsonNode::Number(_)) => {}
            _ => return false,
        }
        i += 1;
    }
    true
}

// 数値の配列の長さ
#[logic(open)]
pub fn p_number_array_len(o: JObj, k: Seq<u8>) -> Result<Option<Int>, ()> {
    pearlite! {
        match p_array(o, k) {
            Err(()) => Err(()),
            Ok(None) => Ok(None),
            Ok(Some(l)) => if all_numbers_l(l) { Ok(Some(jlen(l))) } else { Err(()) },
        }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(v) => p_number_array_len(obj_of(d@, obj@), key@) == Ok(opt_int(v)), Err(()) => p_number_array_len(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_number_array_len(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(v) => p_number_array_len(obj_of(d@, obj@), k) == Ok(opt_int(v)), Err(()) => p_number_array_len(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn get_number_array_len(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<u64>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
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

// "number": 値は解釈しない。あれば true
#[logic(open)]
pub fn p_number(o: JObj, k: Seq<u8>) -> Result<bool, ()> {
    pearlite! { match lookup(o, k) { None => Ok(false), Some(v) => if is_number(v) { Ok(true) } else { Err(()) } } }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(b) => p_number(obj_of(d@, obj@), key@) == Ok(b), Err(()) => p_number(obj_of(d@, obj@), key@) == Err(()) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_number(obj_of(d@, obj@), k))] seq_is(k, key@) ==> match result { Ok(b) => p_number(obj_of(d@, obj@), k) == Ok(b), Err(()) => p_number(obj_of(d@, obj@), k) == Err(()) })]
#[check(terminates)]
pub fn check_number(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<bool, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(JsonNode::Number(_))) => Ok(true),
        Ok(Some(_)) => Err(()),
    }
}

// ちょうど n 個の数値の配列。あれば true
#[logic(open)]
pub fn p_number_array(o: JObj, k: Seq<u8>, n: Int) -> Result<bool, ()> {
    pearlite! {
        match p_number_array_len(o, k) {
            Err(()) => Err(()),
            Ok(None) => Ok(false),
            Ok(Some(m)) => if m == n { Ok(true) } else { Err(()) },
        }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, obj@))]
#[ensures(match result { Ok(b) => p_number_array(obj_of(d@, obj@), key@, len@) == Ok(b), Err(()) => p_number_array(obj_of(d@, obj@), key@, len@) == Err(()) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_number_array(obj_of(d@, obj@), k, len@))] seq_is(k, key@) ==> match result { Ok(b) => p_number_array(obj_of(d@, obj@), k, len@) == Ok(b), Err(()) => p_number_array(obj_of(d@, obj@), k, len@) == Err(()) })]
#[check(terminates)]
pub fn check_number_array(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8], len: u64) -> Result<bool, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_list_index(d@, Seq::empty()));
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

#[logic(open)]
pub fn as_obj(j: JsonS) -> Option<JObj> {
    pearlite! { match j { JsonS::Object(o) => Some(o), _ => None } }
}

// オブジェクトならそのメンバーの列、そうでなければ空
#[logic(open)]
pub fn obj_or_nil(j: JsonS) -> JObj {
    pearlite! { match j { JsonS::Object(o) => o, _ => JObj::Nil } }
}

#[logic(open)]
pub fn is_object(j: JsonS) -> bool {
    pearlite! { match j { JsonS::Object(_) => true, _ => false } }
}

#[requires(nodes_wf(d@))]
#[ensures(match result { Ok(m) => as_obj(tree(d@, id@)) == Some(obj_of(d@, m@)) && ms_in(d@, m@), Err(()) => as_obj(tree(d@, id@)) == None })]
#[ensures(match result { Ok(m) => is_object(tree(d@, id@)) && obj_or_nil(tree(d@, id@)) == obj_of(d@, m@), Err(()) => !is_object(tree(d@, id@)) })]
#[check(terminates)]
pub fn as_object(d: &Vec<JsonNode>, id: usize) -> Result<&Vec<Member>, ()> {
    snapshot!(lemma_tree_node(d@, id@));
    match node_at(d, id) {
        Some(JsonNode::Object(m)) => Ok(m),
        _ => Err(()),
    }
}

// extensions は、あれば、上書きされていないメンバーの値がすべてオブジェクトのオブジェクト
#[logic(open)]
pub fn ext_ok(o: JObj) -> bool {
    pearlite! {
        match lookup(o, key_extensions()) {
            None => true,
            Some(JsonS::Object(e)) => forall<k: Seq<u8>> match lookup(e, k) { Some(v) => is_object(v), None => true },
            Some(_) => false,
        }
    }
}

// x は o の extensions のメンバーのキー
#[logic(open)]
pub fn ext_here(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match lookup(o, key_extensions()) {
            Some(JsonS::Object(e)) => lookup(e, x) != None,
            _ => false,
        }
    }
}

#[logic(open)]
pub fn in_strs(v: Seq<Vec<u8>>, x: Seq<u8>) -> bool {
    pearlite! { exists<k> 0 <= k && k < v.len() && v[k]@ == x }
}

#[logic(open)]
pub fn key_extensions() -> Seq<u8> {
    pearlite! { seq![101u8, 120u8, 116u8, 101u8, 110u8, 115u8, 105u8, 111u8, 110u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 101u8 && s[1] == 120u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 110u8 && s[5] == 115u8 && s[6] == 105u8 && s[7] == 111u8 && s[8] == 110u8 && s[9] == 115u8 ==> seq_is(key_extensions(), s))]
pub fn lemma_key_extensions(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(()) => ext_ok(obj_of(d@, o@)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_here(obj_of(d@, o@), x))),
    Err(()) => !ext_ok(obj_of(d@, o@)),
})]
#[check(terminates)]
pub(crate) fn check_extensions(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    snapshot!(lemma_key_extensions(Seq::empty()));
    match get_object(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's']) {
        Err(()) => Err(()),
        Ok(None) => Ok(()),
        Ok(Some(e)) => collect_extension_names(d, e, ext),
    }
}

#[logic(opaque)]
#[ensures(forall<x: Seq<u8>> in_strs(v.push_back(y), x) == (in_strs(v, x) || y@ == x))]
pub fn lemma_in_strs_push(v: Seq<Vec<u8>>, y: Vec<u8>) {
    proof_assert!(forall<k: Int> 0 <= k && k < v.len() ==> v.push_back(y)[k] == v[k]);
    proof_assert!(v.push_back(y)[v.len()] == y);
}

#[requires(nodes_wf(d@) && ms_in(d@, e@))]
#[ensures(match result {
    Ok(()) => (forall<k: Seq<u8>> match lookup(obj_of(d@, e@), k) { Some(v) => is_object(v), None => true }) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || lookup(obj_of(d@, e@), x) != None)),
    Err(()) => !(forall<k: Seq<u8>> match lookup(obj_of(d@, e@), k) { Some(v) => is_object(v), None => true }),
})]
#[check(terminates)]
fn collect_extension_names(d: &Vec<JsonNode>, e: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_in_strs_push(*_ext0, e@[0].key));
    snapshot!(lemma_tree_node(d@, 0));
    snapshot!(lemma_obj_index(d@, e@));
    snapshot!(lemma_lookup_char(obj_of(d@, e@), Seq::empty()));
    let mut i = 0;
    #[invariant(i@ <= e@.len())]
    #[invariant(forall<t> 0 <= t && t < i@ && is_last(obj_of(d@, e@), t) ==> is_object(tree(d@, e@[t].value@)))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && e@[t].key@ == x && is_last(obj_of(d@, e@), t)))]
    #[variant(e@.len() - i@)]
    while i < e.len() {
        if is_last_member(e, i) {
            match node_at(d, e[i].value) {
                Some(JsonNode::Object(_)) => ext.push(copy_key(&e[i].key)),
                _ => return Err(()),
            }
        }
        i += 1;
    }
    Ok(())
}

// glTFChildOfRootProperty: name は文字列、extensions は ext_ok
#[logic(open, inline)]
pub fn cor_ok(o: JObj) -> bool {
    pearlite! { p_string(o, key_name()) != Err(()) && ext_ok(o) }
}

#[logic(open)]
pub fn key_name() -> Seq<u8> {
    pearlite! { seq![110u8, 97u8, 109u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 4 && s[0] == 110u8 && s[1] == 97u8 && s[2] == 109u8 && s[3] == 101u8 ==> seq_is(key_name(), s))]
pub fn lemma_key_name(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(()) => cor_ok(obj_of(d@, o@)) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_here(obj_of(d@, o@), x))),
    Err(()) => !cor_ok(obj_of(d@, o@)),
})]
#[check(terminates)]
pub(crate) fn check_child_of_root(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    snapshot!(lemma_key_name(Seq::empty()));
    match get_string(d, o, &[b'n', b'a', b'm', b'e']) {
        Err(()) => return Err(()),
        Ok(_) => {}
    }
    check_extensions(d, o, ext)
}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(forall<k: Seq<u8>> #[trigger(p_uint(obj_of(d@, o@), k))] seq_is(k, key@) ==> match result { Ok(v) => p_uint(obj_of(d@, o@), k) == Ok(Some(v@)), Err(()) => match p_uint(obj_of(d@, o@), k) { Ok(Some(_)) => false, _ => true } })]
#[check(terminates)]
pub(crate) fn req_uint(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8]) -> Result<u64, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    match get_uint(d, o, key) {
        Ok(Some(v)) => Ok(v),
        _ => Err(()),
    }
}

#[ensures(result@ == v@)]
#[check(terminates)]
pub(crate) fn copy_key(v: &Vec<u8>) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(out@ == v@[..i@])]
    #[variant(v@.len() - i@)]
    while i < v.len() {
        out.push(v[i]);
        i += 1;
    }
    out
}
