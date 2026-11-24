pub mod number;
pub mod string;

use creusot_std::prelude::*;
use crate::json::number::*;
use crate::json::string::*;

// RFC 8259 §2: 空白
#[logic(open)]
pub fn ws(b: u8) -> bool {
    pearlite! { b@ == 0x20 || b@ == 0x09 || b@ == 0x0A || b@ == 0x0D }
}

// RFC 8259 §2: 空白
#[ensures(result == ws(b))]
#[check(terminates)]
fn is_ws(b: u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D
}

// skip_ws(s, i): i 以上で、|s| に等しいか空白でない最小の位置
#[logic(open)]
#[variant(s.len() - i)]
#[ensures(0 <= i && i <= s.len() ==> i <= result && result <= s.len())]
#[ensures(0 <= i && i <= s.len() ==> (forall<k> i <= k && k < result ==> ws(s[k])) && (result == s.len() || !ws(s[result])))]
#[ensures(!(0 <= i && i <= s.len()) ==> result == i)]
pub fn skip_spec(s: Seq<u8>, i: Int) -> Int {
    pearlite! { if i < 0 || i >= s.len() { i } else if ws(s[i]) { skip_spec(s, i + 1) } else { i } }
}

#[ensures(result@ == skip_spec(s@, i@))]
#[check(terminates)]
pub fn skip_ws(s: &[u8], i: usize) -> usize {
    let mut j = i;
    #[invariant(i@ <= j@ && (i@ <= s@.len() ==> j@ <= s@.len()))]
    #[invariant(skip_spec(s@, i@) == skip_spec(s@, j@))]
    #[variant(s@.len() - j@)]
    while j < s.len() && is_ws(s[j]) {
        j += 1;
    }
    j
}

pub struct Member {
    pub key: Vec<u8>,
    pub value: usize,
}

pub enum JsonNode {
    Null,
    Bool(bool),
    Number(Number),
    String(Vec<u8>),
    Array(Vec<usize>),
    Object(Vec<Member>),
}

pub struct JsonDoc {
    pub nodes: Vec<JsonNode>,
    pub root: usize,
}

pub const MAX_DEPTH: usize = 128;

#[logic(open)]
pub fn lit_at(s: Seq<u8>, i: Int, lit: Seq<u8>) -> bool {
    pearlite! { 0 <= i && i + lit.len() <= s.len() && forall<k> 0 <= k && k < lit.len() ==> s[i + k] == lit[k] }
}

#[requires(lit@.len() > 0)]
#[ensures(match result { None => !lit_at(s@, i@, lit@), Some(j) => lit_at(s@, i@, lit@) && j@ == i@ + lit@.len() })]
#[check(terminates)]
fn parse_literal(s: &[u8], i: usize, lit: &[u8]) -> Option<usize> {
    if i >= s.len() || s.len() - i < lit.len() {
        return None;
    }
    let mut k = 0;
    #[invariant(k@ <= lit@.len() && i@ + lit@.len() <= s@.len())]
    #[invariant(forall<t> 0 <= t && t < k@ ==> s@[i@ + t] == lit@[t])]
    #[variant(lit@.len() - k@)]
    while k < lit.len() {
        if s[i + k] != lit[k] {
            return None;
        }
        k += 1;
    }
    Some(i + lit.len())
}

// 抽象値 JsonS。配列・オブジェクトの要素の列は Box によるリストで表す
// （Creusot は Seq を通る再帰型を受け付けないため）
#[cfg(creusot)]
pub enum JsonS {
    Null,
    Bool(bool),
    Number(NumS),
    Str(Seq<u8>),
    Array(JList),
    Object(JObj),
}

#[cfg(creusot)]
pub enum JList {
    Nil,
    Cons(Box<JsonS>, Box<JList>),
}

#[cfg(creusot)]
pub enum JObj {
    Nil,
    Cons(Seq<u8>, Box<JsonS>, Box<JObj>),
}

#[logic(open)]
pub fn lit_true() -> Seq<u8> { seq![116u8, 114u8, 117u8, 101u8] }

#[logic(open)]
pub fn lit_false() -> Seq<u8> { seq![102u8, 97u8, 108u8, 115u8, 101u8] }

#[logic(open)]
pub fn lit_null() -> Seq<u8> { seq![110u8, 117u8, 108u8, 108u8] }

// value(s, i, d) のうち、文字列・リテラル・数値の場合（s[i] が { [ 以外）
#[logic(open)]
#[ensures(0 <= i && i < s.len() ==> match result { Some((_, e)) => i < e && e <= s.len(), None => true })]
pub fn scalar_spec(s: Seq<u8>, i: Int) -> Option<(JsonS, Int)> {
    pearlite! {
        if s[i]@ == 34 {
            match string_spec(s, i + 1) { Some((v, j)) => Some((JsonS::Str(v), j)), None => None }
        } else if s[i]@ == 116 {
            if lit_at(s, i, lit_true()) { Some((JsonS::Bool(true), i + 4)) } else { None }
        } else if s[i]@ == 102 {
            if lit_at(s, i, lit_false()) { Some((JsonS::Bool(false), i + 5)) } else { None }
        } else if s[i]@ == 110 {
            if lit_at(s, i, lit_null()) { Some((JsonS::Null, i + 4)) } else { None }
        } else if s[i]@ == 45 || is_dec(s[i]) {
            match number_spec(s, i) { Some((n, j)) => Some((JsonS::Number(n), j)), None => None }
        } else {
            None
        }
    }
}

// ノード p の子の添字はすべて p より小さく、数値は表現の不変条件を満たす
#[logic(open)]
pub fn node_wf(nodes: Seq<JsonNode>, p: Int) -> bool {
    pearlite! {
        match nodes[p] {
            JsonNode::Array(v) => forall<k> 0 <= k && k < v@.len() ==> v@[k]@ < p,
            JsonNode::Object(ms) => forall<k> 0 <= k && k < ms@.len() ==> ms@[k].value@ < p,
            JsonNode::Number(n) => num_repr_ok(num_view(n)),
            _ => true,
        }
    }
}

// 文字列・リテラル・数値のノードの値
#[logic(open)]
pub fn scalar_view(n: JsonNode) -> JsonS {
    pearlite! {
        match n {
            JsonNode::Null => JsonS::Null,
            JsonNode::Bool(b) => JsonS::Bool(b),
            JsonNode::Number(x) => JsonS::Number(num_view(x)),
            JsonNode::String(v) => JsonS::Str(v@),
            _ => JsonS::Null,
        }
    }
}

#[logic(open)]
pub fn is_scalar(n: JsonNode) -> bool {
    pearlite! { match n { JsonNode::Array(_) => false, JsonNode::Object(_) => false, _ => true } }
}

#[requires(i@ < s@.len())]
#[ensures(match result {
    None => scalar_spec(s@, i@) == None,
    Some((nd, j)) => is_scalar(nd) && node_wf(Seq::singleton(nd), 0) && scalar_spec(s@, i@) == Some((scalar_view(nd), j@)),
})]
#[check(terminates)]
fn parse_scalar(s: &[u8], i: usize) -> Option<(JsonNode, usize)> {
    let c = s[i];
    if c == b'"' {
        match parse_string(s, i + 1) {
            Some((v, j)) => Some((JsonNode::String(v), j)),
            None => None,
        }
    } else if c == b't' {
        match parse_literal(s, i, &[b't', b'r', b'u', b'e']) {
            Some(j) => Some((JsonNode::Bool(true), j)),
            None => None,
        }
    } else if c == b'f' {
        match parse_literal(s, i, &[b'f', b'a', b'l', b's', b'e']) {
            Some(j) => Some((JsonNode::Bool(false), j)),
            None => None,
        }
    } else if c == b'n' {
        match parse_literal(s, i, &[b'n', b'u', b'l', b'l']) {
            Some(j) => Some((JsonNode::Null, j)),
            None => None,
        }
    } else if c == b'-' || is_digit(c) {
        match parse_number(s, i) {
            Some((n, j)) => Some((JsonNode::Number(n), j)),
            None => None,
        }
    } else {
        None
    }
}

#[cfg(creusot)]
pub use opaque::*;

#[cfg(creusot)]
mod opaque {
    use super::*;

    // 文法。kind: 0 = 配列, 1 = オブジェクト。mode: m_value = value(s, i, d),
    // m_start = array/object(s, i, d)（開き括弧の直後）, m_items = 空でない要素の列
    #[logic]
    #[variant((d, s.len() - i, mode))]
    #[ensures(match result { GRes::V(_, e) => i < e && e <= s.len(), GRes::L(_, e) => i < e && e <= s.len(), GRes::O(_, e) => i < e && e <= s.len(), GRes::GNone => true })]
    #[ensures(mode == m_value() ==> match result { GRes::GNone => true, GRes::V(_, _) => true, _ => false })]
    #[ensures(mode != m_value() && kind == 0 ==> match result { GRes::GNone => true, GRes::L(_, _) => true, _ => false })]
    #[ensures(mode != m_value() && kind != 0 ==> match result { GRes::GNone => true, GRes::O(_, _) => true, _ => false })]
    pub fn gram(mode: Int, kind: Int, s: Seq<u8>, i: Int, d: Int) -> GRes {
        pearlite! {
            if i < 0 || i > s.len() || d < 0 || mode < 0 || mode > 2 {
                GRes::GNone
            } else if mode == m_value() {
                if i >= s.len() {
                    GRes::GNone
                } else if s[i]@ == 123 {
                    if d == 0 { GRes::GNone } else {
                        match gram(m_start(), 1, s, i + 1, d - 1) { GRes::O(o, e) => GRes::V(JsonS::Object(o), e), _ => GRes::GNone }
                    }
                } else if s[i]@ == 91 {
                    if d == 0 { GRes::GNone } else {
                        match gram(m_start(), 0, s, i + 1, d - 1) { GRes::L(l, e) => GRes::V(JsonS::Array(l), e), _ => GRes::GNone }
                    }
                } else {
                    match scalar_spec(s, i) { Some((v, e)) => GRes::V(v, e), None => GRes::GNone }
                }
            } else if mode == m_start() {
                let j = skip_spec(s, i);
                if kind == 0 {
                    if j < s.len() && s[j]@ == 93 { GRes::L(JList::Nil, j + 1) } else { gram(m_items(), 0, s, j, d) }
                } else {
                    if j < s.len() && s[j]@ == 125 { GRes::O(JObj::Nil, j + 1) } else { gram(m_items(), 1, s, j, d) }
                }
            } else if kind == 0 {
                match gram(m_value(), 0, s, i, d) {
                    GRes::V(v, k) => {
                        let j = skip_spec(s, k);
                        if j >= s.len() {
                            GRes::GNone
                        } else if s[j]@ == 44 {
                            match gram(m_items(), 0, s, skip_spec(s, j + 1), d) {
                                GRes::L(rest, e) => GRes::L(JList::Cons(Box::new(v), Box::new(rest)), e),
                                _ => GRes::GNone,
                            }
                        } else if s[j]@ == 93 {
                            GRes::L(JList::Cons(Box::new(v), Box::new(JList::Nil)), j + 1)
                        } else {
                            GRes::GNone
                        }
                    }
                    _ => GRes::GNone,
                }
            } else {
                if i >= s.len() || s[i]@ != 34 {
                    GRes::GNone
                } else {
                    match string_spec(s, i + 1) {
                        None => GRes::GNone,
                        Some((key, e)) => {
                            let j = skip_spec(s, e);
                            if j >= s.len() || s[j]@ != 58 {
                                GRes::GNone
                            } else {
                                match gram(m_value(), 0, s, skip_spec(s, j + 1), d) {
                                    GRes::V(v, k) => {
                                        let j2 = skip_spec(s, k);
                                        if j2 >= s.len() {
                                            GRes::GNone
                                        } else if s[j2]@ == 44 {
                                            match gram(m_items(), 1, s, skip_spec(s, j2 + 1), d) {
                                                GRes::O(rest, e2) => GRes::O(JObj::Cons(key, Box::new(v), Box::new(rest)), e2),
                                                _ => GRes::GNone,
                                            }
                                        } else if s[j2]@ == 125 {
                                            GRes::O(JObj::Cons(key, Box::new(v), Box::new(JObj::Nil)), j2 + 1)
                                        } else {
                                            GRes::GNone
                                        }
                                    }
                                    _ => GRes::GNone,
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // tree(doc, id) を、子の列を作る部分と 1 つの再帰関数にまとめたもの。
    // mode 2: ノード id の値, mode 1: ノード id の子の k 番目以降の列。
    // 子の添字が親より小さいことで停止する（そうでない子は Null とみなす）
    #[logic]
    #[variant((id, mode, child_count(nodes, id) - k))]
    #[ensures(mode == 2 ==> match result { TRes::TV(_) => true, _ => false })]
    #[ensures(mode == 1 && 0 <= id && id < nodes.len() ==> match nodes[id] {
        JsonNode::Object(_) => match result { TRes::TO(_) => true, _ => false },
        _ => match result { TRes::TL(_) => true, _ => false },
    })]
    pub fn tree_g(nodes: Seq<JsonNode>, id: Int, mode: Int, k: Int) -> TRes {
        pearlite! {
            if id < 0 || id >= nodes.len() || (mode != 1 && mode != 2) {
                if mode == 2 { TRes::TV(JsonS::Null) } else { TRes::TL(JList::Nil) }
            } else if mode == 2 {
                match nodes[id] {
                    JsonNode::Null => TRes::TV(JsonS::Null),
                    JsonNode::Bool(b) => TRes::TV(JsonS::Bool(b)),
                    JsonNode::Number(n) => TRes::TV(JsonS::Number(num_view(n))),
                    JsonNode::String(v) => TRes::TV(JsonS::Str(v@)),
                    JsonNode::Array(_) => match tree_g(nodes, id, 1, 0) { TRes::TL(l) => TRes::TV(JsonS::Array(l)), _ => TRes::TV(JsonS::Null) },
                    JsonNode::Object(_) => match tree_g(nodes, id, 1, 0) { TRes::TO(o) => TRes::TV(JsonS::Object(o)), _ => TRes::TV(JsonS::Null) },
                }
            } else {
                match nodes[id] {
                    JsonNode::Array(v) => {
                        if k < 0 || k >= v@.len() {
                            TRes::TL(JList::Nil)
                        } else {
                            let c = v@[k]@;
                            let x = if c < id { match tree_g(nodes, c, 2, 0) { TRes::TV(x) => x, _ => JsonS::Null } } else { JsonS::Null };
                            match tree_g(nodes, id, 1, k + 1) {
                                TRes::TL(rest) => TRes::TL(JList::Cons(Box::new(x), Box::new(rest))),
                                _ => TRes::TL(JList::Nil),
                            }
                        }
                    }
                    JsonNode::Object(ms) => {
                        if k < 0 || k >= ms@.len() {
                            TRes::TO(JObj::Nil)
                        } else {
                            let c = ms@[k].value@;
                            let x = if c < id { match tree_g(nodes, c, 2, 0) { TRes::TV(x) => x, _ => JsonS::Null } } else { JsonS::Null };
                            match tree_g(nodes, id, 1, k + 1) {
                                TRes::TO(rest) => TRes::TO(JObj::Cons(ms@[k].key@, Box::new(x), Box::new(rest))),
                                _ => TRes::TO(JObj::Nil),
                            }
                        }
                    }
                    _ => TRes::TL(JList::Nil),
                }
            }
        }
    }

    // 子の添字 ids の列の表す JsonS の列
    #[logic]
    #[variant(ids.len())]
    pub fn list_of(nodes: Seq<JsonNode>, ids: Seq<usize>) -> JList {
        pearlite! {
            if ids.len() == 0 { JList::Nil }
            else { JList::Cons(Box::new(tree(nodes, ids[0]@)), Box::new(list_of(nodes, ids.tail()))) }
        }
    }

    #[logic]
    #[variant(ms.len())]
    pub fn obj_of(nodes: Seq<JsonNode>, ms: Seq<Member>) -> JObj {
        pearlite! {
            if ms.len() == 0 { JObj::Nil }
            else { JObj::Cons(ms[0].key@, Box::new(tree(nodes, ms[0].value@)), Box::new(obj_of(nodes, ms.tail()))) }
        }
    }

    // ノード id の値は、添字 id 以下のノードだけで決まる
    #[logic(opaque)]
    #[variant((id, mode, child_count(a, id) - k))]
    #[requires(0 <= id && id < n && same_prefix(a, b, n))]
    #[ensures(tree_g(a, id, mode, k) == tree_g(b, id, mode, k))]
    pub fn lemma_tree_frame(a: Seq<JsonNode>, b: Seq<JsonNode>, n: Int, id: Int, mode: Int, k: Int) {
        pearlite! {
            if mode == 2 {
                match a[id] {
                    JsonNode::Array(_) => lemma_tree_frame(a, b, n, id, 1, 0),
                    JsonNode::Object(_) => lemma_tree_frame(a, b, n, id, 1, 0),
                    _ => (),
                }
            } else if mode == 1 {
                match a[id] {
                    JsonNode::Array(v) => {
                        if 0 <= k && k < v@.len() {
                            if v@[k]@ < id { lemma_tree_frame(a, b, n, v@[k]@, 2, 0) };
                            lemma_tree_frame(a, b, n, id, 1, k + 1)
                        }
                    }
                    JsonNode::Object(ms) => {
                        if 0 <= k && k < ms@.len() {
                            if ms@[k].value@ < id { lemma_tree_frame(a, b, n, ms@[k].value@, 2, 0) };
                            lemma_tree_frame(a, b, n, id, 1, k + 1)
                        }
                    }
                    _ => (),
                }
            }
        }
    }

    #[logic]
    pub fn lapp(a: JList, b: JList) -> JList {
        pearlite! {
            match a {
                JList::Nil => b,
                JList::Cons(x, r) => JList::Cons(x, Box::new(lapp(*r, b))),
            }
        }
    }

    #[logic]
    pub fn oapp(a: JObj, b: JObj) -> JObj {
        pearlite! {
            match a {
                JObj::Nil => b,
                JObj::Cons(k, x, r) => JObj::Cons(k, x, Box::new(oapp(*r, b))),
            }
        }
    }

    // 既に読んだ要素の列 p を、残りの解析結果 r の前に付ける
    #[logic]
    pub fn lcat(p: JList, r: GRes) -> GRes {
        pearlite! { match r { GRes::L(l, e) => GRes::L(lapp(p, l), e), _ => GRes::GNone } }
    }

    #[logic]
    pub fn ocat(p: JObj, r: GRes) -> GRes {
        pearlite! { match r { GRes::O(o, e) => GRes::O(oapp(p, o), e), _ => GRes::GNone } }
    }

    #[logic(opaque)]
    #[ensures(lapp(lapp(a, b), c) == lapp(a, lapp(b, c)))]
    pub fn lemma_lapp_assoc(a: JList, b: JList, c: JList) {
        pearlite! { match a { JList::Nil => (), JList::Cons(_, r) => lemma_lapp_assoc(*r, b, c) } }
    }

    #[logic(opaque)]
    #[ensures(oapp(oapp(a, b), c) == oapp(a, oapp(b, c)))]
    pub fn lemma_oapp_assoc(a: JObj, b: JObj, c: JObj) {
        pearlite! { match a { JObj::Nil => (), JObj::Cons(_, _, r) => lemma_oapp_assoc(*r, b, c) } }
    }

    #[logic(opaque)]
    #[ensures(lcat(p, lcat(q, r)) == lcat(lapp(p, q), r))]
    pub fn lemma_lcat(p: JList, q: JList, r: GRes) {
        pearlite! { match r { GRes::L(l, _) => lemma_lapp_assoc(p, q, l), _ => () } }
    }

    #[logic(opaque)]
    #[ensures(ocat(p, ocat(q, r)) == ocat(oapp(p, q), r))]
    pub fn lemma_ocat(p: JObj, q: JObj, r: GRes) {
        pearlite! { match r { GRes::O(o, _) => lemma_oapp_assoc(p, q, o), _ => () } }
    }

    #[logic(opaque)]
    #[variant(ids.len())]
    #[ensures(list_of(nodes, ids.push_back(x)) == lapp(list_of(nodes, ids), JList::Cons(Box::new(tree(nodes, x@)), Box::new(JList::Nil))))]
    pub fn lemma_list_snoc(nodes: Seq<JsonNode>, ids: Seq<usize>, x: usize) {
        pearlite! {
            if ids.len() > 0 {
                proof_assert!(ids.push_back(x).tail().ext_eq(ids.tail().push_back(x)));
                lemma_list_snoc(nodes, ids.tail(), x)
            }
        }
    }

    #[logic(opaque)]
    #[variant(ms.len())]
    #[ensures(obj_of(nodes, ms.push_back(m)) == oapp(obj_of(nodes, ms), JObj::Cons(m.key@, Box::new(tree(nodes, m.value@)), Box::new(JObj::Nil))))]
    pub fn lemma_obj_snoc(nodes: Seq<JsonNode>, ms: Seq<Member>, m: Member) {
        pearlite! {
            if ms.len() > 0 {
                proof_assert!(ms.push_back(m).tail().ext_eq(ms.tail().push_back(m)));
                lemma_obj_snoc(nodes, ms.tail(), m)
            }
        }
    }

    #[logic(opaque)]
    #[variant(ids.len())]
    #[requires(same_prefix(a, b, n))]
    #[requires(forall<t> 0 <= t && t < ids.len() ==> ids[t]@ < n)]
    #[ensures(list_of(a, ids) == list_of(b, ids))]
    pub fn lemma_list_frame(a: Seq<JsonNode>, b: Seq<JsonNode>, n: Int, ids: Seq<usize>) {
        pearlite! {
            if ids.len() > 0 {
                lemma_tree_frame(a, b, n, ids[0]@, 2, 0);
                lemma_list_frame(a, b, n, ids.tail())
            }
        }
    }

    #[logic(opaque)]
    #[variant(ms.len())]
    #[requires(same_prefix(a, b, n))]
    #[requires(forall<t> 0 <= t && t < ms.len() ==> ms[t].value@ < n)]
    #[ensures(obj_of(a, ms) == obj_of(b, ms))]
    pub fn lemma_obj_frame(a: Seq<JsonNode>, b: Seq<JsonNode>, n: Int, ms: Seq<Member>) {
        pearlite! {
            if ms.len() > 0 {
                lemma_tree_frame(a, b, n, ms[0].value@, 2, 0);
                lemma_obj_frame(a, b, n, ms.tail())
            }
        }
    }

    // 配列ノード p の子の列の値
    #[logic(opaque)]
    #[variant(v@.len() - k)]
    #[requires(0 <= p && p < nodes.len() && nodes[p] == JsonNode::Array(v))]
    #[requires(forall<t> 0 <= t && t < v@.len() ==> v@[t]@ < p)]
    #[requires(0 <= k && k <= v@.len())]
    #[ensures(tree_g(nodes, p, 1, k) == TRes::TL(list_of(nodes, v@[k..])))]
    pub fn lemma_tree_array(nodes: Seq<JsonNode>, p: Int, v: Vec<usize>, k: Int) {
        pearlite! {
            if k < v@.len() {
                proof_assert!(v@[k..].tail().ext_eq(v@[k + 1..]));
                lemma_tree_array(nodes, p, v, k + 1)
            }
        }
    }

    #[logic(opaque)]
    #[variant(ms@.len() - k)]
    #[requires(0 <= p && p < nodes.len() && nodes[p] == JsonNode::Object(ms))]
    #[requires(forall<t> 0 <= t && t < ms@.len() ==> ms@[t].value@ < p)]
    #[requires(0 <= k && k <= ms@.len())]
    #[ensures(tree_g(nodes, p, 1, k) == TRes::TO(obj_of(nodes, ms@[k..])))]
    pub fn lemma_tree_object(nodes: Seq<JsonNode>, p: Int, ms: Vec<Member>, k: Int) {
        pearlite! {
            if k < ms@.len() {
                proof_assert!(ms@[k..].tail().ext_eq(ms@[k + 1..]));
                lemma_tree_object(nodes, p, ms, k + 1)
            }
        }
    }

    // ノード p に配列 v を置いたときの値
    #[logic(opaque)]
    #[requires(0 <= p && p < nodes.len() && nodes[p] == JsonNode::Array(v))]
    #[requires(forall<t> 0 <= t && t < v@.len() ==> v@[t]@ < p)]
    #[ensures(tree(nodes, p) == JsonS::Array(list_of(nodes, v@)))]
    pub fn lemma_tree_array0(nodes: Seq<JsonNode>, p: Int, v: Vec<usize>) {
        lemma_tree_array(nodes, p, v, 0);
        proof_assert!(v@[0..].ext_eq(v@));
    }

    #[logic(opaque)]
    #[requires(0 <= p && p < nodes.len() && nodes[p] == JsonNode::Object(ms))]
    #[requires(forall<t> 0 <= t && t < ms@.len() ==> ms@[t].value@ < p)]
    #[ensures(tree(nodes, p) == JsonS::Object(obj_of(nodes, ms@)))]
    pub fn lemma_tree_object0(nodes: Seq<JsonNode>, p: Int, ms: Vec<Member>) {
        lemma_tree_object(nodes, p, ms, 0);
        proof_assert!(ms@[0..].ext_eq(ms@));
    }

    #[logic(opaque)]
    #[requires(0 <= j && j <= s.len() && 0 <= d)]
    #[ensures(gram(m_items(), 0, s, j, d) == match value_spec(s, j, d) { GRes::V(v, k) => items_after(s, v, skip_spec(s, k), d), _ => GRes::GNone })]
    pub fn lemma_items_step(s: Seq<u8>, j: Int, d: Int) {}

    #[logic(opaque)]
    #[requires(0 <= j && j <= s.len() && 0 <= d)]
    #[ensures(gram(m_items(), 1, s, j, d) == member_at(s, j, d))]
    pub fn lemma_members_step(s: Seq<u8>, j: Int, d: Int) {}

    #[logic(opaque)]
    #[requires(0 <= i && i < s.len() && 0 < d)]
    #[ensures(s[i]@ == 91 ==> value_spec(s, i, d) == match gram(m_start(), 0, s, i + 1, d - 1) { GRes::L(l, e) => GRes::V(JsonS::Array(l), e), _ => GRes::GNone })]
    #[ensures(s[i]@ == 123 ==> value_spec(s, i, d) == match gram(m_start(), 1, s, i + 1, d - 1) { GRes::O(o, e) => GRes::V(JsonS::Object(o), e), _ => GRes::GNone })]
    #[ensures(gram(m_start(), 0, s, i + 1, d - 1) == if skip_spec(s, i + 1) < s.len() && s[skip_spec(s, i + 1)]@ == 93 { GRes::L(JList::Nil, skip_spec(s, i + 1) + 1) } else { gram(m_items(), 0, s, skip_spec(s, i + 1), d - 1) })]
    #[ensures(gram(m_start(), 1, s, i + 1, d - 1) == if skip_spec(s, i + 1) < s.len() && s[skip_spec(s, i + 1)]@ == 125 { GRes::O(JObj::Nil, skip_spec(s, i + 1) + 1) } else { gram(m_items(), 1, s, skip_spec(s, i + 1), d - 1) })]
    pub fn lemma_value_open(s: Seq<u8>, i: Int, d: Int) {}

    #[logic(opaque)]
    #[requires(0 <= d)]
    #[ensures(i >= s.len() ==> value_spec(s, i, d) == GRes::GNone)]
    #[ensures(0 <= i && i < s.len() && d == 0 && (s[i]@ == 91 || s[i]@ == 123) ==> value_spec(s, i, d) == GRes::GNone)]
    #[ensures(0 <= i && i < s.len() && s[i]@ != 91 && s[i]@ != 123 ==>
        value_spec(s, i, d) == match scalar_spec(s, i) { Some((v, e)) => GRes::V(v, e), None => GRes::GNone })]
    pub fn lemma_value_scalar(s: Seq<u8>, i: Int, d: Int) {}

    #[logic(opaque)]
    #[requires(0 <= p && p < nodes.len() && is_scalar(nodes[p]))]
    #[ensures(tree(nodes, p) == scalar_view(nodes[p]))]
    pub fn lemma_tree_scalar(nodes: Seq<JsonNode>, p: Int) {}

    #[logic(opaque)]
    #[ensures(lcat(p, GRes::GNone) == GRes::GNone && ocat(q, GRes::GNone) == GRes::GNone)]
    #[ensures(forall<l: JList, e: Int> lcat(p, GRes::L(l, e)) == GRes::L(lapp(p, l), e))]
    #[ensures(forall<o: JObj, e: Int> ocat(q, GRes::O(o, e)) == GRes::O(oapp(q, o), e))]
    #[ensures(forall<l: JList> lapp(JList::Nil, l) == l)]
    #[ensures(forall<o: JObj> oapp(JObj::Nil, o) == o)]
    #[ensures(list_of(nodes, Seq::empty()) == JList::Nil && obj_of(nodes, Seq::empty()) == JObj::Nil)]
    pub fn lemma_cat_basic(p: JList, q: JObj, nodes: Seq<JsonNode>) {}

    #[logic(opaque)]
    #[requires(0 <= j && j < s.len() && s[j]@ == 34 && 0 <= j2 && j2 < s.len() && s[j2]@ == 58)]
    #[requires(match string_spec(s, j + 1) { Some((k2, e)) => k2 == key && skip_spec(s, e) == j2, None => false })]
    #[ensures(member_at(s, j, d) == match value_spec(s, skip_spec(s, j2 + 1), d) {
        GRes::V(v, k) => members_after(s, key, v, skip_spec(s, k), d),
        _ => GRes::GNone,
    })]
    pub fn lemma_member_key(s: Seq<u8>, j: Int, d: Int, key: Seq<u8>, j2: Int) {}

    // 実行時の表現との対応
    #[logic(opaque)]
    #[variant(ids.len())]
    #[ensures(jlen(list_of(nodes, ids)) == ids.len())]
    #[ensures(forall<k> 0 <= k && k < ids.len() ==> nth(list_of(nodes, ids), k) == tree(nodes, ids[k]@))]
    pub fn lemma_list_index(nodes: Seq<JsonNode>, ids: Seq<usize>) {
        pearlite! {
            if ids.len() > 0 {
                lemma_list_index(nodes, ids.tail())
            }
        }
    }

    #[logic(opaque)]
    #[variant(ms.len())]
    #[ensures(olen(obj_of(nodes, ms)) == ms.len())]
    #[ensures(forall<k> 0 <= k && k < ms.len() ==> okey(obj_of(nodes, ms), k) == ms[k].key@)]
    #[ensures(forall<k> 0 <= k && k < ms.len() ==> oval(obj_of(nodes, ms), k) == tree(nodes, ms[k].value@))]
    pub fn lemma_obj_index(nodes: Seq<JsonNode>, ms: Seq<Member>) {
        pearlite! {
            if ms.len() > 0 {
                lemma_obj_index(nodes, ms.tail())
            }
        }
    }

    #[logic(opaque)]
    #[requires(!(0 <= id && id < nodes.len()))]
    #[ensures(tree(nodes, id) == JsonS::Null)]
    pub fn lemma_tree_out(nodes: Seq<JsonNode>, id: Int) {}
}

// value / array / object を 1 つの再帰関数にまとめるための結果の型
// （Creusot は相互再帰の論理関数を受け付けないため、モードの引数で切り替える）
#[cfg(creusot)]
pub enum GRes {
    GNone,
    V(JsonS, Int),
    L(JList, Int),
    O(JObj, Int),
}

#[logic(open)]
pub fn m_value() -> Int { 0 }

#[logic(open)]
pub fn m_items() -> Int { 1 }

#[logic(open)]
pub fn m_start() -> Int { 2 }

// value(s, i, d)
#[logic(open)]
pub fn value_spec(s: Seq<u8>, i: Int, d: Int) -> GRes {
    pearlite! { gram(m_value(), 0, s, i, d) }
}

#[cfg(creusot)]
pub enum TRes {
    TV(JsonS),
    TL(JList),
    TO(JObj),
}

#[logic(open)]
pub fn child_count(nodes: Seq<JsonNode>, id: Int) -> Int {
    pearlite! {
        if 0 <= id && id < nodes.len() {
            match nodes[id] {
                JsonNode::Array(v) => v@.len(),
                JsonNode::Object(ms) => ms@.len(),
                _ => 0,
            }
        } else {
            0
        }
    }
}

// tree(doc, id): ノード id の表す JsonS
#[logic(open)]
pub fn tree(nodes: Seq<JsonNode>, id: Int) -> JsonS {
    pearlite! { match tree_g(nodes, id, 2, 0) { TRes::TV(x) => x, _ => JsonS::Null } }
}

#[logic(open)]
pub fn wf_range(nodes: Seq<JsonNode>, a: Int, b: Int) -> bool {
    pearlite! { forall<p> a <= p && p < b ==> node_wf(nodes, p) }
}

#[logic(open)]
pub fn same_prefix(a: Seq<JsonNode>, b: Seq<JsonNode>, n: Int) -> bool {
    pearlite! { n <= a.len() && n <= b.len() && forall<t> 0 <= t && t < n ==> a[t] == b[t] }
}

#[logic(opaque)]
#[requires(0 <= n0 && n0 <= m && wf_range(a, n0, m) && same_prefix(a, b, m) && wf_range(b, m, b.len()))]
#[ensures(wf_range(b, n0, b.len()))]
pub fn lemma_wf_extend(a: Seq<JsonNode>, b: Seq<JsonNode>, n0: Int, m: Int) {}

#[logic(opaque)]
#[requires(0 <= n0 && n0 <= a.len() && wf_range(a, n0, a.len()) && node_wf(a.push_back(x), a.len()))]
#[ensures(wf_range(a.push_back(x), n0, a.len() + 1))]
#[ensures(same_prefix(a, a.push_back(x), a.len()))]
pub fn lemma_wf_push(a: Seq<JsonNode>, x: JsonNode, n0: Int) {}

#[logic(open)]
pub fn items_after(s: Seq<u8>, v: JsonS, j: Int, d: Int) -> GRes {
    pearlite! {
        if j >= s.len() { GRes::GNone }
        else if s[j]@ == 44 { lcat(JList::Cons(Box::new(v), Box::new(JList::Nil)), gram(m_items(), 0, s, skip_spec(s, j + 1), d)) }
        else if s[j]@ == 93 { GRes::L(JList::Cons(Box::new(v), Box::new(JList::Nil)), j + 1) }
        else { GRes::GNone }
    }
}

#[logic(open)]
pub fn members_after(s: Seq<u8>, key: Seq<u8>, v: JsonS, j: Int, d: Int) -> GRes {
    pearlite! {
        if j >= s.len() { GRes::GNone }
        else if s[j]@ == 44 { ocat(JObj::Cons(key, Box::new(v), Box::new(JObj::Nil)), gram(m_items(), 1, s, skip_spec(s, j + 1), d)) }
        else if s[j]@ == 125 { GRes::O(JObj::Cons(key, Box::new(v), Box::new(JObj::Nil)), j + 1) }
        else { GRes::GNone }
    }
}

#[logic(open)]
pub fn member_at(s: Seq<u8>, j: Int, d: Int) -> GRes {
    pearlite! {
        if j >= s.len() || s[j]@ != 34 {
            GRes::GNone
        } else {
            match string_spec(s, j + 1) {
                None => GRes::GNone,
                Some((key, e)) => {
                    let j2 = skip_spec(s, e);
                    if j2 >= s.len() || s[j2]@ != 58 {
                        GRes::GNone
                    } else {
                        match value_spec(s, skip_spec(s, j2 + 1), d) {
                            GRes::V(v, k) => members_after(s, key, v, skip_spec(s, k), d),
                            _ => GRes::GNone,
                        }
                    }
                }
            }
        }
    }
}

#[ensures(same_prefix((*nodes)@, (^nodes)@, (*nodes)@.len()))]
#[ensures(match result {
    None => value_spec(s@, i@, depth@) == GRes::GNone,
    Some((id, e)) => (*nodes)@.len() <= id@ && id@ < (^nodes)@.len()
        && wf_range((^nodes)@, (*nodes)@.len(), (^nodes)@.len())
        && value_spec(s@, i@, depth@) == GRes::V(tree((^nodes)@, id@), e@),
})]
#[check(terminates)]
#[variant(depth)]
fn parse_value(s: &[u8], i: usize, depth: usize, nodes: &mut Vec<JsonNode>) -> Option<(usize, usize)> {
    let _nodes0 = snapshot!(nodes@);
    snapshot!(lemma_lcat(JList::Nil, JList::Nil, GRes::GNone));
    snapshot!(lemma_ocat(JObj::Nil, JObj::Nil, GRes::GNone));
    snapshot!(lemma_cat_basic(JList::Nil, JObj::Nil, *_nodes0));
    snapshot!(lemma_value_scalar(s@, i@, depth@));
    if i >= s.len() {
        return None;
    }
    let c = s[i];
    if c == b'[' {
        if depth == 0 {
            return None;
        }
        snapshot!(lemma_value_open(s@, i@, depth@));
        let mut items: Vec<usize> = Vec::new();
        let mut j = skip_ws(s, i + 1);
        if j < s.len() && s[j] == b']' {
            proof_assert!(items@.ext_eq(Seq::empty()));
            let _it = snapshot!(items);
            nodes.push(JsonNode::Array(items));
            snapshot!(lemma_wf_push(*_nodes0, JsonNode::Array(*_it), _nodes0.len()));
            snapshot!(lemma_tree_array0(nodes@, nodes@.len() - 1, *_it));
            proof_assert!(tree(nodes@, nodes@.len() - 1) == JsonS::Array(JList::Nil));
            proof_assert!(value_spec(s@, i@, depth@) == GRes::V(JsonS::Array(JList::Nil), j@ + 1));
            return Some((nodes.len() - 1, j + 1));
        }
        let _j0 = snapshot!(j@);
        proof_assert!(items@.ext_eq(Seq::empty()));
        #[invariant(same_prefix(*_nodes0, nodes@, _nodes0.len()))]
        #[invariant(wf_range(nodes@, _nodes0.len(), nodes@.len()))]
        #[invariant(forall<t> 0 <= t && t < items@.len() ==> _nodes0.len() <= items@[t]@ && items@[t]@ < nodes@.len())]
        #[invariant(j@ <= s@.len())]
        #[invariant(gram(m_items(), 0, s@, *_j0, depth@ - 1) == lcat(list_of(nodes@, items@), gram(m_items(), 0, s@, j@, depth@ - 1)))]
        #[variant(s@.len() - j@)]
        loop {
            let _before = snapshot!(nodes@);
            let _jv = snapshot!(j@);
            snapshot!(lemma_items_step(s@, j@, depth@ - 1));
            match parse_value(s, j, depth - 1, nodes) {
                None => return None,
                Some((id, k)) => {
                    snapshot!(lemma_wf_extend(*_before, nodes@, _nodes0.len(), _before.len()));
                    snapshot!(lemma_list_frame(*_before, nodes@, _before.len(), items@));
                    snapshot!(lemma_list_snoc(nodes@, items@, id));
                    proof_assert!(_nodes0.len() <= id@ && id@ < nodes@.len());
                    items.push(id);
                    j = skip_ws(s, k);
                    proof_assert!(gram(m_items(), 0, s@, *_jv, depth@ - 1) == items_after(s@, tree(nodes@, items@[items@.len() - 1]@), j@, depth@ - 1));
                }
            }
            if j >= s.len() {
                return None;
            }
            if s[j] == b',' {
                j = skip_ws(s, j + 1);
                proof_assert!(gram(m_items(), 0, s@, *_jv, depth@ - 1) == lcat(JList::Cons(Box::new(tree(nodes@, items@[items@.len() - 1]@)), Box::new(JList::Nil)), gram(m_items(), 0, s@, j@, depth@ - 1)));
            } else if s[j] == b']' {
                let _last = snapshot!(nodes@);
                let _it = snapshot!(items);
                proof_assert!(gram(m_items(), 0, s@, *_j0, depth@ - 1) == GRes::L(list_of(nodes@, _it@), j@ + 1));
                proof_assert!(forall<t> 0 <= t && t < _it@.len() ==> _it@[t]@ < _last.len());
                nodes.push(JsonNode::Array(items));
                snapshot!(lemma_wf_push(*_last, JsonNode::Array(*_it), _nodes0.len()));
                snapshot!(lemma_list_frame(*_last, nodes@, _last.len(), _it@));
                snapshot!(lemma_tree_array0(nodes@, nodes@.len() - 1, *_it));
                proof_assert!(value_spec(s@, i@, depth@) == GRes::V(tree(nodes@, nodes@.len() - 1), j@ + 1));
                return Some((nodes.len() - 1, j + 1));
            } else {
                return None;
            }
        }
    } else if c == b'{' {
        if depth == 0 {
            return None;
        }
        snapshot!(lemma_value_open(s@, i@, depth@));
        let mut members: Vec<Member> = Vec::new();
        let mut j = skip_ws(s, i + 1);
        if j < s.len() && s[j] == b'}' {
            proof_assert!(members@.ext_eq(Seq::empty()));
            let _ms = snapshot!(members);
            nodes.push(JsonNode::Object(members));
            snapshot!(lemma_wf_push(*_nodes0, JsonNode::Object(*_ms), _nodes0.len()));
            snapshot!(lemma_tree_object0(nodes@, nodes@.len() - 1, *_ms));
            proof_assert!(tree(nodes@, nodes@.len() - 1) == JsonS::Object(JObj::Nil));
            proof_assert!(value_spec(s@, i@, depth@) == GRes::V(JsonS::Object(JObj::Nil), j@ + 1));
            return Some((nodes.len() - 1, j + 1));
        }
        let _j0 = snapshot!(j@);
        proof_assert!(members@.ext_eq(Seq::empty()));
        #[invariant(same_prefix(*_nodes0, nodes@, _nodes0.len()))]
        #[invariant(wf_range(nodes@, _nodes0.len(), nodes@.len()))]
        #[invariant(forall<t> 0 <= t && t < members@.len() ==> _nodes0.len() <= members@[t].value@ && members@[t].value@ < nodes@.len())]
        #[invariant(j@ <= s@.len())]
        #[invariant(gram(m_items(), 1, s@, *_j0, depth@ - 1) == ocat(obj_of(nodes@, members@), gram(m_items(), 1, s@, j@, depth@ - 1)))]
        #[variant(s@.len() - j@)]
        loop {
            let _jv = snapshot!(j@);
            snapshot!(lemma_members_step(s@, j@, depth@ - 1));
            if j >= s.len() || s[j] != b'"' {
                proof_assert!(gram(m_items(), 1, s@, *_jv, depth@ - 1) == GRes::GNone);
                return None;
            }
            let key = match parse_string(s, j + 1) {
                None => return None,
                Some((k, e)) => {
                    j = skip_ws(s, e);
                    k
                }
            };
            if j >= s.len() || s[j] != b':' {
                proof_assert!(gram(m_items(), 1, s@, *_jv, depth@ - 1) == GRes::GNone);
                return None;
            }
            snapshot!(lemma_member_key(s@, *_jv, depth@ - 1, key@, j@));
            j = skip_ws(s, j + 1);
            proof_assert!(gram(m_items(), 1, s@, *_jv, depth@ - 1) == match value_spec(s@, j@, depth@ - 1) {
                GRes::V(v, k) => members_after(s@, key@, v, skip_spec(s@, k), depth@ - 1),
                _ => GRes::GNone,
            });
            let _before = snapshot!(nodes@);
            match parse_value(s, j, depth - 1, nodes) {
                None => return None,
                Some((id, k)) => {
                    snapshot!(lemma_wf_extend(*_before, nodes@, _nodes0.len(), _before.len()));
                    snapshot!(lemma_obj_frame(*_before, nodes@, _before.len(), members@));
                    let _mv = snapshot!(Member { key: key, value: id });
                    snapshot!(lemma_obj_snoc(nodes@, members@, *_mv));
                    proof_assert!(_nodes0.len() <= id@ && id@ < nodes@.len());
                    proof_assert!(gram(m_items(), 1, s@, *_jv, depth@ - 1) == members_after(s@, _mv.key@, tree(nodes@, _mv.value@), skip_spec(s@, k@), depth@ - 1));
                    members.push(Member { key, value: id });
                    j = skip_ws(s, k);
                }
            }
            if j >= s.len() {
                return None;
            }
            if s[j] == b',' {
                j = skip_ws(s, j + 1);
                proof_assert!(gram(m_items(), 1, s@, *_jv, depth@ - 1) == ocat(JObj::Cons(members@[members@.len() - 1].key@, Box::new(tree(nodes@, members@[members@.len() - 1].value@)), Box::new(JObj::Nil)), gram(m_items(), 1, s@, j@, depth@ - 1)));
            } else if s[j] == b'}' {
                let _last = snapshot!(nodes@);
                let _ms = snapshot!(members);
                proof_assert!(gram(m_items(), 1, s@, *_j0, depth@ - 1) == GRes::O(obj_of(nodes@, _ms@), j@ + 1));
                proof_assert!(forall<t> 0 <= t && t < _ms@.len() ==> _ms@[t].value@ < _last.len());
                nodes.push(JsonNode::Object(members));
                snapshot!(lemma_wf_push(*_last, JsonNode::Object(*_ms), _nodes0.len()));
                snapshot!(lemma_obj_frame(*_last, nodes@, _last.len(), _ms@));
                snapshot!(lemma_tree_object0(nodes@, nodes@.len() - 1, *_ms));
                proof_assert!(value_spec(s@, i@, depth@) == GRes::V(tree(nodes@, nodes@.len() - 1), j@ + 1));
                return Some((nodes.len() - 1, j + 1));
            } else {
                return None;
            }
        }
    } else {
        match parse_scalar(s, i) {
            None => None,
            Some((node, j)) => {
                nodes.push(node);
                snapshot!(lemma_wf_push(*_nodes0, nodes@[_nodes0.len()], _nodes0.len()));
                snapshot!(lemma_tree_scalar(nodes@, _nodes0.len()));
                Some((nodes.len() - 1, j))
            }
        }
    }
}

// json_text(s)
// RFC 8259 §2: JSON テキスト
#[logic(open)]
pub fn json_text_spec(s: Seq<u8>) -> Option<JsonS> {
    pearlite! {
        let i0 = if s.len() >= 3 && s[0]@ == 0xEF && s[1]@ == 0xBB && s[2]@ == 0xBF { 3 } else { 0 };
        match value_spec(s, skip_spec(s, i0), 128) {
            GRes::V(v, k) => if skip_spec(s, k) == s.len() { Some(v) } else { None },
            _ => None,
        }
    }
}

// parse_json が返す文書の整形式
#[logic(open)]
pub fn doc_wf(d: JsonDoc) -> bool {
    pearlite! { d.root@ < d.nodes@.len() && wf_range(d.nodes@, 0, d.nodes@.len()) }
}

// RFC 8259 §2: JSON テキスト
#[ensures(match result {
    None => json_text_spec(s@) == None,
    Some(d) => doc_wf(d) && json_text_spec(s@) == Some(tree(d.nodes@, d.root@)),
})]
#[check(terminates)]
pub fn parse_json(s: &[u8]) -> Option<JsonDoc> {
    let mut i = 0;
    if s.len() >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF {
        i = 3;
    }
    i = skip_ws(s, i);
    let mut nodes: Vec<JsonNode> = Vec::new();
    match parse_value(s, i, MAX_DEPTH, &mut nodes) {
        None => None,
        Some((root, j)) => {
            if skip_ws(s, j) == s.len() {
                Some(JsonDoc { nodes, root })
            } else {
                None
            }
        }
    }
}

#[logic(open)]
pub fn olen(o: JObj) -> Int {
    pearlite! { match o { JObj::Nil => 0, JObj::Cons(_, _, r) => 1 + olen(*r) } }
}

#[logic(open)]
pub fn jlen(l: JList) -> Int {
    pearlite! { match l { JList::Nil => 0, JList::Cons(_, r) => 1 + jlen(*r) } }
}

// 配列の k 番目の要素（範囲外は Null）
#[logic(open)]
pub fn nth(l: JList, k: Int) -> JsonS {
    pearlite! {
        match l {
            JList::Nil => JsonS::Null,
            JList::Cons(x, r) => if k == 0 { *x } else { nth(*r, k - 1) },
        }
    }
}

// オブジェクトの i 番目のメンバーのキーと値
#[logic(open)]
pub fn okey(o: JObj, i: Int) -> Seq<u8> {
    pearlite! {
        match o {
            JObj::Nil => Seq::empty(),
            JObj::Cons(k, _, r) => if i == 0 { k } else { okey(*r, i - 1) },
        }
    }
}

#[logic(open)]
pub fn oval(o: JObj, i: Int) -> JsonS {
    pearlite! {
        match o {
            JObj::Nil => JsonS::Null,
            JObj::Cons(_, v, r) => if i == 0 { *v } else { oval(*r, i - 1) },
        }
    }
}

#[logic(opaque)]
#[ensures(jlen(l) >= 0)]
pub fn lemma_jlen_nonneg(l: JList) {
    pearlite! { match l { JList::Nil => (), JList::Cons(_, r) => lemma_jlen_nonneg(*r) } }
}
