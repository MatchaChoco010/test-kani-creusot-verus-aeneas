pub mod number;
pub mod string;

use crate::json::number::*;
use crate::json::string::*;
use vstd::prelude::*;

verus! {

// J.2 文法
pub open spec fn ws(b: u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D
}

// ---- 実行コード ----
fn is_ws(b: u8) -> (r: bool)
    ensures
        r == ws(b),
{
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D
}

// skip_ws(s, i) = j >= i で j = |s| または ¬ws(s[j]) となる最小の j
pub open spec fn skip_ws_at(s: Seq<u8>, i: int, j: int) -> bool {
    &&& i <= j <= s.len()
    &&& (j == s.len() || !ws(s[j]))
    &&& forall|k: int| i <= k < j ==> ws(#[trigger] s[k])
}

pub open spec fn skip_ws_spec(s: Seq<u8>, i: int) -> int {
    choose|j: int| skip_ws_at(s, i, j)
}

// ---- 補題 ----
pub proof fn lemma_skip_ws_unique(s: Seq<u8>, i: int, j: int)
    requires
        skip_ws_at(s, i, j),
    ensures
        skip_ws_spec(s, i) == j,
{
    let j2 = skip_ws_spec(s, i);
    assert(skip_ws_at(s, i, j2));
    if j2 < j {
        assert(ws(s[j2]));
    } else if j < j2 {
        assert(ws(s[j]));
    }
}

pub fn skip_ws(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r == skip_ws_spec(s@, i as int),
        i <= r <= s.len(),
{
    let mut j = i;
    while j < s.len() && is_ws(s[j])
        invariant
            i <= j <= s.len(),
            forall|k: int| i <= k < j ==> ws(#[trigger] s@[k]),
        decreases s.len() - j,
    {
        j += 1;
    }
    proof {
        lemma_skip_ws_unique(s@, i as int, j as int);
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

pub open spec fn lit_at(s: Seq<u8>, i: int, lit: Seq<u8>) -> bool {
    0 <= i && i + lit.len() <= s.len() && s.subrange(i, i + lit.len()) == lit
}

fn parse_literal(s: &[u8], i: usize, lit: &[u8]) -> (r: Option<usize>)
    requires
        i < s.len(),
    ensures
        match r {
            Some(e) => lit_at(s@, i as int, lit@) && e == i + lit.len(),
            None => !lit_at(s@, i as int, lit@),
        },
{
    if i >= s.len() || s.len() - i < lit.len() {
        return None;
    }
    let mut k = 0;
    while k < lit.len()
        invariant
            i + lit.len() <= s.len(),
            0 <= k <= lit.len(),
            forall|m: int| 0 <= m < k ==> s@[i + m] == lit@[m],
        decreases lit.len() - k,
    {
        if s[i + k] != lit[k] {
            assert(s@.subrange(i as int, i + lit.len())[k as int] == s@[i + k]);
            return None;
        }
        k += 1;
    }
    assert(s@.subrange(i as int, i + lit.len()) =~= lit@);
    Some(i + lit.len())
}

// J.1 抽象値
pub enum JsonS {
    Null,
    Bool(bool),
    Number(NumberS),
    String(Seq<u8>),
    Array(Seq<JsonS>),
    Object(Seq<(Seq<u8>, JsonS)>),
}

pub open spec fn node_scalar(n: JsonNode) -> JsonS {
    match n {
        JsonNode::Bool(b) => JsonS::Bool(b),
        JsonNode::Number(x) => JsonS::Number(x@),
        JsonNode::String(v) => JsonS::String(v@),
        _ => JsonS::Null,
    }
}

// value_end(s, i, d, v) = Some(e) ⇔ s[i..e] が予算 d で値 v として構文解析される
pub open spec fn value_end(s: Seq<u8>, i: int, d: nat, v: JsonS) -> Option<int>
    decreases v,
{
    if i < 0 || i >= s.len() {
        None
    } else {
        match v {
            JsonS::Null => if lit_at(s, i, seq![b'n', b'u', b'l', b'l']) {
                Some(i + 4)
            } else {
                None
            },
            JsonS::Bool(b) => if b {
                if lit_at(s, i, seq![b't', b'r', b'u', b'e']) {
                    Some(i + 4)
                } else {
                    None
                }
            } else {
                if lit_at(s, i, seq![b'f', b'a', b'l', b's', b'e']) {
                    Some(i + 5)
                } else {
                    None
                }
            },
            JsonS::Number(n) => if s[i] == b'-' || digit(s[i]) {
                match number_spec(s, i) {
                    Some((n2, e)) => if n2 == n {
                        Some(e)
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            JsonS::String(b) => if s[i] == b'"' {
                match string_spec(s, i + 1) {
                    Some((b2, e)) => if b2 == b {
                        Some(e)
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                None
            },
            JsonS::Array(items) => if s[i] == b'[' && d > 0 {
                let j = skip_ws_spec(s, i + 1);
                if items.len() == 0 {
                    if j < s.len() && s[j] == b']' {
                        Some(j + 1)
                    } else {
                        None
                    }
                } else {
                    items_end(s, j, (d - 1) as nat, items)
                }
            } else {
                None
            },
            JsonS::Object(ms) => if s[i] == b'{' && d > 0 {
                let j = skip_ws_spec(s, i + 1);
                if ms.len() == 0 {
                    if j < s.len() && s[j] == b'}' {
                        Some(j + 1)
                    } else {
                        None
                    }
                } else {
                    members_end(s, j, (d - 1) as nat, ms)
                }
            } else {
                None
            },
        }
    }
}

// 空でない value (ws , ws value)* ws ] の並び
pub open spec fn items_end(s: Seq<u8>, j: int, d: nat, items: Seq<JsonS>) -> Option<int>
    decreases items,
{
    if items.len() == 0 {
        None
    } else {
        match value_end(s, j, d, items[0]) {
            None => None,
            Some(k) => {
                let m = skip_ws_spec(s, k);
                if m < s.len() && s[m] == b',' && items.len() > 1 {
                    items_end(s, skip_ws_spec(s, m + 1), d, items.drop_first())
                } else if m < s.len() && s[m] == b']' && items.len() == 1 {
                    Some(m + 1)
                } else {
                    None
                }
            },
        }
    }
}

// "key" ws : ws の後の値の位置
pub open spec fn member_value_start(s: Seq<u8>, j: int, key: Seq<u8>) -> Option<int> {
    if 0 <= j < s.len() && s[j] == b'"' {
        match string_spec(s, j + 1) {
            Some((k, e)) => {
                let c = skip_ws_spec(s, e);
                if k == key && c < s.len() && s[c] == b':' {
                    Some(skip_ws_spec(s, c + 1))
                } else {
                    None
                }
            },
            None => None,
        }
    } else {
        None
    }
}

// 空でない member (ws , ws member)* ws } の並び
pub open spec fn members_end(s: Seq<u8>, j: int, d: nat, ms: Seq<(Seq<u8>, JsonS)>) -> Option<int>
    decreases ms,
{
    if ms.len() == 0 {
        None
    } else {
        match member_value_start(s, j, ms[0].0) {
            None => None,
            Some(p) => match value_end(s, p, d, ms[0].1) {
                None => None,
                Some(k) => {
                    let m = skip_ws_spec(s, k);
                    if m < s.len() && s[m] == b',' && ms.len() > 1 {
                        members_end(s, skip_ws_spec(s, m + 1), d, ms.drop_first())
                    } else if m < s.len() && s[m] == b'}' && ms.len() == 1 {
                        Some(m + 1)
                    } else {
                        None
                    }
                },
            },
        }
    }
}

pub proof fn lemma_lit_first(s: Seq<u8>, i: int, lit: Seq<u8>)
    requires
        lit_at(s, i, lit),
        lit.len() > 0,
    ensures
        s[i] == lit[0],
{
    assert(s.subrange(i, i + lit.len())[0] == s[i]);
}

pub proof fn lemma_value_end_first(s: Seq<u8>, i: int, d: nat, v: JsonS)
    requires
        value_end(s, i, d, v) is Some,
    ensures
        0 <= i < s.len(),
        v is Null ==> s[i] == b'n',
        v is Bool ==> (s[i] == b't' <==> v->Bool_0) && (s[i] == b'f' <==> !v->Bool_0),
        v is Number ==> s[i] == b'-' || digit(s[i]),
        v is String ==> s[i] == b'"',
        v is Array ==> s[i] == b'[',
        v is Object ==> s[i] == b'{',
{
    match v {
        JsonS::Null => lemma_lit_first(s, i, seq![b'n', b'u', b'l', b'l']),
        JsonS::Bool(b) => {
            if b {
                lemma_lit_first(s, i, seq![b't', b'r', b'u', b'e']);
            } else {
                lemma_lit_first(s, i, seq![b'f', b'a', b'l', b's', b'e']);
            }
        },
        _ => {},
    }
}

pub open spec fn is_scalar(n: JsonNode) -> bool {
    !(n is Array) && !(n is Object)
}

pub open spec fn scalar_wf(n: JsonNode) -> bool {
    match n {
        JsonNode::Number(x) => number_wf(x@),
        _ => true,
    }
}

// 先頭バイトがスカラーの開始でないならスカラー値は読めない
pub proof fn lemma_scalar_first(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        forall|d: nat, v: JsonS| #[trigger] value_end(s, i, d, v) is Some ==> {
            &&& v is Null ==> s[i] == b'n'
            &&& v is Bool ==> (s[i] == b't' <==> v->Bool_0) && (s[i] == b'f' <==> !v->Bool_0)
            &&& v is Number ==> s[i] == b'-' || digit(s[i])
            &&& v is String ==> s[i] == b'"'
            &&& v is Array ==> s[i] == b'['
            &&& v is Object ==> s[i] == b'{'
        },
{
    assert forall|d: nat, v: JsonS| #[trigger] value_end(s, i, d, v) is Some implies {
        &&& v is Null ==> s[i] == b'n'
        &&& v is Bool ==> (s[i] == b't' <==> v->Bool_0) && (s[i] == b'f' <==> !v->Bool_0)
        &&& v is Number ==> s[i] == b'-' || digit(s[i])
        &&& v is String ==> s[i] == b'"'
        &&& v is Array ==> s[i] == b'['
        &&& v is Object ==> s[i] == b'{'
    } by {
        lemma_value_end_first(s, i, d, v);
    }
}

fn parse_scalar(s: &[u8], i: usize) -> (r: Option<(JsonNode, usize)>)
    requires
        i < s.len(),
    ensures
        match r {
            Some((node, j)) => is_scalar(node) && scalar_wf(node) && i < j <= s.len() && forall|d: nat|
                value_end(s@, i as int, d, node_scalar(node)) == Some(j as int),
            None => s@[i as int] != b'[' && s@[i as int] != b'{' ==> forall|d: nat, v: JsonS|
                #[trigger] value_end(s@, i as int, d, v) is None,
        },
{
    proof {
        lemma_scalar_first(s@, i as int);
        assert([b't', b'r', b'u', b'e']@ =~= seq![b't', b'r', b'u', b'e']);
        assert([b'f', b'a', b'l', b's', b'e']@ =~= seq![b'f', b'a', b'l', b's', b'e']);
        assert([b'n', b'u', b'l', b'l']@ =~= seq![b'n', b'u', b'l', b'l']);
    }
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

// tree(doc, id): 子の添字が親より小さいことを使った id についての再帰
pub open spec fn tree(nodes: Seq<JsonNode>, id: int) -> JsonS
    decreases id,
{
    if 0 <= id < nodes.len() {
        match nodes[id] {
            JsonNode::Array(items) => JsonS::Array(
                Seq::new(
                    items.len() as nat,
                    |k: int|
                        if 0 <= items[k] < id {
                            tree(nodes, items[k] as int)
                        } else {
                            JsonS::Null
                        },
                ),
            ),
            JsonNode::Object(ms) => JsonS::Object(
                Seq::new(
                    ms.len() as nat,
                    |k: int|
                        (
                            ms[k].key@,
                            if 0 <= ms[k].value < id {
                                tree(nodes, ms[k].value as int)
                            } else {
                                JsonS::Null
                            },
                        ),
                ),
            ),
            n => node_scalar(n),
        }
    } else {
        JsonS::Null
    }
}

// 文書の整形式性: 子の添字は親より小さい
pub open spec fn children_lt(nodes: Seq<JsonNode>) -> bool {
    forall|i: int|
        0 <= i < nodes.len() ==> match #[trigger] nodes[i] {
            JsonNode::Array(items) => forall|k: int| 0 <= k < items.len() ==> items[k] < i,
            JsonNode::Object(ms) => forall|k: int| 0 <= k < ms.len() ==> ms[k].value < i,
            _ => true,
        }
}

// すべての Number ノードが表現不変条件を満たす
pub open spec fn numbers_wf(nodes: Seq<JsonNode>) -> bool {
    forall|i: int|
        0 <= i < nodes.len() ==> match #[trigger] nodes[i] {
            JsonNode::Number(n) => number_wf(n@),
            _ => true,
        }
}

// 補助: 区切りの途中までの並び
pub open spec fn items_pre(s: Seq<u8>, j: int, d: nat, items: Seq<JsonS>) -> Option<int>
    decreases items.len(),
{
    if items.len() == 0 {
        Some(j)
    } else {
        match value_end(s, j, d, items[0]) {
            None => None,
            Some(k) => {
                let m = skip_ws_spec(s, k);
                if m < s.len() && s[m] == b',' {
                    items_pre(s, skip_ws_spec(s, m + 1), d, items.drop_first())
                } else {
                    None
                }
            },
        }
    }
}

pub open spec fn members_pre(s: Seq<u8>, j: int, d: nat, ms: Seq<(Seq<u8>, JsonS)>) -> Option<int>
    decreases ms.len(),
{
    if ms.len() == 0 {
        Some(j)
    } else {
        match member_value_start(s, j, ms[0].0) {
            None => None,
            Some(p) => match value_end(s, p, d, ms[0].1) {
                None => None,
                Some(k) => {
                    let m = skip_ws_spec(s, k);
                    if m < s.len() && s[m] == b',' {
                        members_pre(s, skip_ws_spec(s, m + 1), d, ms.drop_first())
                    } else {
                        None
                    }
                },
            },
        }
    }
}

pub open spec fn trees(nodes: Seq<JsonNode>, items: Seq<usize>) -> Seq<JsonS> {
    Seq::new(items.len(), |k: int| tree(nodes, items[k] as int))
}

pub open spec fn member_trees(nodes: Seq<JsonNode>, ms: Seq<Member>) -> Seq<(Seq<u8>, JsonS)> {
    Seq::new(ms.len(), |k: int| (ms[k].key@, tree(nodes, ms[k].value as int)))
}

pub open spec fn json_nodes_ok(nodes: Seq<JsonNode>) -> bool {
    children_lt(nodes) && numbers_wf(nodes)
}

pub open spec fn extends(a: Seq<JsonNode>, b: Seq<JsonNode>) -> bool {
    b.len() <= a.len() && a.subrange(0, b.len() as int) == b
}

pub proof fn lemma_skip_ws_le(s: Seq<u8>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        i <= skip_ws_spec(s, i) <= s.len(),
        skip_ws_at(s, i, skip_ws_spec(s, i)),
    decreases s.len() - i,
{
    if i < s.len() && ws(s[i]) {
        lemma_skip_ws_le(s, i + 1);
        let j = skip_ws_spec(s, i + 1);
        assert(skip_ws_at(s, i, j));
        lemma_skip_ws_unique(s, i, j);
    } else {
        assert(skip_ws_at(s, i, i));
        lemma_skip_ws_unique(s, i, i);
    }
}

// 決定性
pub proof fn lemma_value_end_det(s: Seq<u8>, i: int, d: nat, v1: JsonS, v2: JsonS)
    requires
        value_end(s, i, d, v1) is Some,
        value_end(s, i, d, v2) is Some,
    ensures
        v1 == v2,
        value_end(s, i, d, v1) == value_end(s, i, d, v2),
    decreases v1,
{
    lemma_value_end_first(s, i, d, v1);
    lemma_value_end_first(s, i, d, v2);
    lemma_skip_ws_le(s, i + 1);
    match v1 {
        JsonS::Array(it1) => {
            let it2 = v2->Array_0;
            let j = skip_ws_spec(s, i + 1);
            if it1.len() == 0 {
                if it2.len() > 0 {
                    lemma_items_end_close(s, j, (d - 1) as nat, it2, b']');
                }
                assert(it1 =~= it2);
            } else {
                if it2.len() == 0 {
                    lemma_items_end_close(s, j, (d - 1) as nat, it1, b']');
                }
                lemma_items_end_det(s, j, (d - 1) as nat, it1, it2);
            }
        },
        JsonS::Object(m1) => {
            let m2 = v2->Object_0;
            let j = skip_ws_spec(s, i + 1);
            if m1.len() == 0 {
                if m2.len() > 0 {
                    lemma_members_end_close(s, j, (d - 1) as nat, m2);
                }
                assert(m1 =~= m2);
            } else {
                if m2.len() == 0 {
                    lemma_members_end_close(s, j, (d - 1) as nat, m1);
                }
                lemma_members_end_det(s, j, (d - 1) as nat, m1, m2);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_items_end_close(s: Seq<u8>, j: int, d: nat, items: Seq<JsonS>, c: u8)
    requires
        items.len() > 0,
        0 <= j < s.len(),
        s[j] == c,
        c == b']' || c == b'}' || c == b',',
    ensures
        items_end(s, j, d, items) is None,
{
    if value_end(s, j, d, items[0]) is Some {
        lemma_value_end_first(s, j, d, items[0]);
    }
}

pub proof fn lemma_members_end_close(s: Seq<u8>, j: int, d: nat, ms: Seq<(Seq<u8>, JsonS)>)
    requires
        ms.len() > 0,
        0 <= j < s.len(),
        s[j] == b'}',
    ensures
        members_end(s, j, d, ms) is None,
{
}

pub proof fn lemma_items_end_det(s: Seq<u8>, j: int, d: nat, it1: Seq<JsonS>, it2: Seq<JsonS>)
    requires
        items_end(s, j, d, it1) is Some,
        items_end(s, j, d, it2) is Some,
    ensures
        it1 == it2,
        items_end(s, j, d, it1) == items_end(s, j, d, it2),
    decreases it1,
{
    lemma_value_end_det(s, j, d, it1[0], it2[0]);
    let k = value_end(s, j, d, it1[0])->Some_0;
    let m = skip_ws_spec(s, k);
    if it1.len() > 1 {
        lemma_items_end_det(s, skip_ws_spec(s, m + 1), d, it1.drop_first(), it2.drop_first());
        assert(it1 =~= seq![it1[0]] + it1.drop_first());
        assert(it2 =~= seq![it2[0]] + it2.drop_first());
    } else {
        assert(it1 =~= it2);
    }
}

pub proof fn lemma_members_end_det(
    s: Seq<u8>,
    j: int,
    d: nat,
    m1: Seq<(Seq<u8>, JsonS)>,
    m2: Seq<(Seq<u8>, JsonS)>,
)
    requires
        members_end(s, j, d, m1) is Some,
        members_end(s, j, d, m2) is Some,
    ensures
        m1 == m2,
        members_end(s, j, d, m1) == members_end(s, j, d, m2),
    decreases m1,
{
    let p = member_value_start(s, j, m1[0].0)->Some_0;
    assert(m1[0].0 == m2[0].0);
    lemma_value_end_det(s, p, d, m1[0].1, m2[0].1);
    let k = value_end(s, p, d, m1[0].1)->Some_0;
    let m = skip_ws_spec(s, k);
    if m1.len() > 1 {
        lemma_members_end_det(s, skip_ws_spec(s, m + 1), d, m1.drop_first(), m2.drop_first());
        assert(m1 =~= seq![m1[0]] + m1.drop_first());
        assert(m2 =~= seq![m2[0]] + m2.drop_first());
    } else {
        assert(m1 =~= m2);
    }
}

pub proof fn lemma_items_append(s: Seq<u8>, j0: int, d: nat, p: Seq<JsonS>, r: Seq<JsonS>)
    requires
        items_pre(s, j0, d, p) is Some,
        r.len() > 0,
    ensures
        items_end(s, j0, d, p + r) == items_end(s, items_pre(s, j0, d, p)->Some_0, d, r),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(p + r =~= r);
    } else {
        let k = value_end(s, j0, d, p[0])->Some_0;
        let m = skip_ws_spec(s, k);
        assert((p + r)[0] == p[0]);
        assert((p + r).drop_first() =~= p.drop_first() + r);
        lemma_items_append(s, skip_ws_spec(s, m + 1), d, p.drop_first(), r);
    }
}

pub proof fn lemma_items_pre_push(s: Seq<u8>, j0: int, d: nat, p: Seq<JsonS>, v: JsonS)
    requires
        items_pre(s, j0, d, p) is Some,
    ensures
        items_pre(s, j0, d, p.push(v)) == ({
            let j = items_pre(s, j0, d, p)->Some_0;
            match value_end(s, j, d, v) {
                None => None,
                Some(k) => {
                    let m = skip_ws_spec(s, k);
                    if m < s.len() && s[m] == b',' {
                        Some(skip_ws_spec(s, m + 1))
                    } else {
                        None
                    }
                },
            }
        }),
    decreases p.len(),
{
    if p.len() == 0 {
        let w = p.push(v);
        assert(w.len() == 1 && w[0] == v);
        assert(w.drop_first() =~= Seq::<JsonS>::empty());
        match value_end(s, j0, d, v) {
            Some(k) => {
                let m = skip_ws_spec(s, k);
                assert(items_pre(s, skip_ws_spec(s, m + 1), d, w.drop_first()) == Some(skip_ws_spec(s, m + 1)));
            },
            None => {},
        }
    } else {
        let k = value_end(s, j0, d, p[0])->Some_0;
        let m = skip_ws_spec(s, k);
        assert(p.push(v)[0] == p[0]);
        assert(p.push(v).drop_first() =~= p.drop_first().push(v));
        lemma_items_pre_push(s, skip_ws_spec(s, m + 1), d, p.drop_first(), v);
    }
}

// 途中まで読んだ並びは、成功するどの並びの接頭辞でもある
pub proof fn lemma_items_prefix(s: Seq<u8>, j0: int, d: nat, p: Seq<JsonS>, l: Seq<JsonS>)
    requires
        items_pre(s, j0, d, p) is Some,
        items_end(s, j0, d, l) is Some,
    ensures
        l.len() > p.len(),
        l.subrange(0, p.len() as int) == p,
    decreases p.len(),
{
    if p.len() == 0 {
        assert(l.subrange(0, 0) =~= p);
    } else {
        lemma_value_end_det(s, j0, d, p[0], l[0]);
        let k = value_end(s, j0, d, p[0])->Some_0;
        let m = skip_ws_spec(s, k);
        lemma_items_prefix(s, skip_ws_spec(s, m + 1), d, p.drop_first(), l.drop_first());
        assert(l.subrange(0, p.len() as int) =~= p) by {
            assert forall|x: int| 0 <= x < p.len() implies l[x] == p[x] by {
                if x > 0 {
                    assert(l.drop_first().subrange(0, p.drop_first().len() as int)[x - 1] == p.drop_first()[x - 1]);
                }
            }
        }
    }
}

// 現在位置 j 以降の並びがすべて失敗するなら、全体も失敗する
pub proof fn lemma_json_items_fail(s: Seq<u8>, j0: int, d: nat, p: Seq<JsonS>)
    requires
        items_pre(s, j0, d, p) is Some,
        forall|r: Seq<JsonS>|
            r.len() > 0 ==> #[trigger] items_end(s, items_pre(s, j0, d, p)->Some_0, d, r) is None,
    ensures
        forall|l: Seq<JsonS>| #[trigger] items_end(s, j0, d, l) is None,
{
    assert forall|l: Seq<JsonS>| #[trigger] items_end(s, j0, d, l) is None by {
        if items_end(s, j0, d, l) is Some {
            lemma_items_prefix(s, j0, d, p, l);
            let r = l.subrange(p.len() as int, l.len() as int);
            assert(l =~= p + r);
            lemma_items_append(s, j0, d, p, r);
        }
    }
}

// 値 v を読んだ後の区切りが , でも ] でもなければ失敗
pub proof fn lemma_items_step_fail(s: Seq<u8>, j: int, d: nat, v: JsonS)
    requires
        value_end(s, j, d, v) is Some,
        ({
            let m = skip_ws_spec(s, value_end(s, j, d, v)->Some_0);
            !(m < s.len() && (s[m] == b',' || s[m] == b']'))
        }),
    ensures
        forall|r: Seq<JsonS>| r.len() > 0 ==> #[trigger] items_end(s, j, d, r) is None,
{
    assert forall|r: Seq<JsonS>| r.len() > 0 implies #[trigger] items_end(s, j, d, r) is None by {
        if value_end(s, j, d, r[0]) is Some {
            lemma_value_end_det(s, j, d, v, r[0]);
        }
    }
}

pub proof fn lemma_members_append(
    s: Seq<u8>,
    j0: int,
    d: nat,
    p: Seq<(Seq<u8>, JsonS)>,
    r: Seq<(Seq<u8>, JsonS)>,
)
    requires
        members_pre(s, j0, d, p) is Some,
        r.len() > 0,
    ensures
        members_end(s, j0, d, p + r) == members_end(s, members_pre(s, j0, d, p)->Some_0, d, r),
    decreases p.len(),
{
    if p.len() == 0 {
        assert(p + r =~= r);
    } else {
        let q = member_value_start(s, j0, p[0].0)->Some_0;
        let k = value_end(s, q, d, p[0].1)->Some_0;
        let m = skip_ws_spec(s, k);
        assert((p + r)[0] == p[0]);
        assert((p + r).drop_first() =~= p.drop_first() + r);
        lemma_members_append(s, skip_ws_spec(s, m + 1), d, p.drop_first(), r);
    }
}

pub proof fn lemma_members_pre_push(s: Seq<u8>, j0: int, d: nat, p: Seq<(Seq<u8>, JsonS)>, x: (Seq<u8>, JsonS))
    requires
        members_pre(s, j0, d, p) is Some,
    ensures
        members_pre(s, j0, d, p.push(x)) == ({
            let j = members_pre(s, j0, d, p)->Some_0;
            match member_value_start(s, j, x.0) {
                None => None,
                Some(q) => match value_end(s, q, d, x.1) {
                    None => None,
                    Some(k) => {
                        let m = skip_ws_spec(s, k);
                        if m < s.len() && s[m] == b',' {
                            Some(skip_ws_spec(s, m + 1))
                        } else {
                            None
                        }
                    },
                },
            }
        }),
    decreases p.len(),
{
    if p.len() == 0 {
        let w = p.push(x);
        assert(w.len() == 1 && w[0] == x);
        assert(w.drop_first() =~= Seq::<(Seq<u8>, JsonS)>::empty());
        match member_value_start(s, j0, x.0) {
            Some(q) => match value_end(s, q, d, x.1) {
                Some(k) => {
                    let m = skip_ws_spec(s, k);
                    assert(members_pre(s, skip_ws_spec(s, m + 1), d, w.drop_first()) == Some(skip_ws_spec(s, m + 1)));
                },
                None => {},
            },
            None => {},
        }
    } else {
        let q = member_value_start(s, j0, p[0].0)->Some_0;
        let k = value_end(s, q, d, p[0].1)->Some_0;
        let m = skip_ws_spec(s, k);
        assert(p.push(x)[0] == p[0]);
        assert(p.push(x).drop_first() =~= p.drop_first().push(x));
        lemma_members_pre_push(s, skip_ws_spec(s, m + 1), d, p.drop_first(), x);
    }
}

pub proof fn lemma_members_prefix(
    s: Seq<u8>,
    j0: int,
    d: nat,
    p: Seq<(Seq<u8>, JsonS)>,
    l: Seq<(Seq<u8>, JsonS)>,
)
    requires
        members_pre(s, j0, d, p) is Some,
        members_end(s, j0, d, l) is Some,
    ensures
        l.len() > p.len(),
        l.subrange(0, p.len() as int) == p,
    decreases p.len(),
{
    if p.len() == 0 {
        assert(l.subrange(0, 0) =~= p);
    } else {
        let q = member_value_start(s, j0, p[0].0)->Some_0;
        assert(l[0].0 == p[0].0);
        lemma_value_end_det(s, q, d, p[0].1, l[0].1);
        assert(l[0] == p[0]);
        let k = value_end(s, q, d, p[0].1)->Some_0;
        let m = skip_ws_spec(s, k);
        lemma_members_prefix(s, skip_ws_spec(s, m + 1), d, p.drop_first(), l.drop_first());
        assert(l.subrange(0, p.len() as int) =~= p) by {
            assert forall|x: int| 0 <= x < p.len() implies l[x] == p[x] by {
                if x > 0 {
                    assert(l.drop_first().subrange(0, p.drop_first().len() as int)[x - 1] == p.drop_first()[x - 1]);
                }
            }
        }
    }
}

pub proof fn lemma_members_fail(s: Seq<u8>, j0: int, d: nat, p: Seq<(Seq<u8>, JsonS)>)
    requires
        members_pre(s, j0, d, p) is Some,
        forall|r: Seq<(Seq<u8>, JsonS)>|
            r.len() > 0 ==> #[trigger] members_end(s, members_pre(s, j0, d, p)->Some_0, d, r) is None,
    ensures
        forall|l: Seq<(Seq<u8>, JsonS)>| #[trigger] members_end(s, j0, d, l) is None,
{
    assert forall|l: Seq<(Seq<u8>, JsonS)>| #[trigger] members_end(s, j0, d, l) is None by {
        if members_end(s, j0, d, l) is Some {
            lemma_members_prefix(s, j0, d, p, l);
            let r = l.subrange(p.len() as int, l.len() as int);
            assert(l =~= p + r);
            lemma_members_append(s, j0, d, p, r);
        }
    }
}

// 木は配列の拡張で変わらない
pub proof fn lemma_tree_extends(a: Seq<JsonNode>, b: Seq<JsonNode>, id: int)
    requires
        extends(a, b),
        0 <= id < b.len(),
    ensures
        tree(a, id) == tree(b, id),
    decreases id,
{
    assert(a[id] == b[id]) by {
        assert(a.subrange(0, b.len() as int)[id] == a[id]);
    }
    match b[id] {
        JsonNode::Array(items) => {
            assert forall|k: int| 0 <= k < items.len() && 0 <= items[k] < id implies tree(a, items[k] as int)
                == tree(b, items[k] as int) by {
                lemma_tree_extends(a, b, items[k] as int);
            }
            assert(tree(a, id)->Array_0 =~= tree(b, id)->Array_0);
        },
        JsonNode::Object(ms) => {
            assert forall|k: int| 0 <= k < ms.len() && 0 <= ms[k].value < id implies tree(a, ms[k].value as int)
                == tree(b, ms[k].value as int) by {
                lemma_tree_extends(a, b, ms[k].value as int);
            }
            assert(tree(a, id)->Object_0 =~= tree(b, id)->Object_0);
        },
        _ => {},
    }
}

pub proof fn lemma_trees_extends(a: Seq<JsonNode>, b: Seq<JsonNode>, items: Seq<usize>)
    requires
        extends(a, b),
        forall|k: int| 0 <= k < items.len() ==> items[k] < b.len(),
    ensures
        trees(a, items) == trees(b, items),
{
    assert forall|k: int| 0 <= k < items.len() implies trees(a, items)[k] == trees(b, items)[k] by {
        lemma_tree_extends(a, b, items[k] as int);
    }
    assert(trees(a, items) =~= trees(b, items));
}

pub proof fn lemma_member_trees_extends(a: Seq<JsonNode>, b: Seq<JsonNode>, ms: Seq<Member>)
    requires
        extends(a, b),
        forall|k: int| 0 <= k < ms.len() ==> ms[k].value < b.len(),
    ensures
        member_trees(a, ms) == member_trees(b, ms),
{
    assert forall|k: int| 0 <= k < ms.len() implies member_trees(a, ms)[k] == member_trees(b, ms)[k] by {
        lemma_tree_extends(a, b, ms[k].value as int);
    }
    assert(member_trees(a, ms) =~= member_trees(b, ms));
}

pub proof fn lemma_extends_trans_all(b: Seq<JsonNode>, c: Seq<JsonNode>)
    requires
        extends(b, c),
    ensures
        forall|a: Seq<JsonNode>| #[trigger] extends(a, b) ==> extends(a, c),
{
    assert forall|a: Seq<JsonNode>| #[trigger] extends(a, b) implies extends(a, c) by {
        lemma_extends_trans(a, b, c);
    }
}

pub proof fn lemma_extends_trans(a: Seq<JsonNode>, b: Seq<JsonNode>, c: Seq<JsonNode>)
    requires
        extends(a, b),
        extends(b, c),
    ensures
        extends(a, c),
{
    assert(a.subrange(0, c.len() as int) =~= c) by {
        assert forall|x: int| 0 <= x < c.len() implies a[x] == c[x] by {
            assert(a.subrange(0, b.len() as int)[x] == a[x]);
            assert(b.subrange(0, c.len() as int)[x] == b[x]);
        }
    }
}

pub proof fn lemma_ve_oob(s: Seq<u8>, i: int, d: nat)
    requires
        !(0 <= i < s.len()),
    ensures
        forall|v: JsonS| #[trigger] value_end(s, i, d, v) is None,
{
}

pub proof fn lemma_ve_depth0(s: Seq<u8>, i: int)
    requires
        0 <= i < s.len(),
        s[i] == b'[' || s[i] == b'{',
    ensures
        forall|v: JsonS| #[trigger] value_end(s, i, 0, v) is None,
{
    assert forall|v: JsonS| #[trigger] value_end(s, i, 0, v) is None by {
        if value_end(s, i, 0, v) is Some {
            lemma_value_end_first(s, i, 0, v);
        }
    }
}

pub proof fn lemma_ve_array(s: Seq<u8>, i: int, d: nat, items: Seq<JsonS>)
    requires
        0 <= i < s.len(),
        s[i] == b'[',
        d > 0,
    ensures
        value_end(s, i, d, JsonS::Array(items)) == ({
            let j = skip_ws_spec(s, i + 1);
            if items.len() == 0 {
                if j < s.len() && s[j] == b']' {
                    Some(j + 1)
                } else {
                    None
                }
            } else {
                items_end(s, j, (d - 1) as nat, items)
            }
        }),
{
}

pub proof fn lemma_ve_object(s: Seq<u8>, i: int, d: nat, ms: Seq<(Seq<u8>, JsonS)>)
    requires
        0 <= i < s.len(),
        s[i] == b'{',
        d > 0,
    ensures
        value_end(s, i, d, JsonS::Object(ms)) == ({
            let j = skip_ws_spec(s, i + 1);
            if ms.len() == 0 {
                if j < s.len() && s[j] == b'}' {
                    Some(j + 1)
                } else {
                    None
                }
            } else {
                members_end(s, j, (d - 1) as nat, ms)
            }
        }),
{
}

// ノードを 1 つ追加したときの不変条件と木
pub proof fn lemma_push_node(a: Seq<JsonNode>, b: Seq<JsonNode>, n: JsonNode)
    requires
        json_nodes_ok(a),
        b == a.push(n),
        match n {
            JsonNode::Array(items) => forall|k: int| 0 <= k < items.len() ==> items[k] < a.len(),
            JsonNode::Object(ms) => forall|k: int| 0 <= k < ms.len() ==> ms[k].value < a.len(),
            JsonNode::Number(x) => number_wf(x@),
            _ => true,
        },
    ensures
        json_nodes_ok(b),
        extends(b, a),
        is_scalar(n) ==> tree(b, a.len() as int) == node_scalar(n),
{
    assert(b.subrange(0, a.len() as int) =~= a);
    assert forall|i: int| 0 <= i < b.len() implies match #[trigger] b[i] {
        JsonNode::Array(items) => forall|k: int| 0 <= k < items.len() ==> items[k] < i,
        JsonNode::Object(ms) => forall|k: int| 0 <= k < ms.len() ==> ms[k].value < i,
        _ => true,
    } by {
        if i < a.len() {
            assert(b[i] == a[i]);
        }
    }
    assert forall|i: int| 0 <= i < b.len() implies match #[trigger] b[i] {
        JsonNode::Number(x) => number_wf(x@),
        _ => true,
    } by {
        if i < a.len() {
            assert(b[i] == a[i]);
        }
    }
}

pub proof fn lemma_items_none_at(s: Seq<u8>, j: int, d: nat)
    requires
        forall|v: JsonS| #[trigger] value_end(s, j, d, v) is None,
    ensures
        forall|r: Seq<JsonS>| r.len() > 0 ==> #[trigger] items_end(s, j, d, r) is None,
{
    assert forall|r: Seq<JsonS>| r.len() > 0 implies #[trigger] items_end(s, j, d, r) is None by {
        assert(value_end(s, j, d, r[0]) is None);
    }
}

pub proof fn lemma_array_fail(s: Seq<u8>, i: int, d: nat)
    requires
        0 <= i < s.len(),
        s[i] == b'[',
        d > 0,
        ({
            let j0 = skip_ws_spec(s, i + 1);
            !(j0 < s.len() && s[j0] == b']')
        }),
        forall|l: Seq<JsonS>| #[trigger] items_end(s, skip_ws_spec(s, i + 1), (d - 1) as nat, l) is None,
    ensures
        forall|v: JsonS| #[trigger] value_end(s, i, d, v) is None,
{
    assert forall|v: JsonS| #[trigger] value_end(s, i, d, v) is None by {
        if value_end(s, i, d, v) is Some {
            lemma_value_end_first(s, i, d, v);
        }
        if v is Array {
            let it = v->Array_0;
            assert(items_end(s, skip_ws_spec(s, i + 1), (d - 1) as nat, it) is None);
        }
    }
}

pub proof fn lemma_object_fail(s: Seq<u8>, i: int, d: nat)
    requires
        0 <= i < s.len(),
        s[i] == b'{',
        d > 0,
        ({
            let j0 = skip_ws_spec(s, i + 1);
            !(j0 < s.len() && s[j0] == b'}')
        }),
        forall|l: Seq<(Seq<u8>, JsonS)>| #[trigger] members_end(s, skip_ws_spec(s, i + 1), (d - 1) as nat, l) is None,
    ensures
        forall|v: JsonS| #[trigger] value_end(s, i, d, v) is None,
{
    assert forall|v: JsonS| #[trigger] value_end(s, i, d, v) is None by {
        if value_end(s, i, d, v) is Some {
            lemma_value_end_first(s, i, d, v);
        }
        if v is Object {
            let ms = v->Object_0;
            assert(members_end(s, skip_ws_spec(s, i + 1), (d - 1) as nat, ms) is None);
        }
    }
}

pub proof fn lemma_member_start_fail(s: Seq<u8>, j: int, d: nat)
    requires
        forall|key: Seq<u8>| #[trigger] member_value_start(s, j, key) is None,
    ensures
        forall|r: Seq<(Seq<u8>, JsonS)>| r.len() > 0 ==> #[trigger] members_end(s, j, d, r) is None,
{
    assert forall|r: Seq<(Seq<u8>, JsonS)>| r.len() > 0 implies #[trigger] members_end(s, j, d, r) is None by {
        assert(member_value_start(s, j, r[0].0) is None);
    }
}

pub proof fn lemma_member_value_fail(s: Seq<u8>, j: int, d: nat, key: Seq<u8>)
    requires
        member_value_start(s, j, key) is Some,
        forall|v: JsonS| #[trigger] value_end(s, member_value_start(s, j, key)->Some_0, d, v) is None,
    ensures
        forall|r: Seq<(Seq<u8>, JsonS)>| r.len() > 0 ==> #[trigger] members_end(s, j, d, r) is None,
{
    assert forall|r: Seq<(Seq<u8>, JsonS)>| r.len() > 0 implies #[trigger] members_end(s, j, d, r) is None by {
        if member_value_start(s, j, r[0].0) is Some {
            assert(r[0].0 == key);
            assert(value_end(s, member_value_start(s, j, key)->Some_0, d, r[0].1) is None);
        }
    }
}

pub proof fn lemma_members_step_fail(s: Seq<u8>, j: int, d: nat, key: Seq<u8>, v: JsonS)
    requires
        member_value_start(s, j, key) is Some,
        value_end(s, member_value_start(s, j, key)->Some_0, d, v) is Some,
        ({
            let m = skip_ws_spec(s, value_end(s, member_value_start(s, j, key)->Some_0, d, v)->Some_0);
            !(m < s.len() && (s[m] == b',' || s[m] == b'}'))
        }),
    ensures
        forall|r: Seq<(Seq<u8>, JsonS)>| r.len() > 0 ==> #[trigger] members_end(s, j, d, r) is None,
{
    let q = member_value_start(s, j, key)->Some_0;
    assert forall|r: Seq<(Seq<u8>, JsonS)>| r.len() > 0 implies #[trigger] members_end(s, j, d, r) is None by {
        if member_value_start(s, j, r[0].0) is Some {
            assert(r[0].0 == key);
            if value_end(s, q, d, r[0].1) is Some {
                lemma_value_end_det(s, q, d, v, r[0].1);
            }
        }
    }
}

#[verifier::spinoff_prover]
fn parse_value(s: &[u8], i: usize, depth: usize, nodes: &mut Vec<JsonNode>) -> (r: Option<(usize, usize)>)
    requires
        json_nodes_ok(old(nodes)@),
    ensures
        json_nodes_ok(final(nodes)@),
        extends(final(nodes)@, old(nodes)@),
        match r {
            Some((id, k)) => id < final(nodes)@.len() && i < k <= s.len() && value_end(
                s@,
                i as int,
                depth as nat,
                tree(final(nodes)@, id as int),
            ) == Some(k as int),
            None => forall|v: JsonS| #[trigger] value_end(s@, i as int, depth as nat, v) is None,
        },
    decreases depth,
{
    let ghost n0 = nodes@;
    proof {
        assert(nodes@.subrange(0, nodes@.len() as int) =~= nodes@);
    }
    if i >= s.len() {
        proof {
            lemma_ve_oob(s@, i as int, depth as nat);
        }
        return None;
    }
    let c = s[i];
    if c == b'[' {
        if depth == 0 {
            proof {
                lemma_ve_depth0(s@, i as int);
            }
            return None;
        }
        let ghost d1 = (depth - 1) as nat;
        let mut items: Vec<usize> = Vec::new();
        let mut j = skip_ws(s, i + 1);
        let ghost j0 = j as int;
        if j < s.len() && s[j] == b']' {
            let ghost it = items;
            nodes.push(JsonNode::Array(items));
            proof {
                lemma_push_node(n0, nodes@, JsonNode::Array(it));
                assert(tree(nodes@, n0.len() as int)->Array_0 =~= Seq::<JsonS>::empty());
                lemma_ve_array(s@, i as int, depth as nat, Seq::<JsonS>::empty());
            }
            return Some((nodes.len() - 1, j + 1));
        }
        assert(items_pre(s@, j0, d1, trees(nodes@, items@)) == Some(j0)) by {
            assert(trees(nodes@, items@) =~= Seq::<JsonS>::empty());
        }
        loop
            invariant
                i < s.len(),
                s@[i as int] == b'[',
                depth > 0,
                d1 == depth - 1,
                j0 == skip_ws_spec(s@, i + 1),
                !(j0 < s.len() && s@[j0] == b']'),
                i < j <= s.len(),
                n0 == old(nodes)@,
                json_nodes_ok(nodes@),
                extends(nodes@, n0),
                forall|k: int| 0 <= k < items@.len() ==> items@[k] < nodes@.len(),
                items_pre(s@, j0, d1, trees(nodes@, items@)) == Some(j as int),
            decreases s.len() - j,
        {
            let ghost nb = nodes@;
            let ghost p = trees(nb, items@);
            let ghost jb = j as int;
            let ghost mut v: JsonS = JsonS::Null;
            proof {
                if forall|v: JsonS| #[trigger] value_end(s@, j as int, d1, v) is None {
                    lemma_items_none_at(s@, j as int, d1);
                    lemma_json_items_fail(s@, j0, d1, p);
                    lemma_array_fail(s@, i as int, depth as nat);
                }
                lemma_extends_trans_all(nb, n0);
            }
            match parse_value(s, j, depth - 1, nodes) {
                None => return None,
                Some((id, k)) => {
                    proof {
                        lemma_trees_extends(nodes@, nb, items@);
                        lemma_extends_trans(nodes@, nb, n0);
                        lemma_items_pre_push(s@, j0, d1, p, tree(nodes@, id as int));
                        v = tree(nodes@, id as int);
                    }
                    items.push(id);
                    j = skip_ws(s, k);
                    proof {
                        assert(trees(nodes@, items@) =~= p.push(v));
                    }
                }
            }
            if j >= s.len() {
                proof {
                    lemma_items_step_fail(s@, jb, d1, v);
                    lemma_json_items_fail(s@, j0, d1, p);
                    lemma_array_fail(s@, i as int, depth as nat);
                }
                return None;
            }
            if s[j] == b',' {
                j = skip_ws(s, j + 1);
            } else if s[j] == b']' {
                let ghost it = items;
                let ghost nb2 = nodes@;
                nodes.push(JsonNode::Array(items));
                proof {
                    lemma_push_node(nb2, nodes@, JsonNode::Array(it));
                    lemma_extends_trans(nodes@, nb2, n0);
                    lemma_trees_extends(nodes@, nb2, it@);
                    assert(tree(nodes@, nb2.len() as int)->Array_0 =~= trees(nb2, it@));
                    assert(seq![v][0] == v);
                    assert(items_end(s@, jb, d1, seq![v]) == Some(j as int + 1));
                    lemma_items_append(s@, j0, d1, p, seq![v]);
                    assert(p + seq![v] =~= p.push(v));
                    lemma_ve_array(s@, i as int, depth as nat, p.push(v));
                }
                return Some((nodes.len() - 1, j + 1));
            } else {
                proof {
                    lemma_items_step_fail(s@, jb, d1, v);
                    lemma_json_items_fail(s@, j0, d1, p);
                    lemma_array_fail(s@, i as int, depth as nat);
                }
                return None;
            }
        }
    } else if c == b'{' {
        if depth == 0 {
            proof {
                lemma_ve_depth0(s@, i as int);
            }
            return None;
        }
        let ghost d1 = (depth - 1) as nat;
        let mut members: Vec<Member> = Vec::new();
        let mut j = skip_ws(s, i + 1);
        let ghost j0 = j as int;
        if j < s.len() && s[j] == b'}' {
            let ghost ms = members;
            nodes.push(JsonNode::Object(members));
            proof {
                lemma_push_node(n0, nodes@, JsonNode::Object(ms));
                assert(tree(nodes@, n0.len() as int)->Object_0 =~= Seq::<(Seq<u8>, JsonS)>::empty());
                lemma_ve_object(s@, i as int, depth as nat, Seq::<(Seq<u8>, JsonS)>::empty());
            }
            return Some((nodes.len() - 1, j + 1));
        }
        assert(members_pre(s@, j0, d1, member_trees(nodes@, members@)) == Some(j0)) by {
            assert(member_trees(nodes@, members@) =~= Seq::<(Seq<u8>, JsonS)>::empty());
        }
        loop
            invariant
                i < s.len(),
                s@[i as int] == b'{',
                depth > 0,
                d1 == depth - 1,
                j0 == skip_ws_spec(s@, i + 1),
                !(j0 < s.len() && s@[j0] == b'}'),
                i < j <= s.len(),
                n0 == old(nodes)@,
                json_nodes_ok(nodes@),
                extends(nodes@, n0),
                forall|k: int| 0 <= k < members@.len() ==> members@[k].value < nodes@.len(),
                members_pre(s@, j0, d1, member_trees(nodes@, members@)) == Some(j as int),
            decreases s.len() - j,
        {
            let ghost nb = nodes@;
            let ghost p = member_trees(nb, members@);
            let ghost jb = j as int;
            if j >= s.len() || s[j] != b'"' {
                proof {
                    lemma_member_start_fail(s@, jb, d1);
                    lemma_members_fail(s@, j0, d1, p);
                    lemma_object_fail(s@, i as int, depth as nat);
                }
                return None;
            }
            proof {
                if forall|key: Seq<u8>| #[trigger] member_value_start(s@, jb, key) is None {
                    lemma_member_start_fail(s@, jb, d1);
                    lemma_members_fail(s@, j0, d1, p);
                    lemma_object_fail(s@, i as int, depth as nat);
                }
            }
            let key = match parse_string(s, j + 1) {
                None => return None,
                Some((k, e)) => {
                    j = skip_ws(s, e);
                    k
                }
            };
            if j >= s.len() || s[j] != b':' {
                proof {
                    lemma_member_start_fail(s@, jb, d1);
                    lemma_members_fail(s@, j0, d1, p);
                    lemma_object_fail(s@, i as int, depth as nat);
                }
                return None;
            }
            j = skip_ws(s, j + 1);
            assert(member_value_start(s@, jb, key@) == Some(j as int));
            let ghost jv = j as int;
            let ghost mut v: JsonS = JsonS::Null;
            let ghost kk = key@;
            proof {
                if forall|v: JsonS| #[trigger] value_end(s@, j as int, d1, v) is None {
                    lemma_member_value_fail(s@, jb, d1, key@);
                    lemma_members_fail(s@, j0, d1, p);
                    lemma_object_fail(s@, i as int, depth as nat);
                }
                lemma_extends_trans_all(nb, n0);
            }
            match parse_value(s, j, depth - 1, nodes) {
                None => return None,
                Some((id, k)) => {
                    proof {
                        lemma_member_trees_extends(nodes@, nb, members@);
                        lemma_extends_trans(nodes@, nb, n0);
                        lemma_members_pre_push(s@, j0, d1, p, (key@, tree(nodes@, id as int)));
                        v = tree(nodes@, id as int);
                    }
                    members.push(Member { key, value: id });
                    j = skip_ws(s, k);
                    proof {
                        assert(member_trees(nodes@, members@) =~= p.push((kk, v)));
                    }
                }
            }
            if j >= s.len() {
                proof {
                    lemma_members_step_fail(s@, jb, d1, kk, v);
                    lemma_members_fail(s@, j0, d1, p);
                    lemma_object_fail(s@, i as int, depth as nat);
                }
                return None;
            }
            if s[j] == b',' {
                j = skip_ws(s, j + 1);
            } else if s[j] == b'}' {
                let ghost ms = members;
                let ghost nb2 = nodes@;
                nodes.push(JsonNode::Object(members));
                proof {
                    lemma_push_node(nb2, nodes@, JsonNode::Object(ms));
                    lemma_extends_trans(nodes@, nb2, n0);
                    lemma_member_trees_extends(nodes@, nb2, ms@);
                    assert(tree(nodes@, nb2.len() as int)->Object_0 =~= member_trees(nb2, ms@));
                    assert(seq![(kk, v)][0] == (kk, v));
                    assert(members_end(s@, jb, d1, seq![(kk, v)]) == Some(j as int + 1));
                    lemma_members_append(s@, j0, d1, p, seq![(kk, v)]);
                    assert(p + seq![(kk, v)] =~= p.push((kk, v)));
                    lemma_ve_object(s@, i as int, depth as nat, p.push((kk, v)));
                }
                return Some((nodes.len() - 1, j + 1));
            } else {
                proof {
                    lemma_members_step_fail(s@, jb, d1, kk, v);
                    lemma_members_fail(s@, j0, d1, p);
                    lemma_object_fail(s@, i as int, depth as nat);
                }
                return None;
            }
        }
    } else {
        match parse_scalar(s, i) {
            None => None,
            Some((node, j)) => {
                let ghost nd = node;
                nodes.push(node);
                proof {
                    lemma_push_node(n0, nodes@, nd);
                }
                Some((nodes.len() - 1, j))
            }
        }
    }
}

pub open spec fn doc_wf(doc: JsonDoc) -> bool {
    children_lt(doc.nodes@) && numbers_wf(doc.nodes@) && doc.root < doc.nodes.len()
}

// value(s, i, d): 構文解析結果（一意性は lemma_value_end_det）
pub open spec fn json_value(s: Seq<u8>, i: int, d: nat) -> Option<(JsonS, int)> {
    if exists|v: JsonS| #[trigger] value_end(s, i, d, v) is Some {
        let v = choose|v: JsonS| #[trigger] value_end(s, i, d, v) is Some;
        Some((v, value_end(s, i, d, v)->Some_0))
    } else {
        None
    }
}

// RFC 8259 §2: JSON テキスト
pub open spec fn json_text(s: Seq<u8>) -> Option<JsonS> {
    let i0 = if s.len() >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF { 3int } else { 0int };
    let j = skip_ws_spec(s, i0);
    match json_value(s, j, 128) {
        Some((v, k)) => if skip_ws_spec(s, k) == s.len() {
            Some(v)
        } else {
            None
        },
        None => None,
    }
}

// J1
pub fn parse_json(s: &[u8]) -> (r: Option<JsonDoc>)
    ensures
        match r {
            Some(doc) => json_text(s@) == Some(tree(doc.nodes@, doc.root as int)) && doc_wf(doc),
            None => json_text(s@) is None,
        },
{
    let mut i = 0;
    if s.len() >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF {
        i = 3;
    }
    i = skip_ws(s, i);
    let mut nodes: Vec<JsonNode> = Vec::new();
    proof {
        assert(json_nodes_ok(nodes@));
    }
    proof {
        assert((forall|v: JsonS| #[trigger] value_end(s@, i as int, 128, v) is None) ==> !exists|v: JsonS|
            #[trigger] value_end(s@, i as int, 128, v) is Some);
    }
    match parse_value(s, i, MAX_DEPTH, &mut nodes) {
        None => None,
        Some((root, j)) => {
            proof {
                let v = tree(nodes@, root as int);
                assert(value_end(s@, i as int, 128, v) is Some);
                let w = choose|w: JsonS| #[trigger] value_end(s@, i as int, 128, w) is Some;
                lemma_value_end_det(s@, i as int, 128, v, w);
            }
            if skip_ws(s, j) == s.len() {
                Some(JsonDoc { nodes, root })
            } else {
                None
            }
        }
    }
}

} // verus!
