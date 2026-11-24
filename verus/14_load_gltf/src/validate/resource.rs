use crate::model::*;
use crate::validate::mesh::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::json::number::*;

verus! {

// URI（iri-reference の検査する部分集合）
pub open spec fn alpha(b: u8) -> bool {
    (b'A' <= b <= b'Z') || (b'a' <= b <= b'z')
}

pub open spec fn b64char(b: u8) -> bool {
    alpha(b) || digit(b) || b == b'+' || b == b'/'
}

fn base64_char(b: u8) -> (r: bool)
    ensures
        r == b64char(b),
{
    (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'+' || b == b'/'
}

pub open spec fn hexd(b: u8) -> bool {
    (b'0' <= b <= b'9') || (b'A' <= b <= b'F') || (b'a' <= b <= b'f')
}

fn hex_digit(b: u8) -> (r: bool)
    ensures
        r == hexd(b),
{
    (b >= b'0' && b <= b'9') || (b >= b'A' && b <= b'F') || (b >= b'a' && b <= b'f')
}

fn range_eq(s: &Vec<u8>, start: usize, end: usize, lit: &[u8]) -> (r: bool)
    requires
        start <= end <= s.len(),
    ensures
        r == (s@.subrange(start as int, end as int) == lit@),
{
    if end - start != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < lit.len()
        invariant
            start <= end <= s.len(),
            end - start == lit.len(),
            0 <= i <= lit.len(),
            forall|k: int| 0 <= k < i ==> s@[start + k] == lit@[k],
        decreases lit.len() - i,
    {
        if s[start + i] != lit[i] {
            assert(s@.subrange(start as int, end as int)[i as int] == s@[start + i]);
            return false;
        }
        i += 1;
    }
    assert(s@.subrange(start as int, end as int) =~= lit@);
    true
}

fn is_alpha(b: u8) -> (r: bool)
    ensures
        r == alpha(b),
{
    (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z')
}

// u[c] が最初の ':' で、それより前に '/', '?', '#' がない
pub open spec fn scheme_colon(u: Seq<u8>, c: int) -> bool {
    0 <= c < u.len() && u[c] == b':' && forall|k: int|
        0 <= k < c ==> !(#[trigger] u[k] == b':' || u[k] == b'/' || u[k] == b'?' || u[k] == b'#')
}

fn find_scheme_end(uri: &Vec<u8>) -> (r: usize)
    ensures
        r <= uri.len(),
        r < uri.len() ==> scheme_colon(uri@, r as int),
        r == uri.len() ==> forall|c: int| !#[trigger] scheme_colon(uri@, c),
{
    let mut i = 0;
    while i < uri.len()
        invariant
            0 <= i <= uri.len(),
            forall|k: int| 0 <= k < i ==> !(#[trigger] uri@[k] == b':' || uri@[k] == b'/' || uri@[k] == b'?' || uri@[k] == b'#'),
        decreases uri.len() - i,
    {
        let c = uri[i];
        if c == b':' {
            return i;
        }
        if c == b'/' || c == b'?' || c == b'#' {
            proof {
                assert forall|x: int| !#[trigger] scheme_colon(uri@, x) by {
                    if scheme_colon(uri@, x) && x > i {
                        assert(!(uri@[i as int] == b':' || uri@[i as int] == b'/' || uri@[i as int] == b'?' || uri@[i as int] == b'#'));
                    }
                }
            }
            return uri.len();
        }
        i += 1;
    }
    uri.len()
}

pub open spec fn scheme_char(b: u8) -> bool {
    alpha(b) || digit(b) || b == b'+' || b == b'-' || b == b'.'
}

fn scheme_chars_ok(uri: &Vec<u8>, end: usize) -> (r: bool)
    requires
        end <= uri.len(),
    ensures
        r == (forall|k: int| 1 <= k < end ==> scheme_char(#[trigger] uri@[k])),
{
    let mut k = 1;
    while k < end
        invariant
            end <= uri.len(),
            1 <= k,
            k <= end || end == 0,
            forall|x: int| 1 <= x < k ==> scheme_char(#[trigger] uri@[x]),
        decreases end - k,
    {
        let c = uri[k];
        if !(is_alpha(c) || (c >= b'0' && c <= b'9') || c == b'+' || c == b'-' || c == b'.') {
            return false;
        }
        k += 1;
    }
    true
}

pub open spec fn forbidden(b: u8) -> bool {
    b <= 0x20 || b == 0x7F || b == b'"' || b == b'<' || b == b'>' || b == b'\\' || b == b'^' || b == b'`' || b == b'{'
        || b == b'|' || b == b'}'
}

fn uri_chars_ok(uri: &Vec<u8>) -> (r: bool)
    ensures
        r == ({
            let u = uri@;
            &&& forall|k: int| 0 <= k < u.len() ==> !forbidden(#[trigger] u[k])
            &&& forall|k1: int, k2: int| 0 <= k1 < k2 < u.len() && #[trigger] u[k1] == b'#' ==> #[trigger] u[k2] != b'#'
            &&& forall|k: int| 0 <= k < u.len() && #[trigger] u[k] == b'%' ==> k + 2 < u.len() && hexd(u[k + 1]) && hexd(u[k + 2])
        }),
{
    let mut fragment = false;
    let mut i = 0;
    while i < uri.len()
        invariant
            0 <= i <= uri.len(),
            fragment == exists|k: int| 0 <= k < i && #[trigger] uri@[k] == b'#',
            forall|k: int| 0 <= k < i ==> !forbidden(#[trigger] uri@[k]),
            forall|k1: int, k2: int| 0 <= k1 < k2 < i && #[trigger] uri@[k1] == b'#' ==> #[trigger] uri@[k2] != b'#',
            forall|k: int| 0 <= k < i && #[trigger] uri@[k] == b'%' ==> k + 2 < uri.len() && hexd(uri@[k + 1]) && hexd(uri@[k + 2]),
        decreases uri.len() - i,
    {
        let c = uri[i];
        if c <= 0x20 || c == 0x7F || c == b'"' || c == b'<' || c == b'>' || c == b'\\' || c == b'^' || c == b'`' || c == b'{' || c == b'|' || c == b'}' {
            return false;
        }
        if c == b'#' {
            if fragment {
                return false;
            }
            fragment = true;
        }
        if c == b'%' && (uri.len() - i < 3 || !hex_digit(uri[i + 1]) || !hex_digit(uri[i + 2])) {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn uri_syntax(u: Seq<u8>) -> bool {
    &&& forall|c: int| #[trigger] scheme_colon(u, c) ==> c > 0 && alpha(u[0]) && forall|k: int| 1 <= k < c ==> scheme_char(#[trigger] u[k])
    &&& forall|k: int| 0 <= k < u.len() ==> !forbidden(#[trigger] u[k])
    &&& forall|k1: int, k2: int| 0 <= k1 < k2 < u.len() && #[trigger] u[k1] == b'#' ==> #[trigger] u[k2] != b'#'
    &&& forall|k: int| 0 <= k < u.len() && #[trigger] u[k] == b'%' ==> k + 2 < u.len() && hexd(u[k + 1]) && hexd(u[k + 2])
}

pub fn uri_syntax_ok(uri: &Vec<u8>) -> (r: bool)
    ensures
        r == uri_syntax(uri@),
{
    let end = find_scheme_end(uri);
    proof {
        if end < uri.len() {
            assert forall|c: int| #[trigger] scheme_colon(uri@, c) implies c == end by {
                if c < end {
                    assert(!(uri@[c] == b':' || uri@[c] == b'/' || uri@[c] == b'?' || uri@[c] == b'#'));
                } else if c > end {
                    assert(!(uri@[end as int] == b':' || uri@[end as int] == b'/' || uri@[end as int] == b'?' || uri@[end as int] == b'#'));
                }
            }
        }
    }
    let scheme_ok = end == uri.len() || (end > 0 && is_alpha(uri[0]) && scheme_chars_ok(uri, end));
    scheme_ok && uri_chars_ok(uri)
}

pub struct DataUri {
    pub media_end: usize,
    pub length: u64,
}

pub open spec fn data_prefix() -> Seq<u8> {
    seq![b'd', b'a', b't', b'a', b':']
}

pub fn is_data_uri(uri: &Vec<u8>) -> (r: bool)
    ensures
        r == has_prefix(uri@, data_prefix()),
{
    starts_with(uri, &[b'd', b'a', b't', b'a', b':'])
}

fn find_byte(s: &Vec<u8>, from: usize, to: usize, b: u8) -> (r: usize)
    requires
        from <= to <= s.len(),
    ensures
        r == first_byte(s@, from as int, to as int, b),
        from <= r <= to,
{
    let mut i = from;
    while i < to
        invariant
            from <= i <= to <= s.len(),
            forall|k: int| from <= k < i ==> #[trigger] s@[k] != b,
        decreases to - i,
    {
        if s[i] == b {
            proof {
                lemma_first_byte_unique(s@, from as int, to as int, b, i as int);
            }
            return i;
        }
        i += 1;
    }
    proof {
        lemma_first_byte_unique(s@, from as int, to as int, b, to as int);
    }
    to
}

fn parameter_ok(uri: &Vec<u8>, start: usize, end: usize) -> (r: bool)
    requires
        start <= end <= uri.len(),
    ensures
        r == ({
            let eq = first_byte(uri@, start as int, end as int, b'=');
            start < eq && eq < end
        }),
{
    let eq = find_byte(uri, start, end, b'=');
    eq > start && eq < end
}

pub proof fn lemma_first_byte(s: Seq<u8>, from: int, to: int, b: u8)
    requires
        from <= to,
    ensures
        first_at(s, from, to, b, first_byte(s, from, to, b)),
    decreases to - from,
{
    if from < to && s[from] != b {
        lemma_first_byte(s, from + 1, to, b);
        let r = first_byte(s, from + 1, to, b);
        assert(first_at(s, from, to, b, r));
    } else {
        assert(first_at(s, from, to, b, from));
    }
}

pub open spec fn base64_seq() -> Seq<u8> {
    seq![b'b', b'a', b's', b'e', b'6', b'4']
}

// ";" で区切られた引数部分（seg は ';' の位置）: Some(true) なら最後が ;base64
pub open spec fn params_s(u: Seq<u8>, seg: int, comma: int) -> Option<bool>
    decreases comma - seg,
{
    if seg >= comma || seg < 0 {
        Some(false)
    } else {
        let start = seg + 1;
        let end = first_byte(u, start, comma, b';');
        let eq = first_byte(u, start, end, b'=');
        if end == comma && u.subrange(start, end) == base64_seq() {
            Some(true)
        } else if !(start < eq && eq < end) {
            None
        } else {
            proof {
                lemma_first_byte(u, start, comma, b';');
            }
            params_s(u, end, comma)
        }
    }
}

fn parameters(uri: &Vec<u8>, from: usize, comma: usize) -> (r: Option<bool>)
    requires
        from <= comma < uri.len(),
    ensures
        r == params_s(uri@, from as int, comma as int),
{
    let mut seg = from;
    while seg < comma
        invariant
            from <= seg <= comma < uri.len(),
            params_s(uri@, from as int, comma as int) == params_s(uri@, seg as int, comma as int),
        decreases comma - seg,
    {
        let start = seg + 1;
        let end = find_byte(uri, start, comma, b';');
        if end == comma && range_eq(uri, start, end, &[b'b', b'a', b's', b'e', b'6', b'4']) {
            return Some(true);
        }
        if !parameter_ok(uri, start, end) {
            return None;
        }
        seg = end;
    }
    Some(false)
}

fn base64_chars_ok(uri: &Vec<u8>, start: usize, end: usize) -> (r: bool)
    requires
        start <= end <= uri.len(),
    ensures
        r == (forall|k: int| start <= k < end ==> b64char(#[trigger] uri@[k])),
{
    let mut i = start;
    while i < end
        invariant
            start <= i <= end <= uri.len(),
            forall|k: int| start <= k < i ==> b64char(#[trigger] uri@[k]),
        decreases end - i,
    {
        if !base64_char(uri[i]) {
            return false;
        }
        i += 1;
    }
    true
}

pub open spec fn base64_len_s(data: Seq<u8>) -> Option<int> {
    let n = data.len() as int;
    let pad: int = if n > 0 && data[n - 1] == b'=' {
        if n >= 2 && data[n - 2] == b'=' { 2 } else { 1 }
    } else {
        0
    };
    if n % 4 == 0 && forall|k: int| 0 <= k < n - pad ==> b64char(#[trigger] data[k]) {
        Some(n / 4 * 3 - pad)
    } else {
        None
    }
}

fn base64_length(uri: &Vec<u8>, start: usize) -> (r: Option<u64>)
    requires
        start <= uri.len(),
    ensures
        match r {
            Some(n) => base64_len_s(uri@.subrange(start as int, uri.len() as int)) == Some(n as int),
            None => base64_len_s(uri@.subrange(start as int, uri.len() as int)) is None,
        },
{
    let ghost data = uri@.subrange(start as int, uri.len() as int);
    let n = uri.len() - start;
    if n % 4 != 0 {
        return None;
    }
    let pad = if n > 0 && uri[uri.len() - 1] == b'=' {
        if uri[uri.len() - 2] == b'=' { 2 } else { 1 }
    } else {
        0
    };
    proof {
        if n > 0 {
            assert(data[n - 1] == uri@[uri.len() - 1]);
            assert(data[n - 2] == uri@[uri.len() - 2]);
        }
        assert forall|k: int| 0 <= k < n - pad implies data[k] == uri@[start + k] by {}
        if forall|k: int| start <= k < uri.len() - pad ==> b64char(#[trigger] uri@[k]) {
            assert forall|k: int| 0 <= k < n - pad implies b64char(#[trigger] data[k]) by {
                assert(b64char(uri@[start + k]));
            }
        }
        if forall|k: int| 0 <= k < n - pad ==> b64char(#[trigger] data[k]) {
            assert forall|k: int| start <= k < uri.len() - pad implies b64char(#[trigger] uri@[k]) by {
                assert(b64char(data[k - start]));
            }
        }
    }
    if base64_chars_ok(uri, start, uri.len() - pad) {
        Some((n / 4 * 3 - pad) as u64)
    } else {
        None
    }
}

pub open spec fn count_byte(s: Seq<u8>, b: u8) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_byte(s.drop_last(), b) + (if s.last() == b { 1nat } else { 0nat })
    }
}

pub open spec fn percent_len_s(data: Seq<u8>) -> Option<int> {
    if forall|k: int| 0 <= k < data.len() && #[trigger] data[k] == b'%' ==> k + 2 < data.len() && hexd(data[k + 1])
        && hexd(data[k + 2]) {
        Some(data.len() - 2 * count_byte(data, b'%'))
    } else {
        None
    }
}

pub proof fn lemma_count_push(s: Seq<u8>, x: u8, b: u8)
    ensures
        count_byte(s.push(x), b) == count_byte(s, b) + (if x == b { 1nat } else { 0nat }),
{
    assert(s.push(x).drop_last() =~= s);
}

pub proof fn lemma_count_le(s: Seq<u8>, b: u8)
    ensures
        count_byte(s, b) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_le(s.drop_last(), b);
    }
}

fn percent_length(uri: &Vec<u8>, start: usize) -> (r: Option<u64>)
    requires
        start <= uri.len(),
    ensures
        match r {
            Some(n) => percent_len_s(uri@.subrange(start as int, uri.len() as int)) == Some(n as int),
            None => percent_len_s(uri@.subrange(start as int, uri.len() as int)) is None,
        },
{
    let ghost data = uri@.subrange(start as int, uri.len() as int);
    let mut len: u64 = 0;
    let mut i = start;
    proof {
        assert(uri@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    }
    while i < uri.len()
        invariant
            start <= i <= uri.len(),
            data == uri@.subrange(start as int, uri.len() as int),
            forall|k: int| start <= k < i && #[trigger] uri@[k] == b'%' ==> k + 2 < uri.len() && hexd(uri@[k + 1]) && hexd(uri@[k + 2]),
            len as int == (i - start) - 2 * count_byte(uri@.subrange(start as int, i as int), b'%'),
            len <= i - start,
        decreases uri.len() - i,
    {
        let ghost i0 = i as int;
        let ghost pre = uri@.subrange(start as int, i0);
        if uri[i] == b'%' {
            if uri.len() - i < 3 || !hex_digit(uri[i + 1]) || !hex_digit(uri[i + 2]) {
                proof {
                    assert(data[i0 - start] == b'%');
                    if i0 + 2 < uri.len() {
                        assert(data[i0 - start + 1] == uri@[i0 + 1]);
                        assert(data[i0 - start + 2] == uri@[i0 + 2]);
                    }
                }
                return None;
            }
            i += 3;
            proof {
                let p1 = pre.push(uri@[i0]);
                let p2 = p1.push(uri@[i0 + 1]);
                let p3 = p2.push(uri@[i0 + 2]);
                assert(p3 =~= uri@.subrange(start as int, i as int));
                lemma_count_push(pre, uri@[i0], b'%');
                lemma_count_push(p1, uri@[i0 + 1], b'%');
                lemma_count_push(p2, uri@[i0 + 2], b'%');
                assert(uri@[i0 + 1] != b'%');
                assert(uri@[i0 + 2] != b'%');
                lemma_count_le(pre, b'%');
            }
        } else {
            i += 1;
            proof {
                assert(pre.push(uri@[i0]) =~= uri@.subrange(start as int, i as int));
                lemma_count_push(pre, uri@[i0], b'%');
                lemma_count_le(pre, b'%');
            }
        }
        len += 1;
    }
    proof {
        assert(uri@.subrange(start as int, i as int) =~= data);
        assert forall|k: int| 0 <= k < data.len() && #[trigger] data[k] == b'%' implies k + 2 < data.len() && hexd(data[k + 1]) && hexd(data[k + 2]) by {
            assert(uri@[k + start] == b'%');
        }
    }
    Some(len)
}

// data_uri(u): (メディア型, 復号後の長さ)
// RFC 2397: data URL のメディアタイプとデータの長さ
pub open spec fn data_uri(u: Seq<u8>) -> Option<(Seq<u8>, int)> {
    let comma = first_byte(u, 5, u.len() as int, b',');
    let media_end = first_byte(u, 5, comma, b';');
    if comma >= u.len() {
        None
    } else {
        let data = u.subrange(comma + 1, u.len() as int);
        match params_s(u, media_end, comma) {
            None => None,
            Some(b64) => match (if b64 { base64_len_s(data) } else { percent_len_s(data) }) {
                Some(len) => Some((u.subrange(5, media_end), len)),
                None => None,
            },
        }
    }
}

pub fn parse_data_uri(uri: &Vec<u8>) -> (r: Option<DataUri>)
    requires
        uri.len() >= 5,
    ensures
        match r {
            Some(d) => 5 <= d.media_end <= uri.len() && data_uri(uri@) == Some((uri@.subrange(5, d.media_end as int), d.length as int)),
            None => data_uri(uri@) is None,
        },
{
    let comma = find_byte(uri, 5, uri.len(), b',');
    if comma >= uri.len() {
        return None;
    }
    let media_end = find_byte(uri, 5, comma, b';');
    let length = match parameters(uri, media_end, comma) {
        None => None,
        Some(true) => base64_length(uri, comma + 1),
        Some(false) => percent_length(uri, comma + 1),
    };
    match length {
        None => None,
        Some(length) => Some(DataUri { media_end, length }),
    }
}

pub open spec fn octet_stream() -> Seq<u8> {
    seq![
        b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'o', b'c', b't', b'e', b't', b'-',
        b's', b't', b'r', b'e', b'a', b'm',
    ]
}

pub open spec fn gltf_buffer() -> Seq<u8> {
    seq![
        b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'g', b'l', b't', b'f', b'-', b'b',
        b'u', b'f', b'f', b'e', b'r',
    ]
}

// MUST-022: バッファーの data URL のメディアタイプ
fn buffer_media_type_ok(uri: &Vec<u8>, media_end: usize) -> (r: bool)
    requires
        5 <= media_end <= uri.len(),
    ensures
        r == (uri@.subrange(5, media_end as int) == octet_stream() || uri@.subrange(5, media_end as int) == gltf_buffer()),
{
    range_eq(uri, 5, media_end, &[b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'o', b'c', b't', b'e', b't', b'-', b's', b't', b'r', b'e', b'a', b'm'])
        || range_eq(uri, 5, media_end, &[b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'g', b'l', b't', b'f', b'-', b'b', b'u', b'f', b'f', b'e', b'r'])
}

// MUST-021, MUST-022: data URL の長さ ≥ byteLength、メディアタイプ
fn buffer_uri_ok(uri: &Vec<u8>, byte_length: u64) -> (r: bool)
    ensures
        r == (uri_syntax(uri@) && (has_prefix(uri@, data_prefix()) ==> (data_uri(uri@) matches Some((mt, len)) && (mt
            == octet_stream() || mt == gltf_buffer()) && len >= byte_length))),
{
    if !uri_syntax_ok(uri) {
        false
    } else if !is_data_uri(uri) {
        true
    } else {
        match parse_data_uri(uri) {
            None => false,
            Some(d) => buffer_media_type_ok(uri, d.media_end) && d.length >= byte_length,
        }
    }
}

fn image_uri_ok(uri: &Vec<u8>) -> (r: bool)
    ensures
        r == (uri_syntax(uri@) && (has_prefix(uri@, data_prefix()) ==> data_uri(uri@) is Some)),
{
    uri_syntax_ok(uri) && (!is_data_uri(uri) || parse_data_uri(uri).is_some())
}

// BU1（1 バッファ分）
pub open spec fn buffer_rule(g: GltfS, b: int) -> bool {
    let buf = g.buffers[b];
    &&& buf.byte_length > 0
    &&& match buf.uri {
        // MUST-023, MUST-024: GLB のバッファー 0 には byteLength 以上の BIN チャンクが必要
        None => (g.is_glb && b == 0) ==> (g.glb_bin_len matches Some(n) && n >= buf.byte_length),
        // MUST-021, MUST-022: data URL の長さ ≥ byteLength、メディアタイプ
        Some(u) => uri_syntax(u) && (has_prefix(u, data_prefix()) ==> (data_uri(u) matches Some((mt, len)) && (mt
            == octet_stream() || mt == gltf_buffer()) && len >= buf.byte_length)),
    }
}

// BU1
// MUST-021, MUST-022, MUST-023, MUST-024: バッファー 1 つ分の規則
fn buffer_ok(g: &Gltf, b: usize) -> (r: bool)
    requires
        b < g.buffers.len(),
    ensures
        r == buffer_rule(g@, b as int),
{
    proof {
        assert(g@.buffers[b as int] == g.buffers@[b as int]@);
    }
    let buf = &g.buffers[b];
    if buf.byte_length == 0 {
        return false;
    }
    match &buf.uri {
        None => {
            if b == 0 && g.is_glb {
                match g.glb_bin_len {
                    None => false,
                    Some(n) => n >= buf.byte_length,
                }
            } else {
                true
            }
        }
        Some(u) => buffer_uri_ok(u, buf.byte_length),
    }
}

pub(crate) fn buffers_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|b: int| 0 <= b < g@.buffers.len() ==> #[trigger] buffer_rule(g@, b)),
{
    let mut b = 0;
    while b < g.buffers.len()
        invariant
            0 <= b <= g.buffers.len(),
            forall|x: int| 0 <= x < b ==> #[trigger] buffer_rule(g@, x),
        decreases g.buffers.len() - b,
    {
        if !buffer_ok(g, b) {
            return false;
        }
        b += 1;
    }
    true
}

// IM1
// MUST-108, MUST-112: uri と bufferView のどちらか一方、bufferView なら mimeType が必要
pub open spec fn image_rule(im: ImageS) -> bool {
    &&& im.uri is Some != im.buffer_view is Some
    &&& (im.buffer_view is Some ==> im.has_mime_type)
    &&& (im.uri matches Some(u) ==> uri_syntax(u) && (has_prefix(u, data_prefix()) ==> data_uri(u) is Some))
}

// IM1
// MUST-108, MUST-112: uri と bufferView のどちらか一方、bufferView なら mimeType が必要
fn image_ok(im: &Image) -> (r: bool)
    ensures
        r == image_rule(im@),
{
    let uri_ok = match &im.uri {
        None => true,
        Some(u) => image_uri_ok(u),
    };
    im.uri.is_some() != im.buffer_view.is_some() && (im.buffer_view.is_none() || im.has_mime_type) && uri_ok
}

pub(crate) fn images_ok(g: &Gltf) -> (r: bool)
    ensures
        r == (forall|i: int| 0 <= i < g@.images.len() ==> image_rule(#[trigger] g@.images[i])),
{
    let mut i = 0;
    while i < g.images.len()
        invariant
            0 <= i <= g.images.len(),
            forall|k: int| 0 <= k < i ==> image_rule(#[trigger] g@.images[k]),
        decreases g.images.len() - i,
    {
        proof {
            assert(g@.images[i as int] == g.images@[i as int]@);
        }
        if !image_ok(&g.images[i]) {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
