use creusot_std::prelude::*;
use crate::model::*;
use crate::validate::mesh::*;

#[logic(open)]
pub fn alpha_b(b: u8) -> bool {
    pearlite! { (65 <= b@ && b@ <= 90) || (97 <= b@ && b@ <= 122) }
}

#[logic(open)]
pub fn b64_b(b: u8) -> bool {
    pearlite! { alpha_b(b) || (48 <= b@ && b@ <= 57) || b@ == 43 || b@ == 47 }
}

#[ensures(result == b64_b(b))]
#[check(terminates)]
fn base64_char(b: u8) -> bool {
    (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'+' || b == b'/'
}

#[logic(open)]
pub fn hex_b(b: u8) -> bool {
    pearlite! { (48 <= b@ && b@ <= 57) || (65 <= b@ && b@ <= 70) || (97 <= b@ && b@ <= 102) }
}

#[ensures(result == hex_b(b))]
#[check(terminates)]
fn hex_digit(b: u8) -> bool {
    (b >= b'0' && b <= b'9') || (b >= b'A' && b <= b'F') || (b >= b'a' && b <= b'f')
}

#[requires(start@ <= end@ && end@ <= s@.len())]
#[ensures(result == seq_is(s@[start@..end@], lit@))]
#[check(terminates)]
fn range_eq(s: &Vec<u8>, start: usize, end: usize, lit: &[u8]) -> bool {
    if end - start != lit.len() {
        return false;
    }
    let mut i = 0;
    #[invariant(i@ <= lit@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> s@[start@ + k] == lit@[k])]
    #[variant(lit@.len() - i@)]
    while i < lit.len() {
        if s[start + i] != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}

#[ensures(result == alpha_b(b))]
#[check(terminates)]
fn is_alpha(b: u8) -> bool {
    (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z')
}

// c が、最初の '/' '?' '#' より前にある最初の ':' の位置
#[logic(open)]
pub fn scheme_colon(u: Seq<u8>, c: Int) -> bool {
    pearlite! {
        0 <= c && c < u.len() && u[c]@ == 58
            && forall<k> 0 <= k && k < c ==> u[k]@ != 58 && u[k]@ != 47 && u[k]@ != 63 && u[k]@ != 35
    }
}

#[ensures((result@ < uri@.len() && scheme_colon(uri@, result@)) || (result@ == uri@.len() && forall<c> !scheme_colon(uri@, c)))]
#[check(terminates)]
fn find_scheme_end(uri: &Vec<u8>) -> usize {
    let mut i = 0;
    #[invariant(i@ <= uri@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> uri@[k]@ != 58 && uri@[k]@ != 47 && uri@[k]@ != 63 && uri@[k]@ != 35)]
    #[variant(uri@.len() - i@)]
    while i < uri.len() {
        let c = uri[i];
        if c == b':' {
            return i;
        }
        if c == b'/' || c == b'?' || c == b'#' {
            return uri.len();
        }
        i += 1;
    }
    uri.len()
}

#[logic(open)]
pub fn scheme_b(b: u8) -> bool {
    pearlite! { alpha_b(b) || (48 <= b@ && b@ <= 57) || b@ == 43 || b@ == 45 || b@ == 46 }
}

#[requires(end@ <= uri@.len())]
#[ensures(result == forall<k> 1 <= k && k < end@ ==> scheme_b(uri@[k]))]
#[check(terminates)]
fn scheme_chars_ok(uri: &Vec<u8>, end: usize) -> bool {
    let mut k = 1;
    #[invariant(1 <= k@ && (k@ <= end@ || end@ < 1))]
    #[invariant(forall<j> 1 <= j && j < k@ ==> scheme_b(uri@[j]))]
    #[variant(end@ - k@)]
    while k < end {
        let c = uri[k];
        if !(is_alpha(c) || (c >= b'0' && c <= b'9') || c == b'+' || c == b'-' || c == b'.') {
            return false;
        }
        k += 1;
    }
    true
}

// URI に現れてはいけないバイト
#[logic(open)]
pub fn forbidden_b(b: u8) -> bool {
    pearlite! {
        b@ <= 32 || b@ == 127 || b@ == 34 || b@ == 60 || b@ == 62 || b@ == 92 || b@ == 94 || b@ == 96
            || b@ == 123 || b@ == 124 || b@ == 125
    }
}

#[logic(open)]
pub fn pct_ok(u: Seq<u8>) -> bool {
    pearlite! { forall<k> 0 <= k && k < u.len() && u[k]@ == 37 ==> k + 2 < u.len() && hex_b(u[k + 1]) && hex_b(u[k + 2]) }
}

#[logic(open)]
pub fn uri_chars(u: Seq<u8>) -> bool {
    pearlite! {
        (forall<k> 0 <= k && k < u.len() ==> !forbidden_b(u[k]))
            && (forall<i, j> 0 <= i && i < j && j < u.len() ==> !(u[i]@ == 35 && u[j]@ == 35))
            && pct_ok(u)
    }
}

#[ensures(result == uri_chars(uri@))]
#[check(terminates)]
fn uri_chars_ok(uri: &Vec<u8>) -> bool {
    let mut fragment = false;
    let mut i = 0;
    #[invariant(i@ <= uri@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> !forbidden_b(uri@[k]))]
    #[invariant(forall<a, b> 0 <= a && a < b && b < i@ ==> !(uri@[a]@ == 35 && uri@[b]@ == 35))]
    #[invariant(fragment == exists<k> 0 <= k && k < i@ && uri@[k]@ == 35)]
    #[invariant(forall<k> 0 <= k && k < i@ && uri@[k]@ == 37 ==> k + 2 < uri@.len() && hex_b(uri@[k + 1]) && hex_b(uri@[k + 2]))]
    #[variant(uri@.len() - i@)]
    while i < uri.len() {
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

// scheme = ALPHA *(ALPHA / DIGIT / "+" / "-" / ".")
#[logic(open)]
pub fn scheme(s: Seq<u8>) -> bool {
    pearlite! { s.len() >= 1 && alpha_b(s[0]) && forall<k> 1 <= k && k < s.len() ==> scheme_b(s[k]) }
}

// RFC 3986: URI の構文
#[logic(open)]
pub fn uri_syntax(u: Seq<u8>) -> bool {
    pearlite! { (forall<c> scheme_colon(u, c) ==> scheme(u[..c])) && uri_chars(u) }
}

// RFC 3986: URI の構文
#[ensures(result == uri_syntax(uri@))]
#[check(terminates)]
pub fn uri_syntax_ok(uri: &Vec<u8>) -> bool {
    let end = find_scheme_end(uri);
    let scheme_ok = end == uri.len() || (end > 0 && is_alpha(uri[0]) && scheme_chars_ok(uri, end));
    scheme_ok && uri_chars_ok(uri)
}

pub struct DataUri {
    pub media_end: usize,
    pub length: u64,
}

#[logic(open)]
pub fn lit_data() -> Seq<u8> { seq![100u8, 97u8, 116u8, 97u8, 58u8] }

#[logic(open)]
pub fn is_data(u: Seq<u8>) -> bool {
    pearlite! { has_prefix(u, lit_data()) }
}

#[ensures(result == is_data(uri@))]
#[check(terminates)]
pub fn is_data_uri(uri: &Vec<u8>) -> bool {
    starts_with(uri, &[b'd', b'a', b't', b'a', b':'])
}

#[requires(to@ <= s@.len())]
#[ensures(result@ <= to@)]
#[ensures(result@ < to@ ==> from@ <= result@ && s@[result@] == b)]
#[ensures(forall<k> from@ <= k && k < result@ ==> s@[k] != b)]
#[ensures(from@ <= to@ ==> from@ <= result@)]
#[check(terminates)]
fn find_byte(s: &Vec<u8>, from: usize, to: usize, b: u8) -> usize {
    let mut i = from;
    #[invariant(from@ <= i@ && (i@ <= to@ || to@ < from@))]
    #[invariant(forall<k> from@ <= k && k < i@ ==> s@[k] != b)]
    #[variant(to@ - i@)]
    while i < to {
        if s[i] == b {
            return i;
        }
        i += 1;
    }
    to
}

// パラメータ u[s..e] は '=' を含み、属性名（最初の '=' より前）が空でない
#[logic(open)]
pub fn attr_ok(u: Seq<u8>, s: Int, e: Int) -> bool {
    pearlite! { s < e && u[s]@ != 61 && exists<q> s < q && q < e && u[q]@ == 61 }
}

#[requires(start@ <= end@ && end@ <= uri@.len())]
#[ensures(result == attr_ok(uri@, start@, end@))]
#[check(terminates)]
fn parameter_ok(uri: &Vec<u8>, start: usize, end: usize) -> bool {
    let eq = find_byte(uri, start, end, b'=');
    eq > start && eq < end
}

#[logic(open)]
pub fn lit_base64() -> Seq<u8> { seq![98u8, 97u8, 115u8, 101u8, 54u8, 52u8] }

// p の ';' から始まる区切りの終わり e（次の ';' か ','）
#[logic(open)]
pub fn seg_end(u: Seq<u8>, c: Int, p: Int, e: Int) -> bool {
    pearlite! { p < e && e <= c && (e == c || u[e]@ == 59) && forall<r> p < r && r < e ==> u[r]@ != 59 }
}

// p の ';' から始まる区切りが最後の区切りで、";base64" である
#[logic(open)]
pub fn b64_seg(u: Seq<u8>, c: Int, p: Int) -> bool {
    pearlite! { seg_end(u, c, p, c) && seq_is(u[p + 1..c], lit_base64()) }
}

#[logic(open)]
pub fn params_ok(u: Seq<u8>, m: Int, c: Int) -> bool {
    pearlite! {
        forall<p, e> m <= p && p < c && u[p]@ == 59 && seg_end(u, c, p, e) ==> b64_seg(u, c, p) || attr_ok(u, p + 1, e)
    }
}

#[logic(open)]
pub fn b64_flag(u: Seq<u8>, m: Int, c: Int) -> bool {
    pearlite! { exists<p> m <= p && p < c && u[p]@ == 59 && b64_seg(u, c, p) }
}

#[requires(from@ <= comma@ && comma@ < uri@.len())]
#[requires(from@ == comma@ || uri@[from@]@ == 59)]
#[ensures(match result {
    None => !params_ok(uri@, from@, comma@),
    Some(b) => params_ok(uri@, from@, comma@) && b == b64_flag(uri@, from@, comma@),
})]
#[check(terminates)]
fn parameters(uri: &Vec<u8>, from: usize, comma: usize) -> Option<bool> {
    let mut seg = from;
    #[invariant(from@ <= seg@ && seg@ <= comma@)]
    #[invariant(seg@ == comma@ || uri@[seg@]@ == 59)]
    #[invariant(forall<p, e> from@ <= p && p < seg@ && uri@[p]@ == 59 && seg_end(uri@, comma@, p, e) ==> attr_ok(uri@, p + 1, e))]
    #[invariant(forall<p> from@ <= p && p < seg@ && uri@[p]@ == 59 ==> !b64_seg(uri@, comma@, p))]
    #[variant(comma@ - seg@)]
    while seg < comma {
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

#[requires(start@ <= end@ && end@ <= uri@.len())]
#[ensures(result == forall<k> start@ <= k && k < end@ ==> b64_b(uri@[k]))]
#[check(terminates)]
fn base64_chars_ok(uri: &Vec<u8>, start: usize, end: usize) -> bool {
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= end@)]
    #[invariant(forall<k> start@ <= k && k < i@ ==> b64_b(uri@[k]))]
    #[variant(end@ - i@)]
    while i < end {
        if !base64_char(uri[i]) {
            return false;
        }
        i += 1;
    }
    true
}

// base64 のデータ d の長さが 4 の倍数で、末尾の '=' は 2 個まで、復号後の長さが len
#[logic(open)]
pub fn b64_data(d: Seq<u8>, len: Int) -> bool {
    pearlite! {
        d.len() % 4 == 0 && exists<pad> 0 <= pad && pad <= 2 && pad <= d.len()
            && (forall<k> 0 <= k && k < d.len() - pad ==> b64_b(d[k]))
            && (forall<k> d.len() - pad <= k && k < d.len() ==> d[k]@ == 61)
            && len == d.len() / 4 * 3 - pad
    }
}

#[requires(start@ <= uri@.len())]
#[ensures(match result {
    None => forall<len> !b64_data(uri@[start@..], len),
    Some(l) => b64_data(uri@[start@..], l@),
})]
#[check(terminates)]
fn base64_length(uri: &Vec<u8>, start: usize) -> Option<u64> {
    let n = uri.len() - start;
    if n % 4 != 0 {
        return None;
    }
    let pad = if n > 0 && uri[uri.len() - 1] == b'=' {
        if uri[uri.len() - 2] == b'=' { 2 } else { 1 }
    } else {
        0
    };
    if base64_chars_ok(uri, start, uri.len() - pad) {
        Some((n / 4 * 3 - pad) as u64)
    } else {
        None
    }
}

// s に含まれるバイト b の数
#[logic(open)]
#[variant(s.len())]
pub fn occ(s: Seq<u8>, b: Int) -> Int {
    pearlite! { if s.len() <= 0 { 0 } else { occ(s[..s.len() - 1], b) + if s[s.len() - 1]@ == b { 1 } else { 0 } } }
}

// パーセントエンコードのデータ: '%' の後に 16 進 2 桁。%XX を 1 文字と数えた長さが len
#[logic(open)]
pub fn pct_data(d: Seq<u8>, len: Int) -> bool {
    pearlite! { pct_ok(d) && len == d.len() - 2 * occ(d, 37) }
}

#[requires(start@ <= uri@.len())]
#[ensures(match result {
    None => forall<len> !pct_data(uri@[start@..], len),
    Some(l) => pct_data(uri@[start@..], l@),
})]
#[check(terminates)]
fn percent_length(uri: &Vec<u8>, start: usize) -> Option<u64> {
    let mut len: u64 = 0;
    let mut i = start;
    #[invariant(start@ <= i@ && i@ <= uri@.len())]
    #[invariant(forall<k> start@ <= k && k < i@ && uri@[k]@ == 37 ==> k + 2 < i@ && hex_b(uri@[k + 1]) && hex_b(uri@[k + 2]))]
    #[invariant(len@ == (i@ - start@) - 2 * occ(uri@[start@..i@], 37))]
    #[invariant(len@ <= i@ - start@)]
    #[variant(uri@.len() - i@)]
    while i < uri.len() {
        if uri[i] == b'%' {
            if uri.len() - i < 3 || !hex_digit(uri[i + 1]) || !hex_digit(uri[i + 2]) {
                proof_assert!(uri@[start@..][i@ - start@]@ == 37);
                return None;
            }
            proof_assert!(uri@[start@..i@ + 1][..i@ - start@].ext_eq(uri@[start@..i@]));
            proof_assert!(uri@[start@..i@ + 2][..i@ - start@ + 1].ext_eq(uri@[start@..i@ + 1]));
            proof_assert!(uri@[start@..i@ + 3][..i@ - start@ + 2].ext_eq(uri@[start@..i@ + 2]));
            i += 3;
        } else {
            proof_assert!(uri@[start@..i@ + 1][..i@ - start@].ext_eq(uri@[start@..i@]));
            i += 1;
        }
        len += 1;
    }
    proof_assert!(uri@[start@..i@].ext_eq(uri@[start@..]));
    Some(len)
}

// c は "data:" の後で最初の ','
#[logic(open)]
pub fn first_comma(u: Seq<u8>, c: Int) -> bool {
    pearlite! { 5 <= c && c < u.len() && u[c]@ == 44 && forall<k> 5 <= k && k < c ==> u[k]@ != 44 }
}

// m はメディアタイプの終わり（最初の ';' か ','）
#[logic(open)]
pub fn media_end_at(u: Seq<u8>, c: Int, m: Int) -> bool {
    pearlite! { 5 <= m && m <= c && (m == c || u[m]@ == 59) && forall<k> 5 <= k && k < m ==> u[k]@ != 59 }
}

// u が data URI として正しく、メディアタイプが u[5..m]、復号後の長さが len
// RFC 2397: data URL の構文
#[logic(open)]
pub fn data_uri_is(u: Seq<u8>, m: Int, len: Int) -> bool {
    pearlite! {
        exists<c> first_comma(u, c) && media_end_at(u, c, m) && params_ok(u, m, c)
            && if b64_flag(u, m, c) { b64_data(u[c + 1..], len) } else { pct_data(u[c + 1..], len) }
    }
}

#[logic(open)]
pub fn data_uri_valid(u: Seq<u8>) -> bool {
    pearlite! { exists<m, len> data_uri_is(u, m, len) }
}

// RFC 2397: data URL の構文
#[ensures(match result {
    None => !data_uri_valid(uri@),
    Some(d) => data_uri_is(uri@, d.media_end@, d.length@),
})]
#[check(terminates)]
pub fn parse_data_uri(uri: &Vec<u8>) -> Option<DataUri> {
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

#[logic(open)]
pub fn lit_octet_stream() -> Seq<u8> {
    seq![97u8, 112u8, 112u8, 108u8, 105u8, 99u8, 97u8, 116u8, 105u8, 111u8, 110u8, 47u8, 111u8, 99u8, 116u8, 101u8, 116u8, 45u8, 115u8, 116u8, 114u8, 101u8, 97u8, 109u8]
}

#[logic(open)]
pub fn lit_gltf_buffer() -> Seq<u8> {
    seq![97u8, 112u8, 112u8, 108u8, 105u8, 99u8, 97u8, 116u8, 105u8, 111u8, 110u8, 47u8, 103u8, 108u8, 116u8, 102u8, 45u8, 98u8, 117u8, 102u8, 102u8, 101u8, 114u8]
}

// MUST-022: バッファーの data URL のメディアタイプ
#[logic(open)]
pub fn buffer_media_ok(u: Seq<u8>, m: Int) -> bool {
    pearlite! { seq_is(u[5..m], lit_octet_stream()) || seq_is(u[5..m], lit_gltf_buffer()) }
}

// MUST-022: バッファーの data URL のメディアタイプ
#[requires(5 <= media_end@ && media_end@ <= uri@.len())]
#[ensures(result == buffer_media_ok(uri@, media_end@))]
#[check(terminates)]
fn buffer_media_type_ok(uri: &Vec<u8>, media_end: usize) -> bool {
    range_eq(uri, 5, media_end, &[b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'o', b'c', b't', b'e', b't', b'-', b's', b't', b'r', b'e', b'a', b'm'])
        || range_eq(uri, 5, media_end, &[b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'g', b'l', b't', b'f', b'-', b'b', b'u', b'f', b'f', b'e', b'r'])
}

// MUST-021, MUST-022: data URL のバッファーはメディアタイプが正しく、長さ ≥ byteLength
#[logic(open)]
pub fn buffer_uri_spec(u: Seq<u8>, byte_length: Int) -> bool {
    pearlite! {
        uri_syntax(u)
            && (is_data(u) ==> exists<m, len> data_uri_is(u, m, len) && buffer_media_ok(u, m) && len >= byte_length)
    }
}

// MUST-021, MUST-022: data URL のバッファーはメディアタイプが正しく、長さ ≥ byteLength
#[ensures(result == buffer_uri_spec(uri@, byte_length@))]
#[check(terminates)]
fn buffer_uri_ok(uri: &Vec<u8>, byte_length: u64) -> bool {
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

#[ensures(result == (uri_syntax(uri@) && (is_data(uri@) ==> data_uri_valid(uri@))))]
#[check(terminates)]
fn image_uri_ok(uri: &Vec<u8>) -> bool {
    uri_syntax_ok(uri) && (!is_data_uri(uri) || parse_data_uri(uri).is_some())
}

// MUST-021, MUST-023, MUST-024: 参照先の長さ ≥ byteLength、GLB のバッファー 0 には BIN チャンクが必要で長さ ≥ byteLength
#[logic(open)]
pub fn buffer_rule(g: Gltf, b: Int) -> bool {
    pearlite! {
        g.buffers@[b].byte_length@ > 0
            && match g.buffers@[b].uri {
                None => if g.is_glb && b == 0 {
                    match g.glb_bin_len {
                        None => false,
                        Some(n) => n@ >= g.buffers@[b].byte_length@,
                    }
                } else {
                    true
                },
                Some(u) => buffer_uri_spec(u@, g.buffers@[b].byte_length@),
            }
    }
}

// MUST-021, MUST-023, MUST-024: 参照先の長さ ≥ byteLength、GLB のバッファー 0 には BIN チャンクが必要で長さ ≥ byteLength
#[requires(b@ < g.buffers@.len())]
#[ensures(result == buffer_rule(*g, b@))]
#[check(terminates)]
fn buffer_ok(g: &Gltf, b: usize) -> bool {
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

#[logic(open)]
pub fn buffers_spec(g: Gltf) -> bool {
    pearlite! { forall<b> 0 <= b && b < g.buffers@.len() ==> buffer_rule(g, b) }
}

#[ensures(result == buffers_spec(*g))]
#[check(terminates)]
pub(crate) fn buffers_ok(g: &Gltf) -> bool {
    let mut b = 0;
    #[invariant(b@ <= g.buffers@.len())]
    #[invariant(forall<k> 0 <= k && k < b@ ==> buffer_rule(*g, k))]
    #[variant(g.buffers@.len() - b@)]
    while b < g.buffers.len() {
        if !buffer_ok(g, b) {
            return false;
        }
        b += 1;
    }
    true
}

// MUST-108, MUST-112: 画像は bufferView と uri のどちらか一方で、bufferView なら mimeType が必要
#[logic(open)]
pub fn image_rule(im: Image) -> bool {
    pearlite! {
        (im.uri != None) != (im.buffer_view != None)
            && (im.buffer_view != None ==> im.has_mime_type)
            && match im.uri {
                None => true,
                Some(u) => uri_syntax(u@) && (is_data(u@) ==> data_uri_valid(u@)),
            }
    }
}

// MUST-108, MUST-112: 画像は bufferView と uri のどちらか一方で、bufferView なら mimeType が必要
#[ensures(result == image_rule(*im))]
#[check(terminates)]
fn image_ok(im: &Image) -> bool {
    let uri_ok = match &im.uri {
        None => true,
        Some(u) => image_uri_ok(u),
    };
    im.uri.is_some() != im.buffer_view.is_some() && (im.buffer_view.is_none() || im.has_mime_type) && uri_ok
}

#[logic(open)]
pub fn images_spec(g: Gltf) -> bool {
    pearlite! { forall<i> 0 <= i && i < g.images@.len() ==> image_rule(g.images@[i]) }
}

#[ensures(result == images_spec(*g))]
#[check(terminates)]
pub(crate) fn images_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.images@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> image_rule(g.images@[k]))]
    #[variant(g.images@.len() - i@)]
    while i < g.images.len() {
        if !image_ok(&g.images[i]) {
            return false;
        }
        i += 1;
    }
    true
}

#[logic(opaque)]
#[requires(0 <= i && i < s.len())]
#[ensures(occ(s[..i + 1], b) == occ(s[..i], b) + if s[i]@ == b { 1 } else { 0 })]
pub fn lemma_occ_snoc(s: Seq<u8>, i: Int, b: Int) {
    proof_assert!(s[..i + 1][..i].ext_eq(s[..i]));
}

// data URI の分解は一意
#[logic(opaque)]
#[requires(data_uri_is(u, m1, l1) && data_uri_is(u, m2, l2))]
#[ensures(m1 == m2 && l1 == l2)]
pub fn lemma_data_uri_unique(u: Seq<u8>, m1: Int, l1: Int, m2: Int, l2: Int) {}
