use creusot_std::prelude::*;
#[cfg(creusot)]
use crate::model::*;

#[logic(open)]
pub fn hex_val(b: u8) -> Option<Int> {
    pearlite! {
        if 48 <= b@ && b@ <= 57 { Some(b@ - 48) }
        else if 65 <= b@ && b@ <= 70 { Some(b@ - 55) }
        else if 97 <= b@ && b@ <= 102 { Some(b@ - 87) }
        else { None }
    }
}

#[ensures(match result { None => hex_val(b) == None, Some(h) => hex_val(b) == Some(h@) })]
#[check(terminates)]
fn hex_value(b: u8) -> Option<u32> {
    if b >= b'0' && b <= b'9' {
        Some((b - b'0') as u32)
    } else if b >= b'A' && b <= b'F' {
        Some((b - b'A' + 10) as u32)
    } else if b >= b'a' && b <= b'f' {
        Some((b - b'a' + 10) as u32)
    } else {
        None
    }
}

#[logic(open)]
pub fn hv(b: u8) -> Int {
    pearlite! { match hex_val(b) { Some(h) => h, None => 0 } }
}

// s[i..i+k] の 16 進数としての値
#[logic(open)]
#[variant(k)]
pub fn hex_prefix_val(s: Seq<u8>, i: Int, k: Int) -> Int {
    pearlite! { if k <= 0 { 0 } else { hex_prefix_val(s, i, k - 1) * 16 + hv(s[i + k - 1]) } }
}

// \u の後のちょうど 4 桁の 16 進数（大文字・小文字）
#[logic(open)]
pub fn hex4_spec(s: Seq<u8>, i: Int) -> Option<Int> {
    pearlite! {
        if 0 <= i && i + 4 <= s.len() && (forall<k> 0 <= k && k < 4 ==> hex_val(s[i + k]) != None) {
            Some(hex_prefix_val(s, i, 4))
        } else {
            None
        }
    }
}

#[ensures(match result { None => hex4_spec(s@, i@) == None, Some(v) => hex4_spec(s@, i@) == Some(v@) && v@ < 65536 })]
#[check(terminates)]
fn parse_hex4(s: &[u8], i: usize) -> Option<u32> {
    if i >= s.len() || s.len() - i < 4 {
        return None;
    }
    let mut v: u32 = 0;
    let mut k = 0;
    #[invariant(k@ <= 4 && i@ + 4 <= s@.len())]
    #[invariant(forall<t> 0 <= t && t < k@ ==> hex_val(s@[i@ + t]) != None)]
    #[invariant(v@ == hex_prefix_val(s@, i@, k@))]
    #[invariant((k@ == 0 && v@ == 0) || (k@ == 1 && v@ < 16) || (k@ == 2 && v@ < 256) || (k@ == 3 && v@ < 4096) || (k@ == 4 && v@ < 65536))]
    #[variant(4 - k@)]
    while k < 4 {
        match hex_value(s[i + k]) {
            Some(h) => v = v * 16 + h,
            None => return None,
        }
        k += 1;
    }
    Some(v)
}

// コードポイントの UTF-8 による標準の符号化
#[logic(open)]
pub fn utf8_enc(c: Int) -> Seq<u8> {
    pearlite! {
        if c < 0x80 { seq![byte(c)] }
        else if c < 0x800 { seq![byte(0xC0 + c / 64), byte(0x80 + c % 64)] }
        else if c < 0x10000 { seq![byte(0xE0 + c / 4096), byte(0x80 + (c / 64) % 64), byte(0x80 + c % 64)] }
        else { seq![byte(0xF0 + c / 262144), byte(0x80 + (c / 4096) % 64), byte(0x80 + (c / 64) % 64), byte(0x80 + c % 64)] }
    }
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(x@ < 0x110000)]
#[ensures((x >> 6u32)@ == x@ / 64)]
#[ensures((x & 0x3Fu32)@ + (x >> 6u32)@ * 64 == x@)]
pub fn lemma_split6(x: u32) {}

#[logic(opaque)]
#[requires(x@ < 0x110000)]
#[ensures((x & 0x3Fu32)@ == x@ % 64)]
pub fn lemma_low6(x: u32) {
    lemma_split6(x)
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(x@ < 64)]
#[ensures(((0x80u32 | x) as u8)@ == 0x80 + x@)]
pub fn lemma_cont_byte(x: u32) {}

#[logic(opaque)]
#[bitwise_proof]
#[requires(c@ < 0x110000)]
#[ensures(((0x80u32 | (c & 0x3Fu32)) as u8)@ == 0x80 + c@ % 64)]
pub fn lemma_b0(c: u32) {
    lemma_low6(c);
    lemma_cont_byte(c & 0x3Fu32)
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(c@ < 0x110000)]
#[ensures((c >> 6u32)@ == c@ / 64 && (c >> 12u32)@ == c@ / 4096 && (c >> 18u32)@ == c@ / 262144)]
#[ensures((c >> 12u32) == ((c >> 6u32) >> 6u32) && (c >> 18u32) == ((c >> 12u32) >> 6u32))]
pub fn lemma_shifts(c: u32) {}

#[logic(opaque)]
#[bitwise_proof]
#[requires(c@ < 0x110000)]
#[ensures(((0x80u32 | ((c >> 6u32) & 0x3Fu32)) as u8)@ == 0x80 + (c@ / 64) % 64)]
pub fn lemma_b1(c: u32) {
    lemma_shifts(c);
    lemma_b0(c >> 6u32)
}

#[logic(opaque)]
#[bitwise_proof]
#[requires(c@ < 0x110000)]
#[ensures(((0x80u32 | ((c >> 12u32) & 0x3Fu32)) as u8)@ == 0x80 + (c@ / 4096) % 64)]
pub fn lemma_b2(c: u32) {
    lemma_shifts(c);
    lemma_b0(c >> 12u32)
}

#[bitwise_proof]
#[requires(c@ <= 0x10FFFF)]
#[ensures((^out)@ == (*out)@.concat(utf8_enc(c@)))]
#[check(terminates)]
fn push_utf8(out: &mut Vec<u8>, c: u32) {
    let _o0 = snapshot!(out@);
    snapshot!(lemma_b0(c));
    snapshot!(lemma_b1(c));
    snapshot!(lemma_b2(c));
    snapshot!(lemma_shifts(c));
    if c < 0x80 {
        out.push(c as u8);
        proof_assert!(out@.ext_eq(_o0.concat(utf8_enc(c@))));
    } else if c < 0x800 {
        out.push((0xC0 | (c >> 6)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        proof_assert!(((0xC0u32 | (c >> 6u32)) as u8)@ == 0xC0 + c@ / 64);
        proof_assert!(out@.ext_eq(_o0.concat(utf8_enc(c@))));
    } else if c < 0x10000 {
        out.push((0xE0 | (c >> 12)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        proof_assert!(((0xE0u32 | (c >> 12u32)) as u8)@ == 0xE0 + c@ / 4096);
        proof_assert!(out@.ext_eq(_o0.concat(utf8_enc(c@))));
    } else {
        out.push((0xF0 | (c >> 18)) as u8);
        out.push((0x80 | ((c >> 12) & 0x3F)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        proof_assert!(((0xF0u32 | (c >> 18u32)) as u8)@ == 0xF0 + c@ / 262144);
        proof_assert!(out@.ext_eq(_o0.concat(utf8_enc(c@))));
    }
}

#[logic(open)]
pub fn in_range(b: u8, lo: Int, hi: Int) -> bool {
    pearlite! { lo <= b@ && b@ <= hi }
}

#[logic(open)]
pub fn cont(b: u8) -> bool {
    pearlite! { in_range(b, 0x80, 0xBF) }
}

#[ensures(result == cont(b))]
#[check(terminates)]
fn is_cont(b: u8) -> bool {
    b >= 0x80 && b <= 0xBF
}

// Unicode Table 3-7: s[i..] が整形式の UTF-8 の列で始まるならその長さ、そうでなければ 0
#[logic(open)]
pub fn utf8_wf_len(s: Seq<u8>, i: Int) -> Int {
    pearlite! {
        if in_range(s[i], 0xC2, 0xDF) {
            if i + 2 <= s.len() && cont(s[i + 1]) { 2 } else { 0 }
        } else if s[i]@ == 0xE0 {
            if i + 3 <= s.len() && in_range(s[i + 1], 0xA0, 0xBF) && cont(s[i + 2]) { 3 } else { 0 }
        } else if in_range(s[i], 0xE1, 0xEC) || in_range(s[i], 0xEE, 0xEF) {
            if i + 3 <= s.len() && cont(s[i + 1]) && cont(s[i + 2]) { 3 } else { 0 }
        } else if s[i]@ == 0xED {
            if i + 3 <= s.len() && in_range(s[i + 1], 0x80, 0x9F) && cont(s[i + 2]) { 3 } else { 0 }
        } else if s[i]@ == 0xF0 {
            if i + 4 <= s.len() && in_range(s[i + 1], 0x90, 0xBF) && cont(s[i + 2]) && cont(s[i + 3]) { 4 } else { 0 }
        } else if in_range(s[i], 0xF1, 0xF3) {
            if i + 4 <= s.len() && cont(s[i + 1]) && cont(s[i + 2]) && cont(s[i + 3]) { 4 } else { 0 }
        } else if s[i]@ == 0xF4 {
            if i + 4 <= s.len() && in_range(s[i + 1], 0x80, 0x8F) && cont(s[i + 2]) && cont(s[i + 3]) { 4 } else { 0 }
        } else {
            0
        }
    }
}

// Unicode Table 3-7: 整形式の UTF-8 の列
#[requires(i@ < s@.len())]
#[ensures(result@ == utf8_wf_len(s@, i@))]
#[check(terminates)]
fn utf8_len(s: &[u8], i: usize) -> usize {
    let n = s.len() - i;
    let b0 = s[i];
    if b0 >= 0xC2 && b0 <= 0xDF {
        if n >= 2 && is_cont(s[i + 1]) {
            return 2;
        }
    } else if b0 == 0xE0 {
        if n >= 3 && s[i + 1] >= 0xA0 && s[i + 1] <= 0xBF && is_cont(s[i + 2]) {
            return 3;
        }
    } else if (b0 >= 0xE1 && b0 <= 0xEC) || b0 == 0xEE || b0 == 0xEF {
        if n >= 3 && is_cont(s[i + 1]) && is_cont(s[i + 2]) {
            return 3;
        }
    } else if b0 == 0xED {
        if n >= 3 && s[i + 1] >= 0x80 && s[i + 1] <= 0x9F && is_cont(s[i + 2]) {
            return 3;
        }
    } else if b0 == 0xF0 {
        if n >= 4 && s[i + 1] >= 0x90 && s[i + 1] <= 0xBF && is_cont(s[i + 2]) && is_cont(s[i + 3]) {
            return 4;
        }
    } else if b0 >= 0xF1 && b0 <= 0xF3 {
        if n >= 4 && is_cont(s[i + 1]) && is_cont(s[i + 2]) && is_cont(s[i + 3]) {
            return 4;
        }
    } else if b0 == 0xF4 {
        if n >= 4 && s[i + 1] >= 0x80 && s[i + 1] <= 0x8F && is_cont(s[i + 2]) && is_cont(s[i + 3]) {
            return 4;
        }
    }
    0
}

// \" \\ \/ \b \f \n \r \t の表すバイト
#[logic(open)]
pub fn esc_byte(e: u8) -> Option<u8> {
    pearlite! {
        if e@ == 34 || e@ == 92 || e@ == 47 { Some(e) }
        else if e@ == 98 { Some(8u8) }
        else if e@ == 102 { Some(12u8) }
        else if e@ == 110 { Some(10u8) }
        else if e@ == 114 { Some(13u8) }
        else if e@ == 116 { Some(9u8) }
        else { None }
    }
}

#[logic(open)]
pub fn pre(p: Seq<u8>, r: Option<(Seq<u8>, Int)>) -> Option<(Seq<u8>, Int)> {
    pearlite! {
        match r {
            None => None,
            Some((t, e)) => Some((p.concat(t), e)),
        }
    }
}

// string(s, i): 開き引用符の直後 i から、復号したバイト列と閉じ引用符の直後の位置
// RFC 8259 §7: 文字列とエスケープ
#[logic(open)]
#[variant(s.len() - i)]
#[ensures(match result { Some((_, e)) => i < e && e <= s.len(), None => true })]
pub fn string_spec(s: Seq<u8>, i: Int) -> Option<(Seq<u8>, Int)> {
    pearlite! {
        if i < 0 || i >= s.len() {
            None
        } else if s[i]@ == 34 {
            Some((Seq::empty(), i + 1))
        } else if s[i]@ == 92 {
            if i + 1 >= s.len() {
                None
            } else {
                match esc_byte(s[i + 1]) {
                    Some(b) => pre(Seq::singleton(b), string_spec(s, i + 2)),
                    None => {
                        if s[i + 1]@ == 117 {
                            match hex4_spec(s, i + 2) {
                                None => None,
                                Some(u) => {
                                    if 0xD800 <= u && u <= 0xDBFF {
                                        if i + 8 <= s.len() && s[i + 6]@ == 92 && s[i + 7]@ == 117 {
                                            match hex4_spec(s, i + 8) {
                                                Some(l) => {
                                                    if 0xDC00 <= l && l <= 0xDFFF {
                                                        pre(utf8_enc(0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)), string_spec(s, i + 12))
                                                    } else {
                                                        None
                                                    }
                                                }
                                                None => None,
                                            }
                                        } else {
                                            None
                                        }
                                    } else if 0xDC00 <= u && u <= 0xDFFF {
                                        None
                                    } else {
                                        pre(utf8_enc(u), string_spec(s, i + 6))
                                    }
                                }
                            }
                        } else {
                            None
                        }
                    }
                }
            }
        } else if s[i]@ < 0x20 {
            None
        } else if s[i]@ < 0x80 {
            pre(Seq::singleton(s[i]), string_spec(s, i + 1))
        } else if utf8_wf_len(s, i) == 0 {
            None
        } else {
            pre(s[i..i + utf8_wf_len(s, i)], string_spec(s, i + utf8_wf_len(s, i)))
        }
    }
}

#[logic(opaque)]
#[ensures(pre(a, pre(b, r)) == pre(a.concat(b), r))]
pub fn lemma_pre_cat(a: Seq<u8>, b: Seq<u8>, r: Option<(Seq<u8>, Int)>) {
    pearlite! {
        match r {
            None => (),
            Some((t, _)) => { proof_assert!(a.concat(b.concat(t)).ext_eq(a.concat(b).concat(t))); }
        }
    }
}

#[logic(opaque)]
#[ensures(pre(Seq::empty(), r) == r)]
pub fn lemma_pre_empty(r: Option<(Seq<u8>, Int)>) {
    pearlite! { match r { None => (), Some((t, _)) => lemma_snoc_cat(t, 0u8) } }
}

#[logic(opaque)]
#[requires(0 <= j && 0 <= n && j + n <= s.len() && o.len() == o0.len() + n)]
#[requires(forall<t> 0 <= t && t < o0.len() ==> o[t] == o0[t])]
#[requires(forall<t> o0.len() <= t && t < o0.len() + n ==> o[t] == s[j + (t - o0.len())])]
#[ensures(o == o0.concat(s[j..j + n]))]
pub fn lemma_concat_sub(o: Seq<u8>, o0: Seq<u8>, s: Seq<u8>, j: Int, n: Int) {
    proof_assert!(o.ext_eq(o0.concat(s[j..j + n])));
}

// RFC 8259 §7: 文字列とエスケープ
#[bitwise_proof]
#[ensures(match result { None => string_spec(s@, i@) == None, Some((v, j)) => string_spec(s@, i@) == Some((v@, j@)) })]
#[check(terminates)]
pub(crate) fn parse_string(s: &[u8], i: usize) -> Option<(Vec<u8>, usize)> {
    let mut out: Vec<u8> = Vec::new();
    let mut j = i;
    snapshot!(lemma_pre_cat(Seq::empty(), Seq::empty(), None));
    snapshot!(lemma_snoc_cat(Seq::empty(), 0u8));
    snapshot!(lemma_pre_empty(None));
    proof_assert!(out@.ext_eq(Seq::empty()));
    #[invariant(string_spec(s@, i@) == pre(out@, string_spec(s@, j@)))]
    #[variant(s@.len() - j@)]
    loop {
        if j >= s.len() {
            return None;
        }
        let c = s[j];
        if c == b'"' {
            return Some((out, j + 1));
        } else if c == b'\\' {
            if j + 1 >= s.len() {
                return None;
            }
            let e = s[j + 1];
            if e == b'"' || e == b'\\' || e == b'/' {
                out.push(e);
                j += 2;
            } else if e == b'b' {
                out.push(0x08);
                j += 2;
            } else if e == b'f' {
                out.push(0x0C);
                j += 2;
            } else if e == b'n' {
                out.push(0x0A);
                j += 2;
            } else if e == b'r' {
                out.push(0x0D);
                j += 2;
            } else if e == b't' {
                out.push(0x09);
                j += 2;
            } else if e == b'u' {
                match parse_hex4(s, j + 2) {
                    None => return None,
                    Some(u) => {
                        if u >= 0xD800 && u <= 0xDBFF {
                            proof_assert!(0xD800 <= u@ && u@ <= 0xDBFF);
                            if s.len() - j > 7 && s[j + 6] == b'\\' && s[j + 7] == b'u' {
                                proof_assert!(j@ + 8 <= s@.len());
                                match parse_hex4(s, j + 8) {
                                    None => return None,
                                    Some(l) => {
                                        if l >= 0xDC00 && l <= 0xDFFF {
                                            proof_assert!(0xDC00 <= l@ && l@ <= 0xDFFF);
                                            proof_assert!((0x10000u32 + ((u - 0xD800u32) << 10u32) + (l - 0xDC00u32))@ == 0x10000 + (u@ - 0xD800) * 1024 + (l@ - 0xDC00));
                                            proof_assert!(string_spec(s@, j@) == pre(utf8_enc(0x10000 + (u@ - 0xD800) * 1024 + (l@ - 0xDC00)), string_spec(s@, j@ + 12)));
                                            push_utf8(&mut out, 0x10000 + ((u - 0xD800) << 10) + (l - 0xDC00));
                                            j += 12;
                                        } else {
                                            return None;
                                        }
                                    }
                                }
                            } else {
                                return None;
                            }
                        } else if u >= 0xDC00 && u <= 0xDFFF {
                            return None;
                        } else {
                            proof_assert!(!(0xD800 <= u@ && u@ <= 0xDFFF));
                            push_utf8(&mut out, u);
                            j += 6;
                        }
                    }
                }
            } else {
                return None;
            }
        } else if c < 0x20 {
            return None;
        } else if c < 0x80 {
            proof_assert!(0x20 <= c@ && c@ < 0x80 && c@ != 34 && c@ != 92);
            proof_assert!(string_spec(s@, j@) == pre(Seq::singleton(c), string_spec(s@, j@ + 1)));
            out.push(c);
            j += 1;
        } else {
            proof_assert!(0x80 <= c@);
            let n = utf8_len(s, j);
            if n == 0 {
                return None;
            }
            let _out0 = snapshot!(out@);
            let mut k = 0;
            #[invariant(k <= n && k@ <= n@ && j@ + n@ <= s@.len())]
            #[invariant(out@.len() == _out0.len() + k@)]
            #[invariant(forall<t> 0 <= t && t < _out0.len() ==> out@[t] == _out0[t])]
            #[invariant(forall<t> _out0.len() <= t && t < _out0.len() + k@ ==> out@[t] == s@[j@ + (t - _out0.len())])]
            #[variant(n@ - k@)]
            while k < n {
                out.push(s[j + k]);
                k += 1;
            }
            proof_assert!(k@ == n@);
            proof_assert!(string_spec(s@, j@) == pre(s@[j@..j@ + n@], string_spec(s@, j@ + n@)));
            snapshot!(lemma_concat_sub(out@, *_out0, s@, j@, n@));
            j += n;
        }
    }
}
