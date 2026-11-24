use vstd::prelude::*;

verus! {

pub open spec fn hex_val(b: u8) -> Option<int> {
    if b'0' <= b <= b'9' {
        Some(b - b'0')
    } else if b'A' <= b <= b'F' {
        Some(b - b'A' + 10)
    } else if b'a' <= b <= b'f' {
        Some(b - b'a' + 10)
    } else {
        None
    }
}

fn hex_value(b: u8) -> (r: Option<u32>)
    ensures
        match r {
            Some(h) => hex_val(b) == Some(h as int),
            None => hex_val(b) is None,
        },
{
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

// ちょうど 4 桁の 16 進数
pub open spec fn hex4(s: Seq<u8>, i: int) -> Option<int> {
    if 0 <= i && i + 4 <= s.len() && hex_val(s[i]) is Some && hex_val(s[i + 1]) is Some && hex_val(s[i + 2]) is Some
        && hex_val(s[i + 3]) is Some {
        Some(
            hex_val(s[i])->Some_0 * 4096 + hex_val(s[i + 1])->Some_0 * 256 + hex_val(s[i + 2])->Some_0 * 16
                + hex_val(s[i + 3])->Some_0,
        )
    } else {
        None
    }
}

pub open spec fn hex_prefix(s: Seq<u8>, i: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        hex_prefix(s, i, k - 1) * 16 + hex_val(s[i + k - 1])->Some_0
    }
}

fn parse_hex4(s: &[u8], i: usize) -> (r: Option<u32>)
    ensures
        match r {
            Some(v) => hex4(s@, i as int) == Some(v as int),
            None => hex4(s@, i as int) is None,
        },
{
    if i >= s.len() || s.len() - i < 4 {
        return None;
    }
    let mut v: u32 = 0;
    let mut k = 0;
    while k < 4
        invariant
            i + 4 <= s.len(),
            0 <= k <= 4,
            forall|m: int| 0 <= m < k ==> hex_val(#[trigger] s@[i + m]) is Some,
            v as int == hex_prefix(s@, i as int, k as int),
            0 <= v < (if k == 0 { 1int } else if k == 1 { 16 } else if k == 2 { 256 } else if k == 3 { 4096 } else { 65536 }),
        decreases 4 - k,
    {
        match hex_value(s[i + k]) {
            Some(h) => v = v * 16 + h,
            None => return None,
        }
        k += 1;
    }
    proof {
        reveal_with_fuel(hex_prefix, 5);
        assert(hex_val(s@[i + 0]) is Some);
        assert(hex_val(s@[i + 1]) is Some);
        assert(hex_val(s@[i + 2]) is Some);
        assert(hex_val(s@[i + 3]) is Some);
    }
    Some(v)
}

// 符号位置 c の標準 UTF-8 符号化
pub open spec fn utf8_encode(c: int) -> Seq<u8> {
    if c < 0x80 {
        seq![c as u8]
    } else if c < 0x800 {
        seq![(0xC0 + c / 64) as u8, (0x80 + c % 64) as u8]
    } else if c < 0x10000 {
        seq![(0xE0 + c / 4096) as u8, (0x80 + (c / 64) % 64) as u8, (0x80 + c % 64) as u8]
    } else {
        seq![
            (0xF0 + c / 262144) as u8,
            (0x80 + (c / 4096) % 64) as u8,
            (0x80 + (c / 64) % 64) as u8,
            (0x80 + c % 64) as u8,
        ]
    }
}

fn push_utf8(out: &mut Vec<u8>, c: u32)
    requires
        c < 0x110000,
    ensures
        final(out)@ == old(out)@ + utf8_encode(c as int),
{
    let ghost o = out@;
    if c < 0x80 {
        out.push(c as u8);
        assert(out@ =~= o + utf8_encode(c as int));
    } else if c < 0x800 {
        assert((0xC0 | (c >> 6)) == 0xC0 + c / 64 && (0x80 | (c & 0x3F)) == 0x80 + c % 64 && 0xC0 + c / 64 < 256)
            by (bit_vector)
            requires
                0x80 <= c < 0x800,
        ;
        out.push((0xC0 | (c >> 6)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        assert(out@ =~= o + utf8_encode(c as int));
    } else if c < 0x10000 {
        assert((0xE0 | (c >> 12)) == 0xE0 + c / 4096 && (0x80 | ((c >> 6) & 0x3F)) == 0x80 + (c / 64) % 64 && (0x80
            | (c & 0x3F)) == 0x80 + c % 64 && 0xE0 + c / 4096 < 256) by (bit_vector)
            requires
                0x800 <= c < 0x10000,
        ;
        out.push((0xE0 | (c >> 12)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        assert(out@ =~= o + utf8_encode(c as int));
    } else {
        assert((0xF0 | (c >> 18)) == 0xF0 + c / 262144 && (0x80 | ((c >> 12) & 0x3F)) == 0x80 + (c / 4096) % 64 && (
        0x80 | ((c >> 6) & 0x3F)) == 0x80 + (c / 64) % 64 && (0x80 | (c & 0x3F)) == 0x80 + c % 64 && 0xF0 + c
            / 262144 < 256) by (bit_vector)
            requires
                0x10000 <= c < 0x110000,
        ;
        out.push((0xF0 | (c >> 18)) as u8);
        out.push((0x80 | ((c >> 12) & 0x3F)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
        assert(out@ =~= o + utf8_encode(c as int));
    }
}

pub open spec fn cont(b: u8) -> bool {
    0x80 <= b <= 0xBF
}

fn is_cont(b: u8) -> (r: bool)
    ensures
        r == cont(b),
{
    b >= 0x80 && b <= 0xBF
}

// Unicode Table 3-7 のいずれかの行に一致する列の長さ（一致しなければ 0）
pub open spec fn utf8_wf_len(s: Seq<u8>, i: int) -> int {
    let n = s.len() - i;
    let b0 = s[i];
    if 0xC2 <= b0 <= 0xDF && n >= 2 && cont(s[i + 1]) {
        2
    } else if b0 == 0xE0 && n >= 3 && 0xA0 <= s[i + 1] <= 0xBF && cont(s[i + 2]) {
        3
    } else if (0xE1 <= b0 <= 0xEC || 0xEE <= b0 <= 0xEF) && n >= 3 && cont(s[i + 1]) && cont(s[i + 2]) {
        3
    } else if b0 == 0xED && n >= 3 && 0x80 <= s[i + 1] <= 0x9F && cont(s[i + 2]) {
        3
    } else if b0 == 0xF0 && n >= 4 && 0x90 <= s[i + 1] <= 0xBF && cont(s[i + 2]) && cont(s[i + 3]) {
        4
    } else if 0xF1 <= b0 <= 0xF3 && n >= 4 && cont(s[i + 1]) && cont(s[i + 2]) && cont(s[i + 3]) {
        4
    } else if b0 == 0xF4 && n >= 4 && 0x80 <= s[i + 1] <= 0x8F && cont(s[i + 2]) && cont(s[i + 3]) {
        4
    } else {
        0
    }
}

fn utf8_len(s: &[u8], i: usize) -> (r: usize)
    requires
        i < s.len(),
    ensures
        r as int == utf8_wf_len(s@, i as int),
{
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

pub open spec fn prepend(p: Seq<u8>, r: Option<(Seq<u8>, int)>) -> Option<(Seq<u8>, int)> {
    match r {
        Some((b, e)) => Some((p + b, e)),
        None => None,
    }
}

// string(s, i): 開き引用符の直後から。復号したバイト列と閉じ引用符の次の位置
// RFC 8259 §7: 文字列とエスケープ
pub open spec fn string_spec(s: Seq<u8>, i: int) -> Option<(Seq<u8>, int)>
    decreases s.len() - i,
{
    if i < 0 || i >= s.len() {
        None
    } else {
        let c = s[i];
        if c == b'"' {
            Some((seq![], i + 1))
        } else if c == b'\\' {
            if i + 1 >= s.len() {
                None
            } else {
                let e = s[i + 1];
                if e == b'"' || e == b'\\' || e == b'/' {
                    prepend(seq![e], string_spec(s, i + 2))
                } else if e == b'b' {
                    prepend(seq![0x08u8], string_spec(s, i + 2))
                } else if e == b'f' {
                    prepend(seq![0x0Cu8], string_spec(s, i + 2))
                } else if e == b'n' {
                    prepend(seq![0x0Au8], string_spec(s, i + 2))
                } else if e == b'r' {
                    prepend(seq![0x0Du8], string_spec(s, i + 2))
                } else if e == b't' {
                    prepend(seq![0x09u8], string_spec(s, i + 2))
                } else if e == b'u' {
                    match hex4(s, i + 2) {
                        None => None,
                        Some(u) => {
                            if 0xD800 <= u <= 0xDBFF {
                                if i + 7 < s.len() && s[i + 6] == b'\\' && s[i + 7] == b'u' {
                                    match hex4(s, i + 8) {
                                        Some(l) => {
                                            if 0xDC00 <= l <= 0xDFFF {
                                                prepend(
                                                    utf8_encode(0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)),
                                                    string_spec(s, i + 12),
                                                )
                                            } else {
                                                None
                                            }
                                        },
                                        None => None,
                                    }
                                } else {
                                    None
                                }
                            } else if 0xDC00 <= u <= 0xDFFF {
                                None
                            } else {
                                prepend(utf8_encode(u), string_spec(s, i + 6))
                            }
                        },
                    }
                } else {
                    None
                }
            }
        } else if c < 0x20 {
            None
        } else if c < 0x80 {
            prepend(seq![c], string_spec(s, i + 1))
        } else {
            let n = utf8_wf_len(s, i);
            if n == 0 {
                None
            } else {
                prepend(s.subrange(i, i + n), string_spec(s, i + n))
            }
        }
    }
}

pub proof fn lemma_prepend_assoc(a: Seq<u8>, b: Seq<u8>, r: Option<(Seq<u8>, int)>)
    ensures
        prepend(a, prepend(b, r)) == prepend(a + b, r),
{
    match r {
        Some((x, e)) => {
            assert(a + (b + x) =~= (a + b) + x);
        },
        None => {},
    }
}

pub(crate) fn parse_string(s: &[u8], i: usize) -> (r: Option<(Vec<u8>, usize)>)
    requires
        i <= s.len(),
    ensures
        match r {
            Some((v, j)) => string_spec(s@, i as int) == Some((v@, j as int)) && i < j <= s.len(),
            None => string_spec(s@, i as int) is None,
        },
{
    let mut out: Vec<u8> = Vec::new();
    let mut j = i;
    assert(string_spec(s@, i as int) == prepend(out@, string_spec(s@, j as int))) by {
        match string_spec(s@, i as int) {
            Some((b, e)) => {
                assert(out@ + b =~= b);
            },
            None => {},
        }
    }
    loop
        invariant
            i <= j <= s.len(),
            string_spec(s@, i as int) == prepend(out@, string_spec(s@, j as int)),
        decreases s.len() - j,
    {
        if j >= s.len() {
            return None;
        }
        let ghost o = out@;
        let c = s[j];
        if c == b'"' {
            assert(o + seq![] =~= o);
            return Some((out, j + 1));
        } else if c == b'\\' {
            if j + 1 >= s.len() {
                return None;
            }
            let e = s[j + 1];
            if e == b'"' || e == b'\\' || e == b'/' {
                out.push(e);
                j += 2;
                proof {
                    lemma_prepend_assoc(o, seq![e], string_spec(s@, j as int));
                    assert(out@ =~= o + seq![e]);
                }
            } else if e == b'b' {
                out.push(0x08);
                j += 2;
                proof {
                    lemma_prepend_assoc(o, seq![0x08u8], string_spec(s@, j as int));
                    assert(out@ =~= o + seq![0x08u8]);
                }
            } else if e == b'f' {
                out.push(0x0C);
                j += 2;
                proof {
                    lemma_prepend_assoc(o, seq![0x0Cu8], string_spec(s@, j as int));
                    assert(out@ =~= o + seq![0x0Cu8]);
                }
            } else if e == b'n' {
                out.push(0x0A);
                j += 2;
                proof {
                    lemma_prepend_assoc(o, seq![0x0Au8], string_spec(s@, j as int));
                    assert(out@ =~= o + seq![0x0Au8]);
                }
            } else if e == b'r' {
                out.push(0x0D);
                j += 2;
                proof {
                    lemma_prepend_assoc(o, seq![0x0Du8], string_spec(s@, j as int));
                    assert(out@ =~= o + seq![0x0Du8]);
                }
            } else if e == b't' {
                out.push(0x09);
                j += 2;
                proof {
                    lemma_prepend_assoc(o, seq![0x09u8], string_spec(s@, j as int));
                    assert(out@ =~= o + seq![0x09u8]);
                }
            } else if e == b'u' {
                match parse_hex4(s, j + 2) {
                    None => return None,
                    Some(u) => {
                        if u >= 0xD800 && u <= 0xDBFF {
                            if s.len() - j > 7 && s[j + 6] == b'\\' && s[j + 7] == b'u' {
                                match parse_hex4(s, j + 8) {
                                    None => return None,
                                    Some(l) => {
                                        if l >= 0xDC00 && l <= 0xDFFF {
                                            let ghost w: u32 = (u - 0xD800) as u32;
                                            proof {
                                                vstd::arithmetic::power2::lemma2_to64();
                                                vstd::bits::lemma_u32_shl_is_mul(w, 10);
                                            }
                                            let ghost cp = 0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00);
                                            push_utf8(&mut out, 0x10000 + ((u - 0xD800) << 10) + (l - 0xDC00));
                                            j += 12;
                                            proof {
                                                lemma_prepend_assoc(o, utf8_encode(cp), string_spec(s@, j as int));
                                            }
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
                            push_utf8(&mut out, u);
                            j += 6;
                            proof {
                                lemma_prepend_assoc(o, utf8_encode(u as int), string_spec(s@, j as int));
                            }
                        }
                    }
                }
            } else {
                return None;
            }
        } else if c < 0x20 {
            return None;
        } else if c < 0x80 {
            out.push(c);
            j += 1;
            proof {
                lemma_prepend_assoc(o, seq![c], string_spec(s@, j as int));
                assert(out@ =~= o + seq![c]);
            }
        } else {
            let n = utf8_len(s, j);
            if n == 0 {
                return None;
            }
            let mut k = 0;
            while k < n
                invariant
                    j + n <= s.len(),
                    0 <= k <= n,
                    out@ == o + s@.subrange(j as int, j + k),
                decreases n - k,
            {
                out.push(s[j + k]);
                k += 1;
                assert(out@ =~= o + s@.subrange(j as int, j + k));
            }
            proof {
                lemma_prepend_assoc(o, s@.subrange(j as int, j + n), string_spec(s@, j + n));
            }
            j += n;
        }
    }
}

} // verus!
