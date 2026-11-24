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

fn parse_hex4(s: &[u8], i: usize) -> Option<u32> {
    if i >= s.len() || s.len() - i < 4 {
        return None;
    }
    let mut v: u32 = 0;
    let mut k = 0;
    while k < 4 {
        match hex_value(s[i + k]) {
            Some(h) => v = v * 16 + h,
            None => return None,
        }
        k += 1;
    }
    Some(v)
}

fn push_utf8(out: &mut Vec<u8>, c: u32) {
    if c < 0x80 {
        out.push(c as u8);
    } else if c < 0x800 {
        out.push((0xC0 | (c >> 6)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
    } else if c < 0x10000 {
        out.push((0xE0 | (c >> 12)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
    } else {
        out.push((0xF0 | (c >> 18)) as u8);
        out.push((0x80 | ((c >> 12) & 0x3F)) as u8);
        out.push((0x80 | ((c >> 6) & 0x3F)) as u8);
        out.push((0x80 | (c & 0x3F)) as u8);
    }
}

fn is_cont(b: u8) -> bool {
    b >= 0x80 && b <= 0xBF
}

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

pub(crate) fn parse_string(s: &[u8], i: usize) -> Option<(Vec<u8>, usize)> {
    let mut out: Vec<u8> = Vec::new();
    let mut j = i;
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
                            if s.len() - j > 7 && s[j + 6] == b'\\' && s[j + 7] == b'u' {
                                match parse_hex4(s, j + 8) {
                                    None => return None,
                                    Some(l) => {
                                        if l >= 0xDC00 && l <= 0xDFFF {
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
            out.push(c);
            j += 1;
        } else {
            let n = utf8_len(s, j);
            if n == 0 {
                return None;
            }
            let mut k = 0;
            while k < n {
                out.push(s[j + k]);
                k += 1;
            }
            j += n;
        }
    }
}
