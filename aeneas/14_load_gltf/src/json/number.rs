pub struct Number {
    pub negative: bool,
    pub int_digits: Vec<u8>,
    pub frac_digits: Vec<u8>,
    pub exp_negative: bool,
    pub exp_digits: Vec<u8>,
}

pub(crate) fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

fn parse_digits(s: &[u8], i: usize, out: &mut Vec<u8>) -> usize {
    let mut j = i;
    while j < s.len() && is_digit(s[j]) {
        out.push(s[j] - b'0');
        j += 1;
    }
    j
}

pub(crate) fn parse_number(s: &[u8], i: usize) -> Option<(Number, usize)> {
    let mut j = i;
    let mut negative = false;
    if s[j] == b'-' {
        negative = true;
        j += 1;
    }
    let mut int_digits: Vec<u8> = Vec::new();
    if j >= s.len() || !is_digit(s[j]) {
        return None;
    }
    if s[j] == b'0' {
        int_digits.push(0);
        j += 1;
    } else {
        j = parse_digits(s, j, &mut int_digits);
    }
    let mut frac_digits: Vec<u8> = Vec::new();
    if j < s.len() && s[j] == b'.' {
        let k = parse_digits(s, j + 1, &mut frac_digits);
        if k == j + 1 {
            return None;
        }
        j = k;
    }
    let mut exp_negative = false;
    let mut exp_digits: Vec<u8> = Vec::new();
    if j < s.len() && (s[j] == b'e' || s[j] == b'E') {
        j += 1;
        if j < s.len() && (s[j] == b'+' || s[j] == b'-') {
            exp_negative = s[j] == b'-';
            j += 1;
        }
        let k = parse_digits(s, j, &mut exp_digits);
        if k == j {
            return None;
        }
        j = k;
    }
    Some((Number { negative, int_digits, frac_digits, exp_negative, exp_digits }, j))
}

fn digit_at(n: &Number, k: usize) -> u8 {
    if k < n.int_digits.len() { n.int_digits[k] } else { n.frac_digits[k - n.int_digits.len()] }
}

fn all_digits_zero(n: &Number) -> bool {
    let total = n.int_digits.len() + n.frac_digits.len();
    let mut k = 0;
    while k < total {
        if digit_at(n, k) != 0 {
            return false;
        }
        k += 1;
    }
    true
}

fn exponent_value(n: &Number) -> u64 {
    let mut e: u64 = 0;
    let mut k = 0;
    while k < n.exp_digits.len() {
        e = match e.checked_mul(10) {
            Some(t) => match t.checked_add(n.exp_digits[k] as u64) {
                Some(u) => u,
                None => u64::MAX,
            },
            None => u64::MAX,
        };
        k += 1;
    }
    e
}

fn digits_zero_from(n: &Number, from: usize) -> bool {
    let total = n.int_digits.len() + n.frac_digits.len();
    let mut k = from;
    while k < total {
        if digit_at(n, k) != 0 {
            return false;
        }
        k += 1;
    }
    true
}

fn digits_value(n: &Number, keep: usize) -> Option<u64> {
    let mut v: u64 = 0;
    let mut k = 0;
    while k < keep {
        v = match v.checked_mul(10) {
            Some(t) => match t.checked_add(digit_at(n, k) as u64) {
                Some(u) => u,
                None => return None,
            },
            None => return None,
        };
        k += 1;
    }
    Some(v)
}

fn mul_pow10(v: u64, shift: u64) -> Option<u64> {
    let mut r = v;
    let mut s: u64 = 0;
    while s < shift {
        r = match r.checked_mul(10) {
            Some(t) => t,
            None => return None,
        };
        s += 1;
    }
    Some(r)
}

pub fn number_to_u64(n: &Number) -> Option<u64> {
    if all_digits_zero(n) {
        return Some(0);
    }
    if n.negative {
        return None;
    }
    let total = n.int_digits.len() + n.frac_digits.len();
    let e = exponent_value(n);
    let f = n.frac_digits.len() as u64;
    if !n.exp_negative && e >= f {
        match digits_value(n, total) {
            None => None,
            Some(v) => mul_pow10(v, e - f),
        }
    } else {
        let drop = if n.exp_negative { e.saturating_add(f) } else { f - e };
        if drop >= total as u64 {
            return None;
        }
        let keep = total - drop as usize;
        if !digits_zero_from(n, keep) {
            return None;
        }
        digits_value(n, keep)
    }
}
