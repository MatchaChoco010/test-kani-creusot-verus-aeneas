pub struct GlbChunks {
    pub json: Vec<u8>,
    pub bin_len: Option<u64>,
}

fn read_u32(s: &[u8], i: usize) -> u32 {
    (s[i] as u32) | ((s[i + 1] as u32) << 8) | ((s[i + 2] as u32) << 16) | ((s[i + 3] as u32) << 24)
}

pub fn is_glb(bytes: &[u8]) -> bool {
    bytes.len() >= 4 && bytes[0] == 0x67 && bytes[1] == 0x6C && bytes[2] == 0x54 && bytes[3] == 0x46
}

fn copy_range(s: &[u8], start: usize, end: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut k = start;
    while k < end {
        out.push(s[k]);
        k += 1;
    }
    out
}

fn scan_chunks(s: &[u8], total: usize) -> Option<(usize, usize, Option<u64>)> {
    let mut json: Option<(usize, usize)> = None;
    let mut bin_len: Option<u64> = None;
    let mut pos = 12;
    let mut index: usize = 0;
    while pos < total {
        if total - pos < 8 {
            return None;
        }
        let len = read_u32(s, pos) as usize;
        let kind = read_u32(s, pos + 4);
        if len % 4 != 0 || total - pos - 8 < len {
            return None;
        }
        if index == 0 {
            if kind != 0x4E4F534A {
                return None;
            }
            json = Some((pos + 8, len));
        } else if kind == 0x4E4F534A || (kind == 0x004E4942 && index != 1) {
            return None;
        } else if kind == 0x004E4942 {
            bin_len = Some(len as u64);
        }
        pos = pos + 8 + len;
        index += 1;
    }
    match json {
        None => None,
        Some((start, len)) => Some((start, len, bin_len)),
    }
}

pub fn parse_glb(s: &[u8]) -> Option<GlbChunks> {
    if s.len() < 12 || read_u32(s, 0) != 0x46546C67 || read_u32(s, 4) != 2 {
        return None;
    }
    let total = read_u32(s, 8) as usize;
    if total < 12 || total > s.len() {
        return None;
    }
    match scan_chunks(s, total) {
        None => None,
        Some((start, len, bin_len)) => Some(GlbChunks { json: copy_range(s, start, start + len), bin_len }),
    }
}
