use creusot_std::prelude::*;
#[cfg(creusot)]
use crate::model::*;

pub struct GlbChunks {
    pub json: Vec<u8>,
    pub bin_len: Option<u64>,
}

#[logic(open)]
pub fn u32le(s: Seq<u8>, i: Int) -> Int {
    pearlite! { s[i]@ + 256 * s[i + 1]@ + 65536 * s[i + 2]@ + 16777216 * s[i + 3]@ }
}

#[requires(i@ + 4 <= s@.len())]
#[bitwise_proof]
#[ensures(result@ == u32le(s@, i@))]
#[check(terminates)]
fn read_u32(s: &[u8], i: usize) -> u32 {
    (s[i] as u32) | ((s[i + 1] as u32) << 8) | ((s[i + 2] as u32) << 16) | ((s[i + 3] as u32) << 24)
}

#[logic(open)]
pub fn is_glb_spec(s: Seq<u8>) -> bool {
    pearlite! { s.len() >= 4 && s[0]@ == 0x67 && s[1]@ == 0x6C && s[2]@ == 0x54 && s[3]@ == 0x46 }
}

#[ensures(result == is_glb_spec(bytes@))]
#[check(terminates)]
pub fn is_glb(bytes: &[u8]) -> bool {
    bytes.len() >= 4 && bytes[0] == 0x67 && bytes[1] == 0x6C && bytes[2] == 0x54 && bytes[3] == 0x46
}

#[requires(start@ <= end@ && end@ <= s@.len())]
#[ensures(result@ == s@[start@..end@])]
#[check(terminates)]
fn copy_range(s: &[u8], start: usize, end: usize) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut k = start;
    #[invariant(start@ <= k@ && k@ <= end@)]
    #[invariant(out@ == s@[start@..k@])]
    #[variant(end@ - k@)]
    while k < end {
        out.push(s[k]);
        k += 1;
        proof_assert!(out@.ext_eq(s@[start@..k@]));
    }
    out
}

#[logic(open)]
pub fn chunk_json() -> Int {
    0x4E4F534A
}

#[logic(open)]
pub fn chunk_bin() -> Int {
    0x004E4942
}

// チャンク m の位置 p_m（p_0 = 12, p_{m+1} = p_m + 8 + len_m）
#[logic(open)]
#[variant(m)]
pub fn chunk_pos(s: Seq<u8>, m: Int) -> Int {
    pearlite! { if m <= 0 { 12 } else { chunk_pos(s, m - 1) + 8 + u32le(s, chunk_pos(s, m - 1)) } }
}

#[logic(open)]
pub fn chunk_len(s: Seq<u8>, m: Int) -> Int {
    pearlite! { u32le(s, chunk_pos(s, m)) }
}

#[logic(open)]
pub fn chunk_type(s: Seq<u8>, m: Int) -> Int {
    pearlite! { u32le(s, chunk_pos(s, m) + 4) }
}

// MUST-159: chunkLength は 4 の倍数
#[logic(open)]
pub fn chunk_fits(s: Seq<u8>, l: Int, m: Int) -> bool {
    pearlite! { chunk_len(s, m) % 4 == 0 && chunk_pos(s, m) + 8 + chunk_len(s, m) <= l }
}

// s[12..L] がちょうど k 個のチャンクに分かれる
#[logic(open)]
pub fn splits(s: Seq<u8>, l: Int, k: Int) -> bool {
    pearlite! { k >= 1 && chunk_pos(s, k) == l && forall<m> 0 <= m && m < k ==> chunk_fits(s, l, m) }
}

// MUST-160, MUST-161: JSON チャンクは最初に 1 つだけ、BIN チャンクは 2 番目に 1 つまで
#[logic(open)]
pub fn types_ok(s: Seq<u8>, k: Int) -> bool {
    pearlite! {
        chunk_type(s, 0) == chunk_json()
            && (forall<m> 1 <= m && m < k ==> chunk_type(s, m) != chunk_json())
            && (forall<m> 0 <= m && m < k && chunk_type(s, m) == chunk_bin() ==> m == 1)
    }
}

// 位置は 1 チャンクごとに 8 以上進む
#[logic(opaque)]
#[variant(b)]
#[requires(0 <= a && a <= b)]
#[ensures(chunk_pos(s, a) + 8 * (b - a) <= chunk_pos(s, b))]
pub fn lemma_pos_mono(s: Seq<u8>, a: Int, b: Int) {
    if a < b {
        lemma_pos_mono(s, a, b - 1)
    }
}

// 位置 p_i が L より前なら、分割のチャンク数は i より大きい
#[logic(opaque)]
#[requires(0 <= i && chunk_pos(s, i) < l)]
#[ensures(forall<k> splits(s, l, k) ==> i < k && chunk_fits(s, l, i))]
#[ensures(forall<k> splits(s, l, k) && types_ok(s, k) ==>
    (i == 0 ==> chunk_type(s, i) == chunk_json()) && (i >= 1 ==> chunk_type(s, i) != chunk_json())
    && (chunk_type(s, i) == chunk_bin() ==> i == 1))]
pub fn lemma_split_after(s: Seq<u8>, l: Int, i: Int) {
    lemma_pos_mono(s, 0, 0)
}

// MUST-159: chunkLength は 4 の倍数
// MUST-160, MUST-161: JSON チャンクは最初に 1 つだけ、BIN チャンクは 2 番目に 1 つまで
#[requires(12 <= total@ && total@ <= s@.len() && total@ <= u32::MAX@)]
#[ensures(match result {
    None => !exists<k> splits(s@, total@, k) && types_ok(s@, k),
    Some((st, len, bl)) => exists<k> splits(s@, total@, k) && types_ok(s@, k)
        && st@ == chunk_pos(s@, 0) + 8 && len@ == chunk_len(s@, 0) && st@ + len@ <= total@
        && opt_int(bl) == if k >= 2 && chunk_type(s@, 1) == chunk_bin() { Some(chunk_len(s@, 1)) } else { None },
})]
#[check(terminates)]
fn scan_chunks(s: &[u8], total: usize) -> Option<(usize, usize, Option<u64>)> {
    let mut json: Option<(usize, usize)> = None;
    let mut bin_len: Option<u64> = None;
    let mut pos = 12;
    let mut index: usize = 0;
    #[invariant(12 <= pos@ && pos@ <= total@)]
    #[invariant(pos@ == chunk_pos(s@, index@))]
    #[invariant(pos@ >= 12 + 8 * index@)]
    #[invariant(forall<m> 0 <= m && m < index@ ==> chunk_fits(s@, total@, m))]
    #[invariant(index@ >= 1 ==> chunk_type(s@, 0) == chunk_json())]
    #[invariant(forall<m> 1 <= m && m < index@ ==> chunk_type(s@, m) != chunk_json())]
    #[invariant(forall<m> 0 <= m && m < index@ && chunk_type(s@, m) == chunk_bin() ==> m == 1)]
    #[invariant(match json { None => index@ == 0, Some((st, ln)) => index@ >= 1 && st@ == chunk_pos(s@, 0) + 8 && ln@ == chunk_len(s@, 0) })]
    #[invariant(opt_int(bin_len) == if index@ >= 2 && chunk_type(s@, 1) == chunk_bin() { Some(chunk_len(s@, 1)) } else { None })]
    #[variant(total@ - pos@)]
    while pos < total {
        snapshot!(lemma_split_after(s@, total@, index@));
        if total - pos < 8 {
            return None;
        }
        let len = read_u32(s, pos) as usize;
        let kind = read_u32(s, pos + 4);
        proof_assert!(len@ == chunk_len(s@, index@) && kind@ == chunk_type(s@, index@));
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
    snapshot!(lemma_pos_mono(s@, 0, index@));
    proof_assert!(index@ >= 1 ==> splits(s@, total@, index@));
    match json {
        None => None,
        Some((start, len)) => Some((start, len, bin_len)),
    }
}

#[cfg(creusot)]
pub struct GlbS {
    pub json: Seq<u8>,
    pub bin_len: Option<Int>,
}

// MUST-158: GLB の magic
#[logic(open)]
pub fn header_ok(s: Seq<u8>) -> bool {
    pearlite! {
        s.len() >= 12 && u32le(s, 0) == 0x46546C67 && u32le(s, 4) == 2 && 12 <= u32le(s, 8) && u32le(s, 8) <= s.len()
    }
}

// glTF 4.4: GLB のヘッダーとチャンク
#[logic(open)]
pub fn glb_spec(s: Seq<u8>) -> Option<GlbS> {
    pearlite! {
        if header_ok(s) && exists<k> splits(s, u32le(s, 8), k) && types_ok(s, k) {
            Some(GlbS {
                json: s[chunk_pos(s, 0) + 8..chunk_pos(s, 0) + 8 + chunk_len(s, 0)],
                bin_len: if (exists<k> splits(s, u32le(s, 8), k) && k >= 2) && chunk_type(s, 1) == chunk_bin() {
                    Some(chunk_len(s, 1))
                } else {
                    None
                },
            })
        } else {
            None
        }
    }
}

// 分割のチャンク数は一意
#[logic(opaque)]
#[ensures(forall<k1, k2> splits(s, l, k1) && splits(s, l, k2) ==> k1 == k2)]
pub fn lemma_split_unique(s: Seq<u8>, l: Int) {
    lemma_pos_mono(s, 0, 0)
}

// MUST-158: GLB の magic
#[ensures(match result {
    None => glb_spec(s@) == None,
    Some(c) => glb_spec(s@) == Some(GlbS { json: c.json@, bin_len: opt_int(c.bin_len) }),
})]
#[check(terminates)]
pub fn parse_glb(s: &[u8]) -> Option<GlbChunks> {
    if s.len() < 12 || read_u32(s, 0) != 0x46546C67 || read_u32(s, 4) != 2 {
        return None;
    }
    let total = read_u32(s, 8) as usize;
    if total < 12 || total > s.len() {
        return None;
    }
    snapshot!(lemma_split_unique(s@, total@));
    match scan_chunks(s, total) {
        None => None,
        Some((start, len, bin_len)) => Some(GlbChunks { json: copy_range(s, start, start + len), bin_len }),
    }
}
