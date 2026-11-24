use vstd::prelude::*;

verus! {

pub struct GlbChunks {
    pub json: Vec<u8>,
    pub bin_len: Option<u64>,
}

// G: GLB コンテナ
pub open spec fn u32le(s: Seq<u8>, i: int) -> int {
    s[i] + 256 * s[i + 1] + 65536 * s[i + 2] + 16777216 * s[i + 3]
}

pub proof fn lemma_u32le(b0: u8, b1: u8, b2: u8, b3: u8)
    ensures
        ((b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)) == b0 + 256 * b1 + 65536 * b2
            + 16777216 * b3,
{
    assert(((b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24)) == b0 + 256 * b1 + 65536 * b2
        + 16777216 * b3) by (bit_vector);
}

fn read_u32(s: &[u8], i: usize) -> (r: u32)
    requires
        i + 4 <= s.len(),
    ensures
        r as int == u32le(s@, i as int),
{
    proof {
        lemma_u32le(s@[i as int], s@[i + 1], s@[i + 2], s@[i + 3]);
    }
    (s[i] as u32) | ((s[i + 1] as u32) << 8) | ((s[i + 2] as u32) << 16) | ((s[i + 3] as u32) << 24)
}

pub open spec fn is_glb_s(s: Seq<u8>) -> bool {
    s.len() >= 4 && s[0] == 0x67 && s[1] == 0x6C && s[2] == 0x54 && s[3] == 0x46
}

pub fn is_glb(bytes: &[u8]) -> (r: bool)
    ensures
        r == is_glb_s(bytes@),
{
    bytes.len() >= 4 && bytes[0] == 0x67 && bytes[1] == 0x6C && bytes[2] == 0x54 && bytes[3] == 0x46
}

fn copy_range(s: &[u8], start: usize, end: usize) -> (r: Vec<u8>)
    requires
        start <= end <= s.len(),
    ensures
        r@ == s@.subrange(start as int, end as int),
{
    let mut out: Vec<u8> = Vec::new();
    let mut k = start;
    while k < end
        invariant
            start <= k <= end <= s.len(),
            out@ == s@.subrange(start as int, k as int),
        decreases end - k,
    {
        out.push(s[k]);
        k += 1;
        assert(out@ =~= s@.subrange(start as int, k as int));
    }
    out
}

pub struct ChunkS {
    pub pos: int,
    pub len: int,
    pub typ: int,
}

pub open spec fn glb_json() -> int {
    0x4E4F534A
}

pub open spec fn glb_bin() -> int {
    0x004E4942
}

// s[p..l] をちょうど分割するチャンクの列
// MUST-159: chunkLength は 4 の倍数
pub open spec fn chunks_from(s: Seq<u8>, p: int, l: int) -> Option<Seq<ChunkS>>
    decreases l - p,
{
    if p == l {
        Some(seq![])
    } else if p > l || l - p < 8 {
        None
    } else {
        let len = u32le(s, p);
        let typ = u32le(s, p + 4);
        if len % 4 != 0 || p + 8 + len > l {
            None
        } else {
            match chunks_from(s, p + 8 + len, l) {
                Some(rest) => Some(seq![ChunkS { pos: p, len, typ }] + rest),
                None => None,
            }
        }
    }
}

// MUST-160, MUST-161: JSON チャンクは最初に 1 つだけ、BIN チャンクは 2 番目に高々 1 つ
pub open spec fn chunks_ok(cs: Seq<ChunkS>) -> bool {
    &&& cs.len() >= 1
    &&& cs[0].typ == glb_json()
    &&& forall|m: int| 1 <= m < cs.len() ==> (#[trigger] cs[m]).typ != glb_json()
    &&& forall|m: int| 0 <= m < cs.len() && (#[trigger] cs[m]).typ == glb_bin() ==> m == 1
}

pub open spec fn chunks_bin(cs: Seq<ChunkS>) -> Option<u64> {
    if cs.len() >= 2 && cs[1].typ == glb_bin() {
        Some(cs[1].len as u64)
    } else {
        None
    }
}

pub open spec fn lift(p: Seq<ChunkS>, r: Option<Seq<ChunkS>>) -> Option<Seq<ChunkS>> {
    match r {
        Some(rest) => Some(p + rest),
        None => None,
    }
}

// 途中までのチャンクについての条件
pub open spec fn prefix_ok(p: Seq<ChunkS>) -> bool {
    &&& (p.len() >= 1 ==> p[0].typ == glb_json())
    &&& forall|m: int| 1 <= m < p.len() ==> (#[trigger] p[m]).typ != glb_json()
    &&& forall|m: int| 0 <= m < p.len() && (#[trigger] p[m]).typ == glb_bin() ==> m == 1
}

pub proof fn lemma_chunks_fail(s: Seq<u8>, total: int, p: Seq<ChunkS>, c: ChunkS)
    requires
        chunks_from(s, 12, total) matches Some(cs) && cs.len() > p.len() && cs.subrange(0, p.len() as int) == p && cs[p.len() as int] == c,
        !prefix_ok(p.push(c)),
    ensures
        !(chunks_from(s, 12, total) matches Some(cs) && chunks_ok(cs)),
{
    let cs = chunks_from(s, 12, total)->Some_0;
    let q = p.push(c);
    assert forall|m: int| 0 <= m < q.len() implies q[m] == cs[m] by {
        if m < p.len() {
            assert(cs.subrange(0, p.len() as int)[m] == cs[m]);
        }
    }
}

// MUST-159, MUST-160, MUST-161: チャンクの長さと並び
fn scan_chunks(s: &[u8], total: usize) -> (r: Option<(usize, usize, Option<u64>)>)
    requires
        12 <= total <= s.len(),
    ensures
        match r {
            Some((st, ln, bn)) => chunks_from(s@, 12, total as int) matches Some(cs) && chunks_ok(cs) && st == cs[0].pos + 8
                && ln == cs[0].len && bn == chunks_bin(cs),
            None => !(chunks_from(s@, 12, total as int) matches Some(cs) && chunks_ok(cs)),
        },
{
    let mut json: Option<(usize, usize)> = None;
    let mut bin_len: Option<u64> = None;
    let mut pos = 12;
    let mut index: usize = 0;
    let ghost mut pre: Seq<ChunkS> = seq![];
    proof {
        assert(seq![] + chunks_from(s@, 12, total as int)->Some_0 =~= chunks_from(s@, 12, total as int)->Some_0);
    }
    while pos < total
        invariant
            12 <= pos <= total <= s.len(),
            index == pre.len(),
            index <= pos,
            chunks_from(s@, 12, total as int) == lift(pre, chunks_from(s@, pos as int, total as int)),
            prefix_ok(pre),
            json == (if index == 0 { None } else { Some(((pre[0].pos + 8) as usize, pre[0].len as usize)) }),
            index >= 1 ==> 0 <= pre[0].len && pre[0].pos + 8 + pre[0].len <= total,
            bin_len == chunks_bin(pre),
        decreases total - pos,
    {
        if total - pos < 8 {
            return None;
        }
        let len = read_u32(s, pos) as usize;
        let kind = read_u32(s, pos + 4);
        if len % 4 != 0 || total - pos - 8 < len {
            return None;
        }
        let ghost c = ChunkS { pos: pos as int, len: len as int, typ: kind as int };
        let ghost rest = chunks_from(s@, pos + 8 + len, total as int);
        proof {
            assert(chunks_from(s@, pos as int, total as int) == lift(seq![c], rest));
            match rest {
                Some(rr) => {
                    assert(pre + (seq![c] + rr) =~= pre.push(c) + rr);
                    let cs = pre.push(c) + rr;
                    assert(cs.subrange(0, pre.len() as int) =~= pre);
                    assert(cs[pre.len() as int] == c);
                },
                None => {},
            }
        }
        if index == 0 {
            if kind != 0x4E4F534A {
                proof {
                    if rest is Some {
                        lemma_chunks_fail(s@, total as int, pre, c);
                    }
                }
                return None;
            }
            json = Some((pos + 8, len));
        } else if kind == 0x4E4F534A || (kind == 0x004E4942 && index != 1) {
            proof {
                if rest is Some {
                    lemma_chunks_fail(s@, total as int, pre, c);
                }
            }
            return None;
        } else if kind == 0x004E4942 {
            bin_len = Some(len as u64);
        }
        proof {
            let q = pre.push(c);
            assert(q[pre.len() as int] == c);
            assert forall|m: int| 0 <= m < pre.len() implies q[m] == pre[m] by {}
            pre = q;
        }
        pos = pos + 8 + len;
        index += 1;
    }
    proof {
        assert(chunks_from(s@, pos as int, total as int) == Some(Seq::<ChunkS>::empty()));
        assert(pre + Seq::<ChunkS>::empty() =~= pre);
    }
    match json {
        None => None,
        Some((start, len)) => Some((start, len, bin_len)),
    }
}

// MUST-158: magic は glTF、version は 2
pub open spec fn glb_spec(s: Seq<u8>) -> Option<(Seq<u8>, Option<u64>)> {
    if s.len() < 12 || u32le(s, 0) != 0x46546C67 || u32le(s, 4) != 2 {
        None
    } else {
        let l = u32le(s, 8);
        if l < 12 || l > s.len() {
            None
        } else {
            match chunks_from(s, 12, l) {
                Some(cs) => if chunks_ok(cs) {
                    Some((s.subrange(cs[0].pos + 8, cs[0].pos + 8 + cs[0].len), chunks_bin(cs)))
                } else {
                    None
                },
                None => None,
            }
        }
    }
}

// G1
// MUST-158: magic は glTF、version は 2
pub fn parse_glb(s: &[u8]) -> (r: Option<GlbChunks>)
    ensures
        match r {
            Some(c) => glb_spec(s@) == Some((c.json@, c.bin_len)),
            None => glb_spec(s@) is None,
        },
{
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

} // verus!
