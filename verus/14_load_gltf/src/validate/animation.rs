use crate::model::*;
use crate::validate::util::*;
use crate::validate::mesh::*;
use vstd::prelude::*;
#[cfg(verus_only)]
use crate::validate::refs::*;

verus! {

// MUST-152: 1 つのアニメーションの対象は重複なし
fn target_unique(an: &Animation, c: usize) -> (r: bool)
    requires
        c < an.channels.len(),
    ensures
        r == (forall|d: int|
            c < d < an@.channels.len() ==> !(#[trigger] an@.channels[d].node == an@.channels[c as int].node
                && an@.channels[d].path == an@.channels[c as int].path)),
{
    let ch = &an.channels[c];
    let mut d = c + 1;
    while d < an.channels.len()
        invariant
            c < d <= an.channels.len(),
            *ch == an@.channels[c as int],
            forall|x: int|
                c < x < d ==> !(#[trigger] an@.channels[x].node == an@.channels[c as int].node && an@.channels[x].path
                    == an@.channels[c as int].path),
        decreases an.channels.len() - d,
    {
        if opt_eq(an.channels[d].node, ch.node) && an.channels[d].path == ch.path {
            return false;
        }
        d += 1;
    }
    true
}

// MUST-149: 出力のアクセサーの型
pub open spec fn output_type_s(path: u64, out: Accessor) -> bool {
    if path == PATH_TRANSLATION || path == PATH_SCALE {
        !out.is_matrix && out.components == 3 && f32_s(out)
    } else if path == PATH_ROTATION {
        !out.is_matrix && out.components == 4 && (f32_s(out) || unorm_s(out) || snorm_s(out))
    } else {
        !out.is_matrix && out.components == 1 && (f32_s(out) || unorm_s(out) || snorm_s(out))
    }
}

// MUST-149: 出力のアクセサーの型
fn output_type_ok(path: u64, out: &Accessor) -> (r: bool)
    ensures
        r == output_type_s(path, *out),
{
    if out.is_matrix {
        false
    } else if path == PATH_TRANSLATION || path == PATH_SCALE {
        out.components == 3 && float32(out)
    } else if path == PATH_ROTATION {
        out.components == 4 && (float32(out) || unorm8_16(out) || snorm8_16(out))
    } else {
        out.components == 1 && (float32(out) || unorm8_16(out) || snorm8_16(out))
    }
}

// MUST-150: 出力の要素数
fn output_count_ok(input_count: u64, keys: u64, interpolation: u64, output_count: u64) -> (r: bool)
    ensures
        r == (output_count == input_count * keys * (if interpolation == INTERP_CUBICSPLINE { 3int } else { 1 })),
{
    let mult: u64 = if interpolation == INTERP_CUBICSPLINE { 3 } else { 1 };
    proof {
        assert(input_count * keys >= 0) by (nonlinear_arith);
        assert(input_count * keys * mult >= input_count * keys) by (nonlinear_arith)
            requires
                mult >= 1,
        ;
    }
    match input_count.checked_mul(keys) {
        None => false,
        Some(x) => match x.checked_mul(mult) {
            None => false,
            Some(y) => output_count == y,
        },
    }
}

// AN2（1 チャネル分）
// MUST-148, MUST-149, MUST-150, MUST-152: チャネル 1 つ分の規則
pub open spec fn channel_rule(g: GltfS, an: AnimationS, c: int) -> bool {
    let ch = an.channels[c];
    match ch.node {
        None => true,
        Some(nd) => ch.path != KIND_OTHER ==> {
        let node = g.nodes[nd as int];
        let keys: int = if ch.path == PATH_WEIGHTS {
            match node.mesh {
                Some(m) => morph_count(g.meshes[m as int]) as int,
                None => 0,
            }
        } else {
            1
        };
        let sm = an.samplers[ch.sampler as int];
        let out = g.accessors[sm.output as int];
        &&& (ch.path != PATH_WEIGHTS ==> !node.has_matrix)
        &&& (ch.path == PATH_WEIGHTS ==> node.mesh is Some && keys > 0)
        &&& forall|d: int| c < d < an.channels.len() ==> !(#[trigger] an.channels[d].node == ch.node && an.channels[d].path == ch.path)
        &&& output_type_s(ch.path, out)
        &&& out.count == g.accessors[sm.input as int].count * keys * (if sm.interpolation == INTERP_CUBICSPLINE { 3int } else { 1 })
        },
    }
}

// MUST-148, MUST-149, MUST-150, MUST-152: チャネル 1 つ分の規則
fn channel_ok(g: &Gltf, an: &Animation, c: usize) -> (r: bool)
    requires
        refs_ok(g@),
        c < an.channels.len(),
        forall|x: int| 0 <= x < an@.channels.len() ==> #[trigger] channel_refs_s(g@, an@, x),
        forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
    ensures
        r == channel_rule(g@, an@, c as int),
{
    proof {
        assert(channel_refs_s(g@, an@, c as int));
        assert(sampler_refs_s(g@, an@, an@.channels[c as int].sampler as int));
        lemma_refs_ok_split(g@);
    }
    let ch = &an.channels[c];
    match ch.node {
        None => true,
        Some(nd) => {
            if ch.path == KIND_OTHER {
                return true;
            }
            let node = &g.nodes[nd as usize];
            proof {
                assert(g@.nodes[nd as int] == node@);
                assert(node_refs_s(g@, nd as int));
                if node.mesh is Some {
                    assert(g@.meshes[node.mesh->Some_0 as int] == g.meshes@[node.mesh->Some_0 as int]@);
                }
            }
            let keys: u64 = if ch.path == PATH_WEIGHTS {
                match node.mesh {
                    None => 0,
                    Some(m) => morph_target_count(&g.meshes[m as usize]),
                }
            } else {
                1
            };
            let smp = &an.samplers[ch.sampler as usize];
            let out = &g.accessors[smp.output as usize];
            (ch.path == PATH_WEIGHTS || !node.has_matrix)
                && keys > 0
                && target_unique(an, c)
                && output_type_ok(ch.path, out)
                && output_count_ok(g.accessors[smp.input as usize].count, keys, smp.interpolation, out.count)
        }
    }
}pub open spec fn sampler_rule(g: GltfS, sm: AnimationSampler) -> bool {
    let inp = g.accessors[sm.input as int];
    &&& inp.components == 1 && !inp.is_matrix && f32_s(inp) && inp.min_len is Some && inp.max_len is Some
    &&& (sm.interpolation == INTERP_CUBICSPLINE ==> inp.count >= 2)
}

// MUST-057, MUST-141, MUST-145: 入力は SCALAR の float で min / max があり、CUBICSPLINE なら 2 要素以上
fn animation_samplers_ok(g: &Gltf, an: &Animation) -> (r: bool)
    requires
        forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
    ensures
        r == (forall|s: int| 0 <= s < an@.samplers.len() ==> #[trigger] sampler_rule(g@, an@.samplers[s])),
{
    let mut s = 0;
    while s < an.samplers.len()
        invariant
            forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
            0 <= s <= an.samplers.len(),
            forall|x: int| 0 <= x < s ==> #[trigger] sampler_rule(g@, an@.samplers[x]),
        decreases an.samplers.len() - s,
    {
        proof {
            assert(sampler_refs_s(g@, an@, s as int));
        }
        let inp = &g.accessors[an.samplers[s].input as usize];
        if inp.components != 1 || inp.is_matrix || !float32(inp) || inp.min_len.is_none() || inp.max_len.is_none() {
            assert(!sampler_rule(g@, an@.samplers[s as int]));
            return false;
        }
        if an.samplers[s].interpolation == INTERP_CUBICSPLINE && inp.count < 2 {
            assert(!sampler_rule(g@, an@.samplers[s as int]));
            return false;
        }
        assert(sampler_rule(g@, an@.samplers[s as int]));
        s += 1;
    }
    true
}

fn channels_ok(g: &Gltf, an: &Animation) -> (r: bool)
    requires
        refs_ok(g@),
        forall|x: int| 0 <= x < an@.channels.len() ==> #[trigger] channel_refs_s(g@, an@, x),
        forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
    ensures
        r == (forall|c: int| 0 <= c < an@.channels.len() ==> #[trigger] channel_rule(g@, an@, c)),
{
    let mut c = 0;
    while c < an.channels.len()
        invariant
            refs_ok(g@),
            forall|x: int| 0 <= x < an@.channels.len() ==> #[trigger] channel_refs_s(g@, an@, x),
            forall|x: int| 0 <= x < an@.samplers.len() ==> #[trigger] sampler_refs_s(g@, an@, x),
            0 <= c <= an.channels.len(),
            forall|x: int| 0 <= x < c ==> #[trigger] channel_rule(g@, an@, x),
        decreases an.channels.len() - c,
    {
        if !channel_ok(g, an, c) {
            return false;
        }
        c += 1;
    }
    true
}

// AN1
// MUST-057, MUST-141, MUST-145: 入力は SCALAR の float で min / max があり、CUBICSPLINE なら 2 要素以上
pub open spec fn an1(g: GltfS) -> bool {
    forall|i: int, s: int|
        0 <= i < g.animations.len() && 0 <= s < g.animations[i].samplers.len() ==> {
            let sm = #[trigger] g.animations[i].samplers[s];
            let inp = g.accessors[sm.input as int];
            &&& inp.components == 1 && !inp.is_matrix && f32_s(inp) && inp.min_len is Some && inp.max_len is Some
            &&& (sm.interpolation == INTERP_CUBICSPLINE ==> inp.count >= 2)
        }
}

pub open spec fn an2(g: GltfS) -> bool {
    forall|i: int, c: int|
        0 <= i < g.animations.len() && 0 <= c < g.animations[i].channels.len() ==> #[trigger] channel_rule(
            g,
            g.animations[i],
            c,
        )
}

pub proof fn lemma_an_split(g: GltfS)
    ensures
        an1(g) == (forall|k: int, s: int|
            0 <= k < g.animations.len() && 0 <= s < g.animations[k].samplers.len() ==> #[trigger] sampler_rule(g, g.animations[k].samplers[s])),
        an2(g) == (forall|k: int, c: int|
            0 <= k < g.animations.len() && 0 <= c < g.animations[k].channels.len() ==> #[trigger] channel_rule(g, g.animations[k], c)),
{
    assert(an1(g) == (forall|k: int, s: int|
        0 <= k < g.animations.len() && 0 <= s < g.animations[k].samplers.len() ==> #[trigger] sampler_rule(g, g.animations[k].samplers[s]))) by {
        if an1(g) {
            assert forall|k: int, s: int| 0 <= k < g.animations.len() && 0 <= s < g.animations[k].samplers.len() implies #[trigger] sampler_rule(g, g.animations[k].samplers[s]) by {
                let sm = g.animations[k].samplers[s];
            }
        }
        if forall|k: int, s: int| 0 <= k < g.animations.len() && 0 <= s < g.animations[k].samplers.len() ==> #[trigger] sampler_rule(g, g.animations[k].samplers[s]) {
            assert forall|k: int, s: int| 0 <= k < g.animations.len() && 0 <= s < g.animations[k].samplers.len() implies {
                let sm = #[trigger] g.animations[k].samplers[s];
                let inp = g.accessors[sm.input as int];
                &&& inp.components == 1 && !inp.is_matrix && f32_s(inp) && inp.min_len is Some && inp.max_len is Some
                &&& (sm.interpolation == INTERP_CUBICSPLINE ==> inp.count >= 2)
            } by {
                assert(sampler_rule(g, g.animations[k].samplers[s]));
            }
        }
    }
}

// AN1 と AN2
pub(crate) fn animations_ok(g: &Gltf) -> (r: bool)
    requires
        refs_ok(g@),
    ensures
        r == (an1(g@) && an2(g@)),
{
    proof {
        lemma_refs_ok_split(g@);
    }
    let mut i = 0;
    while i < g.animations.len()
        invariant
            refs_ok(g@),
            forall|k: int| 0 <= k < g@.animations.len() ==> #[trigger] anim_refs_s(g@, k),
            0 <= i <= g.animations.len(),
            forall|k: int, s: int|
                0 <= k < i && 0 <= s < g@.animations[k].samplers.len() ==> #[trigger] sampler_rule(g@, g@.animations[k].samplers[s]),
            forall|k: int, c: int|
                0 <= k < i && 0 <= c < g@.animations[k].channels.len() ==> #[trigger] channel_rule(g@, g@.animations[k], c),
        decreases g.animations.len() - i,
    {
        proof {
            assert(g@.animations[i as int] == g.animations@[i as int]@);
            assert(anim_refs_s(g@, i as int));
        }
        if !animation_samplers_ok(g, &g.animations[i]) || !channels_ok(g, &g.animations[i]) {
            proof {
                lemma_an_split(g@);
            }
            return false;
        }
        i += 1;
    }
    proof {
        lemma_an_split(g@);
    }
    true
}

} // verus!
