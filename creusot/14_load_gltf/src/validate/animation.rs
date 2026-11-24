use creusot_std::prelude::*;
use crate::model::*;
use crate::validate::util::*;
use crate::validate::mesh::*;
#[cfg(creusot)]
use crate::validate::refs::*;

// MUST-152: 1 つのアニメーションの対象は重複なし
#[requires(c@ < an.channels@.len())]
#[ensures(result == forall<d> c@ < d && d < an.channels@.len() ==>
    !(an.channels@[d].node == an.channels@[c@].node && an.channels@[d].path == an.channels@[c@].path))]
#[check(terminates)]
fn target_unique(an: &Animation, c: usize) -> bool {
    let ch = &an.channels[c];
    let mut d = c + 1;
    #[invariant(c@ < d@ && d@ <= an.channels@.len())]
    #[invariant(forall<e> c@ < e && e < d@ ==>
        !(an.channels@[e].node == an.channels@[c@].node && an.channels@[e].path == an.channels@[c@].path))]
    #[variant(an.channels@.len() - d@)]
    while d < an.channels.len() {
        if opt_eq(an.channels[d].node, ch.node) && an.channels[d].path == ch.path {
            return false;
        }
        d += 1;
    }
    true
}

// 出力 accessor の型（adoc 3295）。weights 以外の既知のパスは translation/rotation/scale
// MUST-149: 出力のアクセサーの型
#[logic(open)]
pub fn output_spec(path: Int, out: Accessor) -> bool {
    pearlite! {
        if path == PATH_TRANSLATION@ || path == PATH_SCALE@ { vec_n(out, 3) && f32_ty(out) }
        else if path == PATH_ROTATION@ { vec_n(out, 4) && (f32_ty(out) || unorm_ty(out) || snorm_ty(out)) }
        else { vec_n(out, 1) && (f32_ty(out) || unorm_ty(out) || snorm_ty(out)) }
    }
}

// MUST-149: 出力のアクセサーの型
#[ensures(result == output_spec(path@, *out))]
#[check(terminates)]
fn output_type_ok(path: u64, out: &Accessor) -> bool {
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

#[logic(open)]
pub fn interp_mult(interp: Int) -> Int {
    pearlite! { if interp == INTERP_CUBICSPLINE@ { 3 } else { 1 } }
}

// MUST-150: 出力の要素数
#[ensures(result == (input_count@ * keys@ * interp_mult(interpolation@) <= u64::MAX@
    && output_count@ == input_count@ * keys@ * interp_mult(interpolation@)))]
#[check(terminates)]
fn output_count_ok(input_count: u64, keys: u64, interpolation: u64, output_count: u64) -> bool {
    let mult: u64 = if interpolation == INTERP_CUBICSPLINE { 3 } else { 1 };
    match input_count.checked_mul(keys) {
        None => false,
        Some(x) => match x.checked_mul(mult) {
            None => false,
            Some(y) => output_count == y,
        },
    }
}

// keys = weights なら morph_count、それ以外は 1
#[logic(open)]
pub fn channel_keys(g: Gltf, path: Int, node: Node) -> Int {
    pearlite! {
        if path == PATH_WEIGHTS@ {
            match node.mesh { None => 0, Some(m) => morph_count(g.meshes@[m@]) }
        } else { 1 }
    }
}

// AN2: チャネル c（node があり、パスが既知のもの）
// MUST-148, MUST-150, MUST-152: 対象はアニメーション可能で重複がなく、出力の要素数が合う
#[logic(open)]
pub fn channel_spec(g: Gltf, an: Animation, c: Int) -> bool {
    pearlite! {
        let ch = an.channels@[c];
        match ch.node {
            None => true,
            Some(n) => ch.path@ == KIND_OTHER@ || {
                let node = g.nodes@[n@];
                let smp = an.samplers@[ch.sampler@];
                let out = g.accessors@[smp.output@];
                let keys = channel_keys(g, ch.path@, node);
                let expected = g.accessors@[smp.input@].count@ * keys * interp_mult(smp.interpolation@);
                (ch.path@ != PATH_WEIGHTS@ ==> !node.has_matrix)
                    && keys > 0
                    && (forall<d> c < d && d < an.channels@.len() ==>
                        !(an.channels@[d].node == ch.node && an.channels@[d].path == ch.path))
                    && output_spec(ch.path@, out)
                    && expected <= u64::MAX@
                    && out.count@ == expected
            },
        }
    }
}

// MUST-148: アニメーションの対象はアニメーション可能なプロパティ
#[requires(refs_ok(*g))]
#[requires(animation_refs(*g, *an))]
#[requires(c@ < an.channels@.len())]
#[ensures(result == channel_spec(*g, *an, c@))]
#[check(terminates)]
fn channel_ok(g: &Gltf, an: &Animation, c: usize) -> bool {
    let ch = &an.channels[c];
    match ch.node {
        None => true,
        Some(nd) => {
            if ch.path == KIND_OTHER {
                return true;
            }
            let node = &g.nodes[nd as usize];
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
}

// AN1
// MUST-057, MUST-141, MUST-145: 入力は SCALAR float32 で min / max があり、CUBICSPLINE なら 2 要素以上
#[logic(open)]
pub fn anim_sampler_spec(g: Gltf, s: AnimationSampler) -> bool {
    pearlite! {
        let inp = g.accessors@[s.input@];
        vec_n(inp, 1) && f32_ty(inp) && inp.min_len != None && inp.max_len != None
            && (s.interpolation@ == INTERP_CUBICSPLINE@ ==> inp.count@ >= 2)
    }
}

// MUST-057, MUST-141, MUST-145: 入力は SCALAR float32 で min / max があり、CUBICSPLINE なら 2 要素以上
#[requires(animation_refs(*g, *an))]
#[ensures(result == forall<s> 0 <= s && s < an.samplers@.len() ==> anim_sampler_spec(*g, an.samplers@[s]))]
#[check(terminates)]
fn animation_samplers_ok(g: &Gltf, an: &Animation) -> bool {
    let mut s = 0;
    #[invariant(s@ <= an.samplers@.len())]
    #[invariant(forall<k> 0 <= k && k < s@ ==> anim_sampler_spec(*g, an.samplers@[k]))]
    #[variant(an.samplers@.len() - s@)]
    while s < an.samplers.len() {
        let inp = &g.accessors[an.samplers[s].input as usize];
        if inp.components != 1 || inp.is_matrix || !float32(inp) || inp.min_len.is_none() || inp.max_len.is_none() {
            return false;
        }
        if an.samplers[s].interpolation == INTERP_CUBICSPLINE && inp.count < 2 {
            return false;
        }
        s += 1;
    }
    true
}

#[requires(refs_ok(*g))]
#[requires(animation_refs(*g, *an))]
#[ensures(result == forall<c> 0 <= c && c < an.channels@.len() ==> channel_spec(*g, *an, c))]
#[check(terminates)]
fn channels_ok(g: &Gltf, an: &Animation) -> bool {
    let mut c = 0;
    #[invariant(c@ <= an.channels@.len())]
    #[invariant(forall<k> 0 <= k && k < c@ ==> channel_spec(*g, *an, k))]
    #[variant(an.channels@.len() - c@)]
    while c < an.channels.len() {
        if !channel_ok(g, an, c) {
            return false;
        }
        c += 1;
    }
    true
}

#[logic(open)]
pub fn animation_spec(g: Gltf, an: Animation) -> bool {
    pearlite! {
        (forall<s> 0 <= s && s < an.samplers@.len() ==> anim_sampler_spec(g, an.samplers@[s]))
        && (forall<c> 0 <= c && c < an.channels@.len() ==> channel_spec(g, an, c))
    }
}

// AN1〜AN2
#[logic(open)]
pub fn animations_spec(g: Gltf) -> bool {
    pearlite! { forall<i> 0 <= i && i < g.animations@.len() ==> animation_spec(g, g.animations@[i]) }
}

#[requires(refs_ok(*g))]
#[ensures(result == animations_spec(*g))]
#[check(terminates)]
pub(crate) fn animations_ok(g: &Gltf) -> bool {
    let mut i = 0;
    #[invariant(i@ <= g.animations@.len())]
    #[invariant(forall<k> 0 <= k && k < i@ ==> animation_spec(*g, g.animations@[k]))]
    #[variant(g.animations@.len() - i@)]
    while i < g.animations.len() {
        if !animation_samplers_ok(g, &g.animations[i]) || !channels_ok(g, &g.animations[i]) {
            return false;
        }
        i += 1;
    }
    true
}
