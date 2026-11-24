use crate::model::*;
use crate::validate::util::*;
use crate::validate::mesh::*;

fn target_unique(an: &Animation, c: usize) -> bool {
    let ch = &an.channels[c];
    let mut d = c + 1;
    while d < an.channels.len() {
        if opt_eq(an.channels[d].node, ch.node) && an.channels[d].path == ch.path {
            return false;
        }
        d += 1;
    }
    true
}

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

fn animation_samplers_ok(g: &Gltf, an: &Animation) -> bool {
    let mut s = 0;
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

fn channels_ok(g: &Gltf, an: &Animation) -> bool {
    let mut c = 0;
    while c < an.channels.len() {
        if !channel_ok(g, an, c) {
            return false;
        }
        c += 1;
    }
    true
}

pub(crate) fn animations_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.animations.len() {
        if !animation_samplers_ok(g, &g.animations[i]) || !channels_ok(g, &g.animations[i]) {
            return false;
        }
        i += 1;
    }
    true
}
