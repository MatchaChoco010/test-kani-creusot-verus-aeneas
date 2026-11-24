import LoadGltf.Validate.Mesh

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## アニメーション (AN1, AN2) -/

-- AN1
-- MUST-057, MUST-141, MUST-145: 入力は SCALAR float32 で min / max あり、CUBICSPLINE は 2 個以上
def inputOk (g : model.Gltf) (s : model.AnimationSampler) : Prop :=
  let inp := g.accessors.val[s.input.val]!
  inp.components.val = 1 ∧ inp.is_matrix = false ∧ isFloat32 inp ∧ inp.min_len ≠ none ∧
  inp.max_len ≠ none ∧ (s.interpolation.val = 2 → 2 ≤ inp.count.val)

-- 出力アクセサの型 (translation 1, rotation 2, scale 3, weights 4)
-- MUST-149: 出力のアクセサーの型
def outputTypeOk (path : Nat) (out : model.Accessor) : Prop :=
  out.is_matrix = false ∧
  (if path = 1 ∨ path = 3 then out.components.val = 3 ∧ isFloat32 out
  else if path = 2 then out.components.val = 4 ∧ (isFloat32 out ∨ isUnorm816 out ∨ isSnorm816 out)
  else out.components.val = 1 ∧ (isFloat32 out ∨ isUnorm816 out ∨ isSnorm816 out))

-- keys = morph_count (weights) または 1
def channelKeys (g : model.Gltf) (path : Nat) (node : model.Node) : Nat :=
  if path = 4 then (match node.mesh with
    | some m => morphCount g.meshes.val[m.val]!
    | none => 0)
  else 1

-- AN2 (チャンネル c)
-- MUST-148, MUST-150, MUST-152: 対象のプロパティ、出力の要素数、対象の重複なし
def channelOk (g : model.Gltf) (an : model.Animation) (c : Nat) : Prop :=
  let ch := an.channels.val[c]!
  ∀ nd, ch.node = some nd → ch.path.val ≠ 0 →
    let node := g.nodes.val[nd.val]!
    let keys := channelKeys g ch.path.val node
    let smp := an.samplers.val[ch.sampler.val]!
    let out := g.accessors.val[smp.output.val]!
    (ch.path.val ≠ 4 → node.has_matrix = false) ∧ 0 < keys ∧
    (∀ d, c < d → ∀ h : d < an.channels.val.length,
      ¬ ((an.channels.val[d]).node = ch.node ∧ (an.channels.val[d]).path = ch.path)) ∧
    outputTypeOk ch.path.val out ∧
    out.count.val = (g.accessors.val[smp.input.val]!).count.val * keys *
      (if smp.interpolation.val = 2 then 3 else 1)

def animOk (g : model.Gltf) (an : model.Animation) : Prop :=
  (∀ s ∈ an.samplers.val, inputOk g s) ∧ ∀ c < an.channels.val.length, channelOk g an c

def animationsOk (g : model.Gltf) : Prop := ∀ an ∈ g.animations.val, animOk g an

@[step]
theorem target_unique_loop_spec (v : alloc.vec.Vec model.Channel) (ch : model.Channel) (d : Usize)
    (hd : d.val ≤ v.val.length) :
    validate.animation.target_unique_loop v ch d ⦃ r => r = true ↔
      forallFrom v.val d.val (fun c => ¬ (c.node = ch.node ∧ c.path = ch.path)) ⦄ := by
  unfold validate.animation.target_unique_loop
  loop_auto
termination_by v.val.length - d.val
decreasing_by all_goals scalar_decr_tac

-- MUST-149: 出力のアクセサーの型
@[step]
theorem output_type_ok_spec (path : U64) (out : model.Accessor) :
    validate.animation.output_type_ok path out ⦃ r => r = true ↔ outputTypeOk path.val out ⦄ := by
  unfold validate.animation.output_type_ok outputTypeOk
  have hc := anim_consts
  step*

-- MUST-150: 出力の要素数
@[step]
theorem output_count_ok_spec (ic keys interp oc : U64) :
    validate.animation.output_count_ok ic keys interp oc ⦃ r => r = true ↔
      oc.val = ic.val * keys.val * (if interp.val = 2 then 3 else 1) ⦄ := by
  unfold validate.animation.output_count_ok
  have hc := anim_consts
  have hm := U64.max_eq
  have hoc : oc.val ≤ U64.max := by scalar_tac
  split <;> step*
  all_goals simp_all [UScalar.eq_equiv]
  all_goals (intro h; linarith)

-- MUST-152: 対象の重複なし
@[step]
theorem target_unique_spec (an : model.Animation) (c : Usize) (hc : c.val < an.channels.val.length) :
    validate.animation.target_unique an c ⦃ r => r = true ↔ ∀ d, c.val < d → ∀ h : d < an.channels.val.length,
      ¬ ((an.channels.val[d]).node = (an.channels.val[c.val]).node ∧
        (an.channels.val[d]).path = (an.channels.val[c.val]).path) ⦄ := by
  unfold validate.animation.target_unique
  step*
  subst_vars
  simp only [forallFrom] at r_post
  rw [r_post]
  constructor
  · intro h d hd h'; exact h d (by omega) h'
  · intro h d hd h'; exact h d (by omega) h'

-- MUST-148: 対象はアニメーション可能なプロパティ
set_option maxHeartbeats 4000000 in
@[step]
theorem channel_ok_spec (g : model.Gltf) (an : model.Animation) (c : Usize) (hc : c.val < an.channels.val.length)
    (hch : ∀ ch ∈ an.channels.val, ch.sampler.val < an.samplers.val.length ∧ optLt ch.node g.nodes.val.length)
    (hsm : ∀ s ∈ an.samplers.val, s.input.val < g.accessors.val.length ∧ s.output.val < g.accessors.val.length)
    (hn : nodeRefsOk g) :
    validate.animation.channel_ok g an c ⦃ r => r = true ↔ channelOk g an c.val ⦄ := by
  unfold validate.animation.channel_ok channelOk
  have hcst := anim_consts
  rw [getElem!_pos an.channels.val c.val hc]
  have hr1 := hch _ (List.getElem_mem hc)
  rcases hcc : an.channels.val[c.val] with ⟨csm, nd, path⟩
  rw [hcc] at hr1
  simp only [optLt] at hr1
  step
  subst ch_post
  simp only [hcc]
  rcases nd with _ | nd
  · step*
  simp only [Option.some.injEq, forall_eq']
  have hnd : nd.val < g.nodes.val.length := hr1.2 nd rfl
  have hs : csm.val < an.samplers.val.length := hr1.1
  have hsr := hsm _ (List.getElem_mem hs)
  have hnr := (hn _ (List.getElem_mem hnd)).2.1
  rw [getElem!_pos g.nodes.val nd.val hnd, getElem!_pos an.samplers.val csm.val hs,
    getElem!_pos g.accessors.val _ hsr.2, getElem!_pos g.accessors.val _ hsr.1]
  have m1 := mod_numBits_of_lt hnd (alloc.vec.Vec.len_ineq g.nodes)
  have m2 := mod_numBits_of_lt hs (alloc.vec.Vec.len_ineq an.samplers)
  have m3 := mod_numBits_of_lt hsr.1 (alloc.vec.Vec.len_ineq g.accessors)
  have m4 := mod_numBits_of_lt hsr.2 (alloc.vec.Vec.len_ineq g.accessors)
  have hlnd : nd.val ≤ Usize.max := by have := alloc.vec.Vec.len_ineq g.nodes; omega
  have hmr : ∀ m, (g.nodes.val[nd.val]).mesh = some m → m.val < g.meshes.val.length := hnr
  clear hch hsm hn hnr
  rcases hme : (g.nodes.val[nd.val]).mesh with _ | m
  · step*
    all_goals (try (have hiv : i.val = nd.val := by rw [i_post]; exact u64_cast_usize_val _ hlnd))
    all_goals (try (have hnode : node = g.nodes.val[nd.val] := by rw [node_post]; exact getElem_idx_eq hiv _ _))
    all_goals (try subst hnode)
    all_goals (try clear node_post)
    all_goals (try simp only [hme])
    all_goals (try split)
    all_goals step*
    all_goals (try (have hi1 : i1.val = csm.val := by rw [i1_post]; exact u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq an.samplers; omega)))
    all_goals (try (have hsmp : smp = an.samplers.val[csm.val] := by rw [smp_post]; exact getElem_idx_eq hi1 _ _))
    all_goals (try subst hsmp)
    all_goals (try clear smp_post i1_post)
    all_goals (try (have hi2 : i2.val = (an.samplers.val[csm.val]).output.val := by rw [i2_post]; exact u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq g.accessors; omega)))
    all_goals (try (have hout : out = g.accessors.val[(an.samplers.val[csm.val]).output.val] := by rw [out_post]; exact getElem_idx_eq hi2 _ _))
    all_goals (try subst hout)
    all_goals (try clear out_post i2_post)
    all_goals (try (have hi3 : i3.val = (an.samplers.val[csm.val]).input.val := by rw [i3_post]; exact u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq g.accessors; omega)))
    all_goals (try (have ha : a = g.accessors.val[(an.samplers.val[csm.val]).input.val] := by rw [a_post]; exact getElem_idx_eq hi3 _ _))
    all_goals (try subst ha)
    all_goals (try clear a_post i3_post)
    all_goals (try clear smp_post)
    all_goals (try clear out_post)
    all_goals (try clear a_post)
    all_goals (try clear node_post)
    all_goals (try clear m1 m2 m3 m4 hcc hr1 i_post i1_post)
    all_goals (try simp only [channelKeys])
    all_goals (try simp_all [UScalar.eq_equiv])
  · have hml := hmr m hme
    have mm := mod_numBits_of_lt hml (alloc.vec.Vec.len_ineq g.meshes)
    simp only [channelKeys, hme, getElem!_pos g.meshes.val m.val hml]
    clear hmr
    step*
    all_goals (try (have hiv : i.val = nd.val := by rw [i_post]; exact u64_cast_usize_val _ hlnd))
    all_goals (try (have hnode : node = g.nodes.val[nd.val] := by rw [node_post]; exact getElem_idx_eq hiv _ _))
    all_goals (try subst hnode)
    all_goals (try clear node_post)
    all_goals (try simp only [hme])
    all_goals (try split)
    all_goals step*
    all_goals (try (have hi1 : i1.val = csm.val := by rw [i1_post]; exact u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq an.samplers; omega)))
    all_goals (try (have hsmp : smp = an.samplers.val[csm.val] := by rw [smp_post]; exact getElem_idx_eq hi1 _ _))
    all_goals (try subst hsmp)
    all_goals (try clear smp_post i1_post)
    all_goals (try (have hi2 : i2.val = (an.samplers.val[csm.val]).output.val := by rw [i2_post]; exact u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq g.accessors; omega)))
    all_goals (try (have hout : out = g.accessors.val[(an.samplers.val[csm.val]).output.val] := by rw [out_post]; exact getElem_idx_eq hi2 _ _))
    all_goals (try subst hout)
    all_goals (try clear out_post i2_post)
    all_goals (try (have hi3 : i3.val = (an.samplers.val[csm.val]).input.val := by rw [i3_post]; exact u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq g.accessors; omega)))
    all_goals (try (have ha : a = g.accessors.val[(an.samplers.val[csm.val]).input.val] := by rw [a_post]; exact getElem_idx_eq hi3 _ _))
    all_goals (try subst ha)
    all_goals (try clear a_post i3_post)
    all_goals (try clear smp_post)
    all_goals (try clear out_post)
    all_goals (try clear a_post)
    all_goals (try clear node_post)
    all_goals (try clear m1 m2 m3 m4 hcc hr1 i_post i1_post)
    all_goals (try simp only [channelKeys])
    all_goals (try simp_all [UScalar.eq_equiv])

@[step]
theorem animation_samplers_ok_loop_spec (g : model.Gltf) (an : model.Animation) (s : Usize)
    (hsm : ∀ x ∈ an.samplers.val, x.input.val < g.accessors.val.length ∧ x.output.val < g.accessors.val.length)
    (hs : s.val ≤ an.samplers.val.length) :
    validate.animation.animation_samplers_ok_loop g an s ⦃ r => r = true ↔ forallFrom an.samplers.val s.val (inputOk g) ⦄ := by
  unfold validate.animation.animation_samplers_ok_loop
  have hcst := anim_consts
  have h1 : ∀ q (h : q < an.samplers.val.length), (an.samplers.val[q]).input.val < g.accessors.val.length :=
    fun q h => (hsm _ (List.getElem_mem h)).1
  have h2 : ∀ q (h : q < an.samplers.val.length),
      (an.samplers.val[q]).input.val % 2 ^ System.Platform.numBits = (an.samplers.val[q]).input.val :=
    fun q h => mod_numBits_of_lt (h1 q h) (alloc.vec.Vec.len_ineq g.accessors)
  have h3 : ∀ q (h : q < an.samplers.val.length),
      g.accessors.val[(an.samplers.val[q]).input.val]! = g.accessors.val[(an.samplers.val[q]).input.val]'(h1 q h) :=
    fun q h => getElem!_pos _ _ _
  loop_auto [inputOk, UScalar.eq_equiv, Option.isSome_iff_ne_none]
termination_by an.samplers.val.length - s.val
decreasing_by all_goals scalar_decr_tac

-- MUST-057, MUST-141, MUST-145: 入力は SCALAR float32 で min / max あり、CUBICSPLINE は 2 個以上
@[step]
theorem animation_samplers_ok_spec (g : model.Gltf) (an : model.Animation)
    (hsm : ∀ x ∈ an.samplers.val, x.input.val < g.accessors.val.length ∧ x.output.val < g.accessors.val.length) :
    validate.animation.animation_samplers_ok g an ⦃ r => r = true ↔ ∀ s ∈ an.samplers.val, inputOk g s ⦄ := by
  unfold validate.animation.animation_samplers_ok
  step*
  simp_all [forallFrom_zero]

@[step]
theorem channels_ok_loop_spec (g : model.Gltf) (an : model.Animation) (c : Usize)
    (hch : ∀ ch ∈ an.channels.val, ch.sampler.val < an.samplers.val.length ∧ optLt ch.node g.nodes.val.length)
    (hsm : ∀ s ∈ an.samplers.val, s.input.val < g.accessors.val.length ∧ s.output.val < g.accessors.val.length)
    (hn : nodeRefsOk g) (hc : c.val ≤ an.channels.val.length) :
    validate.animation.channels_ok_loop g an c ⦃ r => r = true ↔ forallIdx an.channels.val.length c.val (channelOk g an) ⦄ := by
  unfold validate.animation.channels_ok_loop
  loop_auto
termination_by an.channels.val.length - c.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem channels_ok_spec (g : model.Gltf) (an : model.Animation)
    (hch : ∀ ch ∈ an.channels.val, ch.sampler.val < an.samplers.val.length ∧ optLt ch.node g.nodes.val.length)
    (hsm : ∀ s ∈ an.samplers.val, s.input.val < g.accessors.val.length ∧ s.output.val < g.accessors.val.length)
    (hn : nodeRefsOk g) :
    validate.animation.channels_ok g an ⦃ r => r = true ↔ ∀ c < an.channels.val.length, channelOk g an c ⦄ := by
  unfold validate.animation.channels_ok
  step*
  simp_all [forallIdx_zero]

@[step]
theorem animations_ok_loop_spec (g : model.Gltf) (ha : animationRefsOk g) (hn : nodeRefsOk g) (i : Usize)
    (hi : i.val ≤ g.animations.val.length) :
    validate.animation.animations_ok_loop g i ⦃ r => r = true ↔ forallFrom g.animations.val i.val (animOk g) ⦄ := by
  unfold validate.animation.animations_ok_loop
  have ha' : ∀ q (h : q < g.animations.val.length),
      (∀ ch ∈ (g.animations.val[q]).channels.val, ch.sampler.val < (g.animations.val[q]).samplers.val.length ∧
        optLt ch.node g.nodes.val.length) ∧
      (∀ s ∈ (g.animations.val[q]).samplers.val, s.input.val < g.accessors.val.length ∧
        s.output.val < g.accessors.val.length) := fun q h => ha _ (List.getElem_mem h)
  loop_auto [animOk]
termination_by g.animations.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem animations_ok_spec (g : model.Gltf) (ha : animationRefsOk g) (hn : nodeRefsOk g) :
    validate.animation.animations_ok g ⦃ r => r = true ↔ animationsOk g ⦄ := by
  unfold validate.animation.animations_ok animationsOk
  step*
  simp_all [forallFrom_zero]

end LoadGltf
