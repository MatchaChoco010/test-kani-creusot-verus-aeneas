import LoadGltf.Validate.Mesh

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## ノードの階層 (H1–H4) とスキン (S1, S2) -/

def childVals (n : model.Node) : List Nat := n.children.val.map (·.val)

-- H1: すべてのノードの children を通して、各ノード番号は高々 1 回現れる
-- MUST-016, MUST-017: どのノードも高々 1 つの親を持つ
def childrenUnique (g : model.Gltf) : Prop := (g.nodes.val.flatMap childVals).Nodup

-- p は c の親
def isParent (g : model.Gltf) (p c : Nat) : Prop := ∃ h : p < g.nodes.val.length, c ∈ childVals g.nodes.val[p]

instance (g : model.Gltf) (p c : Nat) : Decidable (isParent g p c) := by
  unfold isParent; infer_instance

-- parent(c): c を子に持つノード (H1 の下では一意)
def parentOf (g : model.Gltf) (c : Nat) : Option Nat :=
  (List.range g.nodes.val.length).find? (fun p => decide (isParent g p c))

-- n から parent を k 回たどったノード
def anc (g : model.Gltf) : Nat → Nat → Option Nat
  | 0, n => some n
  | k + 1, n => (anc g k n).bind (parentOf g)

-- r は n から |N| 未満の回数でたどり着く根
def isRootOf (g : model.Gltf) (n r : Nat) : Prop :=
  ∃ k < g.nodes.val.length, anc g k n = some r ∧ parentOf g r = none

-- H2
-- MUST-016, MUST-017: 親をたどると根に着く (循環なし)
def acyclic (g : model.Gltf) : Prop := ∀ n < g.nodes.val.length, ∃ r, isRootOf g n r

-- a は n の祖先または n 自身
def ancestorOrSelf (g : model.Gltf) (a n : Nat) : Prop := ∃ k, anc g k n = some a

-- 親の配列が parentOf を表す
def ParentArr (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) : Prop :=
  P.val.length = g.nodes.val.length ∧ ∀ c, (P.val.getD c none).map (·.val) = parentOf g c

theorem anc_succ (g : model.Gltf) (k n : Nat) : anc g (k + 1) n = (anc g k n).bind (parentOf g) := rfl

theorem anc_none_mono (g : model.Gltf) (k k' n : Nat) (h : anc g k n = none) (hk : k ≤ k') : anc g k' n = none := by
  induction hk with
  | refl => exact h
  | step _ ih => rw [anc_succ, ih]; rfl

theorem isParent_lt (g : model.Gltf) (p c : Nat) (h : isParent g p c) : p < g.nodes.val.length := h.1

theorem parentOf_some (g : model.Gltf) (c q : Nat) (h : parentOf g c = some q) : isParent g q c := by
  unfold parentOf at h
  have := List.find?_some h
  simpa using this

theorem parentOf_none (g : model.Gltf) (c : Nat) : parentOf g c = none ↔ ∀ p, ¬ isParent g p c := by
  unfold parentOf
  rw [List.find?_eq_none]
  constructor
  · intro h p hp
    have := h p (List.mem_range.mpr hp.1)
    simp_all
  · intro h p _; simp [h p]

theorem parentOf_lt (g : model.Gltf) (c q : Nat) (h : parentOf g c = some q) : q < g.nodes.val.length :=
  (parentOf_some g c q h).1

theorem anc_lt (g : model.Gltf) (k n r : Nat) (hn : n < g.nodes.val.length) (h : anc g k n = some r) :
    r < g.nodes.val.length := by
  cases k with
  | zero => simp [anc] at h; omega
  | succ k =>
    rw [anc_succ] at h
    cases hk : anc g k n with
    | none => rw [hk] at h; simp at h
    | some m => rw [hk] at h; exact parentOf_lt g m r h

theorem parent_getD_lt (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (c : Nat)
    (q : U64) (h : P.val.getD c none = some q) : q.val < g.nodes.val.length := by
  have := hP.2 c; rw [h] at this
  exact parentOf_lt g c q.val this.symm

theorem anc_root_none (g : model.Gltf) (k n r : Nat) (h : anc g k n = some r) (hr : parentOf g r = none) :
    anc g (k + 1) n = none := by
  rw [anc_succ, h]; exact hr

theorem root_unique (g : model.Gltf) (n k1 k2 r1 r2 : Nat) (h1 : anc g k1 n = some r1) (hr1 : parentOf g r1 = none)
    (h2 : anc g k2 n = some r2) (hr2 : parentOf g r2 = none) : k1 = k2 ∧ r1 = r2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := anc_none_mono g (k1 + 1) k2 n (anc_root_none g k1 n r1 h1 hr1) h; simp_all
  · subst h; simp_all
  · have := anc_none_mono g (k2 + 1) k1 n (anc_root_none g k2 n r2 h2 hr2) h; simp_all

theorem parentArr_at (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (c : Nat)
    (hc : c < P.val.length) : (P.val[c]).map (·.val) = parentOf g c := by
  have := hP.2 c; rwa [List.getD_eq_getElem _ _ hc] at this

@[step]
theorem root_of_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (cur : U64) (steps : Usize) (hcur : cur.val < g.nodes.val.length) :
    validate.hierarchy.root_of_loop P cur steps ⦃ res => ∀ n, anc g steps.val n = some cur.val →
      ∀ r, res.map (·.val) = some r ↔ isRootOf g n r ⦄ := by
  unfold validate.hierarchy.root_of_loop
  have hl := hP.1
  have hm := mod_numBits_of_lt hcur (by scalar_tac)
  have hpc := parentArr_at g P hP cur.val (by omega)
  step*
  · intro n hn r
    have hpn : parentOf g cur.val = none := by
      have e : (P.val)[cur.val] = none := by simp_all
      rw [← hpc, e]; rfl
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨steps.val, by scalar_tac, hn, hpn⟩
    · rintro ⟨k, hk, ha, hr⟩
      exact (root_unique g n steps.val k _ _ hn hpn ha hr).2
  · have : parentOf g cur.val = some p.val := by
      have e : (P.val)[cur.val] = some p := by simp_all
      rw [← hpc, e]; rfl
    exact parentOf_lt g _ _ this
  · have : parentOf g cur.val = some p.val := by
      have e : (P.val)[cur.val] = some p := by simp_all
      rw [← hpc, e]; rfl
    apply res_post _
    rw [steps1_post, anc_succ, res_post1]
    exact this
  · intro n hn r
    simp only [Option.map_none, reduceCtorEq, false_iff]
    rintro ⟨k, hk, ha, hr⟩
    have := anc_none_mono g (k + 1) steps.val n (anc_root_none g k n r ha hr) (by scalar_tac)
    simp_all
termination_by g.nodes.val.length - steps.val
decreasing_by all_goals scalar_decr_tac

-- MUST-016, MUST-017: 親をたどると根に着く (循環なし)
@[step]
theorem root_of_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (n : U64)
    (hn : n.val < g.nodes.val.length) :
    validate.hierarchy.root_of P n ⦃ res => ∀ r, res.map (·.val) = some r ↔ isRootOf g n.val r ⦄ := by
  unfold validate.hierarchy.root_of
  step*
  exact res_post n.val rfl r

@[step]
theorem is_ancestor_or_self_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (a cur : U64) (steps : Usize) (hcur : cur.val < g.nodes.val.length) :
    validate.hierarchy.is_ancestor_or_self_loop P a cur steps ⦃ res => ∀ n, anc g steps.val n = some cur.val →
      (res = true ↔ ∃ k, steps.val ≤ k ∧ k < g.nodes.val.length ∧ anc g k n = some a.val) ⦄ := by
  unfold validate.hierarchy.is_ancestor_or_self_loop
  have hl := hP.1
  have hm := mod_numBits_of_lt hcur (by scalar_tac)
  have hpc := parentArr_at g P hP cur.val (by omega)
  step*
  · intro n hn
    have hpn : parentOf g cur.val = none := by
      have e : (P.val)[cur.val] = none := by simp_all
      rw [← hpc, e]; rfl
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro k hk hk2 ha
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · simp_all [UScalar.eq_equiv]
    · have := anc_none_mono g (steps.val + 1) k n (anc_root_none g _ n _ hn hpn) hk
      simp_all
  · have : parentOf g cur.val = some p.val := by
      have e : (P.val)[cur.val] = some p := by simp_all
      rw [← hpc, e]; rfl
    exact parentOf_lt g _ _ this
  · have hpp : parentOf g cur.val = some p.val := by
      have e : (P.val)[cur.val] = some p := by simp_all
      rw [← hpc, e]; rfl
    have hr := res_post _ (by rw [steps1_post, anc_succ, res_post1]; exact hpp)
    rw [hr]
    constructor
    · rintro ⟨k, hk, hk2, ha⟩; exact ⟨k, by omega, hk2, ha⟩
    · rintro ⟨k, hk, hk2, ha⟩
      rcases Nat.eq_or_lt_of_le hk with rfl | hk
      · exfalso; simp_all [UScalar.eq_equiv]
      · exact ⟨k, by omega, hk2, ha⟩
termination_by g.nodes.val.length - steps.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem is_ancestor_or_self_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (a n : U64) (hn : n.val < g.nodes.val.length) :
    validate.hierarchy.is_ancestor_or_self P a n ⦃ res => res = true ↔ ∃ k < g.nodes.val.length, anc g k n.val = some a.val ⦄ := by
  unfold validate.hierarchy.is_ancestor_or_self
  step*
  rw [res_post n.val rfl]
  simp

@[step]
theorem all_roots_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (nodes : alloc.vec.Vec U64) (k : Usize) (hn : ∀ x ∈ nodes.val, x.val < g.nodes.val.length)
    (hk : k.val ≤ nodes.val.length) :
    validate.hierarchy.all_roots_loop P nodes k ⦃ r => r = true ↔ forallFrom nodes.val k.val (fun x => parentOf g x.val = none) ⦄ := by
  unfold validate.hierarchy.all_roots_loop
  have hn' : ∀ q (h : q < nodes.val.length), (nodes.val[q]).val < P.val.length := by
    intro q h; rw [hP.1]; exact hn _ (List.getElem_mem h)
  have hpc : ∀ q (h : q < nodes.val.length), ((P.val)[(nodes.val[q]).val]'(hn' q h)).map (·.val) =
      parentOf g (nodes.val[q]).val := fun q h => parentArr_at g P hP _ _
  have hm : ∀ q (h : q < nodes.val.length), (nodes.val[q]).val % 2 ^ System.Platform.numBits = (nodes.val[q]).val :=
    fun q h => mod_numBits_of_lt (hn' q h) (by scalar_tac)
  step*
  all_goals (try (have e1 := hm k.val (by scalar_tac)))
  all_goals (try (have e2 := hpc k.val (by scalar_tac)))
  all_goals simp_all [forallFrom_step_vec, forallFrom_end_vec, Option.isSome_iff_ne_none]
  intro h _
  have := hpc k.val (by scalar_tac)
  rw [h, Option.map_eq_none_iff] at this
  contradiction
termination_by nodes.val.length - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem all_roots_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (nodes : alloc.vec.Vec U64) (hn : ∀ x ∈ nodes.val, x.val < g.nodes.val.length) :
    validate.hierarchy.all_roots P nodes ⦃ r => r = true ↔ ∀ x ∈ nodes.val, parentOf g x.val = none ⦄ := by
  unfold validate.hierarchy.all_roots
  step*
  simp_all [forallFrom_zero]

@[step]
theorem none_vec_loop_spec (n : Usize) (v : alloc.vec.Vec (Option U64)) (i : Usize)
    (hv : v.val = List.replicate i.val none) (hi : i.val ≤ n.val) :
    validate.hierarchy.none_vec_loop n v i ⦃ r => r.val = List.replicate n.val none ⦄ := by
  unfold validate.hierarchy.none_vec_loop
  step*
  rw [v1_post, hv, i1_post, List.replicate_succ']
termination_by n.val - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem none_vec_spec (n : Usize) : validate.hierarchy.none_vec n ⦃ r => r.val = List.replicate n.val none ⦄ := by
  unfold validate.hierarchy.none_vec
  step*
  simp

theorem getD_set_none {α} (l : List (Option α)) (i j : Nat) (a : Option α) (hi : i < l.length) :
    (l.set i a).getD j none = if i = j then a else l.getD j none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split <;> simp_all

theorem elem_lt_of_forall {children : alloc.vec.Vec U64} {n : Nat} {k : Usize}
    (hc : ∀ x ∈ children.val, x.val < n) (h : k.val < children.val.length) : (children.val[k.val]).val < n :=
  hc _ (List.getElem_mem h)

theorem cast_elem_val_of_forall {children : alloc.vec.Vec U64} {n : Nat} {k : Usize}
    (hc : ∀ x ∈ children.val, x.val < n) (hn : n ≤ Usize.max) (h : k.val < children.val.length) :
    (UScalar.cast .Usize (children.val[k.val])).val = (children.val[k.val]).val :=
  u64_cast_usize_val _ (by have := hc _ (List.getElem_mem h); omega)

theorem assign_step (P : List (Option U64)) (p : U64) (cs : List U64) (k : Nat) (hk : k < cs.length)
    (hcl : (cs[k]).val < P.length) (hPc : P.getD (cs[k]).val none = none) (b : Bool)
    (P' : List (Option U64))
    (h1 : b = true ↔ ((cs.drop (k + 1)).map (·.val)).Nodup ∧
      ∀ x ∈ cs.drop (k + 1), (P.set (cs[k]).val (some p)).getD x.val none = none)
    (h2 : b = true → P'.length = (P.set (cs[k]).val (some p)).length ∧ ∀ c, P'.getD c none =
      if c ∈ (cs.drop (k + 1)).map (·.val) then some p else (P.set (cs[k]).val (some p)).getD c none) :
    (b = true ↔ ((cs.drop k).map (·.val)).Nodup ∧ ∀ x ∈ cs.drop k, P.getD x.val none = none) ∧
    (b = true → P'.length = P.length ∧ ∀ c, P'.getD c none =
      if c ∈ (cs.drop k).map (·.val) then some p else P.getD c none) := by
  have hd := List.drop_eq_getElem_cons hk
  have hs : ∀ j, (P.set (cs[k]).val (some p)).getD j none = if (cs[k]).val = j then some p else P.getD j none :=
    fun j => getD_set_none _ _ _ _ hcl
  simp only [hs] at h1 h2
  rw [hd]
  refine ⟨?_, ?_⟩
  · rw [h1]
    simp only [List.map_cons, List.nodup_cons, List.mem_map, List.mem_cons, forall_eq_or_imp, hPc, true_and]
    constructor
    · rintro ⟨hn, hall⟩
      refine ⟨⟨?_, hn⟩, fun x hx => ?_⟩
      · rintro ⟨y, hy, hyv⟩
        have := hall y hy
        rw [if_pos hyv.symm] at this
        simp at this
      · have := hall x hx
        split at this
        · simp at this
        · exact this
    · rintro ⟨⟨hn1, hn2⟩, hall⟩
      refine ⟨hn2, fun x hx => ?_⟩
      rw [if_neg (fun e => hn1 ⟨x, hx, e.symm⟩)]
      exact hall x hx
  · intro hb
    obtain ⟨hl, hv⟩ := h2 hb
    refine ⟨by rw [hl, List.length_set], fun c' => ?_⟩
    rw [hv c']
    simp only [List.map_cons, List.mem_cons]
    by_cases e1 : c' ∈ List.map (fun x => x.val) (List.drop (k + 1) cs)
    · rw [ite_eq_left e1, ite_eq_left (Or.inr e1)]
    · by_cases e2 : c' = (cs[k]).val
      · rw [ite_eq_right e1, ite_eq_left e2.symm, ite_eq_left (Or.inl e2)]
      · rw [ite_eq_right e1, ite_eq_right (Ne.symm e2), ite_eq_right (by tauto)]

set_option maxRecDepth 8192 in
@[step]
theorem assign_parent_loop_spec (P : alloc.vec.Vec (Option U64)) (p : U64) (children : alloc.vec.Vec U64)
    (k : Usize) (hk : k.val ≤ children.val.length) (hc : ∀ x ∈ children.val, x.val < P.val.length) :
    validate.hierarchy.assign_parent_loop P p children k ⦃ res =>
      (res.1 = true ↔ ((children.val.drop k.val).map (·.val)).Nodup ∧
        ∀ x ∈ children.val.drop k.val, P.val.getD x.val none = none) ∧
      (res.1 = true → res.2.val.length = P.val.length ∧ ∀ c, res.2.val.getD c none =
        if c ∈ (children.val.drop k.val).map (·.val) then some p else P.val.getD c none) ⦄ := by
  unfold validate.hierarchy.assign_parent_loop
  step*
  all_goals first
  | (rw [c_post, i1_post, cast_elem_val_of_forall hc (alloc.vec.Vec.len_ineq P) (usize_lt_len ‹_›)]; exact elem_lt_of_forall hc (usize_lt_len ‹_›))
  | (intro x hx; rw [index_mut_back_post]; simp only [alloc.vec.Vec.set_val_eq, List.length_set]
     exact hc x hx)
  | (have hkn : children.val.length ≤ k.val := Nat.le_of_not_lt (fun h => ‹¬k < children.len›
       (by simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val]; exact h))
     rw [List.drop_eq_nil_of_le hkn]; simp; done)
  | (have hk' : k.val < children.val.length := usize_lt_len ‹_›
     have hd := List.drop_eq_getElem_cons hk'
     have hcv' : c.val = (children.val[k.val]).val := by rw [c_post, i1_post, cast_elem_val_of_forall hc (alloc.vec.Vec.len_ineq P) hk']
     have hoc : o = P.val.getD (children.val[k.val]).val none := by
       rw [o_post, List.getD_eq_getElem _ _ (elem_lt_of_forall hc hk')]; exact getElem_idx_eq hcv' _ _
     simp only [Bool.false_eq_true, false_iff, false_imp_iff, and_true]
     rintro ⟨-, h⟩
     have := h _ (by rw [hd]; exact List.mem_cons_self)
     rw [← hoc] at this
     have h2 := ‹o.isSome = true›
     rw [this] at h2
     simp at h2)
  | (have hk' : k.val < children.val.length := usize_lt_len ‹_›
     have hcv' : c.val = (children.val[k.val]).val := by rw [c_post, i1_post, cast_elem_val_of_forall hc (alloc.vec.Vec.len_ineq P) hk']
     have hoc : o = P.val.getD (children.val[k.val]).val none := by
       rw [o_post, List.getD_eq_getElem _ _ (elem_lt_of_forall hc hk')]; exact getElem_idx_eq hcv' _ _
     have hPc : P.val.getD (children.val[k.val]).val none = none := by
       rw [← hoc]; simpa using ‹¬o.isSome = true›
     rw [k1_post, index_mut_back_post, alloc.vec.Vec.set_val_eq, hcv'] at res_post res_post1
     exact assign_step P.val p children.val k.val hk' (elem_lt_of_forall hc hk') hPc res.1 res.2.val res_post res_post1)
termination_by children.val.length - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem assign_parent_spec (P : alloc.vec.Vec (Option U64)) (p : U64) (children : alloc.vec.Vec U64)
    (hc : ∀ x ∈ children.val, x.val < P.val.length) :
    validate.hierarchy.assign_parent P p children ⦃ res =>
      (res.1 = true ↔ (children.val.map (·.val)).Nodup ∧ ∀ x ∈ children.val, P.val.getD x.val none = none) ∧
      (res.1 = true → res.2.val.length = P.val.length ∧ ∀ c, res.2.val.getD c none =
        if c ∈ children.val.map (·.val) then some p else P.val.getD c none) ⦄ := by
  unfold validate.hierarchy.assign_parent
  have := assign_parent_loop_spec P p children 0#usize (by simp) hc
  simpa only [UScalar.ofNatCore_val_eq, List.drop_zero] using this

-- 先頭 i 個のノードの children をつないだ列
def prefixChildren (v : List model.Node) (i : Nat) : List Nat := (v.take i).flatMap childVals

theorem prefixChildren_succ (v : List model.Node) (i : Nat) (h : i < v.length) :
    prefixChildren v (i + 1) = prefixChildren v i ++ childVals v[i] := by
  unfold prefixChildren
  rw [List.take_succ_eq_append_getElem h, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem mem_prefixChildren (v : List model.Node) (i c : Nat) :
    c ∈ prefixChildren v i ↔ ∃ q, ∃ h : q < v.length, q < i ∧ c ∈ childVals v[q] := by
  simp only [prefixChildren, List.mem_flatMap, List.mem_take_iff_getElem]
  constructor
  · rintro ⟨n, ⟨q, hq, rfl⟩, hc⟩
    exact ⟨q, by omega, by omega, hc⟩
  · rintro ⟨q, hq, hqi, hc⟩
    exact ⟨v[q], ⟨q, by omega, rfl⟩, hc⟩

theorem prefixChildren_sublist (v : List model.Node) (i : Nat) :
    List.Sublist (prefixChildren v i) (v.flatMap childVals) := by
  have : v.flatMap childVals = prefixChildren v i ++ (v.drop i).flatMap childVals := by
    rw [prefixChildren, ← List.flatMap_append, List.take_append_drop]
  rw [this]; exact List.sublist_append_left _ _

-- 親の配列の不変条件 (先頭 i 個のノードを処理済み)
def parentInv (v : List model.Node) (i : Nat) (P : List (Option U64)) : Prop :=
  P.length = v.length ∧ (prefixChildren v i).Nodup ∧
  ∀ c q, (P.getD c none).map (·.val) = some q ↔ ∃ h : q < v.length, q < i ∧ c ∈ childVals v[q]

theorem notin_prefix_of_none (v : List model.Node) (i : Nat) (P : List (Option U64)) (hinv : parentInv v i P)
    (c : Nat) (hc : P.getD c none = none) : c ∉ prefixChildren v i := by
  intro hm
  obtain ⟨q, hq, hqi, hcq⟩ := (mem_prefixChildren v i c).mp hm
  have := (hinv.2.2 c q).mpr ⟨hq, hqi, hcq⟩
  rw [hc] at this; simp at this

theorem parentInv_step (v : List model.Node) (i : Nat) (hi : i < v.length) (P P1 : List (Option U64)) (ip : U64)
    (hip : ip.val = i) (hinv : parentInv v i P)
    (hb : (childVals v[i]).Nodup ∧ ∀ x ∈ (v[i]).children.val, P.getD x.val none = none)
    (hl : P1.length = P.length)
    (hP1 : ∀ c, P1.getD c none = if c ∈ childVals v[i] then some ip else P.getD c none) :
    parentInv v (i + 1) P1 := by
  obtain ⟨hl0, hn0, hm0⟩ := hinv
  have hdis : ∀ c ∈ childVals v[i], c ∉ prefixChildren v i := by
    intro c hc
    simp only [childVals, List.mem_map] at hc
    obtain ⟨y, hy, rfl⟩ := hc
    exact notin_prefix_of_none v i P ⟨hl0, hn0, hm0⟩ _ (hb.2 y hy)
  refine ⟨by omega, ?_, ?_⟩
  · rw [prefixChildren_succ v i hi, List.nodup_append]
    refine ⟨hn0, hb.1, fun a ha b hb' e => hdis b hb' (e ▸ ha)⟩
  · intro c q
    rw [hP1 c]
    by_cases hc : c ∈ childVals v[i]
    · rw [ite_eq_left hc]
      simp only [Option.map_some, Option.some.injEq, hip]
      constructor
      · rintro rfl; exact ⟨hi, by omega, hc⟩
      · rintro ⟨hq, hqi, hcq⟩
        rcases Nat.lt_or_ge q i with h | h
        · exfalso; exact hdis c hc ((mem_prefixChildren v i c).mpr ⟨q, hq, h, hcq⟩)
        · omega
    · rw [ite_eq_right hc, hm0 c q]
      constructor
      · rintro ⟨hq, hqi, hcq⟩; exact ⟨hq, by omega, hcq⟩
      · rintro ⟨hq, hqi, hcq⟩
        refine ⟨hq, ?_, hcq⟩
        rcases Nat.lt_or_ge q i with h | h
        · exact h
        · have : q = i := by omega
          subst this; exact absurd hcq hc

theorem parentInv_fail (v : List model.Node) (i : Nat) (hi : i < v.length) (P : List (Option U64))
    (hinv : parentInv v i P)
    (hb : ¬ ((childVals v[i]).Nodup ∧ ∀ x ∈ (v[i]).children.val, P.getD x.val none = none)) :
    ¬ (v.flatMap childVals).Nodup := by
  intro hn
  apply hb
  have h1 := (prefixChildren_sublist v (i + 1)).nodup hn
  rw [prefixChildren_succ v i hi, List.nodup_append] at h1
  refine ⟨h1.2.1, fun x hx => ?_⟩
  cases hP : P.getD x.val none with
  | none => rfl
  | some q =>
    exfalso
    have hm := (hinv.2.2 x.val q.val).mp (by rw [hP]; rfl)
    obtain ⟨hq, hqi, hcq⟩ := hm
    exact h1.2.2 x.val ((mem_prefixChildren v i x.val).mpr ⟨q.val, hq, hqi, hcq⟩) x.val
      (List.mem_map_of_mem hx) rfl

@[step]
theorem parents_loop_spec (v : alloc.vec.Vec model.Node) (P : alloc.vec.Vec (Option U64)) (i : Usize)
    (hi : i.val ≤ v.val.length) (hr : ∀ nd ∈ v.val, ∀ c ∈ nd.children.val, c.val < v.val.length)
    (hinv : parentInv v.val i.val P.val) :
    validate.hierarchy.parents_loop v P i ⦃ res => match res with
      | some P' => (v.val.flatMap childVals).Nodup ∧ parentInv v.val v.val.length P'.val
      | none => ¬ (v.val.flatMap childVals).Nodup ⦄ := by
  unfold validate.hierarchy.parents_loop
  step*
  · intro x hx
    rw [hinv.1]; exact hr _ (by rw [n_post]; exact List.getElem_mem _) x hx
  · have hi' : i.val < v.val.length := by scalar_tac
    have hb := b_post.mp ‹_›
    obtain ⟨hl, hv⟩ := b_post1 ‹_›
    rw [i3_post]
    subst n_post
    exact parentInv_step v.val i.val hi' P.val parent1.val i2 (by rw [i2_post]; exact usize_cast_u64_val i)
      hinv ⟨hb.1, hb.2⟩ hl hv
  · have hi' : i.val < v.val.length := by scalar_tac
    subst n_post
    exact parentInv_fail v.val i.val hi' P.val hinv (fun h => ‹¬b = true› (b_post.mpr h))
  · have he : i.val = v.val.length := by scalar_tac
    rw [he] at hinv
    refine ⟨?_, hinv⟩
    have := hinv.2.1
    rwa [prefixChildren, List.take_of_length_le (le_refl _)] at this
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem parentArr_of_inv (g : model.Gltf) (P : alloc.vec.Vec (Option U64))
    (hinv : parentInv g.nodes.val g.nodes.val.length P.val) : ParentArr g P := by
  refine ⟨hinv.1, fun c => ?_⟩
  have hiff : ∀ q, (P.val.getD c none).map (·.val) = some q ↔ isParent g q c := by
    intro q; rw [hinv.2.2 c q]
    constructor
    · rintro ⟨hq, -, hc⟩; exact ⟨hq, hc⟩
    · rintro ⟨hq, hc⟩; exact ⟨hq, hq, hc⟩
  cases ho : (P.val.getD c none).map (·.val) with
  | none =>
    symm; rw [parentOf_none]
    intro p hp; have := (hiff p).mpr hp; rw [ho] at this; simp at this
  | some q =>
    have hq := (hiff q).mp ho
    cases hp : parentOf g c with
    | none => rw [parentOf_none] at hp; exact absurd hq (hp q)
    | some q' =>
      have := (hiff q').mpr (parentOf_some g c q' hp)
      rw [ho] at this; exact this

-- MUST-016, MUST-017: どのノードも高々 1 つの親を持つ
/-- H1 と親の配列 -/
@[step]
theorem parents_spec (g : model.Gltf) (hr : nodeRefsOk g) :
    validate.hierarchy.parents g ⦃ res => match res with
      | some P => childrenUnique g ∧ ParentArr g P
      | none => ¬ childrenUnique g ⦄ := by
  unfold validate.hierarchy.parents
  have hr' : ∀ nd ∈ g.nodes.val, ∀ c ∈ nd.children.val, c.val < g.nodes.val.length :=
    fun nd h => (hr nd h).1
  step*
  · refine ⟨by simp_all, by simp [prefixChildren], ?_⟩
    intro c q
    simp_all [List.getD_eq_getElem?_getD]
  · rcases res with _ | P <;> simp only at res_post ⊢
    · exact res_post
    · exact ⟨res_post.1, parentArr_of_inv g P res_post.2⟩

-- H3
-- MUST-018, MUST-102, MUST-103, MUST-104: children の重複なし、weights の長さ、skin なら mesh、JOINTS_0
def nodeOk (g : model.Gltf) (i : Nat) : Prop :=
  let n := g.nodes.val[i]!
  n.children.val.Nodup ∧ ¬(n.has_matrix = true ∧ n.has_trs = true) ∧
  ((n.skin ≠ none ∨ n.weights_len ≠ none) → n.mesh ≠ none) ∧
  (∀ m w, n.mesh = some m → n.weights_len = some w → w.val = morphCount g.meshes.val[m.val]!) ∧
  (∀ m, n.skin ≠ none → n.mesh = some m →
    ∀ p ∈ (g.meshes.val[m.val]!).primitives.val, hasSem p.attributes.val 6 0)

@[step]
theorem skinned_mesh_ok_loop_spec (m : model.Mesh) (p : Usize) (hp : p.val ≤ m.primitives.val.length) :
    validate.hierarchy.skinned_mesh_ok_loop m p ⦃ r => r = true ↔
      forallFrom m.primitives.val p.val (fun q => hasSem q.attributes.val 6 0) ⦄ := by
  unfold validate.hierarchy.skinned_mesh_ok_loop
  have hc := sem_consts
  loop_auto
termination_by m.primitives.val.length - p.val
decreasing_by all_goals scalar_decr_tac

-- MUST-104: スキンのメッシュのプリミティブは JOINTS_0 を持つ
@[step]
theorem skinned_mesh_ok_spec (m : model.Mesh) :
    validate.hierarchy.skinned_mesh_ok m ⦃ r => r = true ↔ ∀ q ∈ m.primitives.val, hasSem q.attributes.val 6 0 ⦄ := by
  unfold validate.hierarchy.skinned_mesh_ok
  step*
  simp_all [forallFrom_zero]

-- MUST-016, MUST-017, MUST-018, MUST-102, MUST-103: 根に着く、children の重複なし、weights の長さ、skin なら mesh
set_option maxHeartbeats 4000000 in
@[step]
theorem node_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (hr : nodeRefsOk g)
    (i : Usize) (hi : i.val < g.nodes.val.length) :
    validate.hierarchy.node_ok g P i ⦃ r => r = true ↔ nodeOk g i.val ∧ ∃ rt, isRootOf g i.val rt ⦄ := by
  unfold validate.hierarchy.node_ok nodeOk
  rw [getElem!_pos g.nodes.val i.val hi]
  have hrefs := hr _ (List.getElem_mem hi)
  have hroot := root_of_spec g P hP (UScalar.cast .U64 i) (by rw [usize_cast_u64_val]; exact hi)
  rw [usize_cast_u64_val] at hroot
  rcases hnd : g.nodes.val[i.val] with ⟨ch, me, ca, sk, hmx, htrs, wl⟩
  rw [hnd] at hrefs
  simp only [optLt] at hrefs
  step
  subst n_post
  simp only [hnd]
  rcases me with _ | m <;> rcases wl with _ | w <;> rcases sk with _ | s <;>
    simp only [reduceCtorEq, false_imp_iff, forall_const, Option.some.injEq, forall_eq'] at hrefs <;>
    step*
  all_goals (try have hmm := mod_numBits_of_lt hrefs.2.1 (alloc.vec.Vec.len_ineq g.meshes))
  all_goals (try rw [getElem!_pos g.meshes.val m.val hrefs.2.1])
  all_goals (try simp_all)
  all_goals (try intro _)
  all_goals (try refine ⟨fun m1 h => by subst h; rw [List.getElem?_eq_getElem (by simp_all)]; rfl, ?_⟩)
  all_goals first
    | (obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ‹¬o = none›
       exact ⟨a.val, (o_post _).mp ⟨a, ha, rfl⟩⟩)
    | (obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ‹¬o = none›
       constructor
       · intro h
         refine ⟨fun m1 hm => ?_, h, ⟨a.val, (o_post _).mp ⟨a, ha, rfl⟩⟩⟩
         subst hm; rw [List.getElem?_eq_getElem (by simp_all)]; rfl
       · rintro ⟨-, h, -⟩; exact h)

@[step]
theorem nodes_ok_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (hr : nodeRefsOk g)
    (i : Usize) (hi : i.val ≤ g.nodes.val.length) :
    validate.hierarchy.nodes_ok_loop g P i ⦃ r => r = true ↔
      forallIdx g.nodes.val.length i.val (fun q => nodeOk g q ∧ ∃ rt, isRootOf g q rt) ⦄ := by
  unfold validate.hierarchy.nodes_ok_loop
  loop_auto
termination_by g.nodes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem nodes_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (hr : nodeRefsOk g) :
    validate.hierarchy.nodes_ok g P ⦃ r => r = true ↔ ∀ q < g.nodes.val.length, nodeOk g q ∧ ∃ rt, isRootOf g q rt ⦄ := by
  unfold validate.hierarchy.nodes_ok
  step*
  simp_all [forallIdx_zero]

-- H4
-- MUST-015: scene.nodes は重複なしの根
def scenesOk (g : model.Gltf) : Prop :=
  ∀ sc ∈ g.scenes.val, sc.nodes.val.Nodup ∧ ∀ x ∈ sc.nodes.val, parentOf g x.val = none

@[step]
theorem scenes_ok_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (hr : sceneRefsOk g) (s : Usize) (hs : s.val ≤ g.scenes.val.length) :
    validate.hierarchy.scenes_ok_loop g P s ⦃ r => r = true ↔ forallFrom g.scenes.val s.val
      (fun sc => sc.nodes.val.Nodup ∧ ∀ x ∈ sc.nodes.val, parentOf g x.val = none) ⦄ := by
  unfold validate.hierarchy.scenes_ok_loop
  have hr' : ∀ j (h : j < g.scenes.val.length), ∀ x ∈ (g.scenes.val[j]).nodes.val, x.val < g.nodes.val.length :=
    fun j h => hr _ (List.getElem_mem h)
  loop_auto
termination_by g.scenes.val.length - s.val
decreasing_by all_goals scalar_decr_tac

-- MUST-015: scene.nodes は重複なしの根
@[step]
theorem scenes_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (hr : sceneRefsOk g) :
    validate.hierarchy.scenes_ok g P ⦃ r => r = true ↔ scenesOk g ⦄ := by
  unfold validate.hierarchy.scenes_ok scenesOk
  step*
  simp_all [forallFrom_zero]

theorem opt_eq_iff_root {o root : Option U64} {X : Nat → Prop} (h : ∀ r, o.map (·.val) = some r ↔ X r) :
    o = root ↔ ∀ r, X r ↔ root.map (·.val) = some r := by
  constructor
  · rintro rfl r; rw [h]
  · intro h2
    have : o.map (·.val) = root.map (·.val) := by
      apply Option.ext; intro r; rw [h, h2]
    rcases o with _ | a <;> rcases root with _ | b <;> simp_all [UScalar.eq_equiv]

@[step]
theorem joints_ok_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (sk : model.Skin)
    (root : Option U64) (k : Usize) (hj : ∀ j ∈ sk.joints.val, j.val < g.nodes.val.length)
    (hk : k.val ≤ sk.joints.val.length) :
    validate.hierarchy.joints_ok_loop P sk root k ⦃ r => r = true ↔ forallFrom sk.joints.val k.val (fun j =>
      (∀ rt, isRootOf g j.val rt ↔ root.map (·.val) = some rt) ∧
      (∀ s, sk.skeleton = some s → ∃ k' < g.nodes.val.length, anc g k' j.val = some s.val)) ⦄ := by
  unfold validate.hierarchy.joints_ok_loop
  have hj' : ∀ q (h : q < sk.joints.val.length), (sk.joints.val[q]).val < g.nodes.val.length :=
    fun q h => hj _ (List.getElem_mem h)
  rcases hs : sk.skeleton with _ | s <;> step*
  all_goals (try rw [opt_eq_iff_root o_post] at b_post)
  all_goals simp_all [forallFrom_step_vec, forallFrom_end_vec]
termination_by sk.joints.val.length - k.val
decreasing_by all_goals scalar_decr_tac

-- MUST-100, MUST-101: 関節の共通の根と skeleton
@[step]
theorem joints_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (sk : model.Skin)
    (root : Option U64) (hj : ∀ j ∈ sk.joints.val, j.val < g.nodes.val.length) :
    validate.hierarchy.joints_ok P sk root ⦃ r => r = true ↔ ∀ j ∈ sk.joints.val,
      (∀ rt, isRootOf g j.val rt ↔ root.map (·.val) = some rt) ∧
      (∀ s, sk.skeleton = some s → ∃ k' < g.nodes.val.length, anc g k' j.val = some s.val) ⦄ := by
  unfold validate.hierarchy.joints_ok
  step*
  simp_all [forallFrom_zero]

-- S1 (スケルトンの祖先関係は |N| 未満の段数で判定する)
def skinOkB (g : model.Gltf) (sk : model.Skin) : Prop :=
  sk.joints.val ≠ [] ∧ sk.joints.val.Nodup ∧
  (∀ j ∈ sk.joints.val, ∀ rt, isRootOf g j.val rt ↔ isRootOf g (sk.joints.val[0]!).val rt) ∧
  (∀ s, sk.skeleton = some s → ∀ j ∈ sk.joints.val, ∃ k < g.nodes.val.length, anc g k j.val = some s.val) ∧
  (∀ a, sk.inverse_bind_matrices = some a →
    (g.accessors.val[a.val]!).is_matrix = true ∧ (g.accessors.val[a.val]!).components.val = 16 ∧
    isFloat32 (g.accessors.val[a.val]!) ∧ sk.joints.val.length ≤ (g.accessors.val[a.val]!).count.val)

-- MUST-096, MUST-097: joints の重複なし、逆バインド行列
set_option maxHeartbeats 2000000 in
@[step]
theorem skin_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (sk : model.Skin)
    (hj : ∀ j ∈ sk.joints.val, j.val < g.nodes.val.length)
    (hb : optLt sk.inverse_bind_matrices g.accessors.val.length) :
    validate.hierarchy.skin_ok g P sk ⦃ r => r = true ↔ skinOkB g sk ⦄ := by
  unfold validate.hierarchy.skin_ok skinOkB
  by_cases he : sk.joints.val = []
  · step* <;> simp_all
  have h0 : 0 < sk.joints.val.length := List.length_pos_iff_ne_nil.mpr he
  rw [getElem!_pos sk.joints.val 0 h0]
  rcases hi : sk.inverse_bind_matrices with _ | a <;> simp only [optLt, hi, reduceCtorEq, false_imp_iff,
    forall_const, Option.some.injEq, forall_eq'] at hb ⊢
  all_goals (try rw [getElem!_pos g.accessors.val a.val hb])
  all_goals (try have hma := mod_numBits_of_lt hb (alloc.vec.Vec.len_ineq g.accessors))
  all_goals step*
  all_goals (try simp_all [UScalar.eq_equiv])
  all_goals first
    | (intro h; obtain ⟨x, hx, hc⟩ := b1_post; obtain ⟨s, hs, hk⟩ := hc (h x hx); exact ⟨s, hs, x, hx, hk⟩)
    | (intro h1 h2; exfalso; obtain ⟨x, hx, hc⟩ := b1_post; obtain ⟨s, hs, hk⟩ := hc (h1 x hx)
       obtain ⟨k, hk1, hk2⟩ := h2 s hs x hx; exact hk k hk1 hk2)

@[step]
theorem skin_list_ok_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (hr : skinRefsOk g) (i : Usize) (hi : i.val ≤ g.skins.val.length) :
    validate.hierarchy.skin_list_ok_loop g P i ⦃ r => r = true ↔ forallFrom g.skins.val i.val (fun sk => skinOkB g sk) ⦄ := by
  unfold validate.hierarchy.skin_list_ok_loop
  have hr' : ∀ j (h : j < g.skins.val.length), (∀ x ∈ (g.skins.val[j]).joints.val, x.val < g.nodes.val.length) ∧
      optLt (g.skins.val[j]).inverse_bind_matrices g.accessors.val.length :=
    fun j h => ⟨(hr _ (List.getElem_mem h)).1, (hr _ (List.getElem_mem h)).2.2⟩
  loop_auto
termination_by g.skins.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem skin_list_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P) (hr : skinRefsOk g) :
    validate.hierarchy.skin_list_ok g P ⦃ r => r = true ↔ ∀ sk ∈ g.skins.val, skinOkB g sk ⦄ := by
  unfold validate.hierarchy.skin_list_ok
  step*
  simp_all [forallFrom_zero]

@[step]
theorem skin_scene_ok_loop_spec (g : model.Gltf) (jr nr : Option U64) (sc : Usize) (hs : sc.val ≤ g.scenes.val.length) :
    validate.hierarchy.skin_scene_ok_loop g jr nr sc ⦃ r => r = true ↔ forallFrom g.scenes.val sc.val (fun s =>
      (∃ x, nr = some x ∧ x ∈ s.nodes.val) → (∃ x, jr = some x ∧ x ∈ s.nodes.val)) ⦄ := by
  unfold validate.hierarchy.skin_scene_ok_loop
  rcases jr with _ | j <;> rcases nr with _ | n <;> loop_auto
termination_by g.scenes.val.length - sc.val
decreasing_by all_goals scalar_decr_tac

-- MUST-105: スキンの関節の根は同じシーンにある
@[step]
theorem skin_scene_ok_spec (g : model.Gltf) (jr nr : Option U64) :
    validate.hierarchy.skin_scene_ok g jr nr ⦃ r => r = true ↔ ∀ s ∈ g.scenes.val,
      (∃ x, nr = some x ∧ x ∈ s.nodes.val) → (∃ x, jr = some x ∧ x ∈ s.nodes.val) ⦄ := by
  unfold validate.hierarchy.skin_scene_ok
  step*
  simp_all [forallFrom_zero]

theorem exists_root_mem {o : Option U64} {X : Nat → Prop} (h : ∀ r, o.map (·.val) = some r ↔ X r)
    (l : List U64) : (∃ x, o = some x ∧ x ∈ l) ↔ ∃ r, X r ∧ r ∈ l.map (·.val) := by
  constructor
  · rintro ⟨x, rfl, hx⟩; exact ⟨x.val, (h _).mp rfl, List.mem_map_of_mem hx⟩
  · rintro ⟨r, hr, hm⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    have := (h x.val).mpr hr
    rcases o with _ | y
    · simp at this
    · simp only [Option.map_some, Option.some.injEq] at this
      have : y = x := by rw [UScalar.eq_equiv]; exact this
      exact ⟨y, rfl, this ▸ hx⟩

theorem scene_cond_iff {o o1 : Option U64} {X Y : Nat → Prop} (ho : ∀ r, o.map (·.val) = some r ↔ X r)
    (ho1 : ∀ r, o1.map (·.val) = some r ↔ Y r) :
    (∀ s ∈ (l : List model.Scene), ∀ x, o1 = some x → x ∈ s.nodes.val → ∃ x, o = some x ∧ x ∈ s.nodes.val) ↔
    (∀ s ∈ l, ∀ r, Y r → r ∈ s.nodes.val.map (·.val) → ∃ r, X r ∧ r ∈ s.nodes.val.map (·.val)) := by
  apply forall₂_congr; intro s _
  have h1 := exists_root_mem ho s.nodes.val
  have h2 := exists_root_mem ho1 s.nodes.val
  constructor
  · intro h r hy hr
    obtain ⟨x, hx, hm⟩ := h2.mpr ⟨r, hy, hr⟩
    exact h1.mp (h x hx hm)
  · intro h x hx hm
    obtain ⟨r, hy, hr⟩ := h2.mp ⟨x, hx, hm⟩
    exact h1.mpr (h r hy hr)

-- S2
-- MUST-105: スキンの関節の根は同じシーンにある
def skinnedNodesOk (g : model.Gltf) : Prop :=
  ∀ q < g.nodes.val.length, ∀ s, (g.nodes.val[q]!).skin = some s →
    (g.skins.val[s.val]!).joints.val ≠ [] ∧
    ∀ sc ∈ g.scenes.val, ∀ r, isRootOf g q r → r ∈ sc.nodes.val.map (·.val) →
      ∃ r', isRootOf g ((g.skins.val[s.val]!).joints.val[0]!).val r' ∧ r' ∈ sc.nodes.val.map (·.val)

set_option maxHeartbeats 2000000 in
@[step]
theorem skinned_nodes_ok_loop_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (hn : nodeRefsOk g) (hs : skinRefsOk g) (i : Usize) (hi : i.val ≤ g.nodes.val.length) :
    validate.hierarchy.skinned_nodes_ok_loop g P i ⦃ r => r = true ↔ forallIdx g.nodes.val.length i.val (fun q =>
      ∀ s, (g.nodes.val[q]!).skin = some s →
        (g.skins.val[s.val]!).joints.val ≠ [] ∧
        ∀ sc ∈ g.scenes.val, ∀ r, isRootOf g q r → r ∈ sc.nodes.val.map (·.val) →
          ∃ r', isRootOf g ((g.skins.val[s.val]!).joints.val[0]!).val r' ∧ r' ∈ sc.nodes.val.map (·.val)) ⦄ := by
  unfold validate.hierarchy.skinned_nodes_ok_loop
  by_cases hlt : i.val < g.nodes.val.length
  · have hsk := (hn _ (List.getElem_mem hlt)).2.2.2
    rcases hnd : (g.nodes.val[i.val]).skin with _ | s
    · simp only [show i < g.nodes.len by scalar_tac, ↓reduceIte]
      step
      subst n_post
      simp only [hnd]
      step*
      rw [forallIdx_step_vec (by scalar_tac), getElem!_pos g.nodes.val i.val hlt, hnd]
      simp_all
    · rw [hnd] at hsk
      have hsl : s.val < g.skins.val.length := hsk s rfl
      have hjs := (hs _ (List.getElem_mem hsl)).1
      have hms := mod_numBits_of_lt hsl (alloc.vec.Vec.len_ineq g.skins)
      simp only [show i < g.nodes.len by scalar_tac, ↓reduceIte]
      step
      subst n_post
      simp only [hnd]
      step*
      all_goals (have hi2 : i2.val = s.val := by rw [i2_post]; exact u64_cast_usize_val _ (by scalar_tac))
      all_goals (have hsk' : sk = g.skins.val[s.val] := by rw [sk_post]; exact getElem_idx_eq hi2 _ _)
      all_goals subst hsk'
      · have he : (g.skins.val[s.val]).joints.val = [] := by
          have h := ‹(g.skins.val[s.val]).joints.len = 0#usize›
          simp only [UScalar.eq_equiv, alloc.vec.Vec.len_val, UScalar.ofNatCore_val_eq] at h
          exact List.eq_nil_of_length_eq_zero h
        rw [forallIdx_step_vec (by scalar_tac), getElem!_pos g.nodes.val i.val hlt, hnd]
        simp only [Option.some.injEq, forall_eq']
        rw [getElem!_pos g.skins.val s.val hsl]
        simp [he]
      · rw [i4_post]; exact hjs _ (List.getElem_mem _)
      all_goals
        have hj0 : 0 < (g.skins.val[s.val]).joints.val.length := by
          rcases Nat.eq_zero_or_pos ((g.skins.val[s.val]).joints.val.length) with h | h
          · exfalso; apply ‹¬(g.skins.val[s.val]).joints.len = 0#usize›; rw [UScalar.eq_equiv]; simp [h]
          · exact h
        rw [forallIdx_step_vec (by scalar_tac), getElem!_pos g.nodes.val i.val hlt, hnd]
        simp only [Option.some.injEq, forall_eq']
        rw [getElem!_pos g.skins.val s.val hsl, getElem!_pos _ 0 hj0]
        rw [i4_post] at o_post
        simp only [i5_post, usize_cast_u64_val] at o1_post
        rw [scene_cond_iff o_post o1_post] at b_post
        first
        | (rw [r_post, i6_post]
           exact ⟨fun h => ⟨⟨List.ne_nil_of_length_pos hj0, b_post.mp ‹_›⟩, h⟩, fun h => h.2⟩)
        | (simp only [Bool.false_eq_true, false_iff, not_and]
           intro h; exact absurd (b_post.mpr h.2) ‹¬ b = true›)
  · step*
    rw [forallIdx_end_vec (by scalar_tac)]
termination_by g.nodes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem skinned_nodes_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (hn : nodeRefsOk g) (hs : skinRefsOk g) :
    validate.hierarchy.skinned_nodes_ok g P ⦃ r => r = true ↔ skinnedNodesOk g ⦄ := by
  unfold validate.hierarchy.skinned_nodes_ok skinnedNodesOk
  step*
  simp only [forallIdx_zero] at r_post
  exact r_post

@[step]
theorem skins_ok_spec (g : model.Gltf) (P : alloc.vec.Vec (Option U64)) (hP : ParentArr g P)
    (hn : nodeRefsOk g) (hs : skinRefsOk g) :
    validate.hierarchy.skins_ok g P ⦃ r => r = true ↔ (∀ sk ∈ g.skins.val, skinOkB g sk) ∧ skinnedNodesOk g ⦄ := by
  unfold validate.hierarchy.skins_ok
  step*

-- H1–H4, S1, S2 (S1 の祖先関係は段数を |N| 未満に制限した形)
def graphOk (g : model.Gltf) : Prop :=
  childrenUnique g ∧ (∀ q < g.nodes.val.length, nodeOk g q ∧ ∃ rt, isRootOf g q rt) ∧ scenesOk g ∧
  (∀ sk ∈ g.skins.val, skinOkB g sk) ∧ skinnedNodesOk g

@[step]
theorem graph_ok_spec (g : model.Gltf) (hr : refsOk g) : validate.hierarchy.graph_ok g ⦃ r => r = true ↔ graphOk g ⦄ := by
  unfold validate.hierarchy.graph_ok graphOk
  obtain ⟨-, hsc, hn, -, -, -, -, -, -, hs, -⟩ := hr
  step*
  all_goals simp_all

/-! ## S1 の祖先関係: |N| 未満の段数の形と段数無制限の形は H2 の下で同値 -/

-- S1 (skeleton は各関節の祖先または自身。段数は制限しない)
-- MUST-096, MUST-097, MUST-100, MUST-101: joints の重複なし、逆バインド行列、共通の根と skeleton
def skinOk (g : model.Gltf) (sk : model.Skin) : Prop :=
  sk.joints.val ≠ [] ∧ sk.joints.val.Nodup ∧
  (∀ j ∈ sk.joints.val, ∀ rt, isRootOf g j.val rt ↔ isRootOf g (sk.joints.val[0]!).val rt) ∧
  (∀ s, sk.skeleton = some s → ∀ j ∈ sk.joints.val, ancestorOrSelf g s.val j.val) ∧
  (∀ a, sk.inverse_bind_matrices = some a →
    (g.accessors.val[a.val]!).is_matrix = true ∧ (g.accessors.val[a.val]!).components.val = 16 ∧
    isFloat32 (g.accessors.val[a.val]!) ∧ sk.joints.val.length ≤ (g.accessors.val[a.val]!).count.val)

/-- H2 の下では、祖先は |N| 未満の段数でたどり着ける -/
theorem ancestorOrSelf_bounded (g : model.Gltf) (ha : acyclic g) (j s : Nat) (hj : j < g.nodes.val.length) :
    (∃ k < g.nodes.val.length, anc g k j = some s) ↔ ancestorOrSelf g s j := by
  constructor
  · rintro ⟨k, -, hk⟩; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    obtain ⟨r, k0, hk0, hr1, hr2⟩ := ha j hj
    refine ⟨k, ?_, hk⟩
    by_contra hge
    have := anc_none_mono g (k0 + 1) k j (anc_root_none g k0 j r hr1 hr2) (by omega)
    rw [this] at hk; exact absurd hk (by simp)

theorem skinOkB_iff (g : model.Gltf) (ha : acyclic g) (sk : model.Skin) (hj : ∀ j ∈ sk.joints.val, j.val < g.nodes.val.length) :
    skinOkB g sk ↔ skinOk g sk := by
  unfold skinOkB skinOk
  have e : (∀ s, sk.skeleton = some s → ∀ j ∈ sk.joints.val, ∃ k < g.nodes.val.length, anc g k j.val = some s.val) ↔
      (∀ s, sk.skeleton = some s → ∀ j ∈ sk.joints.val, ancestorOrSelf g s.val j.val) := by
    apply forall_congr'; intro s; apply forall_congr'; intro _
    apply forall₂_congr; intro j hjm
    exact ancestorOrSelf_bounded g ha j.val s.val (hj j hjm)
  rw [e]

-- H1–H4, S1 (段数無制限の形), S2
def graphSpec (g : model.Gltf) : Prop :=
  childrenUnique g ∧ acyclic g ∧ (∀ q < g.nodes.val.length, nodeOk g q) ∧ scenesOk g ∧
  (∀ sk ∈ g.skins.val, skinOk g sk) ∧ skinnedNodesOk g

theorem graphOk_iff (g : model.Gltf) (hs : skinRefsOk g) : graphOk g ↔ graphSpec g := by
  unfold graphOk graphSpec
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have ha : acyclic g := fun q hq => (h2 q hq).2
    exact ⟨h1, ha, fun q hq => (h2 q hq).1, h3,
      fun sk hsk => (skinOkB_iff g ha sk (hs sk hsk).1).mp (h4 sk hsk), h5⟩
  · rintro ⟨h1, ha, h2, h3, h4, h5⟩
    exact ⟨h1, fun q hq => ⟨h2 q hq, ha q hq⟩, h3,
      fun sk hsk => (skinOkB_iff g ha sk (hs sk hsk).1).mpr (h4 sk hsk), h5⟩

end LoadGltf
