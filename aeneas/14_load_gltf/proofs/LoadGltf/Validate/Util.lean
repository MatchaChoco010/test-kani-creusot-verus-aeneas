import LoadGltf.Model

open Aeneas Aeneas.Std Result

namespace LoadGltf

-- opt_lt(o, n)
def optLt (o : Option U64) (n : Nat) : Prop := ∀ v, o = some v → v.val < n

@[step]
theorem opt_less_spec (o : Option U64) (n : Usize) : validate.util.opt_less o n ⦃ r => r = true ↔ optLt o n.val ⦄ := by
  unfold validate.util.opt_less optLt
  step_auto

@[step]
theorem opt_less_u64_spec (o : Option U64) (n : U64) :
    validate.util.opt_less_u64 o n ⦃ r => r = true ↔ optLt o n.val ⦄ := by
  unfold validate.util.opt_less_u64 optLt
  step_auto

@[step]
theorem all_less_loop_spec (v : alloc.vec.Vec U64) (n : Usize) (i : Usize) (hi : i.val ≤ v.val.length) :
    validate.util.all_less_loop v n i ⦃ r => r = true ↔
      forallFrom v.val i.val (fun x => (x).val < n.val) ⦄ := by
  unfold validate.util.all_less_loop
  loop_auto
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem all_less_spec (v : alloc.vec.Vec U64) (n : Usize) :
    validate.util.all_less v n ⦃ r => r = true ↔ ∀ x ∈ v.val, (x).val < n.val ⦄ := by
  unfold validate.util.all_less
  step*
  simp_all [forallFrom_zero]

-- バイト列の集合としての包含
def bytesSubset (a b : List (alloc.vec.Vec U8)) : Prop := ∀ x ∈ a, x.val ∈ b.map (·.val)

theorem nodup_iff_forallFrom {α} (l : List α) :
    l.Nodup ↔ ∀ p (h : p < l.length), forallFrom l (p + 1) (fun y => y ≠ l[p]) := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  constructor
  · intro h p hp q hq hq'; exact fun e => h p q hp hq' (by omega) e.symm
  · intro h i j hi hj hij e; exact h i hi j hij hj e.symm

@[step]
theorem string_not_in_rest_loop_spec (v : alloc.vec.Vec (alloc.vec.Vec U8)) (i j : Usize)
    (hi0 : i.val < v.val.length) (hi : j.val ≤ v.val.length) :
    validate.util.string_not_in_rest_loop v i j ⦃ r => r = true ↔
      forallFrom v.val j.val (fun y => y.val ≠ (v.val[i.val]).val) ⦄ := by
  unfold validate.util.string_not_in_rest_loop
  loop_auto [eq_comm]
termination_by v.val.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem string_not_in_rest_spec (v : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize)
    (hi0 : i.val < v.val.length) :
    validate.util.string_not_in_rest v i ⦃ r => r = true ↔
      forallFrom v.val (i.val + 1) (fun y => y.val ≠ (v.val[i.val]).val) ⦄ := by
  unfold validate.util.string_not_in_rest
  step_auto

@[step]
theorem strings_unique_loop_spec (v : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize) (hi : i.val ≤ v.val.length) :
    validate.util.strings_unique_loop v i ⦃ r => r = true ↔ forallIdx v.val.length i.val
      (fun p => ∀ h : p < v.val.length, forallFrom v.val (p + 1) (fun y => y.val ≠ (v.val[p]).val)) ⦄ := by
  unfold validate.util.strings_unique_loop
  loop_auto
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem map_val_nodup (v : List (alloc.vec.Vec U8)) :
    (v.map (·.val)).Nodup ↔ ∀ p (h : p < v.length), forallFrom v (p + 1) (fun y => y.val ≠ (v[p]).val) := by
  rw [nodup_iff_forallFrom]
  simp only [List.length_map, forallFrom, List.getElem_map]

@[step]
theorem strings_unique_spec (v : alloc.vec.Vec (alloc.vec.Vec U8)) :
    validate.util.strings_unique v ⦃ r => r = true ↔ (v.val.map (·.val)).Nodup ⦄ := by
  unfold validate.util.strings_unique
  step*
  simp_all [forallIdx_zero, map_val_nodup]

@[step]
theorem strings_contains_loop_spec (v : alloc.vec.Vec (alloc.vec.Vec U8)) (s : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ v.val.length) :
    validate.util.strings_contains_loop v s i ⦃ r => r = false ↔ forallFrom v.val i.val (fun y => y.val ≠ s.val) ⦄ := by
  unfold validate.util.strings_contains_loop
  loop_auto
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem strings_contains_spec (v : alloc.vec.Vec (alloc.vec.Vec U8)) (s : alloc.vec.Vec U8) :
    validate.util.strings_contains v s ⦃ r => r = true ↔ s.val ∈ v.val.map (·.val) ⦄ := by
  unfold validate.util.strings_contains
  step*
  rw [← Bool.not_eq_false, r_post, forallFrom_zero]
  simp [eq_comm]

@[step]
theorem strings_subset_loop_spec (a b : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize) (hi : i.val ≤ a.val.length) :
    validate.util.strings_subset_loop a b i ⦃ r => r = true ↔
      forallFrom a.val i.val (fun x => (x).val ∈ b.val.map (·.val)) ⦄ := by
  unfold validate.util.strings_subset_loop
  loop_auto
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem strings_subset_spec (a b : alloc.vec.Vec (alloc.vec.Vec U8)) :
    validate.util.strings_subset a b ⦃ r => r = true ↔ bytesSubset a.val b.val ⦄ := by
  unfold validate.util.strings_subset bytesSubset
  step*
  simp_all [forallFrom_zero]

def isFloat32 (a : model.Accessor) : Prop := a.component_type.val = 5126

def isUnorm816 (a : model.Accessor) : Prop :=
  a.normalized = true ∧ (a.component_type.val = 5121 ∨ a.component_type.val = 5123)

def isSnorm816 (a : model.Accessor) : Prop :=
  a.normalized = true ∧ (a.component_type.val = 5120 ∨ a.component_type.val = 5122)

@[step]
theorem float32_spec (a : model.Accessor) : validate.util.float32 a ⦃ r => r = true ↔ isFloat32 a ⦄ := by
  unfold validate.util.float32 isFloat32; step*

@[step]
theorem unorm8_16_spec (a : model.Accessor) : validate.util.unorm8_16 a ⦃ r => r = true ↔ isUnorm816 a ⦄ := by
  unfold validate.util.unorm8_16 isUnorm816; step_auto

@[step]
theorem snorm8_16_spec (a : model.Accessor) : validate.util.snorm8_16 a ⦃ r => r = true ↔ isSnorm816 a ⦄ := by
  unfold validate.util.snorm8_16 isSnorm816; step_auto

@[step]
theorem not_in_rest_loop_spec (v : alloc.vec.Vec U64) (i j : Usize) (hi0 : i.val < v.val.length)
    (hj : j.val ≤ v.val.length) :
    validate.util.not_in_rest_loop v i j ⦃ r => r = true ↔ forallFrom v.val j.val (fun y => y ≠ v.val[i.val]) ⦄ := by
  unfold validate.util.not_in_rest_loop
  loop_auto [eq_comm]
termination_by v.val.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem unique_loop_spec (v : alloc.vec.Vec U64) (i : Usize) (hi : i.val ≤ v.val.length) :
    validate.util.unique_loop v i ⦃ r => r = true ↔ forallIdx v.val.length i.val
      (fun p => ∀ h : p < v.val.length, forallFrom v.val (p + 1) (fun y => y ≠ v.val[p])) ⦄ := by
  unfold validate.util.unique_loop validate.util.not_in_rest
  loop_auto
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem unique_spec (v : alloc.vec.Vec U64) : validate.util.unique v ⦃ r => r = true ↔ v.val.Nodup ⦄ := by
  unfold validate.util.unique
  step*
  simp_all [forallIdx_zero, nodup_iff_forallFrom]

@[step]
theorem contains_loop_spec (v : alloc.vec.Vec U64) (x : U64) (i : Usize) (hi : i.val ≤ v.val.length) :
    validate.util.contains_loop v x i ⦃ r => r = false ↔ forallFrom v.val i.val (fun y => y ≠ x) ⦄ := by
  unfold validate.util.contains_loop
  loop_auto
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem contains_spec (v : alloc.vec.Vec U64) (x : U64) : validate.util.contains v x ⦃ r => r = true ↔ x ∈ v.val ⦄ := by
  unfold validate.util.contains
  step*
  rw [← Bool.not_eq_false, r_post, forallFrom_zero]
  simp only [ne_eq, not_forall, Decidable.not_not, exists_prop, exists_eq_right]

end LoadGltf
