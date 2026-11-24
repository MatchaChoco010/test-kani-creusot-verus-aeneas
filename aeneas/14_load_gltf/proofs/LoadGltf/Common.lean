import Aeneas
import LoadGltf.Code.Funs

open Aeneas Aeneas.Std Result

namespace LoadGltf

set_option linter.unusedSimpArgs false


theorem usize_cast_u64_val (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]

theorem u64_cast_usize_val (x : U64) (h : x.val ≤ Usize.max) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by simp [Usize.max, Usize.numBits]
  have : 0 < 2 ^ UScalarTy.Usize.numBits := by positivity
  omega

theorem usize_max_le_u64 : Usize.max ≤ U64.max := by
  have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits, U64.max_eq]

theorem u32_max_le_usize : U32.max ≤ Usize.max := by
  have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits, U32.max_eq]

theorem saturating_add_val (a b : U64) :
    (core.num.U64.saturating_add a b).val = min U64.max (a.val + b.val) := by
  simp only [core.num.U64.saturating_add, UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · simp
  · simp only [UScalar.max]; have : 0 < 2 ^ UScalarTy.U64.numBits := by positivity
    omega

attribute [agrind =] U64.rMax UScalar.ofNatCore_val_eq U8.cast_U64_val_eq U8.cast_U32_val_eq
  U8.cast_Usize_val_eq U32.cast_U64_val_eq U32.cast_Usize_val_eq usize_cast_u64_val saturating_add_val
  alloc.vec.Vec.len_val Slice.len_val

-- ループの不変条件: 添字 i 以降の要素がすべて P を満たす
def forallFrom {α} (l : List α) (i : Nat) (P : α → Prop) : Prop :=
  ∀ q, i ≤ q → ∀ h : q < l.length, P l[q]

theorem forallFrom_step {α} {l : List α} {P : α → Prop} {i : Nat} (hi : i < l.length) :
    forallFrom l i P ↔ P l[i] ∧ forallFrom l (i + 1) P := by
  unfold forallFrom
  constructor
  · intro h; exact ⟨h i (Nat.le_refl _) hi, fun q hq h' => h q (by omega) h'⟩
  · rintro ⟨h1, h2⟩ q hq h'
    rcases Nat.eq_or_lt_of_le hq with rfl | hq
    · exact h1
    · exact h2 q hq h'

theorem forallFrom_end {α} {l : List α} {P : α → Prop} {i : Nat} (hi : l.length ≤ i) :
    forallFrom l i P ↔ True := by
  simp only [forallFrom, iff_true]; intro q hq h; omega

theorem forallFrom_step_vec {α} {v : alloc.vec.Vec α} {P : α → Prop} {i : Usize} (hi : i < v.len) :
    forallFrom v.val i.val P ↔ P (v.val[i.val]'(by scalar_tac)) ∧ forallFrom v.val (i.val + 1) P :=
  forallFrom_step _

theorem forallFrom_end_vec {α} {v : alloc.vec.Vec α} {P : α → Prop} {i : Usize} (hi : ¬ i < v.len) :
    forallFrom v.val i.val P ↔ True :=
  forallFrom_end (by scalar_tac)

theorem forallFrom_zero {α} (l : List α) (P : α → Prop) : forallFrom l 0 P ↔ ∀ x ∈ l, P x := by
  simp [forallFrom, List.forall_mem_iff_getElem]

@[simp, agrind =]
theorem vec_deref_val {α} (v : alloc.vec.Vec α) : (alloc.vec.Vec.deref v).val = v.val := by
  simp [alloc.vec.Vec.deref]

@[simp, agrind =]
theorem array_make_to_slice_val {α} (n : Usize) (l : List α) (h : l.length = n.val) :
    (Array.make n l h).to_slice.val = l := by
  simp [Array.to_slice]

-- usize への変換で値が変わらない (Vec の長さ未満の値)
theorem mod_numBits_of_lt {α} {x : Nat} {v : List α} (h : x < v.length) (hv : v.length ≤ Usize.max) :
    x % 2 ^ System.Platform.numBits = x := by
  apply Nat.mod_eq_of_lt
  have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by simp [Usize.max, Usize.numBits]
  simp only [UScalarTy.numBits] at this
  have : 0 < 2 ^ System.Platform.numBits := by positivity
  omega

theorem getElem_idx_eq {α} {l : List α} {i j : Nat} (h : i = j) (hi : i < l.length) (hj : j < l.length) :
    l[i] = l[j] := by subst h; rfl

-- 添字版: i 以降 n 未満のすべての添字 q で P q
def forallIdx (n i : Nat) (P : Nat → Prop) : Prop := ∀ q, i ≤ q → q < n → P q

theorem forallIdx_step_vec {α} {v : alloc.vec.Vec α} {P : Nat → Prop} {i : Usize} (hi : i < v.len) :
    forallIdx v.val.length i.val P ↔ P i.val ∧ forallIdx v.val.length (i.val + 1) P := by
  have : i.val < v.val.length := by scalar_tac
  unfold forallIdx
  constructor
  · intro h; exact ⟨h _ (Nat.le_refl _) this, fun q hq h' => h q (by omega) h'⟩
  · rintro ⟨h1, h2⟩ q hq h'
    rcases Nat.eq_or_lt_of_le hq with rfl | hq
    · exact h1
    · exact h2 q hq h'

theorem forallIdx_end_vec {α} {v : alloc.vec.Vec α} {P : Nat → Prop} {i : Usize} (hi : ¬ i < v.len) :
    forallIdx v.val.length i.val P ↔ True := by
  have : v.val.length ≤ i.val := by scalar_tac
  simp only [forallIdx, iff_true]; intro q hq h; omega

theorem forallIdx_step_slice {α} {v : Slice α} {P : Nat → Prop} {i : Usize} (hi : i < v.len) :
    forallIdx v.val.length i.val P ↔ P i.val ∧ forallIdx v.val.length (i.val + 1) P := by
  have : i.val < v.val.length := by scalar_tac
  unfold forallIdx
  constructor
  · intro h; exact ⟨h _ (Nat.le_refl _) this, fun q hq h' => h q (by omega) h'⟩
  · rintro ⟨h1, h2⟩ q hq h'
    rcases Nat.eq_or_lt_of_le hq with rfl | hq
    · exact h1
    · exact h2 q hq h'

theorem forallIdx_end_slice {α} {v : Slice α} {P : Nat → Prop} {i : Usize} (hi : ¬ i < v.len) :
    forallIdx v.val.length i.val P ↔ True := by
  have : v.val.length ≤ i.val := by scalar_tac
  simp only [forallIdx, iff_true]; intro q hq h; omega

theorem forallFrom_step_slice {α} {v : Slice α} {P : α → Prop} {i : Usize} (hi : i < v.len) :
    forallFrom v.val i.val P ↔ P (v.val[i.val]'(by scalar_tac)) ∧ forallFrom v.val (i.val + 1) P :=
  forallFrom_step _

theorem forallFrom_end_slice {α} {v : Slice α} {P : α → Prop} {i : Usize} (hi : ¬ i < v.len) :
    forallFrom v.val i.val P ↔ True :=
  forallFrom_end (by scalar_tac)

theorem forallIdx_zero (n : Nat) (P : Nat → Prop) : forallIdx n 0 P ↔ ∀ q < n, P q := by
  simp [forallIdx]

-- step* の後に残ったゴールを閉じる
macro "step_auto" : tactic => `(tactic| (step* <;> try agrind))

macro "loop_auto" : tactic => `(tactic| (step* <;> simp_all [forallFrom_step_vec, forallFrom_end_vec, forallIdx_step_vec, forallIdx_end_vec, forallFrom_step_slice, forallFrom_end_slice, forallIdx_step_slice, forallIdx_end_slice] <;> agrind))

macro "loop_auto" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (step* <;> simp_all [forallFrom_step_vec, forallFrom_end_vec, forallIdx_step_vec, forallIdx_end_vec, forallFrom_step_slice, forallFrom_end_slice, forallIdx_step_slice, forallIdx_end_slice, $ls,*] <;> agrind))

theorem true_eq_iff (b : Bool) : (true = b) ↔ b = true := eq_comm

theorem false_eq_iff (b : Bool) : (false = b) ↔ b = false := eq_comm

theorem usize_ge_iff (a b : Usize) : a ≥ b ↔ b.val ≤ a.val := Iff.rfl

theorem u8_ge_iff (a b : U8) : a ≥ b ↔ b.val ≤ a.val := Iff.rfl

theorem slice_length_eq {α} (s : Slice α) : s.length = s.val.length := rfl

theorem slice_len_val_eq {α} (s : Slice α) : (Slice.len s).val = s.val.length := Slice.len_val s

theorem usize_lt_len {α} {k : Usize} {v : alloc.vec.Vec α} (h : k < v.len) : k.val < v.val.length := by
  simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val] at h; exact h

end LoadGltf
