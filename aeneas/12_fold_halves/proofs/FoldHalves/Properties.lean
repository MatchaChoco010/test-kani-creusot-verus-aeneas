import Aeneas
import FoldHalves.Code.Funs

open Aeneas Aeneas.Std Result
open FoldHalves

@[step]
theorem fold_loop_spec {T : Type} (inst : FoldHalves.Monoid T) (f : T → T → T)
    (hop : ∀ a b, inst.op a b ⦃ r => r = f a b ⦄) (v : Slice T) (acc : T) (i : Usize)
    (h : i.val ≤ v.length) :
    fold_loop inst v acc i ⦃ r => r = List.foldl f acc (v.val.drop i.val) ⦄ := by
  unfold fold_loop
  step*
  · rw [r_post, i2_post, List.drop_eq_getElem_cons (i := i.val) (by agrind), acc1_post, t_post]
    rfl
  · rw [List.drop_of_length_le (by agrind)]
    rfl
termination_by v.length - i.val
decreasing_by scalar_decr_tac

@[step]
theorem fold_spec {T : Type} (inst : FoldHalves.Monoid T) (f : T → T → T) (e : T)
    (hop : ∀ a b, inst.op a b ⦃ r => r = f a b ⦄) (hid : inst.id ⦃ r => r = e ⦄) (v : Slice T) :
    fold inst v ⦃ r => r = List.foldl f e v.val ⦄ := by
  unfold fold
  step*
  simp_all

theorem foldl_assoc {T : Type} (f : T → T → T)
    (hassoc : ∀ a b c, f (f a b) c = f a (f b c)) (a b : T) (l : List T) :
    List.foldl f (f a b) l = f a (List.foldl f b l) := by
  induction l generalizing b <;> simp_all

theorem fold_halves_spec {T : Type} (inst : FoldHalves.Monoid T) (f : T → T → T) (e : T)
    (hop : ∀ a b, inst.op a b ⦃ r => r = f a b ⦄) (hid : inst.id ⦃ r => r = e ⦄)
    (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
    (hidr : ∀ a, f a e = a) (v : Slice T) :
    fold_halves inst v ⦃ r => r = List.foldl f e v.val ⦄ := by
  unfold fold_halves
  step*
  rw [r_post, t_post, t1_post, left_post2, left_post3, ← foldl_assoc f hassoc, hidr,
    ← List.foldl_append, List.take_append_drop]

def maxOp (a b : Max) : Max := if a ≥ b then a else b

theorem max_halves_spec (v : Slice Max) :
    max_halves v ⦃ r => r = List.foldl maxOp 0#u32 v.val ⦄ := by
  unfold max_halves
  apply fold_halves_spec _ maxOp 0#u32 _ (by simp [Max.Insts.Fold_halvesMonoid.id])
  · intro a b c
    unfold maxOp
    agrind
  · intro a
    unfold maxOp
    agrind
  · intro a b
    simp only [Max.Insts.Fold_halvesMonoid.op, maxOp]
    split <;> simp

-- 証明失敗: Diff は結合律を満たさないので、fold_halves_spec の仮定 hassoc を示せない
-- def diffOp (a b : Diff) : Diff := if a ≥ b then U32.wrapping_sub a b else U32.wrapping_sub b a
--
-- theorem diff_halves_spec (v : Slice Diff) :
--     diff_halves v ⦃ r => r = List.foldl diffOp 0#u32 v.val ⦄ := by
--   unfold diff_halves
--   apply fold_halves_spec _ diffOp 0#u32 _ (by simp [Diff.Insts.Fold_halvesMonoid.id])
--   · intro a b c
--     unfold diffOp
--     agrind
--   · intro a
--     unfold diffOp
--     agrind
--   · intro a b
--     simp only [Diff.Insts.Fold_halvesMonoid.op, diffOp]
--     split <;> step* <;> agrind
