import Aeneas
import ClampAll.Code.Funs

open Aeneas Aeneas.Std Result core.slice
open ClampAll

def clamp (hi x : U32) : U32 := if x > hi then hi else x

def BackInv (a : Slice U32) (hi : U32) (i : Nat) (back : iter.IterMut U32 → iter.IterMut U32) :
    Prop :=
  ∀ it' : iter.IterMut U32, it'.slice.length = a.length →
    (back it').slice.length = a.length ∧
    (∀ j < i, (back it').slice.val[j]! = clamp hi a.val[j]!) ∧
    (∀ j, i ≤ j → j < a.length → (back it').slice.val[j]! = it'.slice.val[j]!)

theorem BackInv.step (a : Slice U32) (hi : U32) (i : Nat) (y : U32)
    (back : iter.IterMut U32 → iter.IterMut U32) (h1 : i < a.length)
    (h2 : y = clamp hi a.val[i]!) (h3 : BackInv a hi i back) :
    BackInv a hi (i + 1) (fun it' => back { it' with slice := it'.slice.setAtNat i y }) := by
  intro it' hl
  obtain ⟨b1, b2, b3⟩ := h3 { it' with slice := it'.slice.setAtNat i y } (by agrind [Slice.setAtNat_length])
  refine ⟨b1, fun j hj => ?_, fun j hj hj' => ?_⟩
  · by_cases hji : j = i
    · agrind [Slice.getElem!_Nat_setAtNat]
    · agrind
  · agrind [Slice.getElem!_Nat_setAtNat]

@[step]
theorem clamp_all_loop_spec (a : Slice U32) (hi : U32) (it : iter.IterMut U32)
    (back : iter.IterMut U32 → iter.IterMut U32)
    (h1 : it.slice = a) (h2 : it.i ≤ a.length) (h3 : BackInv a hi it.i back) :
    clamp_all_loop it back hi ⦃ r =>
      r.slice.length = a.length ∧ ∀ j < a.length, r.slice.val[j]! = clamp hi a.val[j]! ⦄ := by
  unfold clamp_all_loop
  subst h1
  step*
  · obtain ⟨b1, b2, -⟩ := h3 iter1 (by agrind)
    agrind
  all_goals
    rename_i hx _
    subst hx
    obtain ⟨hlt, hx, hi1, hback⟩ := o_post2
    simp only [hback, hi1]
    exact BackInv.step _ _ _ _ _ hlt (by agrind [clamp]) h3
termination_by a.length - it.i
decreasing_by all_goals scalar_decr_tac

theorem clamp_all_spec (v : Slice U32) (hi : U32) :
    clamp_all v hi ⦃ r => r.length = v.length ∧ ∀ j < v.length, r.val[j]! = clamp hi v.val[j]! ⦄ := by
  unfold clamp_all core.slice.Slice.iter_mut
  step with clamp_all_loop_spec v hi
  · intro it' hl
    agrind
  · agrind
