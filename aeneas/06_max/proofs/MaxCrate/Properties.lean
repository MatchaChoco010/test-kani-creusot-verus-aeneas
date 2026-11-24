import Aeneas
import MaxCrate.Code.Funs

open Aeneas Aeneas.Std Result
open MaxCrate

def MaxPost (v : Slice U32) (r : U32) : Prop :=
  (∀ j < v.length, v.val[j]! ≤ r) ∧ ∃ j < v.length, v.val[j]! = r

@[step]
theorem max_loop_spec (v : Slice U32) (m : U32) (i : Usize)
    (h1 : i.val ≤ v.length)
    (h2 : ∀ j < i.val, v.val[j]! ≤ m) (h3 : ∃ j < i.val, v.val[j]! = m) :
    max_loop v m i ⦃ r => MaxPost v r ⦄ := by
  unfold max_loop
  step*
  · split <;> step*
    · agrind [getElem!_pos]
    · exact ⟨i.val, by agrind, by agrind [getElem!_pos]⟩
    · agrind [getElem!_pos]
  · unfold MaxPost
    split_conjs <;> agrind
termination_by v.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem max_spec (v : Slice U32) (h : 0 < v.length) :
    MaxCrate.max v ⦃ r => MaxPost v r ⦄ := by
  unfold MaxCrate.max
  step*
  · agrind [getElem!_pos]
  · exact ⟨0, by agrind, by agrind [getElem!_pos]⟩
