import Aeneas
import CountEq.Code.Funs

open Aeneas Aeneas.Std Result
open CountEq

def count (x : U32) : List U32 → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + count x ys

theorem count_append (x y : U32) (l : List U32) :
    count x (l ++ [y]) = count x l + (if y = x then 1 else 0) := by
  induction l <;> agrind [count]

@[step]
theorem count_eq_loop_spec (v : Slice U32) (x : U32) (c i : Usize)
    (h1 : i.val ≤ v.length) (h2 : c.val ≤ i.val) (h3 : c.val = count x (v.val.take i.val)) :
    count_eq_loop v x c i ⦃ r => r.val = count x v.val ⦄ := by
  unfold count_eq_loop
  step*
  · split <;> step* <;> agrind [count_append, List.take_succ_eq_append_getElem]
  · agrind [List.take_of_length_le]
termination_by v.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem count_eq_spec (v : Slice U32) (x : U32) :
    count_eq v x ⦃ r => r.val = count x v.val ⦄ := by
  unfold count_eq
  step*
  agrind [count, List.take_zero]
