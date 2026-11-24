import Aeneas
import AddCrate.Code.Funs

open Aeneas Aeneas.Std Result
open AddCrate

attribute [local agrind =] U32.rMax UScalar.ofNatCore_val_eq

@[step]
theorem add_spec (a b : U32) (h : a.val + b.val ≤ U32.max) :
    add a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold add
  step*

-- 証明失敗: a に制約が無いので add の事前条件 a + a ≤ U32.max を示せない
-- theorem double_spec (a : U32) :
--     double a ⦃ _ => True ⦄ := by
--   unfold double
--   step*

theorem double_checked_spec (a : U32) :
    double_checked a ⦃ r => match r with
      | some c => a.val ≤ U32.max / 2 ∧ c.val = 2 * a.val
      | none => U32.max / 2 < a.val ⦄ := by
  unfold double_checked
  step*
