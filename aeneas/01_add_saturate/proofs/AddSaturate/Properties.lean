import Aeneas
import AddSaturate.Code.Funs

open Aeneas Aeneas.Std Result
open AddSaturate

attribute [local agrind =] U32.rMax UScalar.ofNatCore_val_eq

theorem add_saturate_spec (a b : U32) :
    add_saturate a b ⦃ r =>
      (a.val + b.val ≤ U32.max → r.val = a.val + b.val) ∧
      (U32.max < a.val + b.val → r.val = U32.max) ⦄ := by
  unfold add_saturate
  step*
