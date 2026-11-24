import Aeneas
import GetOr.Code.Funs

open Aeneas Aeneas.Std Result
open GetOr

theorem get_or_spec {T : Type} (inst : core.marker.Copy T) (v : Slice T)
    (i : Usize) (default : T) :
    get_or inst v i default ⦃ r => r = (v.val[i.val]?).getD default ⦄ := by
  unfold get_or
  step*
  · rw [List.getElem?_eq_getElem (by agrind)]
    simp_all
  · simp_all
