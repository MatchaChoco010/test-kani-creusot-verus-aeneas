import Aeneas
import ParSum.Code.Funs

open Aeneas Aeneas.Std Result
open ParSum

attribute [local agrind =] U64.rMax UScalar.ofNatCore_val_eq

def sum : List U64 → Nat
  | [] => 0
  | x :: xs => x.val + sum xs

theorem sum_append (s t : List U64) : sum (s ++ t) = sum s + sum t := by
  induction s <;> agrind [sum]

theorem sum_take_succ (l : List U64) (i : Nat) (h : i < l.length) :
    sum (l.take (i + 1)) = sum (l.take i) + l[i].val := by
  rw [List.take_succ_eq_append_getElem h, sum_append]
  agrind [sum]

theorem sum_take_le (l : List U64) (i : Nat) : sum (l.take i) ≤ sum l := by
  have := sum_append (l.take i) (l.drop i)
  rw [List.take_append_drop] at this
  agrind

@[step]
theorem sum_fits_u64_loop_spec (v : Slice U64) (s : U64) (i : Usize)
    (h1 : i.val ≤ v.length) (h2 : s.val = sum (v.val.take i.val)) :
    sum_fits_u64_loop v s i ⦃ r => r = true ↔ sum v.val ≤ U64.max ⦄ := by
  unfold sum_fits_u64_loop
  step*
  · simp only [*] at o_post
    have := sum_take_le v.val (i.val + 1)
    rw [sum_take_succ _ _ (by agrind)] at this
    simp only [Bool.false_eq_true, false_iff, not_le]
    agrind
  · simp only [*] at o_post
    rw [i3_post, sum_take_succ _ _ (by agrind)]
    agrind
  · simp only [true_iff]
    agrind [List.take_of_length_le]
termination_by v.length - i.val
decreasing_by scalar_decr_tac

theorem saturating_add_val (a b : U64) :
    (core.num.U64.saturating_add a b).val = min U64.max (a.val + b.val) := by
  simp only [core.num.U64.saturating_add, UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by agrind)]
  agrind

theorem foldl_saturating_add (a : U64) (l : List U64) :
    (List.foldl core.num.U64.saturating_add a l).val = min U64.max (a.val + sum l) := by
  induction l generalizing a <;> agrind [sum, saturating_add_val]

-- 本体は検証しない。T がモノイドなら、rayon の並列の畳み込みが順の畳み込みと等しいことを信用する
axiom par_sum_spec {T : Type} (inst : ParSum.Monoid T) (f : T → T → T) (e : T)
    (hop : ∀ a b, inst.op a b ⦃ r => r = f a b ⦄) (hid : inst.id ⦃ r => r = e ⦄)
    (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
    (hidl : ∀ a, f e a = a) (hidr : ∀ a, f a e = a) (v : Slice T) :
    par_sum inst v ⦃ r => r = List.foldl f e v.val ⦄

-- 本体は検証しない。rayon::join が両クロージャを実行して結果を返すことを信用する
axiom join_spec {A B RA RB : Type} (ia : core.ops.function.FnOnce A Unit RA)
    (ib : core.ops.function.FnOnce B Unit RB) (a : A) (b : B) :
    rayon_core.join.join ia ib a b = do
      let ra ← ia.call_once a ()
      let rb ← ib.call_once b ()
      ok (ra, rb)

@[step]
theorem par_sum_u64_spec (v : Slice U64) :
    par_sum U64.Insts.Par_sumMonoid v ⦃ r => r.val = min U64.max (sum v.val) ⦄ := by
  apply WP.spec_mono (par_sum_spec _ core.num.U64.saturating_add 0#u64 ?_ ?_ ?_ ?_ ?_ v)
  · intro r hr
    rw [hr, foldl_saturating_add]
    agrind
  · intro a b
    simp [U64.Insts.Par_sumMonoid.op]
  · simp [U64.Insts.Par_sumMonoid.id]
  · intro a b c
    agrind [saturating_add_val]
  · intro a
    agrind [saturating_add_val]
  · intro a
    agrind [saturating_add_val]

theorem mean_spec (v : Slice U64) (h0 : 0 < v.length) (h1 : sum v.val ≤ U64.max) :
    mean v ⦃ r => r.val = sum v.val / v.length ⦄ := by
  unfold mean sum_fits_u64
  step*
  · simp [sum]
  · have hs : sum v.val = sum left.val + sum right.val := by
      rw [left_post2, left_post3, ← sum_append, List.take_append_drop]
    rw [join_spec]
    simp only [mean.closure.Insts.CoreOpsFunctionFnOnceTupleU64.call_once,
      mean.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64.call_once]
    step*
    all_goals
      have hlen : i4.val = v.length := by
        rw [i4_post, UScalar.cast_val_mod_pow_greater_numBits_eq]
        · agrind
        · cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
      agrind

-- 証明失敗: Diff は結合律を満たさないので、par_sum_spec の仮定 hassoc を示せない（par_sum は axiom で、使える事実は par_sum_spec だけ）
-- def diffOp (a b : Diff) : Diff := if a ≥ b then U64.wrapping_sub a b else U64.wrapping_sub b a
--
-- theorem diff_sum_ok (v : Slice Diff) : diff_sum v ⦃ _ => True ⦄ := by
--   unfold diff_sum
--   apply WP.spec_mono (par_sum_spec _ diffOp 0#u64 ?_ ?_ ?_ ?_ ?_ v)
--   · simp
--   · intro a b
--     simp only [Diff.Insts.Par_sumMonoid.op, diffOp]
--     split <;> step* <;> agrind
--   · simp [Diff.Insts.Par_sumMonoid.id]
--   · intro a b c
--     unfold diffOp
--     agrind
--   · intro a
--     unfold diffOp
--     agrind
--   · intro a
--     unfold diffOp
--     agrind
