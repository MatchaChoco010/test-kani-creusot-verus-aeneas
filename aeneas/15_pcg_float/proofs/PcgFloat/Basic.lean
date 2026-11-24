import Aeneas
import PcgFloat.Code.Funs

open Aeneas Aeneas.Std Result

namespace PcgFloat

set_option linter.unusedSimpArgs false

/-- 乗数 -/
def A : ℕ := 0x2360_ED05_1FC6_5DA4_4385_DF64_9FCC_F645

theorem MULTIPLIER_val : MULTIPLIER.val = A := by
  unfold MULTIPLIER; rfl

theorem size128 : UScalar.size UScalarTy.U128 = 2 ^ 128 := by rw [UScalar.size_def]; rfl

theorem eq_ok_of_spec {α : Type} {m : Result α} {y : α} (h : m ⦃ r => r = y ⦄) : m = ok y := by
  cases m <;> simp_all [WP.spec_ok, WP.spec_vis, WP.spec_div]

/-- XSL RR 出力関数の仕様 (コアの `rotateRight` を使う) -/
def xslRr (x : BitVec 128) : BitVec 64 :=
  ((x >>> 64).setWidth 64 ^^^ x.setWidth 64).rotateRight (x >>> 122).toNat

/-- 1 ステップ後の生成器 -/
def stepP (p : Pcg64) : Pcg64 :=
  { p with state := core.num.U128.wrapping_add (core.num.U128.wrapping_mul p.state MULTIPLIER) p.increment }

/-- 状態 `s` に対する出力 -/
def outU (s : U128) : U64 := ⟨xslRr s.bv⟩

theorem outU_bv (s : U128) : (outU s).bv = xslRr s.bv := rfl

theorem stepP_state_val (p : Pcg64) :
    (stepP p).state.val = (A * p.state.val + p.increment.val) % 2 ^ 128 := by
  simp only [stepP, core.num.U128.wrapping_add_val_eq, core.num.U128.wrapping_mul,
    UScalar.wrapping_mul_val_eq, MULTIPLIER_val]
  rw [size128, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mul_comm]

theorem stepP_increment (p : Pcg64) : (stepP p).increment = p.increment := by
  unfold stepP; rfl

theorem step_eq (p : Pcg64) : Pcg64.step p = ok (stepP p) := by
  simp only [Pcg64.step, lift, stepP, bind_ok]

theorem rotr_shift (y : BitVec 64) (r : ℕ) (hr : r < 64) :
    y >>> r ||| y <<< ((64 - r) &&& 63) = y.rotateRight r := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hr]
  rcases Nat.eq_zero_or_pos r with rfl | h
  · simp
  · have : (64 - r) &&& 63 = 64 - r := by
      rw [show (63 : ℕ) = 2 ^ 6 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [this]

theorem output_xsl_rr_spec (s : U128) : output_xsl_rr s ⦃ r => r = outU s ⦄ := by
  unfold output_xsl_rr
  have hrot : s.val >>> 122 < 64 := by
    have : s.val < 2 ^ 128 := s.hBounds
    simp only [Nat.shiftRight_eq_div_pow]
    omega
  step*
  have hr : rot.val = s.val >>> 122 := by
    rw [rot_post, UScalar.cast_val_eq, i_post, UScalarTy.U32_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have h6 : i6.val = (64 - (s.val >>> 122)) &&& 63 := by
    have : i6.val = i5.val &&& 63 := by rw [i6_post]; rfl
    rw [this, i5_post, hr]
  rw [UScalar.eq_equiv_bv_eq]
  change i4.bv ||| i7.bv = _
  simp only [i4_post1, i7_post1, h6, hr]
  rw [rotr_shift _ _ hrot]
  simp only [xsl_post1, i2_post, i3_post, UScalar.cast_bv_eq, i1_post1, outU, xslRr,
    BitVec.toNat_ushiftRight, U128.bv_toNat]
  rfl

theorem next_u64_eq (p : Pcg64) : p.next_u64 = ok (outU (stepP p).state, stepP p) := by
  simp only [Pcg64.next_u64, step_eq, bind_ok, eq_ok_of_spec (output_xsl_rr_spec _)]

/-- P1: `next_u64` は必ず成功し、状態は LCG で 1 歩進み、出力は XSL RR -/
theorem next_u64_spec (p : Pcg64) :
    p.next_u64 ⦃ r q =>
      q.state.val = (A * p.state.val + p.increment.val) % 2 ^ 128 ∧
      q.increment = p.increment ∧
      r.bv = xslRr q.state.bv ⦄ := by
  rw [next_u64_eq, WP.spec_ok]
  exact ⟨stepP_state_val p, stepP_increment p, outU_bv _⟩

/-- P1: `new` は必ず成功し、increment は奇数 -/
theorem new_spec (st sm : U128) :
    Pcg64.new st sm ⦃ p =>
      p.increment.val = (2 * sm.val + 1) % 2 ^ 128 ∧
      p.increment.val % 2 = 1 ∧
      p.state.val = (A * ((st.val + p.increment.val) % 2 ^ 128) + p.increment.val) % 2 ^ 128 ⦄ := by
  unfold Pcg64.new
  step*
  have hsz : U128.size = 2 ^ 128 := by rw [U128.size_def, U128.numBits_def]; rfl
  have hi : i.val = 2 * sm.val % 2 ^ 128 := by
    rw [i_post, hsz, Nat.shiftLeft_eq, Nat.mul_comm, pow_one]
  have hinc : increment.val = 2 * sm.val % 2 ^ 128 + 1 := by
    rw [increment_post, UScalar.val_or]
    have h1 : (1#u128).val = 1 := rfl
    have h2 : i.val = 2 ^ 1 * (i.val / 2) := by omega
    rw [h1, h2, ← Nat.two_pow_add_eq_or_of_lt (by norm_num)]
    omega
  rw [step_eq, WP.spec_ok, stepP_state_val, stepP_increment, i1_post,
    core.num.U128.wrapping_add_val_eq, size128, hinc]
  refine ⟨by omega, by omega, rfl⟩

end PcgFloat
