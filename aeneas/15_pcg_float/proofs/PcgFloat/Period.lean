import PcgFloat.Basic

open Aeneas Aeneas.Std Result

namespace PcgFloat

set_option linter.unusedSimpArgs false

abbrev M : ℕ := 2 ^ 128

/-- 状態遷移 `f(s) = A·s + c (mod 2^128)` -/
def lcg (c : ZMod M) (s : ZMod M) : ZMod M := A * s + c

/-- `S_n = 1 + A + … + A^(n-1)` -/
def geom (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, A ^ i

theorem geom_succ (n : ℕ) : geom (n + 1) = A * geom n + 1 := by
  simp only [geom, Finset.sum_range_succ', pow_succ, Finset.mul_sum, pow_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem geom_add (n m : ℕ) : geom (n + m) = geom n + A ^ n * geom m := by
  simp only [geom, Finset.sum_range_add, pow_add, Finset.mul_sum]

/-- `f^[n](s) = s + S_n·((A-1)s + c)` -/
theorem lcg_iterate (c s : ZMod M) (n : ℕ) :
    (lcg c)^[n] s = s + (geom n : ZMod M) * ((A - 1) * s + c) := by
  induction n generalizing s with
  | zero => simp [geom]
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, geom_succ]
    simp only [lcg]
    push_cast
    ring

theorem A_mod_four : A % 4 = 1 := by norm_num [A]

/-- `v₂(S_{2^j}) = j` -/
theorem geom_two_pow (j : ℕ) : ∃ o, geom (2 ^ j) = 2 ^ j * (2 * o + 1) := by
  induction j with
  | zero => exact ⟨0, by simp [geom]⟩
  | succ j ih =>
    obtain ⟨o, ho⟩ := ih
    have hA : A ^ 2 ^ j % 4 = 1 := by rw [Nat.pow_mod, A_mod_four, one_pow]; rfl
    obtain ⟨q, hq⟩ : ∃ q, A ^ 2 ^ j = 4 * q + 1 := ⟨A ^ 2 ^ j / 4, by omega⟩
    refine ⟨2 * o * q + o + q, ?_⟩
    rw [pow_succ, mul_two, geom_add, ho, hq]
    ring

theorem zmod_two_pow_odd (w : ℕ) : ((2 ^ 127 * (2 * w + 1) : ℕ) : ZMod M) = 2 ^ 127 := by
  have : (2 ^ 127 * (2 * w + 1) : ℕ) = 2 ^ 127 + M * w := by ring
  rw [this, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  push_cast; rfl

/-- `f^[2^128] = id` -/
theorem lcg_iter_full (c s : ZMod M) : (lcg c)^[2 ^ 128] s = s := by
  obtain ⟨o, ho⟩ := geom_two_pow 128
  rw [lcg_iterate, ho, Nat.cast_mul, ZMod.natCast_self]
  ring

/-- `c` が奇数なら `f^[2^127](s) = s + 2^127` -/
theorem lcg_iter_half (c s : ZMod M) (hc : c.val % 2 = 1) :
    (lcg c)^[2 ^ 127] s = s + 2 ^ 127 := by
  obtain ⟨o, ho⟩ := geom_two_pow 127
  obtain ⟨w, hw⟩ : ∃ w, (A - 1) * s.val + c.val = 2 * w + 1 := by
    have : A % 2 = 1 := by norm_num [A]
    obtain ⟨k, hk⟩ : ∃ k, A = 2 * k + 1 := ⟨A / 2, by omega⟩
    refine ⟨k * s.val + c.val / 2, ?_⟩
    rw [hk, Nat.add_sub_cancel, mul_assoc]; omega
  have hu : ((A - 1) * s + c : ZMod M) = ((2 * w + 1 : ℕ) : ZMod M) := by
    rw [← hw]
    have : 1 ≤ A := by norm_num [A]
    push_cast [this]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [lcg_iterate, ho, hu, ← Nat.cast_mul, mul_assoc,
    show (2 * o + 1) * (2 * w + 1) = 2 * (2 * o * w + o + w) + 1 by ring, zmod_two_pow_odd]

theorem two_pow_127_ne_zero : (2 ^ 127 : ZMod M) ≠ 0 := by
  have : ((2 ^ 127 : ℕ) : ZMod M) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.pow_dvd_pow_iff_le_right (by norm_num) |>.not.mpr (by norm_num)
  exact_mod_cast this

/-- 状態の最小周期は 2^128 -/
theorem lcg_minimalPeriod (c s : ZMod M) (hc : c.val % 2 = 1) :
    Function.minimalPeriod (lcg c) s = 2 ^ 128 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Function.minimalPeriod_eq_prime_pow (k := 127)
  · intro h
    have h' : (lcg c)^[2 ^ 127] s = s := h
    rw [lcg_iter_half c s hc] at h'
    exact two_pow_127_ne_zero (by simpa using h')
  · exact lcg_iter_full c s

theorem lcg_iter_ne (c s : ZMod M) (hc : c.val % 2 = 1) (n : ℕ) (h0 : 0 < n) (h1 : n < 2 ^ 128) :
    (lcg c)^[n] s ≠ s := by
  intro h
  have := (Function.isPeriodicPt_iff_minimalPeriod_dvd).mp (h : Function.IsPeriodicPt (lcg c) n s)
  rw [lcg_minimalPeriod c s hc] at this
  exact absurd (Nat.le_of_dvd h0 this) (by omega)

end PcgFloat
