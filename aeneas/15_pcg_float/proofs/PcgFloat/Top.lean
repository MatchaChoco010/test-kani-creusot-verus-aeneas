import PcgFloat.Uniform

open Aeneas Aeneas.Std Result

namespace PcgFloat

/-- `new` の後に何回 `next_u64` を呼んでも increment は奇数のまま -/
theorem reachable_odd (st sm : U128) (m : ℕ) (p0 p : Pcg64)
    (h0 : Pcg64.new st sm = ok p0) (hm : run m p0 = ok p) : p.increment.val % 2 = 1 := by
  have h := new_spec st sm
  rw [h0, WP.spec_ok] at h
  rw [run_eq, Result.ok.injEq] at hm
  rw [← hm, iter_increment]
  exact h.2.1

/-- P2: `new` で作り `next_u64` を何回か呼んだ生成器の状態は、ちょうど 2^128 回の呼び出しで元に戻る -/
theorem state_period (st sm : U128) (m : ℕ) (p0 p : Pcg64)
    (h0 : Pcg64.new st sm = ok p0) (hm : run m p0 = ok p) :
    run (2 ^ 128) p = ok p ∧ ∀ n, 0 < n → n < 2 ^ 128 → run n p ≠ ok p :=
  state_period_of_odd p (reachable_odd st sm m p0 p h0 hm)

/-- P3: 出力列 `o_k` の周期はちょうど 2^128 -/
theorem output_period (st sm : U128) (m : ℕ) (p0 p : Pcg64)
    (h0 : Pcg64.new st sm = ok p0) (hm : run m p0 = ok p) :
    (∀ k, nthOut p (k + 2 ^ 128) = nthOut p k) ∧
    ∀ n, 0 < n → n < 2 ^ 128 → ∃ k, nthOut p (k + n) ≠ nthOut p k :=
  output_period_of_odd p (reachable_odd st sm m p0 p h0 hm)

open Classical in
/-- P4: 1 周期の出力で各 u64 値はちょうど 2^64 回現れる -/
theorem output_uniform (st sm : U128) (m : ℕ) (p0 p : Pcg64)
    (h0 : Pcg64.new st sm = ok p0) (hm : run m p0 = ok p) (v : U64) :
    ((Finset.range (2 ^ 128)).filter (fun k => nthOut p k = ok v)).card = 2 ^ 64 :=
  output_uniform_of_odd p (reachable_odd st sm m p0 p h0 hm) v

end PcgFloat
