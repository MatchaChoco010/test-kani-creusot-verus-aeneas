import PcgFloat.Period

open Aeneas Aeneas.Std Result

namespace PcgFloat

set_option linter.unusedSimpArgs false

/-- `next_u64` を n 回呼んだ後の生成器 -/
def run : ℕ → Pcg64 → Result Pcg64
  | 0, p => ok p
  | n + 1, p => do
    let r ← p.next_u64
    run n r.2

/-- k 回呼んだ後の次の `next_u64` の出力 `o_k` -/
def nthOut (p : Pcg64) (k : ℕ) : Result U64 := do
  let q ← run k p
  let r ← q.next_u64
  ok r.1

theorem run_succ (n : ℕ) (p : Pcg64) : run (n + 1) p = run n (stepP p) := by
  simp only [run, next_u64_eq, bind_ok]

theorem run_eq (n : ℕ) (p : Pcg64) : run n p = ok (stepP^[n] p) := by
  induction n generalizing p with
  | zero => simp only [run, Function.iterate_zero, id]
  | succ n ih => rw [run_succ, ih, Function.iterate_succ_apply]

theorem nthOut_eq (p : Pcg64) (k : ℕ) : nthOut p k = ok (outU (stepP^[k + 1] p).state) := by
  simp only [nthOut, run_eq, next_u64_eq, bind_ok, Function.iterate_succ_apply']

theorem iter_increment (n : ℕ) (p : Pcg64) : (stepP^[n] p).increment = p.increment := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', stepP_increment, ih]

/-- 状態の列は ZMod 上の LCG の反復 -/
theorem iter_state (n : ℕ) (p : Pcg64) :
    ((stepP^[n] p).state.val : ZMod M) = (lcg (p.increment.val : ZMod M))^[n] (p.state.val : ZMod M) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', stepP_state_val, ZMod.natCast_mod,
      Nat.cast_add, Nat.cast_mul, ih, iter_increment]
    rfl

theorem val_lt (x : U128) : x.val < 2 ^ 128 := x.hBounds

theorem pcg_eq_iff (p q : Pcg64) (h : p.increment = q.increment) :
    p = q ↔ (p.state.val : ZMod M) = (q.state.val : ZMod M) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (val_lt _), Nat.mod_eq_of_lt (val_lt _),
    ← UScalar.eq_equiv]
  cases p; cases q
  simp_all

theorem inc_odd (p : Pcg64) (hp : p.increment.val % 2 = 1) :
    ((p.increment.val : ℕ) : ZMod M).val % 2 = 1 := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (val_lt _), hp]

/-- P2 (一般形): increment が奇数なら状態の周期はちょうど 2^128 -/
theorem state_period_of_odd (p : Pcg64) (hp : p.increment.val % 2 = 1) :
    run (2 ^ 128) p = ok p ∧ ∀ n, 0 < n → n < 2 ^ 128 → run n p ≠ ok p := by
  refine ⟨?_, fun n h0 h1 h => ?_⟩
  · rw [run_eq, (pcg_eq_iff _ _ (iter_increment _ _)).mpr]
    rw [iter_state, lcg_iter_full]
  · rw [run_eq] at h
    have h' := (pcg_eq_iff _ _ (iter_increment _ _)).mp (Result.ok_injective h)
    rw [iter_state] at h'
    exact lcg_iter_ne _ _ (inc_odd p hp) n h0 h1 h'

/-! ## 出力の周期 -/

theorem rotr_bit (y : BitVec 64) (r i : ℕ) (hr : r < 64) (hi : i < 64) :
    (y.rotateRight r).getLsbD i = y.getLsbD ((i + r) % 64) := by
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr]
  split_ifs with h
  · congr 1; omega
  · simp only [hi, decide_true, Bool.true_and]
    congr 1; omega

theorem xslRr_bit (x : BitVec 128) (i : ℕ) (hi : i < 64) :
    (xslRr x).getLsbD i =
      (x.getLsbD (64 + (i + x.toNat / 2 ^ 122) % 64) ^^ x.getLsbD ((i + x.toNat / 2 ^ 122) % 64)) := by
  have hr : x.toNat / 2 ^ 122 < 64 := by have := x.isLt; omega
  unfold xslRr
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, rotr_bit _ _ _ hr hi]
  have hj : (i + x.toNat / 2 ^ 122) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  simp [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, Nat.add_comm, Nat.mod_lt]

/-- 最上位ビットを反転した状態 (= +2^127) では出力が必ず変わる -/
theorem outU_flip (x y : U128) (hy : y.val = (x.val + 2 ^ 127) % 2 ^ 128) : outU y ≠ outU x := by
  intro h
  have hx := val_lt x
  have hb : ∀ j, j < 128 → y.bv.getLsbD j = if j = 127 then !x.bv.getLsbD j else x.bv.getLsbD j := by
    intro j hj
    rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, U128.bv_toNat, U128.bv_toNat, hy, Nat.add_comm,
      Nat.testBit_mod_two_pow]
    simp only [hj, decide_true, Bool.true_and]
    split_ifs with h127
    · subst h127; exact Nat.testBit_two_pow_add_eq _ _
    · exact Nat.testBit_two_pow_add_gt (by omega) _
  have hr' : y.val / 2 ^ 122 = (x.val / 2 ^ 122 + 32) % 64 := by omega
  have hbv : ∀ i, i < 64 → (xslRr y.bv).getLsbD i = (xslRr x.bv).getLsbD i := by
    intro i hi
    have := congrArg (fun u : U64 => u.bv.getLsbD i) h
    simpa only [outU] using this
  set r := x.val / 2 ^ 122 with hr
  have hr64 : r < 64 := by omega
  have e1 := hbv ((127 - r) % 64) (Nat.mod_lt _ (by norm_num))
  have e2 := hbv ((95 - r) % 64) (Nat.mod_lt _ (by norm_num))
  rw [xslRr_bit _ _ (Nat.mod_lt _ (by norm_num)), xslRr_bit _ _ (Nat.mod_lt _ (by norm_num)),
    U128.bv_toNat, U128.bv_toNat, hr', ← hr] at e1 e2
  rw [show ((127 - r) % 64 + (r + 32) % 64) % 64 = 31 by omega,
    show ((127 - r) % 64 + r) % 64 = 63 by omega] at e1
  rw [show ((95 - r) % 64 + (r + 32) % 64) % 64 = 63 by omega,
    show ((95 - r) % 64 + r) % 64 = 31 by omega] at e2
  rw [hb _ (by norm_num), hb _ (by norm_num)] at e1 e2
  simp only [show (64 + 31 : ℕ) = 95 by rfl, show (64 + 63 : ℕ) = 127 by rfl] at e1 e2
  simp at e1 e2
  rw [e1] at e2
  simp at e2

/-- 周期の最大公約数をとる論法: 2^128 周期で、2^128 未満の周期 n があれば 2^127 も周期 -/
theorem period_half {α : Type} (f : ℕ → α) (hP : ∀ k, f (k + 2 ^ 128) = f k) (n : ℕ) (h0 : 0 < n)
    (h1 : n < 2 ^ 128) (hn : ∀ k, f (k + n) = f k) : ∀ k, f (k + 2 ^ 127) = f k := by
  have mul : ∀ d, (∀ k, f (k + d) = f k) → ∀ m k, f (k + m * d) = f k := by
    intro d hd m
    induction m with
    | zero => simp
    | succ m ih => intro k; rw [Nat.succ_mul, ← Nat.add_assoc, hd, ih]
  set g := Nat.gcd n (2 ^ 128) with hg
  have hgn : g ≤ n := Nat.le_of_dvd h0 (Nat.gcd_dvd_left _ _)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd (k := 2 ^ 128) (n := n) (by omega)
  have hgp : ∀ k, f (k + g) = f k := by
    intro k
    have hdm := Nat.div_add_mod (n * m) (2 ^ 128)
    rw [hm] at hdm
    rw [← mul (2 ^ 128) hP (n * m / 2 ^ 128) (k + g)]
    have : k + g + n * m / 2 ^ 128 * 2 ^ 128 = k + m * n := by rw [Nat.mul_comm m n]; omega
    rw [this, mul n hn]
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_right n (2 ^ 128))
  have hi' : i ≤ 127 := by
    by_contra hc
    have : i = 128 := by omega
    rw [← hg, this] at hgi
    omega
  intro k
  have : 2 ^ 127 = 2 ^ (127 - i) * g := by rw [hg, hgi, ← pow_add]; congr 1; omega
  rw [this, mul g hgp]

theorem iter_full_pcg (p : Pcg64) (k : ℕ) : stepP^[k + 2 ^ 128] p = stepP^[k] p := by
  rw [pcg_eq_iff _ _ (by rw [iter_increment, iter_increment]), iter_state, iter_state,
    Function.iterate_add_apply, lcg_iter_full]

theorem iter_half_val (p : Pcg64) (hp : p.increment.val % 2 = 1) (k : ℕ) :
    (stepP^[k + 2 ^ 127] p).state.val = ((stepP^[k] p).state.val + 2 ^ 127) % 2 ^ 128 := by
  have hz := iter_state (2 ^ 127) (stepP^[k] p)
  rw [lcg_iter_half _ _ (inc_odd _ (by rw [iter_increment]; exact hp)), ← Function.iterate_add_apply,
    Nat.add_comm] at hz
  have h2 : ((stepP^[k] p).state.val : ZMod M) + 2 ^ 127 =
      (((stepP^[k] p).state.val + 2 ^ 127 : ℕ) : ZMod M) := by push_cast; rfl
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (hz.trans h2)
  rwa [Nat.mod_eq_of_lt (val_lt _)] at this

/-- P3 (一般形): increment が奇数なら出力列の周期はちょうど 2^128 -/
theorem output_period_of_odd (p : Pcg64) (hp : p.increment.val % 2 = 1) :
    (∀ k, nthOut p (k + 2 ^ 128) = nthOut p k) ∧
    ∀ n, 0 < n → n < 2 ^ 128 → ∃ k, nthOut p (k + n) ≠ nthOut p k := by
  have hP : ∀ k, nthOut p (k + 2 ^ 128) = nthOut p k := by
    intro k
    rw [nthOut_eq, nthOut_eq, show k + 2 ^ 128 + 1 = (k + 1) + 2 ^ 128 by omega, iter_full_pcg]
  refine ⟨hP, fun n h0 h1 => ?_⟩
  by_contra hc
  have hc' : ∀ k, nthOut p (k + n) = nthOut p k := fun k => by
    by_contra h; exact hc ⟨k, h⟩
  have h2 := period_half (nthOut p) hP n h0 h1 hc' 0
  rw [nthOut_eq, nthOut_eq] at h2
  refine outU_flip _ _ ?_ (Result.ok_injective h2)
  rw [show 0 + 2 ^ 127 + 1 = 1 + 2 ^ 127 by omega]
  exact iter_half_val p hp 1

end PcgFloat
