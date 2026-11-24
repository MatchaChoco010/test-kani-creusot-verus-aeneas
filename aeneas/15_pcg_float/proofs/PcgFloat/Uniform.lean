import PcgFloat.Stream

open Aeneas Aeneas.Std Result

namespace PcgFloat

set_option linter.unusedSimpArgs false

/-! ## P4: 1 周期の中で各 u64 値はちょうど 2^64 回出る -/

theorem rotr_inv (y : BitVec 64) (r : ℕ) (hr : r < 64) :
    (y.rotateRight r).rotateRight ((64 - r) % 64) = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [rotr_bit _ _ _ (Nat.mod_lt _ (by norm_num)) hi, rotr_bit _ _ _ hr (Nat.mod_lt _ (by norm_num))]
  congr 1; omega

/-- 状態の値 `x` に対する出力 -/
def outN (x : ℕ) : BitVec 64 := xslRr (BitVec.ofNat 128 x)

/-- 上位 64 ビットが `h` のとき出力が `v` になる下位 64 ビット -/
def loOf (v : BitVec 64) (h : ℕ) : ℕ :=
  (BitVec.ofNat 64 h ^^^ v.rotateRight ((64 - h / 2 ^ 58) % 64)).toNat

theorem outN_iff (v : BitVec 64) (x : ℕ) (hx : x < 2 ^ 128) :
    outN x = v ↔ x % 2 ^ 64 = loOf v (x / 2 ^ 64) := by
  have hr : x / 2 ^ 122 = x / 2 ^ 64 / 2 ^ 58 := by rw [Nat.div_div_eq_div_mul, ← pow_add]
  have hr64 : x / 2 ^ 122 < 64 := by omega
  have hH : (BitVec.ofNat 128 x >>> 64).setWidth 64 = BitVec.ofNat 64 (x / 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx]
  have hL : (BitVec.ofNat 128 x).setWidth 64 = BitVec.ofNat 64 x :=
    BitVec.setWidth_ofNat_of_le (by norm_num) x
  have hrot : (BitVec.ofNat 128 x >>> 122).toNat = x / 2 ^ 122 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hx]
  unfold outN xslRr loOf
  rw [hH, hL, hrot, ← hr]
  set H := BitVec.ofNat 64 (x / 2 ^ 64)
  set r := x / 2 ^ 122
  constructor
  · intro h
    have h1 : H ^^^ BitVec.ofNat 64 x = v.rotateRight ((64 - r) % 64) := by
      rw [← h, rotr_inv _ _ hr64]
    have h2 : BitVec.ofNat 64 x = H ^^^ v.rotateRight ((64 - r) % 64) := by
      rw [← h1, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [← h2, BitVec.toNat_ofNat]
  · intro h
    have h2 : BitVec.ofNat 64 x = H ^^^ v.rotateRight ((64 - r) % 64) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, h]
    rw [h2, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have := rotr_inv v ((64 - r) % 64) (Nat.mod_lt _ (by norm_num))
    rw [show (64 - (64 - r) % 64) % 64 = r by omega] at this
    exact this

open Classical in
/-- 各値の原像は 2^64 個 -/
theorem outN_card (v : BitVec 64) :
    ((Finset.range (2 ^ 128)).filter (fun x => outN x = v)).card = 2 ^ 64 := by
  have hlo : ∀ h, loOf v h < 2 ^ 64 := fun h => BitVec.isLt _
  have : (Finset.range (2 ^ 128)).filter (fun x => outN x = v) =
      (Finset.range (2 ^ 64)).image (fun h => h * 2 ^ 64 + loOf v h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨x / 2 ^ 64, by omega, ?_⟩
      rw [← (outN_iff v x hx).mp h]; omega
    · rintro ⟨h, hh, rfl⟩
      have h1 := hlo h
      have hx : h * 2 ^ 64 + loOf v h < 2 ^ 128 := by omega
      refine ⟨hx, (outN_iff v _ hx).mpr ?_⟩
      rw [show (h * 2 ^ 64 + loOf v h) / 2 ^ 64 = h by omega]
      omega
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro h1 _ h2 _ he
  have := hlo h1
  have := hlo h2
  simp only at he
  omega

theorem outU_eq_iff (s : U128) (v : U64) : outU s = v ↔ outN s.val = v.bv := by
  have : s.bv = BitVec.ofNat 128 s.val := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, U128.bv_toNat, Nat.mod_eq_of_lt (val_lt s)]
  rw [UScalar.eq_equiv_bv_eq]
  change xslRr s.bv = v.bv ↔ _
  rw [outN, this]

/-- k ↦ k+1 回目の状態は 1 周期の中で互いに異なる -/
theorem state_injOn (p : Pcg64) (hp : p.increment.val % 2 = 1) :
    Set.InjOn (fun k => (stepP^[k + 1] p).state.val) (Finset.range (2 ^ 128) : Set ℕ) := by
  intro i hi j hj he
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hz : ((stepP^[i + 1] p).state.val : ZMod M) = ((stepP^[j + 1] p).state.val : ZMod M) := by
    simp only at he; rw [he]
  rw [iter_state, iter_state] at hz
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (lcg (p.increment.val : ZMod M))^[j - i] ((lcg (p.increment.val : ZMod M))^[i + 1] p.state.val) =
        (lcg (p.increment.val : ZMod M))^[i + 1] p.state.val := by
      rw [← Function.iterate_add_apply, show j - i + (i + 1) = j + 1 by omega, ← hz]
    exact lcg_iter_ne _ _ (inc_odd p hp) (j - i) (by omega) (by omega) this
  · have : (lcg (p.increment.val : ZMod M))^[i - j] ((lcg (p.increment.val : ZMod M))^[j + 1] p.state.val) =
        (lcg (p.increment.val : ZMod M))^[j + 1] p.state.val := by
      rw [← Function.iterate_add_apply, show i - j + (j + 1) = i + 1 by omega, hz]
    exact lcg_iter_ne _ _ (inc_odd p hp) (i - j) (by omega) (by omega) this

open Classical in
/-- P4 (一般形): 1 周期 (2^128 回) の出力で、各 u64 値はちょうど 2^64 回現れる -/
theorem output_uniform_of_odd (p : Pcg64) (hp : p.increment.val % 2 = 1) (v : U64) :
    ((Finset.range (2 ^ 128)).filter (fun k => nthOut p k = ok v)).card = 2 ^ 64 := by
  rw [← outN_card v.bv]
  have hinj := state_injOn p hp
  have hsurj : ∀ x ∈ Finset.range (2 ^ 128), ∃ k, ∃ (_ : k ∈ Finset.range (2 ^ 128)),
      x = (stepP^[k + 1] p).state.val :=
    Finset.surj_on_of_inj_on_of_card_le (fun k _ => (stepP^[k + 1] p).state.val)
      (fun k _ => Finset.mem_range.mpr (val_lt _)) (fun a b ha hb h => hinj (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) h) le_rfl
  apply Finset.card_bij (fun k _ => (stepP^[k + 1] p).state.val)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    rw [nthOut_eq, Result.ok.injEq, outU_eq_iff] at hk
    exact ⟨val_lt _, hk.2⟩
  · intro a ha b hb h
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨k, hk, rfl⟩ := hsurj x hx1
    refine ⟨k, Finset.mem_filter.mpr ⟨hk, ?_⟩, rfl⟩
    rw [nthOut_eq, Result.ok.injEq, outU_eq_iff]
    exact hx2

end PcgFloat
