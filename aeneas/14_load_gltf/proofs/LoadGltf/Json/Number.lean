import LoadGltf.Common

open Aeneas Aeneas.Std Result

namespace LoadGltf

set_option linter.unusedSimpArgs false


/-! ## N. JSON の数の整数値 -/

-- 数字列の十進の値 val
def digitsVal (l : List Nat) : Nat := l.foldl (fun a d => 10 * a + d) 0

theorem foldl_digits (acc : Nat) (l : List Nat) :
    l.foldl (fun a d => 10 * a + d) acc = acc * 10 ^ l.length + digitsVal l := by
  induction l generalizing acc with
  | nil => simp [digitsVal]
  | cons x xs ih =>
    simp only [List.foldl_cons, digitsVal, List.length_cons] at *
    rw [ih, ih (10 * 0 + x)]
    ring

theorem digitsVal_append (a b : List Nat) :
    digitsVal (a ++ b) = digitsVal a * 10 ^ b.length + digitsVal b := by
  rw [digitsVal, List.foldl_append, foldl_digits]
  rfl

theorem digitsVal_concat (a : List Nat) (x : Nat) :
    digitsVal (a ++ [x]) = 10 * digitsVal a + x := by
  rw [digitsVal_append]; simp [digitsVal]; ring

theorem digitsVal_take_succ (l : List Nat) (k : Nat) (h : k < l.length) :
    digitsVal (l.take (k + 1)) = 10 * digitsVal (l.take k) + l[k] := by
  rw [List.take_succ_eq_append_getElem h, digitsVal_concat]

theorem digitsVal_lt (l : List Nat) (h : ∀ d ∈ l, d ≤ 9) : digitsVal l < 10 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [digitsVal]
  | append_singleton a x ih =>
    rw [digitsVal_concat]
    have h1 := ih (fun d hd => h d (by simp [hd]))
    have h2 := h x (by simp)
    simp only [List.length_append, List.length_singleton, pow_succ]
    omega

theorem digitsVal_eq_zero (l : List Nat) : digitsVal l = 0 ↔ ∀ d ∈ l, d = 0 := by
  induction l using List.reverseRecOn with
  | nil => simp [digitsVal]
  | append_singleton a x ih =>
    rw [digitsVal_concat]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro h d hd
      rcases hd with hd | hd
      · exact ih.mp (by omega) d hd
      · omega
    · intro h
      have := ih.mpr (fun d hd => h d (Or.inl hd))
      have := h x (Or.inr rfl)
      omega

theorem digitsVal_le_append (a b : List Nat) : digitsVal a ≤ digitsVal (a ++ b) := by
  rw [digitsVal_append]
  have : 1 ≤ 10 ^ b.length := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

theorem digitsVal_take_mono (l : List Nat) (a b : Nat) (h : a ≤ b) :
    digitsVal (l.take a) ≤ digitsVal (l.take b) := by
  have h2 : (l.take b).take a = l.take a := by rw [List.take_take, min_eq_left h]
  have h3 := List.take_append_drop a (l.take b)
  rw [h2] at h3
  rw [← h3]
  exact digitsVal_le_append _ _

theorem forall_drop_iff {α} (l : List α) (k : Nat) (h : k < l.length) (P : α → Prop) :
    (∀ x ∈ l.drop k, P x) ↔ P l[k] ∧ ∀ x ∈ l.drop (k + 1), P x := by
  rw [List.drop_eq_getElem_cons h, List.forall_mem_cons]

-- I ++ F の数字の値の列
def json.number.Number.digits (n : json.number.Number) : List Nat := (n.int_digits.val ++ n.frac_digits.val).map (·.val)

-- val(E)
def json.number.Number.expVal (n : json.number.Number) : Nat := digitsVal (n.exp_digits.val.map (·.val))

-- Number(neg, I, F, eneg, E) が表す有理数 q = (-1)^neg · val(I ++ F) · 10^(e − |F|)
def json.number.Number.q (n : json.number.Number) : ℚ :=
  let e : ℤ := if n.exp_negative then -(n.expVal : ℤ) else (n.expVal : ℤ)
  (-1 : ℚ) ^ n.negative.toNat * (digitsVal n.digits : ℚ) *
    (10 : ℚ) ^ (e - (n.frac_digits.val.length : ℤ))

-- Number の表現不変条件（parse_number が作る値はこれを満たす）: 数字は 0..9、桁数の合計が usize に収まる
def json.number.Number.wf (n : json.number.Number) : Prop :=
  (∀ d ∈ n.int_digits.val ++ n.frac_digits.val ++ n.exp_digits.val, d.val ≤ 9) ∧
  n.int_digits.val.length + n.frac_digits.val.length + n.exp_digits.val.length ≤ Usize.max

theorem json.number.Number.digits_length (n : json.number.Number) :
    n.digits.length = n.int_digits.val.length + n.frac_digits.val.length := by
  simp [json.number.Number.digits]

theorem forall_drop_iff_getD (l : List Nat) (k : Nat) :
    (∀ d ∈ l.drop k, d = 0) ↔ ∀ j, k ≤ j → j < l.length → l.getD j 0 = 0 := by
  constructor
  · intro h j hj1 hj2
    rw [List.getD_eq_getElem _ _ hj2]
    apply h
    rw [List.mem_iff_getElem]
    exact ⟨j - k, by simp; omega, by simp; congr 1; omega⟩
  · intro h d hd
    rw [List.mem_iff_getElem] at hd
    obtain ⟨i, hi, rfl⟩ := hd
    have := h (k + i) (by omega) (by simp at hi; omega)
    rw [List.getD_eq_getElem _ _ (by simp at hi; omega)] at this
    simpa using this

@[step]
theorem digit_at_spec (n : json.number.Number) (k : Usize)
    (h : k.val < n.int_digits.val.length + n.frac_digits.val.length) :
    json.number.digit_at n k ⦃ d => d.val = n.digits.getD k.val 0 ⦄ := by
  unfold json.number.digit_at
  have hk : k.val < n.digits.length := by rw [json.number.Number.digits_length]; exact h
  step* <;> rw [List.getD_eq_getElem _ _ hk] <;>
    simp only [json.number.Number.digits, List.getElem_map, List.getElem_append] <;> split <;> agrind

-- all_digits_zero と digits_zero_from のループ: k 以降の数字がすべて 0
@[step]
theorem all_digits_zero_loop_spec (b : Bool) (v v1 : alloc.vec.Vec U8) (b1 : Bool)
    (v2 : alloc.vec.Vec U8) (total k : Usize)
    (ht : total.val = v.val.length + v1.val.length) (hk : k.val ≤ total.val) :
    json.number.all_digits_zero_loop b v v1 b1 v2 total k ⦃ r => r = true ↔
      ∀ j, k.val ≤ j → j < total.val → (json.number.Number.mk b v v1 b1 v2).digits.getD j 0 = 0 ⦄ := by
  unfold json.number.all_digits_zero_loop
  step*
termination_by total.val - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem digits_zero_from_loop_spec (b : Bool) (v v1 : alloc.vec.Vec U8) (b1 : Bool)
    (v2 : alloc.vec.Vec U8) (total k : Usize)
    (ht : total.val = v.val.length + v1.val.length) (hk : k.val ≤ total.val) :
    json.number.digits_zero_from_loop b v v1 b1 v2 total k ⦃ r => r = true ↔
      ∀ j, k.val ≤ j → j < total.val → (json.number.Number.mk b v v1 b1 v2).digits.getD j 0 = 0 ⦄ := by
  unfold json.number.digits_zero_from_loop
  step*
termination_by total.val - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem all_digits_zero_spec (n : json.number.Number) (hn : n.wf) :
    json.number.all_digits_zero n ⦃ r => r = true ↔ digitsVal n.digits = 0 ⦄ := by
  unfold json.number.all_digits_zero
  obtain ⟨_, _⟩ := hn
  step*
  rw [digitsVal_eq_zero, ← List.drop_zero (l := n.digits), forall_drop_iff_getD, json.number.Number.digits_length]
  simp_all

@[step]
theorem digits_zero_from_spec (n : json.number.Number) (k : Usize) (hn : n.wf)
    (hk : k.val ≤ n.int_digits.val.length + n.frac_digits.val.length) :
    json.number.digits_zero_from n k ⦃ r => r = true ↔ ∀ d ∈ n.digits.drop k.val, d = 0 ⦄ := by
  unfold json.number.digits_zero_from
  obtain ⟨_, _⟩ := hn
  step*
  rw [forall_drop_iff_getD, json.number.Number.digits_length]
  simp_all

@[step]
theorem exponent_value_loop_spec (n : json.number.Number) (e : U64) (k : Usize)
    (hk : k.val ≤ n.exp_digits.val.length)
    (he : e.val = min U64.max (digitsVal ((n.exp_digits.val.map (·.val)).take k.val))) :
    json.number.exponent_value_loop n e k ⦃ r => r.val = min U64.max n.expVal ⦄ := by
  unfold json.number.exponent_value_loop
  step*
  · have hd := digitsVal_take_succ (n.exp_digits.val.map (·.val)) k.val (by simp; agrind)
    simp only [List.getElem_map] at hd
    split
    · step*
    · step*
      split <;> step*
  · simp only [json.number.Number.expVal]
    rw [List.take_of_length_le (by simp; agrind)] at he
    exact he
termination_by n.exp_digits.val.length - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem digits_value_loop_spec (n : json.number.Number) (keep : Usize) (v : U64) (k : Usize)
    (hkeep : keep.val ≤ n.int_digits.val.length + n.frac_digits.val.length) (hk : k.val ≤ keep.val)
    (hv : v.val = digitsVal (n.digits.take k.val)) :
    json.number.digits_value_loop n keep v k ⦃ r => match r with
      | some x => x.val = digitsVal (n.digits.take keep.val)
      | none => U64.max < digitsVal (n.digits.take keep.val) ⦄ := by
  unfold json.number.digits_value_loop
  have hl := json.number.Number.digits_length n
  step*
  all_goals
    have hd := digitsVal_take_succ n.digits k.val (by agrind)
    have hm := digitsVal_take_mono n.digits (k.val + 1) keep.val (by agrind)
    have hg : n.digits.getD k.val 0 = n.digits[k.val]'(by agrind) := List.getD_eq_getElem _ _ _
    agrind
termination_by keep.val - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mul_pow10_loop_spec (shift r s : U64) (hs : s.val ≤ shift.val) :
    json.number.mul_pow10_loop shift r s ⦃ o => match o with
      | some x => x.val = r.val * 10 ^ (shift.val - s.val)
      | none => U64.max < r.val * 10 ^ (shift.val - s.val) ⦄ := by
  unfold json.number.mul_pow10_loop
  step*
  · have : 10 ^ 1 ≤ 10 ^ (shift.val - s.val) := Nat.pow_le_pow_right (by norm_num) (by agrind)
    subst_vars
    simp only at o_post
    have := Nat.mul_le_mul_left r.val this
    agrind
  · have : 10 ^ (shift.val - s.val) = 10 ^ (shift.val - s1.val) * 10 := by
      rw [← pow_succ]; congr 1; agrind
    have ht : t.val = r.val * 10 := by agrind
    have key : r.val * 10 ^ (shift.val - s.val) = t.val * 10 ^ (shift.val - s1.val) := by
      rw [this, ht]; ring
    rw [key]
    exact o_post
termination_by shift.val - s.val
decreasing_by all_goals scalar_decr_tac

/-! 有理数 q についての補題 -/

theorem q_of_pos_exp (n : json.number.Number) (hneg : n.negative = false) (heneg : n.exp_negative = false)
    (hf : n.frac_digits.val.length ≤ n.expVal) :
    n.q = ((digitsVal n.digits * 10 ^ (n.expVal - n.frac_digits.val.length) : Nat) : ℚ) := by
  simp only [json.number.Number.q, hneg, heneg, Bool.toNat_false, pow_zero, one_mul, Bool.false_eq_true,
    ↓reduceIte]
  have : (n.expVal : ℤ) - (n.frac_digits.val.length : ℤ) =
      ((n.expVal - n.frac_digits.val.length : Nat) : ℤ) := by omega
  rw [this, zpow_natCast]
  push_cast
  ring

theorem q_of_drop (n : json.number.Number) (hneg : n.negative = false) (d : Nat)
    (hd : (if n.exp_negative then -(n.expVal : ℤ) else (n.expVal : ℤ)) -
      (n.frac_digits.val.length : ℤ) = -(d : ℤ)) :
    n.q = (digitsVal n.digits : ℚ) / (10 : ℚ) ^ d := by
  simp only [json.number.Number.q, hneg, Bool.toNat_false, pow_zero, one_mul]
  rw [hd, zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem q_eq_nat_iff_drop (D : List Nat) (hD : ∀ x ∈ D, x ≤ 9) (d : Nat) (hd : d < D.length)
    (x : Nat) :
    (digitsVal D : ℚ) / (10 : ℚ) ^ d = (x : ℚ) ↔
      (∀ y ∈ D.drop (D.length - d), y = 0) ∧ x = digitsVal (D.take (D.length - d)) := by
  have hsplit := digitsVal_append (D.take (D.length - d)) (D.drop (D.length - d))
  rw [List.take_append_drop] at hsplit
  have hlen : (D.drop (D.length - d)).length = d := by simp; omega
  rw [hlen] at hsplit
  have hlt := digitsVal_lt (D.drop (D.length - d)) (fun y hy => hD y (List.mem_of_mem_drop hy))
  rw [hlen] at hlt
  rw [← digitsVal_eq_zero]
  have hp : (0 : ℚ) < (10 : ℚ) ^ d := by positivity
  rw [div_eq_iff (ne_of_gt hp)]
  have : ((x : ℚ) * (10 : ℚ) ^ d) = ((x * 10 ^ d : Nat) : ℚ) := by push_cast; ring
  rw [this, Nat.cast_inj, hsplit]
  constructor
  · intro h
    have h1 := congrArg (· / 10 ^ d) h
    have h2 := congrArg (· % 10 ^ d) h
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
      Nat.mul_div_cancel _ (by positivity)] at h1
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt, Nat.mul_mod_left] at h2
    omega
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    ring

theorem q_ne_nat_of_drop_ge (D : List Nat) (hD : ∀ x ∈ D, x ≤ 9) (d : Nat) (hd : D.length ≤ d)
    (hpos : digitsVal D ≠ 0) (x : Nat) :
    (digitsVal D : ℚ) / (10 : ℚ) ^ d ≠ (x : ℚ) := by
  have hlt := digitsVal_lt D hD
  have : 10 ^ D.length ≤ 10 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have hp : (0 : ℚ) < (10 : ℚ) ^ d := by positivity
  rw [ne_eq, div_eq_iff (ne_of_gt hp)]
  have : ((x : ℚ) * (10 : ℚ) ^ d) = ((x * 10 ^ d : Nat) : ℚ) := by push_cast; ring
  rw [this, Nat.cast_inj]
  intro h
  rcases Nat.eq_zero_or_pos x with hx | hx
  · simp_all
  · have : 10 ^ d ≤ x * 10 ^ d := Nat.le_mul_of_pos_left _ hx
    omega

theorem q_neg (n : json.number.Number) (hneg : n.negative = true) (hpos : digitsVal n.digits ≠ 0) (x : Nat) :
    n.q ≠ (x : ℚ) := by
  simp only [json.number.Number.q, hneg, Bool.toNat_true, pow_one]
  have h1 : (0 : ℚ) < (digitsVal n.digits : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hpos
  have h2 : (0 : ℚ) < (10 : ℚ) ^ ((if n.exp_negative then -(n.expVal : ℤ) else (n.expVal : ℤ)) -
      (n.frac_digits.val.length : ℤ)) := zpow_pos (by norm_num) _
  have h3 : (0 : ℚ) ≤ (x : ℚ) := by positivity
  intro h
  have := mul_pos h1 h2
  nlinarith

theorem q_zero (n : json.number.Number) (h : digitsVal n.digits = 0) : n.q = 0 := by
  simp [json.number.Number.q, h]

-- 小数点を左に動かす桁数（eneg ∨ E < |F| の場合）
def json.number.Number.dropTrue (n : json.number.Number) : Nat :=
  if n.exp_negative then n.expVal + n.frac_digits.val.length else n.frac_digits.val.length - n.expVal

theorem q_drop_eq (n : json.number.Number) (hneg : n.negative = false)
    (h : n.exp_negative = true ∨ n.expVal ≤ n.frac_digits.val.length) :
    n.q = (digitsVal n.digits : ℚ) / (10 : ℚ) ^ n.dropTrue := by
  apply q_of_drop n hneg
  simp only [json.number.Number.dropTrue]
  split <;> simp_all; omega

theorem q_drop_none (n : json.number.Number) (hD : ∀ x ∈ n.digits, x ≤ 9) (hneg : n.negative = false)
    (h : n.exp_negative = true ∨ n.expVal ≤ n.frac_digits.val.length)
    (hV : digitsVal n.digits ≠ 0) (hT : n.digits.length ≤ n.dropTrue) (x : Nat) : n.q ≠ (x : ℚ) := by
  rw [q_drop_eq n hneg h]
  exact q_ne_nat_of_drop_ge _ hD _ hT hV x

theorem q_drop_iff (n : json.number.Number) (hD : ∀ x ∈ n.digits, x ≤ 9) (hneg : n.negative = false)
    (h : n.exp_negative = true ∨ n.expVal ≤ n.frac_digits.val.length)
    (hT : n.dropTrue < n.digits.length) (x : Nat) :
    n.q = (x : ℚ) ↔ (∀ y ∈ n.digits.drop (n.digits.length - n.dropTrue), y = 0) ∧
      x = digitsVal (n.digits.take (n.digits.length - n.dropTrue)) := by
  rw [q_drop_eq n hneg h]
  exact q_eq_nat_iff_drop _ hD _ hT x

-- 指数が u64::MAX を超えるなら指数部は 20 桁以上あり、|F| + 20 ≤ u64::MAX
theorem frac_room (n : json.number.Number) (hn : n.wf) (hE : U64.max < n.expVal) :
    n.frac_digits.val.length + 20 ≤ U64.max := by
  obtain ⟨hdig, htot⟩ := hn
  have hlt := digitsVal_lt (n.exp_digits.val.map (·.val)) (by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hdig d (by simp [hd]))
  simp only [List.length_map] at hlt
  have h1 : 10 ^ 19 < 10 ^ n.exp_digits.val.length := by
    simp only [json.number.Number.expVal] at hE
    have : (10 : Nat) ^ 19 ≤ U64.max := by simp [U64.max_eq]
    omega
  have h2 : 19 < n.exp_digits.val.length := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have := usize_max_le_u64
  omega

theorem big_pow (V k : Nat) (hV : V ≠ 0) (hk : 20 ≤ k) : U64.max < V * 10 ^ k := by
  have : 10 ^ 20 ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have : U64.max < 10 ^ 20 := by simp [U64.max_eq]
  have : 10 ^ k ≤ V * 10 ^ k := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hV)
  omega

theorem opt_iff_of_match (r : Option U64) (N1 N2 : Nat)
    (hr : match r with | some x => x.val = N1 | none => U64.max < N1)
    (h : N1 = N2 ∨ (U64.max < N1 ∧ U64.max < N2)) (v : U64) : r = some v ↔ v.val = N2 := by
  have hv : v.val ≤ U64.max := by agrind
  rcases r with _ | x <;> simp only at hr
  · simp only [reduceCtorEq, false_iff]; omega
  · simp only [Option.some.injEq, UScalar.eq_equiv]; omega

-- 負の指数の経路: 飽和した e + |F| が桁数未満なら飽和していない
theorem drop_eneg (n : json.number.Number) (e f drop : U64) (T : Nat) (hT : T ≤ Usize.max)
    (he : e.val = min U64.max n.expVal) (hf : f.val = n.frac_digits.val.length) (hd : drop.val = T)
    (h : ¬ core.num.U64.saturating_add e f ≥ drop) (heneg : n.exp_negative = true) :
    (UScalar.cast .Usize (core.num.U64.saturating_add e f)).val = n.dropTrue ∧ n.dropTrue < T := by
  have hu := usize_max_le_u64
  have hs := saturating_add_val e f
  have : (core.num.U64.saturating_add e f).val < drop.val := by
    simp only [ge_iff_le, UScalar.le_equiv, not_le] at h; exact h
  rw [u64_cast_usize_val _ (by omega)]
  simp only [json.number.Number.dropTrue, heneg, ↓reduceIte]
  omega

-- 正の指数で e < |F| の経路
theorem drop_pos (n : json.number.Number) (e f drop i3 : U64) (T : Nat)
    (he : e.val = min U64.max n.expVal) (hf : f.val = n.frac_digits.val.length) (hfm : f.val ≤ U64.max)
    (hge : ¬ e ≥ f) (hdrop : drop.val = f.val - e.val) (hi3 : i3.val = T) (hd : ¬ drop ≥ i3)
    (hT : T ≤ Usize.max) (heneg : ¬ n.exp_negative = true) :
    (UScalar.cast .Usize drop).val = n.dropTrue ∧ n.dropTrue < T ∧
      n.expVal ≤ n.frac_digits.val.length := by
  simp only [ge_iff_le, UScalar.le_equiv, not_le] at hge hd
  rw [u64_cast_usize_val _ (by have := usize_max_le_u64; omega)]
  simp only [json.number.Number.dropTrue, Bool.not_eq_true] at heneg ⊢
  simp only [heneg, Bool.false_eq_true, ↓reduceIte]
  omega

-- 正の指数で e ≥ |F| の経路
theorem pos_path (n : json.number.Number) (hn : n.wf) (hneg : n.negative = false) (heneg : n.exp_negative = false)
    (hV : digitsVal n.digits ≠ 0) (e f i3 : U64)
    (he : e.val = min U64.max n.expVal) (hf : f.val = n.frac_digits.val.length) (hge : f.val ≤ e.val)
    (hi3 : i3.val = e.val - f.val) (r : Option U64)
    (hr : match r with
      | some x => x.val = digitsVal n.digits * 10 ^ (i3.val - 0)
      | none => U64.max < digitsVal n.digits * 10 ^ (i3.val - 0)) (v : U64) :
    r = some v ↔ n.q = (v.val : ℚ) := by
  rw [q_of_pos_exp n hneg heneg (by omega), Nat.cast_inj, opt_iff_of_match r _ _ hr ?_ v]
  · exact eq_comm
  · simp only [Nat.sub_zero, hi3, he, hf]
    by_cases hE : n.expVal ≤ U64.max
    · left; rw [min_eq_right hE]
    · right
      have := frac_room n hn (by omega)
      constructor <;> apply big_pow _ _ hV <;> omega

theorem pos_none (n : json.number.Number) (hneg : n.negative = false) (heneg : n.exp_negative = false)
    (hf : n.frac_digits.val.length ≤ n.expVal) (hV : U64.max < digitsVal n.digits) (v : U64) :
    n.q ≠ (v.val : ℚ) := by
  rw [q_of_pos_exp n hneg heneg hf, ne_eq, Nat.cast_inj]
  have : digitsVal n.digits ≤ digitsVal n.digits * 10 ^ (n.expVal - n.frac_digits.val.length) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have : v.val ≤ U64.max := by agrind
  omega

-- MUST-006, MUST-013: 整数のプロパティは小数部が 0 で、添字は 0 以上
/-- N1: number_to_u64(n) = Some(v) ⇔ q が 0 以上 u64::MAX 以下の整数で v = q -/
@[step]
theorem number_to_u64_spec (n : json.number.Number) (hn : n.wf) :
    json.number.number_to_u64 n ⦃ r => ∀ v : U64, r = some v ↔ n.q = (v.val : ℚ) ⦄ := by
  unfold json.number.number_to_u64
  have hl := json.number.Number.digits_length n
  have hwf : n.wf := hn
  have hwf' : (∀ d ∈ n.int_digits.val ++ n.frac_digits.val, d.val ≤ 9) ∧
      n.int_digits.val.length + n.frac_digits.val.length ≤ Usize.max := by
    obtain ⟨h1, h2⟩ := hn
    exact ⟨fun d hd => h1 d (List.mem_append_left _ hd), by omega⟩
  obtain ⟨hdig, htot⟩ := hwf'
  have hD : ∀ x ∈ n.digits, x ≤ 9 := by
    intro x hx
    simp only [json.number.Number.digits, List.mem_map] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact hdig d hd
  have hfl : n.frac_digits.val.length ≤ U64.max := by
    have := usize_max_le_u64; omega
  have hTl : n.digits.length ≤ U64.max := by
    have := usize_max_le_u64; omega
  have hroom := frac_room n hwf
  have hq0 := q_zero n
  have hqn := q_neg n
  have hqp := q_of_pos_exp n
  have hqd := q_of_drop n
  have hdn := q_drop_none n hD
  have hdi := q_drop_iff n hD
  have hdt : n.dropTrue = if n.exp_negative then n.expVal + n.frac_digits.val.length
      else n.frac_digits.val.length - n.expVal := rfl
  step*
  · -- 全桁 0
    intro v
    rw [hq0 (by agrind)]
    simp only [Option.some.injEq, UScalar.eq_equiv]
    simp only [UScalar.ofNatCore_val_eq]
    norm_cast
  · simp [digitsVal]
  · subst_vars; rw [u64_cast_usize_val _ (by agrind)]; agrind
  · simp [digitsVal]
  · -- G1
    have hfv : f.val = n.frac_digits.val.length := by rw [f_post, usize_cast_u64_val]; rfl
    obtain ⟨hi4, hlt⟩ := drop_eneg n e f drop n.digits.length (by agrind) e_post hfv
      (by rw [drop_post, usize_cast_u64_val]; agrind) ‹_› ‹_›
    have hk : keep.val = n.digits.length - n.dropTrue := by
      rw [keep_post, i4_post, hi4]; agrind
    rw [hdi (by agrind) (by agrind) hlt v.val, ← hk, and_iff_right (b1_post.mp ‹b1 = true›)]
    exact opt_iff_of_match r _ _ r_post (Or.inl rfl) v
  · -- G2
    have hfv : f.val = n.frac_digits.val.length := by rw [f_post, usize_cast_u64_val]; rfl
    obtain ⟨hi4, hlt⟩ := drop_eneg n e f drop n.digits.length (by agrind) e_post hfv
      (by rw [drop_post, usize_cast_u64_val]; agrind) ‹_› ‹_›
    have hk : keep.val = n.digits.length - n.dropTrue := by
      rw [keep_post, i4_post, hi4]; agrind
    intro v
    simp only [reduceCtorEq, false_iff]
    rw [hdi (by agrind) (by agrind) hlt v.val, ← hk, ← b1_post]
    simp_all
  · simp [digitsVal]
  · -- o = none
    intro v
    simp only [reduceCtorEq, false_iff]
    subst_vars
    simp only at o_post
    rw [List.take_of_length_le (by agrind)] at o_post
    exact pos_none n (by agrind) (by agrind) (by agrind) o_post v
  · -- G3
    have hfv : f.val = n.frac_digits.val.length := by rw [f_post, usize_cast_u64_val]; rfl
    have hw := ‹o = some _›
    rw [hw] at o_post
    simp only at o_post
    rw [List.take_of_length_le (by agrind)] at o_post
    rw [o_post] at r_post
    exact pos_path n hwf (by agrind) (by agrind) (by agrind) e f i3 e_post hfv (by agrind)
      i3_post r r_post v
  · subst_vars; rw [u64_cast_usize_val _ (by agrind)]; agrind
  · simp [digitsVal]
  · -- G4
    have hfv : f.val = n.frac_digits.val.length := by rw [f_post, usize_cast_u64_val]; rfl
    obtain ⟨hi4, hlt, hEF⟩ := drop_pos n e f drop i3 n.digits.length e_post hfv (by agrind)
      ‹_› drop_post (by rw [i3_post, usize_cast_u64_val]; agrind) ‹_› (by agrind) ‹_›
    have hk : keep.val = n.digits.length - n.dropTrue := by
      rw [keep_post, i4_post, hi4]; agrind
    rw [hdi (by agrind) (Or.inr hEF) hlt v.val, ← hk, and_iff_right (b1_post.mp ‹b1 = true›)]
    exact opt_iff_of_match r _ _ r_post (Or.inl rfl) v
  · -- G5
    have hfv : f.val = n.frac_digits.val.length := by rw [f_post, usize_cast_u64_val]; rfl
    obtain ⟨hi4, hlt, hEF⟩ := drop_pos n e f drop i3 n.digits.length e_post hfv (by agrind)
      ‹_› drop_post (by rw [i3_post, usize_cast_u64_val]; agrind) ‹_› (by agrind) ‹_›
    have hk : keep.val = n.digits.length - n.dropTrue := by
      rw [keep_post, i4_post, hi4]; agrind
    intro v
    simp only [reduceCtorEq, false_iff]
    rw [hdi (by agrind) (Or.inr hEF) hlt v.val, ← hk, ← b1_post]
    simp_all

/-! ## J.2 文法 (RFC 8259 §2–§7) -/

-- s[i] の値 (範囲外は none)
def byteAt (s : List U8) (i : Nat) : Option Nat := s[i]?.map (·.val)

def isDigit (b : Nat) : Bool := 0x30 ≤ b && b ≤ 0x39

-- 最長の数字列 [0-9]* (数字の値の列, 終了位置)
def digitsAt (s : List U8) (i : Nat) : List Nat × Nat :=
  if h : i < s.length then
    if isDigit s[i].val then
      let r := digitsAt s (i + 1)
      ((s[i].val - 0x30) :: r.1, r.2)
    else ([], i)
  else ([], i)
termination_by s.length - i

-- (neg, int_digits, frac_digits, exp_neg, exp_digits)
abbrev NumParts := Bool × List Nat × List Nat × Bool × List Nat

-- 整数部 0 | [1-9][0-9]*
def intPart (s : List U8) (j : Nat) : Option (List Nat × Nat) :=
  match byteAt s j with
  | none => none
  | some c => if isDigit c then (if c = 0x30 then some ([0], j + 1) else some (digitsAt s j)) else none

-- 小数部 (. [0-9]+)?
def fracPart (s : List U8) (j : Nat) : Option (List Nat × Nat) :=
  if byteAt s j = some 0x2E then
    if (digitsAt s (j + 1)).1 = [] then none else some (digitsAt s (j + 1))
  else some ([], j)

-- 指数部 ([eE] [+-]? [0-9]+)?
def expPart (s : List U8) (j : Nat) : Option (Bool × List Nat × Nat) :=
  if byteAt s j = some 0x65 ∨ byteAt s j = some 0x45 then
    let j3 := if byteAt s (j + 1) = some 0x2B ∨ byteAt s (j + 1) = some 0x2D then j + 2 else j + 1
    if (digitsAt s j3).1 = [] then none
    else some (decide (byteAt s (j + 1) = some 0x2D), (digitsAt s j3).1, (digitsAt s j3).2)
  else some (false, [], j)

-- number(s, i): -? int frac? exp?
-- RFC 8259 §6: 数値の構文
def numAt (s : List U8) (i : Nat) : Option (NumParts × Nat) :=
  let neg := decide (byteAt s i = some 0x2D)
  (intPart s (if neg then i + 1 else i)).bind fun ip =>
    (fracPart s ip.2).bind fun fp =>
      (expPart s fp.2).map fun ep => ((neg, ip.1, fp.1, ep.1, ep.2.1), ep.2.2)

theorem byteAt_some' {s : List U8} {i b : Nat} (h : byteAt s i = some b) : i < s.length := by
  unfold byteAt at h
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h; cases h

def json.number.Number.toParts (n : json.number.Number) : NumParts :=
  (n.negative, n.int_digits.val.map (·.val), n.frac_digits.val.map (·.val), n.exp_negative,
    n.exp_digits.val.map (·.val))

theorem byteAt_ge {s : List U8} {i : Nat} (h : s.length ≤ i) : byteAt s i = none := by
  simp [byteAt, h]

theorem byteAt_some {s : List U8} {i b : Nat} (h : byteAt s i = some b) : i < s.length := by
  by_contra hc; rw [byteAt_ge (by omega)] at h; cases h

@[step]
theorem is_digit_spec (b : U8) : json.number.is_digit b ⦃ r => r = isDigit b.val ⦄ := by
  unfold json.number.is_digit isDigit
  step*

-- 範囲外は 0 とした s[k] の値
def byteD (s : List U8) (k : Nat) : Nat := (byteAt s k).getD 0

theorem getElem_val_eq_byteD {s : List U8} {k : Nat} (h : k < s.length) : (s[k]'h).val = byteD s k := by
  simp [byteD, byteAt, h]

theorem byteAt_eq_byteD {s : List U8} {k : Nat} (h : k < s.length) : byteAt s k = some (byteD s k) := by
  simp [byteD, byteAt, h]

theorem lit_eq_byteD (n : Nat) (s : List U8) (k : Nat) : (n = byteD s k) ↔ (byteD s k = n) := eq_comm

-- s[k] を byteD で表す index_usize の仕様 (step* に局所仮定として渡す)
theorem index_u8_spec (s : Slice U8) :
    ∀ k : Usize, k.val < s.length → s.index_usize k ⦃ x => x.val = byteD s.val k.val ⦄ := by
  intro k hk
  apply WP.spec_mono (Slice.index_usize_spec s k hk)
  intro x hx; rw [hx, getElem_val_eq_byteD]

/-! 数 (parse_digits, parse_number) -/

theorem digitsAt_lt {s : List U8} {j : Nat} (h : j < s.length) :
    digitsAt s j = if isDigit (byteD s j) then ((byteD s j - 0x30) :: (digitsAt s (j + 1)).1, (digitsAt s (j + 1)).2)
      else ([], j) := by
  rw [digitsAt, dite_eq_left h, getElem_val_eq_byteD]

theorem digitsAt_ge {s : List U8} {j : Nat} (h : s.length ≤ j) : digitsAt s j = ([], j) := by
  rw [digitsAt, dite_eq_right (by omega)]

theorem digitsAt_snd (s : List U8) (j : Nat) : (digitsAt s j).2 = j + (digitsAt s j).1.length := by
  by_cases h : j < s.length
  · rw [digitsAt_lt h]
    split
    · simp only [List.length_cons]; rw [digitsAt_snd s (j + 1)]; omega
    · simp
  · rw [digitsAt_ge (by omega)]; simp
termination_by s.length - j

theorem digitsAt_le9 (s : List U8) (j : Nat) : ∀ d ∈ (digitsAt s j).1, d ≤ 9 := by
  by_cases h : j < s.length
  · rw [digitsAt_lt h]
    split
    · rename_i hd
      simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
      intro d hd'
      simp only [List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · omega
      · exact digitsAt_le9 s (j + 1) d hd'
    · simp
  · rw [digitsAt_ge (by omega)]; simp
termination_by s.length - j

theorem digitsAt_bound (s : List U8) (j : Nat) (h : j ≤ s.length) : (digitsAt s j).2 ≤ s.length := by
  by_cases h' : j < s.length
  · rw [digitsAt_lt h']
    split
    · exact digitsAt_bound s (j + 1) (by omega)
    · simp; omega
  · rw [digitsAt_ge (by omega)]; simp; omega
termination_by s.length - j

theorem parse_digits_loop_spec_aux (s : Slice U8) (out : alloc.vec.Vec U8) (j : Usize)
    (hl : out.val.length + (s.length - j.val) ≤ Usize.max) :
    json.number.parse_digits_loop s out j ⦃ p => p.1.val = (digitsAt s.val j.val).2 ∧
      p.2.val.map (·.val) = out.val.map (·.val) ++ (digitsAt s.val j.val).1 ⦄ := by
  unfold json.number.parse_digits_loop
  have hidx := index_u8_spec s
  step*
  all_goals
    simp_all only [UScalar.le_equiv, UScalar.lt_equiv, UScalar.eq_equiv, usize_ge_iff,
      u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq, true_eq_iff, false_eq_iff,
      List.length_append, List.length_singleton, lit_eq_byteD, isDigit, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    try simp only [usize_ge_iff, u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq,
      List.length_append, List.length_singleton, lit_eq_byteD, isDigit, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
  all_goals first
    | omega
    | (rw [digitsAt_ge (by omega)]; simp)
    | (rw [digitsAt_lt (s := s.val) (j := j.val) (by omega)]
       simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
       split_ifs <;> simp_all <;> omega)
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem parse_digits_loop_spec (s : Slice U8) (out : alloc.vec.Vec U8) (j : Usize)
    (hl : out.val.length + (s.length - j.val) ≤ Usize.max) :
    json.number.parse_digits_loop s out j ⦃ p => p.1.val = j.val + (digitsAt s.val j.val).1.length ∧
      p.2.val.map (·.val) = out.val.map (·.val) ++ (digitsAt s.val j.val).1 ⦄ := by
  apply WP.spec_mono (parse_digits_loop_spec_aux s out j hl)
  intro p hp; rw [← digitsAt_snd]; exact hp

theorem vec_new_val (α : Type) : (alloc.vec.Vec.new α).val = [] := rfl

theorem self_eq_add_iff (a b : Nat) : (a = a + b) ↔ b = 0 := by omega

theorem add_eq_self_iff (a b : Nat) : (a + b = a) ↔ b = 0 := by omega

theorem eq_nil_iff_len {α} (l : List α) : l = [] ↔ l.length = 0 := List.length_eq_zero_iff.symm

-- if を束縛の外に出す
theorem bind_ite_res {α β} (c : Prop) [Decidable c] (a b : Result α) (k : α → Result β) :
    Std.bind (if c then a else b) k = if c then Std.bind a k else Std.bind b k := by
  split <;> rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 40000000 in
theorem parse_number_spec_aux (s : Slice U8) (i : Usize) (h : i.val < s.length) :
    json.number.parse_number s i ⦃ r => r.map (fun p => (p.1.toParts, p.2.val)) = numAt s.val i.val ⦄ := by
  unfold json.number.parse_number
  simp only [bind_ite_res]
  have hidx := index_u8_spec s
  step*
  all_goals try (simp only [bind_ite_res]; step*)
  all_goals
    clear hidx
    simp_all only [UScalar.le_equiv, UScalar.lt_equiv, UScalar.eq_equiv, usize_ge_iff,
      u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq, true_eq_iff, false_eq_iff,
      List.length_append, List.length_singleton, lit_eq_byteD, isDigit, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_eq_false_iff, decide_eq_false_iff_not, self_eq_add_iff, add_eq_self_iff, eq_nil_iff_len, vec_new_val, List.length_nil,
      List.nil_append, List.length_map]
    try simp only [usize_ge_iff, u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq,
      List.length_append, List.length_singleton, lit_eq_byteD, isDigit, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at *
  all_goals first
    | omega
    | (simp (disch := omega) only [numAt, intPart, fracPart, expPart, byteAt_eq_byteD, byteAt_ge, ite_eq_left,
        ite_eq_right, Option.bind_some, Option.bind_none, Option.map_some, Option.map_none, Option.some.injEq,
        reduceCtorEq, and_false, false_and, ↓reduceIte, isDigit, Bool.and_eq_true, decide_eq_true_eq, eq_nil_iff_len,
        digitsAt_snd, decide_true, decide_false, json.number.Number.toParts, or_false, false_or, true_or, or_true,
        decide_eq_true, decide_eq_false, vec_new_val, List.map_nil, and_true, true_and, and_self]
       all_goals simp_all)

/-! 数の仕様の整理、リテラル、スカラー値 -/

theorem intPart_some {s : List U8} {j : Nat} {I : List Nat} {j1 : Nat} (h : intPart s j = some (I, j1)) :
    j < j1 ∧ j1 ≤ s.length ∧ (∀ d ∈ I, d ≤ 9) ∧ j1 = j + I.length := by
  unfold intPart at h
  split at h
  · cases h
  · rename_i c hc
    have hj := byteAt_some' hc
    split at h
    · rename_i hd
      split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; simp; omega
      · simp at h
        have hI : I = (digitsAt s j).1 := by rw [h]
        have hJ : j1 = (digitsAt s j).2 := by rw [h]
        subst hI hJ
        have e1 := digitsAt_snd s j
        have e2 := digitsAt_le9 s j
        have e3 := digitsAt_bound s j (by omega)
        rw [digitsAt_lt hj] at e1 e2 e3 ⊢
        rw [byteAt_eq_byteD hj] at hc; cases hc
        simp only [hd, ↓reduceIte, List.length_cons] at e1 e2 e3 ⊢
        refine ⟨by omega, e3, e2, e1⟩
    · cases h

theorem fracPart_some {s : List U8} {j : Nat} {F : List Nat} {j2 : Nat} (hj : j ≤ s.length)
    (h : fracPart s j = some (F, j2)) : j ≤ j2 ∧ j2 ≤ s.length ∧ (∀ d ∈ F, d ≤ 9) ∧ F.length ≤ j2 - j := by
  unfold fracPart at h
  split at h
  · rename_i hb
    have := byteAt_some' hb
    split at h
    · cases h
    · simp at h
      have hI : F = (digitsAt s (j + 1)).1 := by rw [h]
      have hJ : j2 = (digitsAt s (j + 1)).2 := by rw [h]
      subst hI hJ
      have e1 := digitsAt_snd s (j + 1)
      have e3 := digitsAt_bound s (j + 1) (by omega)
      exact ⟨by omega, e3, digitsAt_le9 s (j + 1), by omega⟩
  · simp at h; obtain ⟨rfl, rfl⟩ := h; simp; omega

theorem expPart_some {s : List U8} {j : Nat} {en : Bool} {E : List Nat} {k : Nat} (hj : j ≤ s.length)
    (h : expPart s j = some (en, E, k)) : j ≤ k ∧ k ≤ s.length ∧ (∀ d ∈ E, d ≤ 9) ∧ E.length ≤ k - j := by
  unfold expPart at h
  by_cases hb : byteAt s j = some 0x65 ∨ byteAt s j = some 0x45
  · have : j < s.length := by rcases hb with hb | hb <;> exact byteAt_some' hb
    rw [ite_eq_left hb] at h
    have key : ∀ j3, j + 1 ≤ j3 → j3 ≤ j + 2 → j3 ≤ s.length →
        (if (digitsAt s j3).1 = [] then none
          else some (decide (byteAt s (j + 1) = some 0x2D), (digitsAt s j3).1, (digitsAt s j3).2)) =
          some (en, E, k) → j ≤ k ∧ k ≤ s.length ∧ (∀ d ∈ E, d ≤ 9) ∧ E.length ≤ k - j := by
      intro j3 h1 h2 h3 hh
      split at hh
      · cases hh
      · simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨_, rfl, rfl⟩ := hh
        have e1 := digitsAt_snd s j3
        have e3 := digitsAt_bound s j3 h3
        exact ⟨by omega, e3, digitsAt_le9 s _, by omega⟩
    by_cases hs : byteAt s (j + 1) = some 0x2B ∨ byteAt s (j + 1) = some 0x2D
    · have : j + 1 < s.length := by rcases hs with hs | hs <;> exact byteAt_some' hs
      rw [ite_eq_left hs] at h
      exact key (j + 2) (by omega) (by omega) (by omega) h
    · rw [ite_eq_right hs] at h
      exact key (j + 1) (by omega) (by omega) (by omega) h
  · rw [ite_eq_right hb] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; simpa using hj

theorem numAt_some {s : List U8} {i : Nat} {p : NumParts} {k : Nat} (h : numAt s i = some (p, k)) :
    i < k ∧ k ≤ s.length ∧ (∀ d ∈ p.2.1 ++ p.2.2.1 ++ p.2.2.2.2, d ≤ 9) ∧
      p.2.1.length + p.2.2.1.length + p.2.2.2.2.length ≤ k - i := by
  unfold numAt at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨I, j1⟩, hI, ⟨F, j2⟩, hF, ⟨en, E, k'⟩, hE, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨a1, a2, a3, a4⟩ := intPart_some hI
  obtain ⟨b1, b2, b3, b4⟩ := fracPart_some a2 hF
  obtain ⟨c1, c2, c3, c4⟩ := expPart_some b2 hE
  have hj0 : i ≤ (if decide (byteAt s i = some 0x2D) = true then i + 1 else i) := by split <;> omega
  generalize (if decide (byteAt s i = some 0x2D) = true then i + 1 else i) = j0 at a1 a4 hj0
  refine ⟨by omega, c2, ?_, ?_⟩
  rotate_left
  · dsimp only; omega
  intro d hd
  simp only [List.mem_append] at hd
  rcases hd with (hd | hd) | hd
  · exact a3 d hd
  · exact b3 d hd
  · exact c3 d hd

-- RFC 8259 §6: 数値の構文
@[step]
theorem parse_number_spec (s : Slice U8) (i : Usize) (h : i.val < s.length) :
    json.number.parse_number s i ⦃ r => match r with
      | none => numAt s.val i.val = none
      | some (n, k) => numAt s.val i.val = some (n.toParts, k.val) ∧ n.wf ∧ i.val < k.val ∧ k.val ≤ s.length ⦄ := by
  apply WP.spec_mono (parse_number_spec_aux s i h)
  rintro (_ | ⟨n, k⟩) hr
  · simpa using hr.symm
  · simp only [Option.map_some] at hr
    have hk := numAt_some hr.symm
    simp only [json.number.Number.toParts] at hk
    refine ⟨hr.symm, ⟨?_, ?_⟩, hk.1, hk.2.1⟩
    · intro d hd
      have := hk.2.2.1 d.val (by simp only [List.mem_append, List.mem_map] at hd ⊢; rcases hd with (hd | hd) | hd <;> [exact Or.inl (Or.inl ⟨d, hd, rfl⟩); exact Or.inl (Or.inr ⟨d, hd, rfl⟩); exact Or.inr ⟨d, hd, rfl⟩])
      exact this
    · obtain ⟨hk1, hk2, _, hk4⟩ := hk
      simp only [List.length_map] at hk4
      have : s.val.length ≤ Usize.max := by scalar_tac
      omega

end LoadGltf
