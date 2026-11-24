import LoadGltf.Json.Number

open Aeneas Aeneas.Std Result

namespace LoadGltf

set_option linter.unusedSimpArgs false


-- 16 進数字 (大文字・小文字)
def hexVal (b : Nat) : Option Nat :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b - 0x30)
  else if 0x41 ≤ b ∧ b ≤ 0x46 then some (b - 0x41 + 10)
  else if 0x61 ≤ b ∧ b ≤ 0x66 then some (b - 0x61 + 10)
  else none

-- s[i..i+n] の n 桁の 16 進数の値
def hexDigitsVal (s : List U8) (i : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => match hexDigitsVal s i n, (byteAt s (i + n)).bind hexVal with
    | some a, some h => some (a * 16 + h)
    | _, _ => none

def hex4At (s : List U8) (i : Nat) : Option Nat := hexDigitsVal s i 4

-- 符号位置 c の標準 UTF-8 符号化
def utf8Enc (c : Nat) : List Nat :=
  if c < 0x80 then [c]
  else if c < 0x800 then [0xC0 + c / 64, 0x80 + c % 64]
  else if c < 0x10000 then [0xE0 + c / 4096, 0x80 + c / 64 % 64, 0x80 + c % 64]
  else [0xF0 + c / 262144, 0x80 + c / 4096 % 64, 0x80 + c / 64 % 64, 0x80 + c % 64]

-- バックスラッシュの次の位置 i からのエスケープ: (復号したバイト列, 次の位置)
def escAt (s : List U8) (i : Nat) : Option (List Nat × Nat) :=
  match byteAt s i with
  | none => none
  | some e =>
    if e = 0x22 ∨ e = 0x5C ∨ e = 0x2F then some ([e], i + 1)
    else if e = 0x62 then some ([0x08], i + 1)
    else if e = 0x66 then some ([0x0C], i + 1)
    else if e = 0x6E then some ([0x0A], i + 1)
    else if e = 0x72 then some ([0x0D], i + 1)
    else if e = 0x74 then some ([0x09], i + 1)
    else if e = 0x75 then
      match hex4At s (i + 1) with
      | none => none
      | some u =>
        if 0xD800 ≤ u ∧ u ≤ 0xDBFF then
          if byteAt s (i + 5) = some 0x5C ∧ byteAt s (i + 6) = some 0x75 then
            match hex4At s (i + 7) with
            | none => none
            | some l =>
              if 0xDC00 ≤ l ∧ l ≤ 0xDFFF then
                some (utf8Enc (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)), i + 11)
              else none
          else none
        else if 0xDC00 ≤ u ∧ u ≤ 0xDFFF then none
        else some (utf8Enc u, i + 5)
    else none

def inRange (b : Option Nat) (lo hi : Nat) : Bool :=
  match b with
  | some x => lo ≤ x && x ≤ hi
  | none => false

-- Unicode Table 3-7: s[i..] から始まる整形式 UTF-8 列の長さ (なければ 0)
-- Unicode Table 3-7: UTF-8 のバイト列
def utf8Len (s : List U8) (i : Nat) : Nat :=
  let r := fun k lo hi => inRange (byteAt s (i + k)) lo hi
  if r 0 0xC2 0xDF && r 1 0x80 0xBF then 2
  else if r 0 0xE0 0xE0 && r 1 0xA0 0xBF && r 2 0x80 0xBF then 3
  else if r 0 0xE1 0xEC && r 1 0x80 0xBF && r 2 0x80 0xBF then 3
  else if r 0 0xED 0xED && r 1 0x80 0x9F && r 2 0x80 0xBF then 3
  else if r 0 0xEE 0xEF && r 1 0x80 0xBF && r 2 0x80 0xBF then 3
  else if r 0 0xF0 0xF0 && r 1 0x90 0xBF && r 2 0x80 0xBF && r 3 0x80 0xBF then 4
  else if r 0 0xF1 0xF3 && r 1 0x80 0xBF && r 2 0x80 0xBF && r 3 0x80 0xBF then 4
  else if r 0 0xF4 0xF4 && r 1 0x80 0x8F && r 2 0x80 0xBF && r 3 0x80 0xBF then 4
  else 0

theorem escAt_lt {s : List U8} {i : Nat} {bs : List Nat} {j : Nat} (h : escAt s i = some (bs, j)) : i < j := by
  unfold escAt at h
  split at h
  · cases h
  · split_ifs at h <;> (try split at h) <;> (try split_ifs at h) <;> (try split at h) <;> (try split_ifs at h) <;>
      simp at h <;> omega

-- string(s, i): 開始引用符の直後から。(復号したバイト列, 終了引用符の次の位置)
-- RFC 8259 §7: 文字列の構文
set_option linter.unusedVariables false in
def strAt (s : List U8) (i : Nat) : Option (List Nat × Nat) :=
  match hb : byteAt s i with
  | none => none
  | some c =>
    if c = 0x22 then some ([], i + 1)
    else if c = 0x5C then
      match he : escAt s (i + 1) with
      | none => none
      | some (bs, j) => (strAt s j).map fun p => (bs ++ p.1, p.2)
    else if c < 0x20 then none
    else if c < 0x80 then (strAt s (i + 1)).map fun p => (c :: p.1, p.2)
    else if utf8Len s i = 0 then none
    else (strAt s (i + utf8Len s i)).map fun p => (((s.drop i).take (utf8Len s i)).map (·.val) ++ p.1, p.2)
termination_by s.length - i
decreasing_by
  · have := escAt_lt he; have := byteAt_some' hb; omega
  · have := byteAt_some' hb; omega
  · have := byteAt_some' hb; omega

/-! 文法の補題 -/

theorem byteAt_lt {s : List U8} {i : Nat} (h : i < s.length) : byteAt s i = some s[i].val := by
  simp [byteAt, h]

theorem strAt_of_none {s : List U8} {i : Nat} (h : byteAt s i = none) : strAt s i = none := by
  rw [strAt]; split <;> simp_all

theorem strAt_of_some {s : List U8} {i c : Nat} (h : byteAt s i = some c) : strAt s i =
    if c = 0x22 then some ([], i + 1)
    else if c = 0x5C then (escAt s (i + 1)).bind fun q => (strAt s q.2).map fun p => (q.1 ++ p.1, p.2)
    else if c < 0x20 then none
    else if c < 0x80 then (strAt s (i + 1)).map fun p => (c :: p.1, p.2)
    else if utf8Len s i = 0 then none
    else (strAt s (i + utf8Len s i)).map fun p => (((s.drop i).take (utf8Len s i)).map (·.val) ++ p.1, p.2) := by
  rw [strAt]
  split
  · simp_all
  · rename_i c' hc
    rw [h] at hc; cases hc
    split_ifs <;> try rfl
    split <;> simp_all

@[step]
theorem hex_value_spec (b : U8) : json.string.hex_value b ⦃ r => r.map (·.val) = hexVal b.val ⦄ := by
  unfold json.string.hex_value
  step* <;> simp [hexVal] <;> agrind

theorem hexVal_lt {b h : Nat} (hh : hexVal b = some h) : h < 16 := by
  unfold hexVal at hh; split at hh <;> (try split at hh) <;> (try split at hh) <;> simp at hh <;> omega

theorem hexDigitsVal_lt {s : List U8} {i : Nat} : ∀ {n v : Nat}, hexDigitsVal s i n = some v → v < 16 ^ n
  | 0, v, h => by simp [hexDigitsVal] at h; omega
  | n + 1, v, h => by
    simp only [hexDigitsVal] at h
    split at h
    · rename_i a hh ha hb
      cases h
      have := hexDigitsVal_lt ha
      have := hexVal_lt (Option.bind_eq_some_iff.mp hb |>.choose_spec.2)
      rw [pow_succ]; omega
    · cases h

theorem hexDigitsVal_none {s : List U8} {i n : Nat} (h : hexDigitsVal s i n = none) :
    ∀ m, n ≤ m → hexDigitsVal s i m = none := by
  intro m hm
  induction m with
  | zero => have : n = 0 := by omega
            subst this; simp [hexDigitsVal] at h
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hm with rfl | hlt
    · exact h
    · simp [hexDigitsVal, ih (by omega)]

theorem hexDigitsVal_oob {s : List U8} {i : Nat} : ∀ {n : Nat}, 0 < n → s.length < i + n → hexDigitsVal s i n = none
  | 0, h0, h => by omega
  | n + 1, _, h => by
    simp only [hexDigitsVal]
    by_cases hn : 0 < n ∧ s.length < i + n
    · rw [hexDigitsVal_oob hn.1 hn.2]
    · rw [byteAt_ge (by omega)]; split <;> simp_all

@[step]
theorem parse_hex4_loop_spec (s : Slice U8) (i : Usize) (v : U32) (k : Usize) (hk : k.val ≤ 4)
    (hb : i.val + 4 ≤ s.length) (hv : hexDigitsVal s.val i.val k.val = some v.val) :
    json.string.parse_hex4_loop s i v k ⦃ r => r.map (·.val) = hexDigitsVal s.val i.val 4 ⦄ := by
  unfold json.string.parse_hex4_loop
  have hvl := hexDigitsVal_lt hv
  step*
  · have hb' : byteAt s.val (i.val + k.val) = some i2.val := by rw [byteAt_lt (by scalar_tac)]; simp_all
    have hh : hexVal i2.val = none := by rw [← o_post]; simp_all
    rw [hexDigitsVal_none (n := k.val + 1) (by simp [hexDigitsVal, hv, hb', hh]) 4 (by scalar_tac)]; simp
  · have : 16 ^ k.val ≤ 16 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by scalar_tac)
    scalar_tac
  · have := hexVal_lt (b := i2.val) (h := h.val) (by rw [← o_post]; simp_all)
    have : 16 ^ k.val ≤ 16 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by scalar_tac)
    scalar_tac
  · have hb' : byteAt s.val (i.val + k.val) = some i2.val := by rw [byteAt_lt (by scalar_tac)]; simp_all
    have hh : hexVal i2.val = some h.val := by rw [← o_post]; simp_all
    rw [k1_post]; simp [hexDigitsVal, hv, hb', hh]; scalar_tac
  · have : k.val = 4 := by scalar_tac
    rw [← this, hv]; rfl
termination_by 4 - k.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem parse_hex4_spec (s : Slice U8) (i : Usize) :
    json.string.parse_hex4 s i ⦃ r => hex4At s.val i.val = r.map (·.val) ∧
      ∀ v, r = some v → i.val + 4 ≤ s.length ∧ v.val < 0x10000 ⦄ := by
  unfold json.string.parse_hex4 hex4At
  step*
  · rw [hexDigitsVal_oob (by omega) (by scalar_tac)]; simp
  · rw [hexDigitsVal_oob (by omega) (by scalar_tac)]; simp
  · simp [hexDigitsVal]
  · refine ⟨r_post.symm, fun v hv => ⟨by scalar_tac, ?_⟩⟩
    subst hv
    have := hexDigitsVal_lt (r_post.symm.trans rfl : hexDigitsVal s.val i.val 4 = some v.val)
    simpa using this

theorem lor_eq_add (a x n : Nat) (hx : x < 2 ^ n) (ha : a % 2 ^ n = 0) : a ||| x = a + x := by
  have := Nat.two_pow_add_eq_or_of_lt hx (a / 2 ^ n)
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha)] at this
  omega

theorem utf8Enc_length_le (c : Nat) : (utf8Enc c).length ≤ 4 := by
  unfold utf8Enc; split_ifs <;> simp

theorem utf8Enc_length_bmp (c : Nat) (h : c < 0x10000) : (utf8Enc c).length ≤ 3 := by
  unfold utf8Enc; split_ifs <;> simp

theorem or_lead (a x n : Nat) (hx : x < 2 ^ n) (ha : a % 2 ^ n = 0) : a ||| x = a + x := lor_eq_add a x n hx ha

theorem and63 (x : Nat) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6

theorem or192 {x : Nat} (h : x < 32) : 192 ||| x = 192 + x := or_lead 192 x 5 h rfl

theorem or128 {x : Nat} (h : x < 64) : 128 ||| x = 128 + x := or_lead 128 x 6 h rfl

theorem or224 {x : Nat} (h : x < 16) : 224 ||| x = 224 + x := or_lead 224 x 4 h rfl

theorem or240 {x : Nat} (h : x < 16) : 240 ||| x = 240 + x := or_lead 240 x 4 h rfl

theorem cast_u8_val (x : U32) : (UScalar.cast .U8 x).val = x.val % 256 := by
  rw [UScalar.cast_val_eq]; rfl

@[step]
theorem push_utf8_spec (out : alloc.vec.Vec U8) (c : U32) (hc : c.val < 0x110000)
    (hl : out.val.length + 4 ≤ Usize.max) :
    json.string.push_utf8 out c ⦃ r => r.val.map (·.val) = out.val.map (·.val) ++ utf8Enc c.val ∧
      r.val.length = out.val.length + (utf8Enc c.val).length ∧ (utf8Enc c.val).length ≤ 4 ∧
      (c.val < 0x10000 → (utf8Enc c.val).length ≤ 3) ⦄ := by
  have h3 := utf8Enc_length_bmp c.val
  have h4 := utf8Enc_length_le c.val
  suffices H : json.string.push_utf8 out c ⦃ r => r.val.map (·.val) = out.val.map (·.val) ++ utf8Enc c.val ∧
      r.val.length = out.val.length + (utf8Enc c.val).length ⦄ by
    apply WP.spec_mono H; intro r hr; exact ⟨hr.1, hr.2, h4, h3⟩
  unfold json.string.push_utf8
  have hlen := utf8Enc_length_le c.val
  step*
  all_goals (try (simp_all only [List.length_append, List.length_singleton]; scalar_tac))
  · have h1 : c.val < 128 := by scalar_tac
    have e : i.val = c.val := by rw [i_post, cast_u8_val]; omega
    simp [r_post, e, utf8Enc, h1]
  · have h1 : 128 ≤ c.val ∧ c.val < 2048 := by scalar_tac
    have e1 : i2.val = 0xC0 + c.val / 64 := by
      rw [i2_post, cast_u8_val, i1_post, UScalar.val_or, i_post, Nat.shiftRight_eq_div_pow]
      simp only [UScalar.ofNatCore_val_eq, Nat.reducePow]; rw [or192 (by omega)]; omega
    have e2 : i5.val = 0x80 + c.val % 64 := by
      rw [i5_post, cast_u8_val, i4_post, UScalar.val_or, i3_post, UScalar.val_and]
      simp only [UScalar.ofNatCore_val_eq]; rw [and63, or128 (by omega)]; omega
    simp [r_post, out1_post, e1, e2, utf8Enc, h1, show ¬ c.val < 128 by omega]
  · have h1 : 2048 ≤ c.val ∧ c.val < 65536 := by scalar_tac
    have e1 : i2.val = 0xE0 + c.val / 4096 := by
      rw [i2_post, cast_u8_val, i1_post, UScalar.val_or, i_post, Nat.shiftRight_eq_div_pow]
      simp only [UScalar.ofNatCore_val_eq, Nat.reducePow]; rw [or224 (by omega)]; omega
    have e2 : i6.val = 0x80 + c.val / 64 % 64 := by
      rw [i6_post, cast_u8_val, i5_post, UScalar.val_or, i4_post, UScalar.val_and, i3_post,
        Nat.shiftRight_eq_div_pow]
      simp only [UScalar.ofNatCore_val_eq, Nat.reducePow]; rw [and63, or128 (by omega)]; omega
    have e3 : i9.val = 0x80 + c.val % 64 := by
      rw [i9_post, cast_u8_val, i8_post, UScalar.val_or, i7_post, UScalar.val_and]
      simp only [UScalar.ofNatCore_val_eq]; rw [and63, or128 (by omega)]; omega
    simp [r_post, out1_post, out2_post, e1, e2, e3, utf8Enc, h1, show ¬ c.val < 128 by omega,
      show ¬ c.val < 2048 by omega]
  · have h1 : 65536 ≤ c.val ∧ c.val < 0x110000 := by scalar_tac
    simp only [*, cast_u8_val, UScalar.val_or, UScalar.val_and, UScalar.ofNatCore_val_eq,
      Nat.shiftRight_eq_div_pow, and63, Nat.reducePow, List.map_append, List.map_cons, List.map_nil]
    rw [or240 (by omega), or128 (by omega), or128 (by omega), or128 (by omega)]
    simp [utf8Enc, show ¬ c.val < 128 by omega, show ¬ c.val < 2048 by omega, show ¬ c.val < 65536 by omega]
    omega

@[step]
theorem is_cont_spec (b : U8) : json.string.is_cont b ⦃ r => r = (0x80 ≤ b.val && b.val ≤ 0xBF) ⦄ := by
  unfold json.string.is_cont
  step*

theorem inRange_byteAt (s : List U8) (k lo hi : Nat) :
    inRange (byteAt s k) lo hi = (decide (k < s.length) && decide (lo ≤ byteD s k) && decide (byteD s k ≤ hi)) := by
  by_cases h : k < s.length <;> simp [inRange, byteAt, byteD, h]

-- utf8_len の分岐構造に沿った utf8Len の言い換え
def utf8LenCode (s : List U8) (i : Nat) : Nat :=
  let b0 := byteD s i
  let b1 := byteD s (i + 1)
  let b2 := byteD s (i + 2)
  let b3 := byteD s (i + 3)
  if 0xC2 ≤ b0 ∧ b0 ≤ 0xDF then (if i + 2 ≤ s.length ∧ (0x80 ≤ b1 ∧ b1 ≤ 0xBF) then 2 else 0)
  else if b0 = 0xE0 then
    (if i + 3 ≤ s.length ∧ 0xA0 ≤ b1 ∧ b1 ≤ 0xBF ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) then 3 else 0)
  else if (0xE1 ≤ b0 ∧ b0 ≤ 0xEC) ∨ b0 = 0xEE ∨ b0 = 0xEF then
    (if i + 3 ≤ s.length ∧ (0x80 ≤ b1 ∧ b1 ≤ 0xBF) ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) then 3 else 0)
  else if b0 = 0xED then
    (if i + 3 ≤ s.length ∧ 0x80 ≤ b1 ∧ b1 ≤ 0x9F ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) then 3 else 0)
  else if b0 = 0xF0 then
    (if i + 4 ≤ s.length ∧ 0x90 ≤ b1 ∧ b1 ≤ 0xBF ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) ∧ (0x80 ≤ b3 ∧ b3 ≤ 0xBF) then 4 else 0)
  else if 0xF1 ≤ b0 ∧ b0 ≤ 0xF3 then
    (if i + 4 ≤ s.length ∧ (0x80 ≤ b1 ∧ b1 ≤ 0xBF) ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) ∧ (0x80 ≤ b3 ∧ b3 ≤ 0xBF) then 4 else 0)
  else if b0 = 0xF4 then
    (if i + 4 ≤ s.length ∧ 0x80 ≤ b1 ∧ b1 ≤ 0x8F ∧ (0x80 ≤ b2 ∧ b2 ≤ 0xBF) ∧ (0x80 ≤ b3 ∧ b3 ≤ 0xBF) then 4 else 0)
  else 0

theorem utf8LenCode_eq (s : List U8) (i : Nat) (h : i < s.length) : utf8LenCode s i = utf8Len s i := by
  simp only [utf8Len, utf8LenCode, inRange_byteAt, Nat.add_zero]
  have : byteD s i < 0xC2 ∨ (0xC2 ≤ byteD s i ∧ byteD s i ≤ 0xDF) ∨ byteD s i = 0xE0 ∨
      (0xE1 ≤ byteD s i ∧ byteD s i ≤ 0xEC) ∨ byteD s i = 0xED ∨ (0xEE ≤ byteD s i ∧ byteD s i ≤ 0xEF) ∨
      byteD s i = 0xF0 ∨ (0xF1 ≤ byteD s i ∧ byteD s i ≤ 0xF3) ∨ byteD s i = 0xF4 ∨ 0xF4 < byteD s i := by omega
  rcases this with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.false_and, Bool.and_true,
      Bool.and_false, ite_eq_left, ite_eq_right, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      decide_eq_true_eq] <;>
    split_ifs <;> omega

set_option maxHeartbeats 4000000 in
theorem utf8_len_spec_aux (s : Slice U8) (i : Usize) (h : i.val < s.length) :
    json.string.utf8_len s i ⦃ n => n.val = utf8Len s.val i.val ⦄ := by
  rw [← utf8LenCode_eq _ _ h]
  unfold json.string.utf8_len
  step*
  all_goals
    simp_all only [getElem_val_eq_byteD, UScalar.le_equiv, UScalar.lt_equiv, UScalar.eq_equiv, usize_ge_iff,
      u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq,
      true_eq_iff, false_eq_iff, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
      decide_eq_false_iff_not]
    try simp only [usize_ge_iff, u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq,
      true_eq_iff, false_eq_iff, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
      decide_eq_false_iff_not] at *
  all_goals first
    | (exfalso; omega)
    | (simp (disch := omega) only [utf8LenCode, ite_eq_left, ite_eq_right])

theorem utf8Len_bound (s : List U8) (i : Nat) (h : utf8Len s i ≠ 0) : i + utf8Len s i ≤ s.length := by
  revert h
  simp only [utf8Len, inRange_byteAt, Nat.add_zero, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> omega

-- Unicode Table 3-7: UTF-8 のバイト列
@[step]
theorem utf8_len_spec (s : Slice U8) (i : Usize) (h : i.val < s.length) :
    json.string.utf8_len s i ⦃ n => n.val = utf8Len s.val i.val ∧ (n.val ≠ 0 → i.val + n.val ≤ s.length) ⦄ := by
  apply WP.spec_mono (utf8_len_spec_aux s i h)
  intro n hn
  exact ⟨hn, fun h0 => by rw [hn] at h0 ⊢; exact utf8Len_bound _ _ h0⟩

theorem shl10 (x : Nat) (h : x < 1024) : x <<< 10 % U32.size = x * 1024 := by
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt] <;> simp [U32.size, U32.numBits] <;> omega

theorem drop_take_succ {α} (l : List α) (a m : Nat) (h : a < l.length) :
    (l.drop a).take (m + 1) = l[a] :: (l.drop (a + 1)).take m := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons]

@[step]
theorem parse_string_loop0_loop0_spec (s : Slice U8) (out : alloc.vec.Vec U8) (j n k : Usize)
    (hk : k.val ≤ n.val) (hn : j.val + n.val ≤ s.length) (hl : out.val.length + (n.val - k.val) ≤ Usize.max) :
    json.string.parse_string_loop0_loop0 s out j n k ⦃ r =>
      r.val = out.val ++ (s.val.drop (j.val + k.val)).take (n.val - k.val) ⦄ := by
  unfold json.string.parse_string_loop0_loop0
  step*
  · simp_all; scalar_tac
  · rw [r_post, out1_post, k1_post, show n.val - k.val = (n.val - (k.val + 1)) + 1 by scalar_tac,
      drop_take_succ _ _ _ (by scalar_tac)]
    simp [Nat.add_assoc, i1_post, i_post]
  · simp [show n.val - k.val = 0 by scalar_tac]
termination_by n.val - k.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 8000000 in
@[step]
theorem parse_string_loop0_spec (s : Slice U8) (out : alloc.vec.Vec U8) (j : Usize)
    (hl : out.val.length + (s.length - j.val) ≤ Usize.max) :
    json.string.parse_string_loop0 s out j ⦃ r => r.map (fun p => (p.1.val.map (·.val), p.2.val)) =
      (strAt s.val j.val).map (fun p => (out.val.map (·.val) ++ p.1, p.2)) ⦄ := by
  unfold json.string.parse_string_loop0
  have hidx := index_u8_spec s
  step*
  all_goals
    simp_all only [getElem_val_eq_byteD, UScalar.le_equiv, UScalar.lt_equiv, UScalar.eq_equiv, usize_ge_iff,
      u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq, true_eq_iff, false_eq_iff,
      Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
      List.length_append, List.length_singleton, List.length_take, List.length_drop, lit_eq_byteD]
    try simp only [usize_ge_iff, u8_ge_iff, slice_len_val_eq, slice_length_eq, UScalar.ofNatCore_val_eq,
      true_eq_iff, false_eq_iff, Bool.and_eq_true, Bool.and_eq_false_iff, decide_eq_true_eq,
      decide_eq_false_iff_not, List.length_append, List.length_singleton, lit_eq_byteD] at *
  all_goals first
    | omega
    | (rw [strAt_of_none (byteAt_ge (by omega))]; rfl)
    | (rw [strAt_of_some (byteAt_eq_byteD (k := j.val) (by omega))]
       simp (disch := omega) only [ite_eq_left, ite_eq_right, escAt, byteAt_eq_byteD, byteAt_ge, Option.bind_some,
         Option.bind_none, Option.map_none, Option.map_some, Nat.add_assoc, Option.bind_eq_bind, Nat.reduceAdd,
         Option.some.injEq, reduceCtorEq, and_false, false_and, ↓reduceIte]
       all_goals first
       | rfl
       | (simp [i1_post]; done)
       | (simp [Option.map_map, Function.comp_def]; done)
       | (simp [Option.map_map, Function.comp_def, e_post]; done)
       | (simp [Option.map_map, Function.comp_def, c_post]; done)
       | (simp only [o_post]
          simp (disch := omega) only [ite_eq_left, ite_eq_right, byteAt_eq_byteD, byteAt_ge, Option.bind_some,
            Nat.add_assoc, Nat.reduceAdd, Option.some.injEq, Option.map_none, Option.map_some, reduceCtorEq, and_false,
            false_and, ↓reduceIte]
          all_goals first
          | rfl
          | (simp [Option.map_map, Function.comp_def]; done)
          | (simp only [o1_post]
             simp (disch := omega) only [ite_eq_left, ite_eq_right, Option.bind_some, Nat.add_assoc, Nat.reduceAdd,
               Option.map_none, Option.map_some]
             all_goals first
             | rfl
             | (rw [shl10 _ (by omega)]; simp [Option.map_map, Function.comp_def]; done))))
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

-- RFC 8259 §7: 文字列の構文
theorem parse_string_spec (s : Slice U8) :
    ∀ i : Usize, json.string.parse_string s i ⦃ r => match r with
      | none => strAt s.val i.val = none
      | some (o, e) => strAt s.val i.val = some (o.val.map (·.val), e.val) ⦄ := by
  intro i
  apply WP.spec_mono (parse_string_loop0_spec s (alloc.vec.Vec.new U8) i (by simp; scalar_tac))
  rintro (_ | ⟨o, e⟩) h
  · cases hs : strAt s.val i.val <;> simp_all
  · cases hs : strAt s.val i.val <;> simp_all

end LoadGltf
