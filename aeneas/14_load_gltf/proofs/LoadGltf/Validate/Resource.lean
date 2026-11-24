import LoadGltf.Validate.Mesh

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## URI の構文 (iri-reference の部分集合) と data URI (RFC 2397) -/

def isAlphaB (c : U8) : Prop := (65 ≤ c.val ∧ c.val ≤ 90) ∨ (97 ≤ c.val ∧ c.val ≤ 122)

def isHexB (c : U8) : Prop := (48 ≤ c.val ∧ c.val ≤ 57) ∨ (65 ≤ c.val ∧ c.val ≤ 70) ∨ (97 ≤ c.val ∧ c.val ≤ 102)

-- ALPHA / DIGIT / + / - / .
def schemeCharB (c : U8) : Prop := isAlphaB c ∨ (48 ≤ c.val ∧ c.val ≤ 57) ∨ c.val = 43 ∨ c.val = 45 ∨ c.val = 46

-- A–Z a–z 0–9 + /
def base64CharB (c : U8) : Prop := isAlphaB c ∨ (48 ≤ c.val ∧ c.val ≤ 57) ∨ c.val = 43 ∨ c.val = 47

-- ≤ 0x20, 0x7F, " < > \ ^ ` { | }
def forbiddenB (c : U8) : Prop :=
  c.val ≤ 32 ∨ c.val = 127 ∨ c.val = 34 ∨ c.val = 60 ∨ c.val = 62 ∨ c.val = 92 ∨ c.val = 94 ∨
  c.val = 96 ∨ c.val = 123 ∨ c.val = 124 ∨ c.val = 125

@[step]
theorem is_alpha_spec (b : U8) : validate.resource.is_alpha b ⦃ r => r = true ↔ isAlphaB b ⦄ := by
  unfold validate.resource.is_alpha isAlphaB; step_auto

@[step]
theorem hex_digit_spec (b : U8) : validate.resource.hex_digit b ⦃ r => r = true ↔ isHexB b ⦄ := by
  unfold validate.resource.hex_digit isHexB; step_auto

@[step]
theorem base64_char_spec (b : U8) : validate.resource.base64_char b ⦃ r => r = true ↔ base64CharB b ⦄ := by
  unfold validate.resource.base64_char base64CharB isAlphaB; step_auto

-- 区切り / ? # : 以外
def noDelim (c : U8) : Prop := c.val ≠ 47 ∧ c.val ≠ 63 ∧ c.val ≠ 35 ∧ c.val ≠ 58

-- k は i 以降で / ? # より前にある最初の ':'
def firstColon (u : List U8) (i k : Nat) : Prop :=
  i ≤ k ∧ ∃ h : k < u.length, u[k].val = 58 ∧ ∀ j, i ≤ j → (hj : j < k) → noDelim u[j]

theorem firstColon_step (u : List U8) (i k : Nat) (hi : i < u.length) :
    firstColon u i k ↔ (k = i ∧ u[i].val = 58) ∨ (noDelim u[i] ∧ firstColon u (i + 1) k) := by
  unfold firstColon
  constructor
  · rintro ⟨hk, h, hc, hj⟩
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · exact Or.inl ⟨rfl, hc⟩
    · exact Or.inr ⟨hj i (Nat.le_refl _) hk, by omega, h, hc, fun j hj1 hj2 => hj j (by omega) hj2⟩
  · rintro (⟨rfl, hc⟩ | ⟨hn, hk, h, hc, hj⟩)
    · exact ⟨Nat.le_refl _, hi, hc, fun j hj1 hj2 => absurd hj2 (by omega)⟩
    · refine ⟨by omega, h, hc, fun j hj1 hj2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hj1
      · exact hn
      · exact hj j hj1 hj2

theorem firstColon_end (u : List U8) (i k : Nat) (hi : u.length ≤ i) : ¬ firstColon u i k := by
  rintro ⟨hk, h, -⟩; omega

@[step]
theorem find_scheme_end_loop_spec (uri : alloc.vec.Vec U8) (i : Usize) (hi : i.val ≤ uri.length) :
    validate.resource.find_scheme_end_loop uri i ⦃ r => r.val ≤ uri.length ∧
      ∀ k, firstColon uri.val i.val k ↔ (r.val = k ∧ k < uri.length) ⦄ := by
  unfold validate.resource.find_scheme_end_loop
  step*
  all_goals first
    | (refine ⟨by scalar_tac, fun k => ?_⟩
       have hlt : i.val < uri.val.length := by scalar_tac
       rw [firstColon_step _ _ _ hlt]
       simp_all [noDelim, UScalar.eq_equiv]
       try omega)
    | (refine ⟨by scalar_tac, fun k => ?_⟩
       rw [iff_false_intro (firstColon_end _ _ _ (by scalar_tac))]
       simp only [false_iff, not_and]; intro h; scalar_tac)
    | skip
termination_by uri.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem uri_forallIdx_step {P : Nat → Prop} {n i : Nat} (h : i < n) :
    forallIdx n i P ↔ P i ∧ forallIdx n (i + 1) P := by
  unfold forallIdx
  constructor
  · intro h'; exact ⟨h' _ (Nat.le_refl _) h, fun q hq h'' => h' q (by omega) h''⟩
  · rintro ⟨h1, h2⟩ q hq h'
    rcases Nat.eq_or_lt_of_le hq with rfl | hq
    · exact h1
    · exact h2 q hq h'

theorem uri_forallIdx_end {P : Nat → Prop} {n i : Nat} (h : n ≤ i) : forallIdx n i P ↔ True := by
  simp only [forallIdx, iff_true]; intro q hq h'; omega

@[step]
theorem scheme_chars_ok_loop_spec (uri : alloc.vec.Vec U8) (e k : Usize) (he : e.val ≤ uri.length) :
    validate.resource.scheme_chars_ok_loop uri e k ⦃ r => r = true ↔ forallIdx e.val k.val (fun j => schemeCharB uri.val[j]!) ⦄ := by
  unfold validate.resource.scheme_chars_ok_loop
  step*
  all_goals first
    | (simp only [uri_forallIdx_end (show e.val ≤ k.val by scalar_tac)]; done)
    | (rw [uri_forallIdx_step (by scalar_tac), getElem!_pos uri.val k.val (by scalar_tac), ← c_post]
       try rw [r_post, k1_post]
       simp only [schemeCharB, ← b_post]
       agrind)
termination_by e.val - k.val
decreasing_by all_goals scalar_decr_tac

-- i 以降のすべての '%' の後に 16 進数字が 2 つ続く
def pctFrom (u : List U8) (i : Nat) : Prop :=
  ∀ j, i ≤ j → ∀ h : j < u.length, u[j].val = 37 → ∃ h2 : j + 2 < u.length, isHexB u[j + 1] ∧ isHexB u[j + 2]

theorem pctFrom_step (u : List U8) (i : Nat) (hi : i < u.length) :
    pctFrom u i ↔ (u[i].val = 37 → ∃ h2 : i + 2 < u.length, isHexB u[i + 1] ∧ isHexB u[i + 2]) ∧
      pctFrom u (i + 1) := by
  unfold pctFrom
  constructor
  · intro h; exact ⟨h i (Nat.le_refl _) hi, fun j hj => h j (by omega)⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases Nat.eq_or_lt_of_le hj with rfl | hj
    · exact fun _ => h1
    · exact h2 j hj

theorem pctFrom_end (u : List U8) (i : Nat) (hi : u.length ≤ i) : pctFrom u i := by
  intro j hj h; omega

-- i 以降の文字の条件。frag は既に '#' が現れたか
def uriCharsFrom (u : List U8) (frag : Bool) (i : Nat) : Prop :=
  (∀ c ∈ u.drop i, ¬ forbiddenB c) ∧ (u.drop i).countP (fun c => c.val = 35) + (if frag then 1 else 0) ≤ 1 ∧
  pctFrom u i

theorem uriCharsFrom_step (u : List U8) (frag : Bool) (i : Nat) (hi : i < u.length) :
    uriCharsFrom u frag i ↔ ¬ forbiddenB u[i] ∧ (u[i].val = 35 → frag = false) ∧
      (u[i].val = 37 → ∃ h2 : i + 2 < u.length, isHexB u[i + 1] ∧ isHexB u[i + 2]) ∧
      uriCharsFrom u (frag || decide (u[i].val = 35)) (i + 1) := by
  unfold uriCharsFrom
  rw [List.drop_eq_getElem_cons hi, pctFrom_step _ _ hi]
  simp only [List.mem_cons, forall_eq_or_imp, List.countP_cons]
  by_cases h : u[i].val = 35 <;> cases frag <;> simp [h] <;> intro _ <;> tauto

theorem uriCharsFrom_end (u : List U8) (frag : Bool) (i : Nat) (hi : u.length ≤ i) :
    uriCharsFrom u frag i ↔ True := by
  unfold uriCharsFrom
  rw [List.drop_eq_nil_of_le hi]
  cases frag <;> simp [pctFrom_end _ _ hi]

@[step]
theorem uri_chars_ok_loop_spec (uri : alloc.vec.Vec U8) (fragment : Bool) (i : Usize) (hi : i.val ≤ uri.length) :
    validate.resource.uri_chars_ok_loop uri fragment i ⦃ r => r = true ↔ uriCharsFrom uri.val fragment i.val ⦄ := by
  unfold validate.resource.uri_chars_ok_loop
  step*
  all_goals first
    | (simp only [uriCharsFrom_end _ _ _ (show uri.val.length ≤ i.val by scalar_tac)]; done)
    | (rw [uriCharsFrom_step _ _ _ (by scalar_tac), ← c_post]
       first
       | (show false = true ↔ _
          refine iff_of_false Bool.false_ne_true (fun h => ?_)
          first
          | (apply h.1; unfold forbiddenB; scalar_tac)
          | (have := h.2.1 (by scalar_tac); simp_all; done)
          | (obtain ⟨h2, -⟩ := h.2.2.1 (by scalar_tac); scalar_tac)
          | (obtain ⟨h2, hx, hy⟩ := h.2.2.1 (by scalar_tac)
             have e5 : i5 = uri.val[i.val + 1] := by rw [i5_post]; exact getElem_idx_eq (by scalar_tac) _ _
             rw [← e5] at hx
             first
             | exact ‹¬b = true› (b_post.mpr hx)
             | (have e7 : i7 = uri.val[i.val + 2] := by rw [i7_post]; exact getElem_idx_eq (by scalar_tac) _ _
                rw [← e7] at hy; exact ‹¬b1 = true› (b1_post.mpr hy))))
       | (have hc : c.val = 35 := by scalar_tac
          have hf : fragment = false := by simpa using ‹¬fragment = true›
          rw [r_post, i2_post]
          simp [hc, hf, forbiddenB])
       | (have hn : ¬ forbiddenB c := by unfold forbiddenB; scalar_tac
          have h35 : c.val ≠ 35 := by scalar_tac
          have h37 : c.val ≠ 37 := by scalar_tac
          rw [r_post, i2_post]
          simp [hn, h35, h37])
       | (have hc : c.val = 37 := by scalar_tac
          have hl : i.val + 2 < uri.val.length := by scalar_tac
          have e5 : i5 = uri.val[i.val + 1] := by rw [i5_post]; exact getElem_idx_eq (by scalar_tac) _ _
          have e7 : i7 = uri.val[i.val + 2] := by rw [i7_post]; exact getElem_idx_eq (by scalar_tac) _ _
          have hx := b_post.mp ‹_›
          have hy := b1_post.mp ‹_›
          rw [e5] at hx; rw [e7] at hy
          rw [r_post, i4_post]
          simp only [hc]
          exact ⟨fun h => ⟨by unfold forbiddenB; omega, by omega, fun _ => ⟨by scalar_tac, hx, hy⟩, by simpa using h⟩,
            fun h => by simpa using h.2.2.2⟩))
termination_by uri.length - i.val
decreasing_by all_goals scalar_decr_tac

-- スキーム部: / ? # より前に ':' があれば、その前はスキーム ALPHA *(ALPHA / DIGIT / + / - / .)
def schemePart (u : List U8) : Prop :=
  ∀ k (hk : k < u.length), u[k].val = 58 →
    (∀ j (hj : j < k), u[j].val ≠ 47 ∧ u[j].val ≠ 63 ∧ u[j].val ≠ 35 ∧ u[j].val ≠ 58) →
    0 < k ∧ isAlphaB u[0] ∧ ∀ j, 1 ≤ j → (hj : j < k) → schemeCharB u[j]

-- uri_syntax(u)
def uriSyntax (u : List U8) : Prop :=
  schemePart u ∧ (∀ c ∈ u, ¬ forbiddenB c) ∧ u.countP (fun c => c.val = 35) ≤ 1 ∧
  (∀ i (hi : i < u.length), u[i].val = 37 → ∃ h2 : i + 2 < u.length, isHexB u[i + 1] ∧ isHexB u[i + 2])

theorem firstColon_zero (u : List U8) (k : Nat) :
    firstColon u 0 k ↔ ∃ hk : k < u.length, u[k].val = 58 ∧
      ∀ j (hj : j < k), u[j].val ≠ 47 ∧ u[j].val ≠ 63 ∧ u[j].val ≠ 35 ∧ u[j].val ≠ 58 := by
  unfold firstColon noDelim
  constructor
  · rintro ⟨-, hk, h1, h2⟩; exact ⟨hk, h1, fun j hj => h2 j (Nat.zero_le _) hj⟩
  · rintro ⟨hk, h1, h2⟩; exact ⟨Nat.zero_le _, hk, h1, fun j _ hj => h2 j hj⟩

theorem uriCharsFrom_zero (u : List U8) :
    uriCharsFrom u false 0 ↔ (∀ c ∈ u, ¬ forbiddenB c) ∧ u.countP (fun c => c.val = 35) ≤ 1 ∧
      (∀ i (hi : i < u.length), u[i].val = 37 → ∃ h2 : i + 2 < u.length, isHexB u[i + 1] ∧ isHexB u[i + 2]) := by
  unfold uriCharsFrom pctFrom
  simp

theorem schemePart_of_end (u : List U8) (hfc : ∀ k, firstColon u 0 k ↔ u.length = k ∧ k < u.length) :
    schemePart u := by
  intro k hk hc hj
  have := (hfc k).mp ((firstColon_zero u k).mpr ⟨hk, hc, hj⟩)
  omega

theorem schemePart_iff_of (u : List U8) (e : Nat) (he : e < u.length)
    (hfc : ∀ k, firstColon u 0 k ↔ e = k ∧ k < u.length) :
    schemePart u ↔ 0 < e ∧ (∀ h : 0 < u.length, isAlphaB u[0]) ∧ forallIdx e 1 (fun j => schemeCharB u[j]!) := by
  obtain ⟨hk, hc, hj⟩ := (firstColon_zero u e).mp ((hfc e).mpr ⟨rfl, he⟩)
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := h e hk hc hj
    refine ⟨h1, fun _ => h2, fun q hq1 hq2 => ?_⟩
    show schemeCharB u[q]!
    rw [getElem!_pos u q (by omega)]; exact h3 q hq1 hq2
  · rintro ⟨h1, h2, h3⟩ k hk' hc' hj'
    have := (hfc k).mp ((firstColon_zero u k).mpr ⟨hk', hc', hj'⟩)
    obtain ⟨rfl, -⟩ := this
    refine ⟨h1, h2 (by omega), fun q hq1 hq2 => ?_⟩
    have : schemeCharB u[q]! := h3 q hq1 hq2
    rwa [getElem!_pos u q (by omega)] at this

@[step]
theorem uri_syntax_ok_spec (uri : alloc.vec.Vec U8) : validate.resource.uri_syntax_ok uri ⦃ r => r = true ↔ uriSyntax uri.val ⦄ := by
  unfold validate.resource.uri_syntax_ok uriSyntax
  rw [← uriCharsFrom_zero]
  step
  split
  next h1 =>
    have he : «end».val = uri.val.length := by scalar_tac
    have hsp : schemePart uri.val := schemePart_of_end _ (by simpa [he] using end_post1)
    step*
  next h1 =>
    have hlt : «end».val < uri.val.length := by scalar_tac
    simp only [schemePart_iff_of _ _ hlt end_post1]
    split
    next h2 =>
      have hpos : 0 < «end».val := by scalar_tac
      step as ⟨c0, hc0⟩
      step as ⟨xa, hxa⟩
      rw [hc0] at hxa
      split
      next h3 =>
        step*
        rw [r_post, ← scheme_ok_post]
        simp_all
      next h3 =>
        step*
    next h2 =>
      have h0 : «end».val = 0 := by scalar_tac
      step*

/-! ### data URI の補助関数 -/

-- u[a..b]
def uriSeg (u : List U8) (a b : Nat) : List U8 := (u.drop a).take (b - a)

@[step]
theorem find_byte_loop_spec (s : alloc.vec.Vec U8) (t : Usize) (b : U8) (i : Usize)
    (hi : i.val ≤ t.val) (ht : t.val ≤ s.length) :
    validate.resource.find_byte_loop s t b i ⦃ r => i.val ≤ r.val ∧ r.val ≤ t.val ∧ (r.val < t.val → s.val[r.val]? = some b) ∧
      ∀ j, i.val ≤ j → j < r.val → s.val[j]? ≠ some b ⦄ := by
  unfold validate.resource.find_byte_loop
  step*
  · refine ⟨by omega, by omega, fun _ => ?_, fun j h1 h2 => by omega⟩
    rw [List.getElem?_eq_getElem (by scalar_tac)]; simp_all
  · refine ⟨by omega, by omega, r_post2, fun j h1 h2 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · rw [List.getElem?_eq_getElem (by scalar_tac)]; simp_all
    · exact r_post3 j (by omega) h2
termination_by t.val - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem range_eq_loop_spec (s : alloc.vec.Vec U8) (start : Usize) (lit : Slice U8) (i : Usize)
    (hl : start.val + lit.length ≤ s.length) (hi : i.val ≤ lit.length) :
    validate.resource.range_eq_loop s start lit i ⦃ r => r = true ↔
      forallIdx lit.val.length i.val (fun q => s.val[start.val + q]? = lit.val[q]?) ⦄ := by
  unfold validate.resource.range_eq_loop
  step*
  · simp only [Bool.false_eq_true, false_iff, forallIdx, not_forall]
    refine ⟨i.val, Nat.le_refl _, by scalar_tac, ?_⟩
    rw [List.getElem?_eq_getElem (by scalar_tac), List.getElem?_eq_getElem (by scalar_tac)]
    simp_all
  · rw [r_post, i5_post, forallIdx_step_slice (i := i) ‹_›,
      List.getElem?_eq_getElem (by scalar_tac : start.val + i.val < s.val.length),
      List.getElem?_eq_getElem (by scalar_tac : i.val < lit.val.length)]
    simp_all [UScalar.eq_equiv]
  · simp [forallIdx_end_slice ‹_›]
termination_by lit.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem range_eq_spec (s : alloc.vec.Vec U8) (start e : Usize) (lit : Slice U8)
    (h : start.val ≤ e.val) (he : e.val ≤ s.length) :
    validate.resource.range_eq s start e lit ⦃ r => r = true ↔ uriSeg s.val start.val e.val = lit.val ⦄ := by
  unfold validate.resource.range_eq
  step*
  · simp only [Bool.false_eq_true, false_iff]
    intro h2; have := congrArg List.length h2; simp [uriSeg] at this; scalar_tac
  · rw [r_post, forallIdx_zero]
    have hlen : (uriSeg s.val start.val e.val).length = lit.val.length := by simp [uriSeg]; scalar_tac
    constructor
    · intro h2; apply List.ext_getElem? ; intro q
      by_cases hq : q < lit.val.length
      · rw [← h2 q hq]; simp [uriSeg, List.getElem?_take, List.getElem?_drop]; scalar_tac
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · intro h2 q hq
      rw [← h2]; simp [uriSeg, List.getElem?_take, List.getElem?_drop]; scalar_tac

-- 引数の区間: '=' を含み、属性名 (最初の '=' の前) が空でない
def paramOk (p : List U8) : Prop := (∃ c ∈ p, c.val = 61) ∧ ∀ c, p.head? = some c → c.val ≠ 61

theorem uriSeg_getElem? (u : List U8) (a b k : Nat) :
    (uriSeg u a b)[k]? = if k < b - a then u[a + k]? else none := by
  unfold uriSeg
  rw [List.getElem?_take, List.getElem?_drop]

theorem uri_u8_val_eq_iff (c d : U8) : c.val = d.val ↔ c = d := by
  rw [UScalar.eq_equiv]

theorem paramOk_iff (u : List U8) (a b q : Nat) (h0 : a ≤ q) (h1 : q ≤ b)
    (h2 : q < b → u[q]? = some 61#u8) (h3 : ∀ j, a ≤ j → j < q → u[j]? ≠ some 61#u8) :
    paramOk (uriSeg u a b) ↔ a < q ∧ q < b := by
  have e61 : ∀ c : U8, c.val = 61 ↔ c = 61#u8 := fun c => uri_u8_val_eq_iff c 61#u8
  unfold paramOk
  simp only [List.mem_iff_getElem?, uriSeg_getElem?, List.head?_eq_getElem?, e61]
  constructor
  · rintro ⟨⟨c, ⟨k, hk⟩, rfl⟩, hh⟩
    split at hk
    · have hqb : q < b := by
        by_contra hc
        exact h3 (a + k) (by omega) (by omega) hk
      refine ⟨?_, hqb⟩
      by_contra hc
      have hq : q = a := by omega
      subst hq
      have := hh 61#u8
      simp only [show 0 < b - q by omega, ↓reduceIte, Nat.add_zero, h2 hqb, true_implies] at this
      exact this rfl
    · simp at hk
  · rintro ⟨hq1, hq2⟩
    refine ⟨⟨61#u8, ⟨q - a, ?_⟩, rfl⟩, fun c hc => ?_⟩
    · simp only [show q - a < b - a by omega, ↓reduceIte, show a + (q - a) = q by omega, h2 hq2]
    · simp only [show 0 < b - a by omega, ↓reduceIte, Nat.add_zero] at hc
      intro he; rw [e61] at he; subst he; exact h3 a (Nat.le_refl _) hq1 hc

@[step]
theorem parameter_ok_spec (uri : alloc.vec.Vec U8) (start e : Usize) (h : start.val ≤ e.val) (he : e.val ≤ uri.length) :
    validate.resource.parameter_ok uri start e ⦃ r => r = true ↔ paramOk (uriSeg uri.val start.val e.val) ⦄ := by
  unfold validate.resource.parameter_ok
  step*
  all_goals rw [paramOk_iff _ _ _ _ eq_post eq_post1 eq_post2 eq_post3]
  · simp only [decide_eq_true_eq]; scalar_tac
  · simp only [Bool.false_eq_true, false_iff, not_and]; scalar_tac

theorem uriSeg_length (u : List U8) (a b : Nat) (hb : b ≤ u.length) : (uriSeg u a b).length = b - a := by
  simp [uriSeg]; omega

theorem uriSeg_get (u : List U8) (a b : Nat) (L : List U8) (h : uriSeg u a b = L) (hb : b ≤ u.length) :
    b - a = L.length ∧ ∀ k, k < L.length → u[a + k]? = L[k]? := by
  have hl := uriSeg_length u a b hb
  rw [h] at hl
  refine ⟨hl.symm, fun k hk => ?_⟩
  rw [← h, uriSeg_getElem?]; simp [show k < b - a by omega]

theorem uriSeg_sub (u : List U8) (a b m n : Nat) (L : List U8) (h : uriSeg u a b = L) (hb : b ≤ u.length)
    (hmn : m + n ≤ L.length) : uriSeg u (a + m) (a + m + n) = (L.drop m).take n := by
  obtain ⟨h1, h2⟩ := uriSeg_get u a b L h hb
  apply List.ext_getElem?; intro k
  rw [uriSeg_getElem?, List.getElem?_take, List.getElem?_drop]
  simp only [show a + m + n - (a + m) = n by omega]
  split
  · rw [show a + m + k = a + (m + k) by omega, h2 _ (by omega)]
  · rfl

-- 2 つの「最初の出現位置」は一致する
theorem uri_first_unique (u : List U8) (b : U8) (i t q x : Nat) (hq0 : i ≤ q) (hq1 : q ≤ t)
    (hq2 : q < t → u[q]? = some b) (hq3 : ∀ j, i ≤ j → j < q → u[j]? ≠ some b)
    (hx0 : i ≤ x) (hx1 : x ≤ t) (hx2 : x < t → u[x]? = some b) (hx3 : ∀ j, i ≤ j → j < x → u[j]? ≠ some b) :
    q = x := by
  rcases Nat.lt_trichotomy q x with h | h | h
  · exact absurd (hq2 (by omega)) (hx3 q hq0 h)
  · exact h
  · exact absurd (hx2 (by omega)) (hq3 x hx0 h)

theorem flatMap_semi_ne_nil (ps : List (List U8)) (h : ps ≠ []) : ps.flatMap (fun p => 59#u8 :: p) ≠ [] := by
  cases ps with
  | nil => exact absurd rfl h
  | cons p ps => simp

theorem lit_base64 : lit "base64" = [98#u8, 97#u8, 115#u8, 101#u8, 54#u8, 52#u8] := rfl

theorem not_paramOk_base64 : ¬ paramOk (lit "base64") := by
  rw [lit_base64]; unfold paramOk; simp

theorem params_split (u : List U8) (sg comma e : Nat) (hc : comma ≤ u.length) (hs : sg < comma)
    (he0 : sg + 1 ≤ e) (he1 : e ≤ comma) (he2 : e < comma → u[e]? = some 59#u8)
    (he3 : ∀ j, sg + 1 ≤ j → j < e → u[j]? ≠ some 59#u8) (params : List (List U8))
    (hp : uriSeg u sg comma = params.flatMap (fun p => 59#u8 :: p)) (hnp : ∀ p ∈ params, ∀ c ∈ p, c.val ≠ 59) :
    ∃ p rest, params = p :: rest ∧ uriSeg u (sg + 1) e = p ∧
      uriSeg u e comma = rest.flatMap (fun p => 59#u8 :: p) ∧ (e = comma ↔ rest = []) := by
  have hlen := uriSeg_length u sg comma hc
  cases params with
  | nil => simp [hp] at hlen; omega
  | cons p rest =>
    refine ⟨p, rest, rfl, ?_⟩
    simp only [List.flatMap_cons, List.cons_append] at hp
    obtain ⟨g1, g2⟩ := uriSeg_get u sg comma _ hp hc
    simp only [List.length_cons, List.length_append] at g1
    have hpn : ∀ c ∈ p, c.val ≠ 59 := hnp p (List.mem_cons_self ..)
    have hx : e = sg + 1 + p.length := by
      apply uri_first_unique u 59#u8 (sg + 1) comma e (sg + 1 + p.length) he0 he1 he2 he3 (by omega) (by omega)
      · intro hlt
        have := g2 (1 + p.length) (by simp only [List.length_cons, List.length_append]; omega)
        rw [show sg + (1 + p.length) = sg + 1 + p.length by omega] at this
        rw [this]
        cases rest with
        | nil => simp at hlt g1; omega
        | cons r0 rs => simp
      · intro j hj1 hj2
        have := g2 (j - sg) (by simp only [List.length_cons, List.length_append]; omega)
        rw [show sg + (j - sg) = j by omega] at this
        rw [this, show j - sg = (j - sg - 1) + 1 by omega, List.getElem?_cons_succ,
          List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
        intro h; simp only [Option.some.injEq] at h
        exact hpn _ (List.getElem_mem _) (by rw [h]; rfl)
    subst hx
    refine ⟨?_, ?_, ?_⟩
    · have := uriSeg_sub u sg comma 1 p.length _ hp hc (by simp only [List.length_cons, List.length_append]; omega)
      rw [show sg + 1 + p.length = sg + 1 + p.length from rfl, this]
      simp
    · have := uriSeg_sub u sg comma (1 + p.length) (rest.flatMap (fun p => 59#u8 :: p)).length _ hp hc (by simp only [List.length_cons, List.length_append]; omega)
      rw [show sg + (1 + p.length) = sg + 1 + p.length by omega,
        show sg + 1 + p.length + (rest.flatMap (fun p => 59#u8 :: p)).length = comma by omega] at this
      rw [this, show 1 + p.length = (p.length + 1) by omega, ← List.drop_drop]
      simp
    · constructor
      · intro h
        have : (rest.flatMap (fun p => 59#u8 :: p)).length = 0 := by omega
        by_contra hne
        exact flatMap_semi_ne_nil rest hne (List.eq_nil_of_length_eq_zero this)
      · intro h; subst h; simp at g1; omega

-- 区間 [uriSeg, comma) が ';' で始まる引数の列 params に分かれるときの結果
@[step]
theorem parameters_loop_spec (uri : alloc.vec.Vec U8) (comma sg : Usize) (hs : sg.val ≤ comma.val)
    (hc : comma.val ≤ uri.length) :
    validate.resource.parameters_loop uri comma sg ⦃ r => ∀ params : List (List U8),
      uriSeg uri.val sg.val comma.val = params.flatMap (fun p => 59#u8 :: p) →
      (∀ p ∈ params, ∀ c ∈ p, c.val ≠ 59) →
      (r = some true ↔ params.getLast? = some (lit "base64") ∧ ∀ p ∈ params.dropLast, paramOk p) ∧
      (r = some false ↔ ∀ p ∈ params, paramOk p) ⦄ := by
  unfold validate.resource.parameters_loop
  step*
  · -- 最後の区間が base64
    intro params hp hnp
    obtain ⟨p, rest, rfl, hp1, -, hpe⟩ := params_split _ _ _ _ hc (by scalar_tac) (by scalar_tac) end_post1
      end_post2 (by rw [← start_post]; exact end_post3) params hp hnp
    have hE : «end».val = comma.val := by scalar_tac
    have hr : rest = [] := hpe.mp hE
    subst hr
    have hpb : p = lit "base64" := by
      have := b_post.mp ‹_›
      rw [s_post, array_make_to_slice_val, start_post] at this
      rw [← hp1, hE, this]; rfl
    subst hpb
    simp [not_paramOk_base64]
  · -- 最後の区間が通常の引数
    have hp := r_post1; have hnp := r_post2
    obtain ⟨p, rest, rfl, hp1, -, hpe⟩ := params_split _ _ _ _ hc (by scalar_tac) (by scalar_tac) end_post1
      end_post2 (by rw [← start_post]; exact end_post3) params hp hnp
    have hE : «end».val = comma.val := by scalar_tac
    have hr : rest = [] := hpe.mp hE
    subst hr
    have hp1' : uriSeg uri.val start.val comma.val = p := by rw [start_post, ← hE]; exact hp1
    have hnb : p ≠ lit "base64" := by
      intro h; apply ‹¬b = true›; rw [b_post, s_post, array_make_to_slice_val, hp1', h]; rfl
    have hok : paramOk p := by rw [← hp1']; exact b1_post.mp ‹_›
    have := r_post [] (by simp [uriSeg]) (by simp)
    simp only [List.getLast?_nil, reduceCtorEq, List.dropLast_nil, List.not_mem_nil, false_iff,
      false_and, iff_true] at this
    simp only [List.getLast?_singleton, Option.some.injEq, hnb, List.dropLast_singleton, false_and,
      iff_false, List.mem_singleton, forall_eq, hok, iff_true]
    rcases r with _ | _ | _ <;> simp_all
  · intro params hp hnp
    obtain ⟨p, rest, rfl, hp1, -, hpe⟩ := params_split _ _ _ _ hc (by scalar_tac) (by scalar_tac) end_post1
      end_post2 (by rw [← start_post]; exact end_post3) params hp hnp
    have hE : «end».val = comma.val := by scalar_tac
    have hr : rest = [] := hpe.mp hE
    subst hr
    have hp1' : uriSeg uri.val start.val comma.val = p := by rw [start_post, ← hE]; exact hp1
    have hnb : p ≠ lit "base64" := by
      intro h; apply ‹¬b = true›; rw [b_post, s_post, array_make_to_slice_val, hp1', h]; rfl
    have hok : ¬ paramOk p := by rw [← hp1']; exact fun h => ‹¬b1 = true› (b1_post.mpr h)
    simp [hnb, hok]
  · -- 途中の区間
    have hp := r_post1; have hnp := r_post2
    obtain ⟨p, rest, rfl, hp1, hp2, hpe⟩ := params_split _ _ _ _ hc (by scalar_tac) (by scalar_tac) end_post1
      end_post2 (by rw [← start_post]; exact end_post3) params hp hnp
    have hE : «end».val ≠ comma.val := by scalar_tac
    have hok : paramOk p := by rw [← hp1, ← start_post]; exact b1_post.mp ‹_›
    obtain ⟨r1, r2⟩ := r_post rest hp2 (fun q hq => hnp q (List.mem_cons_of_mem _ hq))
    cases rest with
    | nil => exact absurd (hpe.mpr rfl) hE
    | cons q rs =>
      rw [r1, r2]
      simp [List.dropLast_cons₂, hok]
  · intro params hp hnp
    obtain ⟨p, rest, rfl, hp1, -, hpe⟩ := params_split _ _ _ _ hc (by scalar_tac) (by scalar_tac) end_post1
      end_post2 (by rw [← start_post]; exact end_post3) params hp hnp
    have hE : «end».val ≠ comma.val := by scalar_tac
    have hok : ¬ paramOk p := by rw [← hp1, ← start_post]; exact fun h => ‹¬b1 = true› (b1_post.mpr h)
    cases rest with
    | nil => exact absurd (hpe.mpr rfl) hE
    | cons q rs => simp [List.dropLast_cons₂, hok]
  · intro params hp hnp
    have : uriSeg uri.val sg.val comma.val = [] := by simp [uriSeg]; scalar_tac
    rw [this] at hp
    cases params with
    | nil => simp
    | cons p ps => simp at hp
termination_by comma.val - sg.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem base64_chars_ok_loop_spec (uri : alloc.vec.Vec U8) (e i : Usize) (he : e.val ≤ uri.length) :
    validate.resource.base64_chars_ok_loop uri e i ⦃ r => r = true ↔ forallIdx e.val i.val (fun j => base64CharB uri.val[j]!) ⦄ := by
  unfold validate.resource.base64_chars_ok_loop
  step*
  all_goals first
    | (simp only [uri_forallIdx_end (show e.val ≤ i.val by scalar_tac)]; done)
    | (rw [uri_forallIdx_step (by scalar_tac), getElem!_pos uri.val i.val (by scalar_tac), ← i1_post]
       try rw [r_post, i2_post]
       simp only [← b_post]
       agrind)
termination_by e.val - i.val
decreasing_by all_goals scalar_decr_tac

-- base64 データ: 長さは 4 の倍数、末尾に高々 2 個の '='、それ以外は base64 文字。復号長は 3·len/4 − pad
def base64Len (d : List U8) (n : Nat) : Prop :=
  d.length % 4 = 0 ∧ ∃ pad ≤ 2, pad ≤ d.length ∧
    (∀ i (h : i < d.length), (i < d.length - pad → base64CharB d[i]) ∧ (d.length - pad ≤ i → d[i].val = 61)) ∧
    n = d.length / 4 * 3 - pad

theorem base64CharB_ne (c : U8) (h : base64CharB c) : c.val ≠ 61 := by
  unfold base64CharB isAlphaB at h; omega

theorem base64Len_iff (d : List U8) (pad m : Nat) (h4 : d.length % 4 = 0)
    (hpad : pad = if 0 < d.length ∧ d[d.length - 1]? = some 61#u8 then
      (if d[d.length - 2]? = some 61#u8 then 2 else 1) else 0) :
    base64Len d m ↔ (∀ i, i < d.length - pad → base64CharB d[i]!) ∧ m = d.length / 4 * 3 - pad := by
  have e61 : ∀ c : U8, c.val = 61 ↔ c = 61#u8 := fun c => uri_u8_val_eq_iff c 61#u8
  have h4' : d.length = 0 ∨ 4 ≤ d.length := by omega
  unfold base64Len
  constructor
  · rintro ⟨-, p, hp2, hpl, hc, rfl⟩
    -- '=' の位置は末尾 p 個に限る
    have hq : ∀ i (h : i < d.length), d[i].val = 61 ↔ d.length - p ≤ i := by
      intro i h
      constructor
      · intro h1; by_contra h2; exact base64CharB_ne _ ((hc i h).1 (by omega)) h1
      · intro h1; exact (hc i h).2 h1
    have : pad = p := by
      rcases h4' with h0 | h0
      · subst hpad; simp only [h0, Nat.lt_irrefl, false_and, ↓reduceIte]; omega
      · have g1 := hq (d.length - 1) (by omega)
        have g2 := hq (d.length - 2) (by omega)
        rw [e61] at g1 g2
        rw [List.getElem?_eq_getElem (by omega : d.length - 1 < d.length),
          List.getElem?_eq_getElem (by omega : d.length - 2 < d.length)] at hpad
        simp only [Option.some.injEq, g1, g2, show 0 < d.length by omega, true_and] at hpad
        split at hpad <;> (try split at hpad) <;> omega
    subst this
    refine ⟨fun i hi => ?_, rfl⟩
    rw [getElem!_pos d i (by omega)]; exact (hc i (by omega)).1 hi
  · rintro ⟨hc, rfl⟩
    refine ⟨h4, pad, ?_, ?_, fun i h => ⟨fun hi => ?_, fun hi => ?_⟩, rfl⟩
    · subst hpad; split <;> (try split) <;> omega
    · subst hpad; split <;> (try split) <;> omega
    · have := hc i hi; rwa [getElem!_pos d i h] at this
    · rw [e61]
      subst hpad
      split at hi
      · rename_i hh
        split at hi
        · rename_i hh2
          rcases (show i = d.length - 1 ∨ i = d.length - 2 by omega) with rfl | rfl
          · have := hh.2; rw [List.getElem?_eq_getElem h] at this; simpa using this
          · rw [List.getElem?_eq_getElem h] at hh2; simpa using hh2
        · have : i = d.length - 1 := by omega
          subst this
          have := hh.2; rw [List.getElem?_eq_getElem h] at this; simpa using this
      · omega

theorem uri_forallIdx_drop (u : List U8) (start e : Nat) (Q : U8 → Prop) (he : e ≤ u.length) :
    forallIdx e start (fun j => Q u[j]!) ↔ ∀ i, i < e - start → Q (u.drop start)[i]! := by
  unfold forallIdx
  constructor
  · intro h i hi
    have : Q u[start + i]! := h (start + i) (by omega) (by omega)
    have hb : i < (u.drop start).length := by simp; omega
    rw [getElem!_pos (u.drop start) i hb, List.getElem_drop]
    rwa [getElem!_pos u (start + i) (by omega)] at this
  · intro h q hq1 hq2
    have := h (q - start) (by omega)
    show Q u[q]!
    rwa [getElem!_pos (u.drop start) (q - start) (by simp; omega), List.getElem_drop,
      ← getElem!_pos u _ (by omega), show start + (q - start) = q by omega] at this

theorem b64_finish (d : List U8) (pad m : Nat) (h4 : d.length % 4 = 0)
    (hpad : pad = if 0 < d.length ∧ d[d.length - 1]? = some 61#u8 then
      (if d[d.length - 2]? = some 61#u8 then 2 else 1) else 0)
    (P : Prop) (hP : P ↔ ∀ i, i < d.length - pad → base64CharB d[i]!) :
    base64Len d m ↔ P ∧ m = d.length / 4 * 3 - pad := by
  rw [base64Len_iff d pad m h4 hpad, hP]

@[step]
theorem base64_length_spec (uri : alloc.vec.Vec U8) (start : Usize) (h : start.val ≤ uri.length) :
    validate.resource.base64_length uri start ⦃ r => ∀ m, base64Len (uri.val.drop start.val) m ↔ ∃ x, r = some x ∧ x.val = m ⦄ := by
  unfold validate.resource.base64_length
  have hd : (uri.val.drop start.val).length = uri.val.length - start.val := by simp
  step*
  · intro m
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    rintro ⟨h4, -⟩
    simp only [bne_iff_ne, ne_eq, UScalar.eq_equiv] at *
    scalar_tac
  · have hi0 : n.val % 4 = 0 := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not, UScalar.eq_equiv] at *; scalar_tac
    have hdl0 : (uri.val.drop start.val).length = n.val := by simp; scalar_tac
    generalize hdd : uri.val.drop start.val = d at hdl0 ⊢
    have h4 : d.length % 4 = 0 := by omega
    split
    next hn =>
      have hn4 : 4 ≤ n.val := by scalar_tac
      have hpos : 0 < d.length := by omega
      step as ⟨q1, hq1, hq1'⟩
      step as ⟨c1, hc1⟩
      have hlast : d[d.length - 1]? = some c1 := by
        rw [← hdd, List.getElem?_drop, hdd, show start.val + (d.length - 1) = q1.val by scalar_tac,
          List.getElem?_eq_getElem (by scalar_tac), hc1]
      split
      next h61 =>
        step as ⟨q2, hq2, hq2'⟩
        step as ⟨c2, hc2⟩
        have hlast2 : d[d.length - 2]? = some c2 := by
          rw [← hdd, List.getElem?_drop, hdd, show start.val + (d.length - 2) = q2.val by scalar_tac,
            List.getElem?_eq_getElem (by scalar_tac), hc2]
        split
        next h61' =>
          step*
          all_goals intro m
          all_goals rw [b64_finish d 2 m h4 (by rw [hlast, hlast2]; simp [h61, h61', hpos]) (b = true)
            (by rw [b_post, uri_forallIdx_drop _ _ _ _ (by scalar_tac), hdd, show i3.val - start.val = d.length - 2 by scalar_tac])]
          all_goals simp_all
          all_goals scalar_tac
        next h61' =>
          step*
          all_goals intro m
          all_goals rw [b64_finish d 1 m h4 (by rw [hlast, hlast2]; simp [h61, h61', hpos]) (b = true)
            (by rw [b_post, uri_forallIdx_drop _ _ _ _ (by scalar_tac), hdd, show i3.val - start.val = d.length - 1 by scalar_tac])]
          all_goals simp_all
          all_goals scalar_tac
      next h61 =>
        step*
        all_goals intro m
        all_goals rw [b64_finish d 0 m h4 (by rw [hlast]; simp [h61]) (b = true)
          (by rw [b_post, uri_forallIdx_drop _ _ _ _ (by scalar_tac), hdd, show i3.val - start.val = d.length - 0 by scalar_tac])]
        all_goals simp_all
        all_goals scalar_tac
    next hn =>
      have hd0 : d.length = 0 := by scalar_tac
      step*
      all_goals intro m
      all_goals rw [b64_finish d 0 m h4 (by simp [hd0]) (b = true)
        (by rw [b_post, uri_forallIdx_drop _ _ _ _ (by scalar_tac), hdd, show i3.val - start.val = d.length - 0 by scalar_tac])]
      all_goals simp_all
      all_goals scalar_tac

-- percent-encoded データ: '%' の後に 16 進数字 2 つ。復号長 n は %XX を 1 文字と数えた文字数
-- (n + 2·(% の個数) = 全体の長さ)
def percentLen (d : List U8) (n : Nat) : Prop :=
  (∀ i (h : i < d.length), d[i].val = 37 → ∃ h2 : i + 2 < d.length, isHexB d[i + 1] ∧ isHexB d[i + 2]) ∧
  n + 2 * d.countP (fun c => c.val = 37) = d.length

theorem isHexB_ne (c : U8) (h : isHexB c) : c.val ≠ 37 := by unfold isHexB at h; omega

def pctCnt (u : List U8) (i : Nat) : Nat := (u.drop i).countP (fun c => c.val = 37)

theorem pct_step_plain (u : List U8) (i : Nat) (hi : i < u.length) (hc : u[i].val ≠ 37) :
    (pctFrom u i ↔ pctFrom u (i + 1)) ∧ pctCnt u i = pctCnt u (i + 1) := by
  refine ⟨?_, ?_⟩
  · rw [pctFrom_step _ _ hi]; simp [hc]
  · unfold pctCnt
    rw [List.drop_eq_getElem_cons hi]
    simp only [List.countP_cons, hc, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem pct_step_pct (u : List U8) (i : Nat) (hi : i + 2 < u.length) (hc : u[i].val = 37)
    (h1 : isHexB u[i + 1]) (h2 : isHexB u[i + 2]) :
    (pctFrom u i ↔ pctFrom u (i + 3)) ∧ pctCnt u i = pctCnt u (i + 3) + 1 := by
  have n1 := isHexB_ne _ h1
  have n2 := isHexB_ne _ h2
  refine ⟨?_, ?_⟩
  · rw [pctFrom_step _ _ (by omega), pctFrom_step _ (i + 1) (by omega), pctFrom_step _ (i + 1 + 1) (by omega)]
    simp only [n1, n2, false_imp_iff, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun _ => ⟨hi, h1, h2⟩, h⟩⟩
  · unfold pctCnt
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega : i + 1 < u.length),
      List.drop_eq_getElem_cons (by omega : i + 1 + 1 < u.length)]
    simp only [List.countP_cons, hc, n1, n2, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem pct_fail (u : List U8) (i : Nat) (hi : i < u.length) (hc : u[i].val = 37)
    (hf : ¬ ∃ h2 : i + 2 < u.length, isHexB u[i + 1] ∧ isHexB u[i + 2]) : ¬ pctFrom u i := by
  rw [pctFrom_step _ _ hi]; exact fun h => hf (h.1 hc)

@[step]
theorem percent_length_loop_spec (uri : alloc.vec.Vec U8) (len : U64) (i : Usize)
    (hi : i.val ≤ uri.length) (hl : len.val ≤ i.val) :
    validate.resource.percent_length_loop uri len i ⦃ r => ∀ m, (pctFrom uri.val i.val ∧
      m + 2 * pctCnt uri.val i.val = len.val + (uri.val.drop i.val).length) ↔ ∃ x, r = some x ∧ x.val = m ⦄ := by
  unfold validate.resource.percent_length_loop
  have hmax := usize_max_le_u64
  step*
  all_goals first
    | (have hlt : i.val < uri.val.length := by scalar_tac
       have hc : uri.val[i.val].val = 37 := by
         have h' : i2.val = 37 := by scalar_tac
         rw [i2_post] at h'; exact h'
       intro m
       simp only [reduceCtorEq, false_and, exists_false, iff_false, not_and]
       intro hp
       refine absurd hp (pct_fail _ _ hlt hc ?_)
       rintro ⟨h2, hx, hy⟩
       first
       | scalar_tac
       | (apply ‹¬b = true›; rw [b_post, i6_post]; rwa [getElem_idx_eq (l := uri.val) i5_post (by scalar_tac) (by scalar_tac)])
       | (apply ‹¬b1 = true›; rw [b1_post, i8_post]; rwa [getElem_idx_eq (l := uri.val) i7_post (by scalar_tac) (by scalar_tac)]))
    | (have hlt : i.val < uri.val.length := by scalar_tac
       have hc : uri.val[i.val].val ≠ 37 := by
         have h' : i2.val ≠ 37 := by intro h; apply ‹¬i2 = 37#u8›; scalar_tac
         rw [i2_post] at h'; exact h'
       obtain ⟨e1, e2⟩ := pct_step_plain uri.val i.val hlt hc
       rw [e1, e2, ← r_post m, i9_post, len1_post]
       simp only [List.length_drop]
       constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
    | (have hge : uri.val.length ≤ i.val := by scalar_tac
       intro m
       simp only [pctCnt, List.drop_eq_nil_of_le hge, pctFrom_end _ _ hge, List.countP_nil, true_and,
         List.length_nil, Nat.mul_zero, Nat.add_zero, Option.some.injEq, exists_eq_left']
       constructor <;> intro h <;> scalar_tac)
    | (have hlt : i.val + 2 < uri.val.length := by scalar_tac
       have hc : uri.val[i.val].val = 37 := by
         have h' : i2.val = 37 := by scalar_tac
         rw [i2_post] at h'; exact h'
       have hx : isHexB uri.val[i.val + 1] := by
         have := b_post.mp ‹_›; rw [i6_post] at this; rwa [getElem_idx_eq (l := uri.val) i5_post (by scalar_tac) (by scalar_tac)] at this
       have hy : isHexB uri.val[i.val + 2] := by
         have := b1_post.mp ‹_›; rw [i8_post] at this; rwa [getElem_idx_eq (l := uri.val) i7_post (by scalar_tac) (by scalar_tac)] at this
       obtain ⟨e1, e2⟩ := pct_step_pct uri.val i.val hlt hc hx hy
       rw [e1, e2, ← r_post m, i9_post, len1_post]
       simp only [List.length_drop]
       constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩)
termination_by uri.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem pctFrom_drop (u : List U8) (s : Nat) :
    pctFrom u s ↔ ∀ i (h : i < (u.drop s).length), (u.drop s)[i].val = 37 →
      ∃ h2 : i + 2 < (u.drop s).length, isHexB (u.drop s)[i + 1] ∧ isHexB (u.drop s)[i + 2] := by
  unfold pctFrom
  simp only [List.length_drop, List.getElem_drop]
  constructor
  · intro h i hi hc
    obtain ⟨h2, hx, hy⟩ := h (s + i) (by omega) (by omega) hc
    have e1 : s + (i + 1) = s + i + 1 := by omega
    have e2 : s + (i + 2) = s + i + 2 := by omega
    refine ⟨by omega, ?_, ?_⟩
    · simp only [e1]; exact hx
    · simp only [e2]; exact hy
  · intro h j hj hjl hc
    have e0 : s + (j - s) = j := by omega
    have := h (j - s) (by omega) (by simp only [e0]; exact hc)
    obtain ⟨h2, hx, hy⟩ := this
    refine ⟨by omega, ?_, ?_⟩
    · have e : s + (j - s + 1) = j + 1 := by omega
      simp only [e] at hx; exact hx
    · have e : s + (j - s + 2) = j + 2 := by omega
      simp only [e] at hy; exact hy

@[step]
theorem percent_length_spec (uri : alloc.vec.Vec U8) (start : Usize) (h : start.val ≤ uri.length) :
    validate.resource.percent_length uri start ⦃ r => ∀ m, percentLen (uri.val.drop start.val) m ↔ ∃ x, r = some x ∧ x.val = m ⦄ := by
  unfold validate.resource.percent_length
  step*
  rw [← r_post m, percentLen, ← pctFrom_drop]
  simp [pctCnt]

-- data_uri(u) (RFC 2397): "data:" mediatype *(";" 引数) [";base64"] "," data。media は媒体型、n は復号長
-- RFC 2397: data URL の構文
def dataUri (u media : List U8) (n : Nat) : Prop :=
  ∃ (params : List (List U8)) (data : List U8), u = lit "data:" ++ media ++ params.flatMap (fun p => 59#u8 :: p) ++ 44#u8 :: data ∧
    (∀ c ∈ media, c.val ≠ 44 ∧ c.val ≠ 59) ∧ (∀ p ∈ params, ∀ c ∈ p, c.val ≠ 44 ∧ c.val ≠ 59) ∧
    ((params.getLast? = some (lit "base64") ∧ (∀ p ∈ params.dropLast, paramOk p) ∧ base64Len data n) ∨
     ((∀ p ∈ params, paramOk p) ∧ percentLen data n))

theorem uri_drop_split (u : List U8) (a b : Nat) (h : a ≤ b) : u.drop a = uriSeg u a b ++ u.drop b := by
  unfold uriSeg
  conv => lhs; rw [← List.take_append_drop (b - a) (u.drop a)]
  rw [List.drop_drop, show a + (b - a) = b by omega]

theorem split_semi : ∀ (n : Nat) (t : List U8), t.length ≤ n → (t = [] ∨ t.head? = some 59#u8) →
    ∃ params : List (List U8), t = params.flatMap (fun p => 59#u8 :: p) ∧ ∀ p ∈ params, ∀ c ∈ p, c ≠ 59#u8 := by
  intro n
  induction n with
  | zero => intro t ht _; exact ⟨[], by simp_all, by simp⟩
  | succ n ih =>
    intro t ht h
    rcases h with rfl | h
    · exact ⟨[], by simp, by simp⟩
    · cases t with
      | nil => simp at h
      | cons c rest =>
        simp only [List.head?_cons, Option.some.injEq] at h
        subst h
        have hsplit := List.takeWhile_append_dropWhile (p := fun c => decide (c ≠ 59#u8)) (l := rest)
        have hlen : (rest.dropWhile (fun c => decide (c ≠ 59#u8))).length ≤ n := by
          have := congrArg List.length hsplit; simp only [List.length_append, List.length_cons] at this ht; omega
        have hhead : rest.dropWhile (fun c => decide (c ≠ 59#u8)) = [] ∨
            (rest.dropWhile (fun c => decide (c ≠ 59#u8))).head? = some 59#u8 := by
          rcases hd : rest.dropWhile (fun c => decide (c ≠ 59#u8)) with _ | ⟨d, ds⟩
          · exact Or.inl rfl
          · right
            have := List.head?_dropWhile_not (fun c => decide (c ≠ 59#u8)) rest
            rw [hd] at this
            simp only [List.head?_cons, decide_eq_false_iff_not, Decidable.not_not] at this
            simp [this]
        obtain ⟨ps, hps, hpc⟩ := ih _ hlen hhead
        refine ⟨rest.takeWhile (fun c => decide (c ≠ 59#u8)) :: ps, ?_, ?_⟩
        · simp only [List.flatMap_cons, List.cons_append]
          rw [← hps, hsplit]
        · intro p hp c hc
          rcases List.mem_cons.mp hp with rfl | hp
          · have := List.all_takeWhile (l := rest) (p := fun c => decide (c ≠ 59#u8))
            rw [List.all_eq_true] at this
            simpa using this c hc
          · exact hpc p hp c hc

theorem mem_uriSeg (u : List U8) (a b : Nat) (y : U8) (h : y ∈ uriSeg u a b) :
    ∃ j, a ≤ j ∧ j < b ∧ u[j]? = some y := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h
  rw [uriSeg_getElem?] at hk
  split at hk
  · exact ⟨a + k, by omega, by omega, hk⟩
  · simp at hk

theorem lit_data_length : (lit "data:").length = 5 := rfl

theorem mem_flat_ne (params : List (List U8)) (y : U8) (hy : y ∈ params.flatMap (fun p => 59#u8 :: p))
    (hp : ∀ p ∈ params, ∀ c ∈ p, c.val ≠ 44 ∧ c.val ≠ 59) : y.val ≠ 44 := by
  obtain ⟨p, hp1, hp2⟩ := List.mem_flatMap.mp hy
  rcases List.mem_cons.mp hp2 with rfl | hp2
  · simp
  · exact (hp p hp1 y hp2).1

-- comma と media_end が最初の ',' と ';' のとき、data URI の分解は一意に定まる
theorem data_decomp (u : List U8) (h : lit "data:" <+: u) (c me : Nat) (hc0 : 5 ≤ c) (hc1 : c < u.length)
    (hc2 : u[c]? = some 44#u8) (hc3 : ∀ j, 5 ≤ j → j < c → u[j]? ≠ some 44#u8)
    (hm0 : 5 ≤ me) (hm1 : me ≤ c) (hm2 : me < c → u[me]? = some 59#u8)
    (hm3 : ∀ j, 5 ≤ j → j < me → u[j]? ≠ some 59#u8) (media : List U8) (n : Nat) :
    dataUri u media n ↔ media = uriSeg u 5 me ∧ ∃ params : List (List U8),
      uriSeg u me c = params.flatMap (fun p => 59#u8 :: p) ∧ (∀ p ∈ params, ∀ x ∈ p, x.val ≠ 44 ∧ x.val ≠ 59) ∧
      ((params.getLast? = some (lit "base64") ∧ (∀ p ∈ params.dropLast, paramOk p) ∧ base64Len (u.drop (c + 1)) n) ∨
       ((∀ p ∈ params, paramOk p) ∧ percentLen (u.drop (c + 1)) n)) := by
  constructor
  · rintro ⟨params, data, hu, hmed, hpar, hrest⟩
    let P := params.flatMap (fun p => 59#u8 :: p)
    have hW : u.drop 5 = media ++ (P ++ 44#u8 :: data) := by
      rw [hu, List.append_assoc, List.append_assoc, ← lit_data_length, List.drop_left]
    have hg : ∀ k, u[5 + k]? = (media ++ (P ++ 44#u8 :: data))[k]? := by
      intro k; rw [← hW, List.getElem?_drop]
    have hlenu : u.length = 5 + (media.length + (P.length + 1 + data.length)) := by
      have := congrArg List.length hW; simp only [List.length_drop, List.length_append, List.length_cons] at this
      omega
    -- ',' の位置
    have hcx : c = 5 + media.length + P.length := by
      apply uri_first_unique u 44#u8 5 u.length c _ hc0 (by omega) (fun _ => hc2) hc3 (by omega) (by omega)
      · intro _
        rw [show 5 + media.length + P.length = 5 + (media.length + P.length) by omega, hg,
          List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp
      · intro j hj1 hj2 hj
        rw [show j = 5 + (j - 5) by omega, hg] at hj
        rw [← List.append_assoc, List.getElem?_append_left (by simp; omega)] at hj
        have hmem := List.mem_of_getElem? hj
        rcases List.mem_append.mp hmem with hm | hm
        · exact (hmed _ hm).1 rfl
        · exact mem_flat_ne params _ hm hpar rfl
    -- ';' の位置
    have hmx : me = 5 + media.length := by
      apply uri_first_unique u 59#u8 5 c me _ hm0 hm1 hm2 hm3 (by omega) (by omega)
      · intro hlt
        rw [hg, List.getElem?_append_right (by omega), Nat.sub_self]
        cases params with
        | nil => simp [P] at hcx; omega
        | cons p ps => simp [P]
      · intro j hj1 hj2 hj
        rw [show j = 5 + (j - 5) by omega, hg, List.getElem?_append_left (by omega)] at hj
        exact (hmed _ (List.mem_of_getElem? hj)).2 rfl
    refine ⟨?_, params, ?_, hpar, ?_⟩
    · unfold uriSeg; rw [hW, hmx, show 5 + media.length - 5 = media.length by omega]; simp
    · unfold uriSeg
      rw [hmx, hcx, ← List.drop_drop, hW, show 5 + media.length + P.length - (5 + media.length) = P.length by omega]
      simp [P]
    · have hd : u.drop (c + 1) = data := by
        rw [hcx, show 5 + media.length + P.length + 1 = 5 + (media.length + (P.length + 1)) by omega,
          ← List.drop_drop, hW, ← List.drop_drop]
        simp
      rw [hd]; exact hrest
  · rintro ⟨rfl, params, hP, hpar, hrest⟩
    refine ⟨params, u.drop (c + 1), ?_, ?_, hpar, hrest⟩
    · have ht : u.take 5 = lit "data:" := by
        have := List.prefix_iff_eq_take.mp h; rw [lit_data_length] at this; exact this.symm
      conv => lhs; rw [← List.take_append_drop 5 u]
      rw [ht, uri_drop_split u 5 me hm0, uri_drop_split u me c hm1, ← hP, List.drop_eq_getElem_cons hc1]
      have : u[c] = 44#u8 := by rw [List.getElem?_eq_getElem hc1] at hc2; simpa using hc2
      rw [this]; simp only [List.append_assoc]
    · intro y hy
      obtain ⟨j, hj1, hj2, hj⟩ := mem_uriSeg u 5 me y hy
      exact ⟨fun e => hc3 j hj1 (by omega) (by rw [hj, (uri_u8_val_eq_iff y 44#u8).mp e]),
        fun e => hm3 j hj1 hj2 (by rw [hj, (uri_u8_val_eq_iff y 59#u8).mp e])⟩

theorem dataUri_has_comma (u media : List U8) (n : Nat) (h : dataUri u media n) :
    ∃ c, 5 ≤ c ∧ c < u.length ∧ u[c]? = some 44#u8 := by
  obtain ⟨params, data, hu, -⟩ := h
  generalize params.flatMap (fun p => 59#u8 :: p) = P at hu
  refine ⟨5 + media.length + P.length, by omega, ?_, ?_⟩
  · rw [hu]; simp [lit_data_length]; omega
  · rw [hu, List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp [lit_data_length]; omega)]
    rw [List.getElem?_append_right (by simp [lit_data_length]; omega),
      List.getElem?_append_right (by simp [lit_data_length]; omega)]
    simp only [lit_data_length]
    rw [show 5 + media.length + P.length - 5 - media.length - P.length = 0 by omega]; rfl

theorem params_exist (u : List U8) (me c : Nat) (hm1 : me ≤ c) (hc1 : c ≤ u.length)
    (hm2 : me < c → u[me]? = some 59#u8) (hc3 : ∀ j, 5 ≤ j → j < c → u[j]? ≠ some 44#u8) (hm0 : 5 ≤ me) :
    ∃ params : List (List U8), uriSeg u me c = params.flatMap (fun p => 59#u8 :: p) ∧
      ∀ p ∈ params, ∀ x ∈ p, x.val ≠ 44 ∧ x.val ≠ 59 := by
  have hh : uriSeg u me c = [] ∨ (uriSeg u me c).head? = some 59#u8 := by
    by_cases hlt : me < c
    · right; rw [List.head?_eq_getElem?, uriSeg_getElem?]; simp [show 0 < c - me by omega, hm2 hlt]
    · left; simp [uriSeg, show c - me = 0 by omega]
  obtain ⟨params, hps, hpc⟩ := split_semi _ _ (Nat.le_refl _) hh
  refine ⟨params, hps, fun p hp x hx => ⟨fun e => ?_, fun e => hpc p hp x hx ((uri_u8_val_eq_iff x 59#u8).mp e)⟩⟩
  have : x ∈ uriSeg u me c := by rw [hps]; exact List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_of_mem _ hx⟩
  obtain ⟨j, hj1, hj2, hj⟩ := mem_uriSeg u me c x this
  exact hc3 j (by omega) hj2 (by rw [hj, (uri_u8_val_eq_iff x 44#u8).mp e])

theorem decomp_simpl (u : List U8) (me c : Nat)
    (hex : ∃ params : List (List U8), uriSeg u me c = params.flatMap (fun p => 59#u8 :: p) ∧
      ∀ p ∈ params, ∀ x ∈ p, x.val ≠ 44 ∧ x.val ≠ 59)
    (o : Option Bool) (ho : ∀ params : List (List U8), uriSeg u me c = params.flatMap (fun p => 59#u8 :: p) →
      (∀ p ∈ params, ∀ c ∈ p, c.val ≠ 59) →
      (o = some true ↔ params.getLast? = some (lit "base64") ∧ ∀ p ∈ params.dropLast, paramOk p) ∧
      (o = some false ↔ ∀ p ∈ params, paramOk p)) (B64 PCT : Prop) :
    (∃ params : List (List U8),
      uriSeg u me c = params.flatMap (fun p => 59#u8 :: p) ∧ (∀ p ∈ params, ∀ x ∈ p, x.val ≠ 44 ∧ x.val ≠ 59) ∧
      ((params.getLast? = some (lit "base64") ∧ (∀ p ∈ params.dropLast, paramOk p) ∧ B64) ∨
       ((∀ p ∈ params, paramOk p) ∧ PCT))) ↔ (o = some true ∧ B64) ∨ (o = some false ∧ PCT) := by
  constructor
  · rintro ⟨params, hps, hpc, hr⟩
    obtain ⟨hA, hB⟩ := ho params hps (fun p hp x hx => (hpc p hp x hx).2)
    rcases hr with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hA.mpr ⟨h1, h2⟩, h3⟩
    · exact Or.inr ⟨hB.mpr h1, h2⟩
  · intro hr
    obtain ⟨params, hps, hpc⟩ := hex
    obtain ⟨hA, hB⟩ := ho params hps (fun p hp x hx => (hpc p hp x hx).2)
    refine ⟨params, hps, hpc, ?_⟩
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(hA.mp h1).1, (hA.mp h1).2, h2⟩
    · exact Or.inr ⟨hB.mp h1, h2⟩

-- RFC 2397: data URL の構文
@[step]
theorem parse_data_uri_spec (uri : alloc.vec.Vec U8) (h : lit "data:" <+: uri.val) :
    validate.resource.parse_data_uri uri ⦃ r => (∀ d, r = some d → 5 ≤ d.media_end.val ∧ d.media_end.val ≤ uri.length) ∧
      ∀ media n, dataUri uri.val media n ↔
        ∃ d, r = some d ∧ media = (uri.val.drop 5).take (d.media_end.val - 5) ∧ n = d.length.val ⦄ := by
  have h5 : 5 ≤ uri.val.length := by have := h.length_le; simp [lit] at this; exact this
  unfold validate.resource.parse_data_uri
  step*
  · refine ⟨by simp, fun media n => ?_⟩
    simp only [reduceCtorEq, false_and, exists_false, iff_false]
    intro hd
    obtain ⟨c, hc0, hc1, hc2⟩ := dataUri_has_comma _ _ _ hd
    exact comma_post3 c hc0 (by scalar_tac) hc2
  · have hc1 : comma.val < uri.val.length := by scalar_tac
    have hc2 := comma_post2 (by scalar_tac)
    have hdec := fun media n => data_decomp uri.val h comma.val media_end.val comma_post hc1 hc2 comma_post3
      media_end_post media_end_post1 media_end_post2 media_end_post3 media n
    have hex := params_exist uri.val media_end.val comma.val media_end_post1 (by scalar_tac) media_end_post2
      comma_post3 media_end_post
    have hsimp := fun B64 PCT => decomp_simpl uri.val media_end.val comma.val hex o o_post B64 PCT
    rcases o with _ | _ | _
    · simp only
      step*
    · simp only [Bool.false_eq_true, ↓reduceIte]
      step*
      refine ⟨fun d hd => ?_, fun media n => ?_⟩
      · simp only [Option.some.injEq] at hd; subst hd; exact ⟨media_end_post, by scalar_tac⟩
      · have hl := length_post n
        rw [x_post, ‹length = some length1›] at hl
        rw [hdec, hsimp]
        simp only [reduceCtorEq, false_and, Option.some.injEq, true_and, false_or, or_false, exists_eq_left'] at hl ⊢
        rw [hl]
        unfold uriSeg
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
    · simp only [↓reduceIte]
      step*
      refine ⟨fun d hd => ?_, fun media n => ?_⟩
      · simp only [Option.some.injEq] at hd; subst hd; exact ⟨media_end_post, by scalar_tac⟩
      · have hl := length_post n
        rw [x_post, ‹length = some length1›] at hl
        rw [hdec, hsimp]
        simp only [reduceCtorEq, false_and, Option.some.injEq, true_and, false_or, or_false, exists_eq_left'] at hl ⊢
        rw [hl]
        unfold uriSeg
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩

/-! ### バッファと画像の URI (BU1, IM1) -/

theorem lit_data : lit "data:" = [100#u8, 97#u8, 116#u8, 97#u8, 58#u8] := rfl

@[step]
theorem is_data_uri_spec (uri : alloc.vec.Vec U8) : validate.resource.is_data_uri uri ⦃ r => r = true ↔ lit "data:" <+: uri.val ⦄ := by
  unfold validate.resource.is_data_uri
  step*
  rw [r_post, s_post, array_make_to_slice_val, lit_data]

theorem lit_octet : lit "application/octet-stream" = [97#u8, 112#u8, 112#u8, 108#u8, 105#u8, 99#u8, 97#u8,
    116#u8, 105#u8, 111#u8, 110#u8, 47#u8, 111#u8, 99#u8, 116#u8, 101#u8, 116#u8, 45#u8, 115#u8, 116#u8,
    114#u8, 101#u8, 97#u8, 109#u8] := rfl

theorem lit_gltf_buffer : lit "application/gltf-buffer" = [97#u8, 112#u8, 112#u8, 108#u8, 105#u8, 99#u8, 97#u8,
    116#u8, 105#u8, 111#u8, 110#u8, 47#u8, 103#u8, 108#u8, 116#u8, 102#u8, 45#u8, 98#u8, 117#u8, 102#u8,
    102#u8, 101#u8, 114#u8] := rfl

-- MUST-022: バッファーの data URL のメディアタイプ
@[step]
theorem buffer_media_type_ok_spec (uri : alloc.vec.Vec U8) (me : Usize) (h0 : 5 ≤ me.val) (h1 : me.val ≤ uri.length) :
    validate.resource.buffer_media_type_ok uri me ⦃ r => r = true ↔
      (uriSeg uri.val 5 me.val = lit "application/octet-stream" ∨ uriSeg uri.val 5 me.val = lit "application/gltf-buffer") ⦄ := by
  unfold validate.resource.buffer_media_type_ok
  step*
  all_goals simp_all [lit_octet, lit_gltf_buffer]

-- buffer の uri の条件 (BU1)
-- MUST-021, MUST-022: data URL のメディアタイプと長さ ≥ byteLength
def bufferUriOk (u : List U8) (len : Nat) : Prop :=
  uriSyntax u ∧ (lit "data:" <+: u → ∃ media n, dataUri u media n ∧
    (media = lit "application/octet-stream" ∨ media = lit "application/gltf-buffer") ∧ len ≤ n)

-- image の uri の条件 (IM1)
def imageUriOk (u : List U8) : Prop := uriSyntax u ∧ (lit "data:" <+: u → ∃ media n, dataUri u media n)

-- MUST-021: data URL の長さ ≥ byteLength
@[step]
theorem buffer_uri_ok_spec (uri : alloc.vec.Vec U8) (len : U64) :
    validate.resource.buffer_uri_ok uri len ⦃ r => r = true ↔ bufferUriOk uri.val len.val ⦄ := by
  unfold validate.resource.buffer_uri_ok bufferUriOk
  step*
  all_goals
    have hD : ∀ media n, dataUri uri.val media n ↔ media = uriSeg uri.val 5 d.media_end.val ∧ n = d.length.val := by
      intro media n; rw [o_post1]; simp [‹o = some d›, uriSeg]
    simp only [hD]
    simp_all

@[step]
theorem image_uri_ok_spec (uri : alloc.vec.Vec U8) : validate.resource.image_uri_ok uri ⦃ r => r = true ↔ imageUriOk uri.val ⦄ := by
  unfold validate.resource.image_uri_ok imageUriOk
  step*
  constructor
  · intro h
    refine ⟨b_post.mp ‹_›, fun _ => ?_⟩
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
    exact ⟨_, _, (o_post1 _ _).mpr ⟨d, hd, rfl, rfl⟩⟩
  · rintro ⟨-, h⟩
    obtain ⟨m, n, hd⟩ := h (b1_post.mp ‹_›)
    obtain ⟨d, hd, -⟩ := (o_post1 m n).mp hd
    simp [hd]

-- BU1 (バッファごと)
-- MUST-021, MUST-023, MUST-024: GLB のバッファー 0 は BIN チャンクに収まる
def bufferOk (g : model.Gltf) (b : Nat) (buf : model.Buffer) : Prop :=
  0 < buf.byte_length.val ∧
  (buf.uri = none → b = 0 → g.is_glb = true → ∃ n, g.glb_bin_len = some n ∧ buf.byte_length.val ≤ n.val) ∧
  (∀ u, buf.uri = some u → bufferUriOk u.val buf.byte_length.val)

-- BU1
def buffersOk (g : model.Gltf) : Prop := ∀ b (h : b < g.buffers.val.length), bufferOk g b g.buffers.val[b]

-- MUST-021, MUST-023, MUST-024: GLB のバッファー 0 は BIN チャンクに収まる
@[step]
theorem buffer_ok_spec (g : model.Gltf) (b : Usize) (hb : b.val < g.buffers.val.length) :
    validate.resource.buffer_ok g b ⦃ r => r = true ↔ bufferOk g b.val g.buffers.val[b.val] ⦄ := by
  unfold validate.resource.buffer_ok bufferOk
  step*
  all_goals simp_all [Nat.pos_iff_ne_zero]

@[step]
theorem buffers_ok_loop_spec (g : model.Gltf) (b : Usize) (hb : b.val ≤ g.buffers.val.length) :
    validate.resource.buffers_ok_loop g b ⦃ r => r = true ↔
      forallIdx g.buffers.val.length b.val (fun q => ∀ h : q < g.buffers.val.length, bufferOk g q g.buffers.val[q]) ⦄ := by
  unfold validate.resource.buffers_ok_loop
  loop_auto
termination_by g.buffers.val.length - b.val
decreasing_by all_goals scalar_decr_tac

/-- BU1: buffers_ok(g) ⇔ すべてのバッファが BU1 を満たす -/
@[step]
theorem buffers_ok_spec (g : model.Gltf) : validate.resource.buffers_ok g ⦃ r => r = true ↔ buffersOk g ⦄ := by
  unfold validate.resource.buffers_ok buffersOk
  step*
  simp_all [forallIdx_zero]

-- IM1 (画像ごと)
-- MUST-108, MUST-112: uri と bufferView のどちらか一方、bufferView なら mimeType
def imageOk (im : model.Image) : Prop :=
  (im.uri ≠ none ↔ im.buffer_view = none) ∧ (im.buffer_view ≠ none → im.has_mime_type = true) ∧
  ∀ u, im.uri = some u → imageUriOk u.val

-- IM1
def imagesOk (g : model.Gltf) : Prop := ∀ im ∈ g.images.val, imageOk im

-- MUST-108, MUST-112: uri と bufferView のどちらか一方、bufferView なら mimeType
@[step]
theorem image_ok_spec (im : model.Image) : validate.resource.image_ok im ⦃ r => r = true ↔ imageOk im ⦄ := by
  unfold validate.resource.image_ok imageOk
  rcases hu : im.uri with _ | u <;> rcases hb : im.buffer_view with _ | v <;> simp only [hu, hb] <;> step* <;> simp_all

@[step]
theorem images_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.images.val.length) :
    validate.resource.images_ok_loop g i ⦃ r => r = true ↔ forallFrom g.images.val i.val imageOk ⦄ := by
  unfold validate.resource.images_ok_loop
  loop_auto
termination_by g.images.val.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- IM1: images_ok(g) ⇔ すべての画像が IM1 を満たす -/
@[step]
theorem images_ok_spec (g : model.Gltf) : validate.resource.images_ok g ⦃ r => r = true ↔ imagesOk g ⦄ := by
  unfold validate.resource.images_ok imagesOk
  step*
  simp_all [forallFrom_zero]

end LoadGltf
