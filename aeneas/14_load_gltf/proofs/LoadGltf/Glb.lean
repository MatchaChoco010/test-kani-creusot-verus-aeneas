import LoadGltf.Common

open Aeneas Aeneas.Std Result

namespace LoadGltf

-- u32le(s, i)
def u32le (s : List U8) (i : Nat) : Nat :=
  (s.getD i 0#u8).val + 256 * (s.getD (i + 1) 0#u8).val + 65536 * (s.getD (i + 2) 0#u8).val +
    16777216 * (s.getD (i + 3) 0#u8).val

theorem or_shift (x y k : Nat) (hx : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [← Nat.shiftLeft_eq, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  ring

@[step]
theorem read_u32_spec (s : Slice U8) (i : Usize) (h : i.val + 3 < s.length) :
    glb.read_u32 s i ⦃ r => r.val = u32le s.val i.val ⦄ := by
  unfold glb.read_u32
  have h' : i.val + 3 < s.val.length := h
  step*
  have ha : i1.val < 256 := by scalar_tac
  have hb : i4.val < 256 := by scalar_tac
  have hc : i9.val < 256 := by scalar_tac
  have hd : i14.val < 256 := by scalar_tac
  have e2 : i2.val = i1.val := by rw [i2_post]; exact U8.cast_U32_val_eq _
  have e5 : i5.val = i4.val := by rw [i5_post]; exact U8.cast_U32_val_eq _
  have e10 : i10.val = i9.val := by rw [i10_post]; exact U8.cast_U32_val_eq _
  have e15 : i15.val = i14.val := by rw [i15_post]; exact U8.cast_U32_val_eq _
  have hs : U32.size = 2 ^ 32 := by simp [U32.size, U32.numBits]
  have e6 : i6.val = i4.val * 2 ^ 8 := by
    rw [i6_post, e5, Nat.shiftLeft_eq, hs, Nat.mod_eq_of_lt (by omega)]
  have e11 : i11.val = i9.val * 2 ^ 16 := by
    rw [i11_post, e10, Nat.shiftLeft_eq, hs, Nat.mod_eq_of_lt (by omega)]
  have e16 : i16.val = i14.val * 2 ^ 24 := by
    rw [i16_post, e15, Nat.shiftLeft_eq, hs, Nat.mod_eq_of_lt (by omega)]
  have e7 : i7.val = i1.val + i4.val * 2 ^ 8 := by
    rw [i7_post, UScalar.val_or, e2, e6, or_shift _ _ _ (by omega)]
  have e12 : i12.val = i1.val + i4.val * 2 ^ 8 + i9.val * 2 ^ 16 := by
    rw [i12_post, UScalar.val_or, e7, e11, or_shift _ _ _ (by omega)]
  rw [UScalar.val_or, e12, e16, or_shift _ _ _ (by omega)]
  simp only [u32le, List.getD_eq_getElem _ _ (by omega : i.val < s.val.length),
    List.getD_eq_getElem _ _ (by omega : i.val + 1 < s.val.length),
    List.getD_eq_getElem _ _ (by omega : i.val + 2 < s.val.length),
    List.getD_eq_getElem _ _ (by omega : i.val + 3 < s.val.length)]
  simp only [i1_post, i4_post, i9_post, i14_post, i3_post, i8_post, i13_post]
  omega

/-! ## G. GLB コンテナ -/

structure Chunk where
  pos : Nat
  len : Nat
  type : Nat

def chunkAt (s : List U8) (p : Nat) : Chunk := ⟨p, u32le s p, u32le s (p + 4)⟩

-- 位置 p から L までをチャンク列に分割する: p_{m+1} = p_m + 8 + len_m, len_m % 4 = 0, p_m + 8 + len_m ≤ L, p_k = L
-- MUST-159: chunkLength は 4 の倍数
def chunksFrom (s : List U8) (L p : Nat) : Option (List Chunk) :=
  if p < L then
    if p + 8 ≤ L ∧ u32le s p % 4 = 0 ∧ p + 8 + u32le s p ≤ L then
      (chunksFrom s L (p + 8 + u32le s p)).map (chunkAt s p :: ·)
    else none
  else if p = L then some [] else none
termination_by L - p

def JSON_CHUNK : Nat := 0x4E4F534A

def BIN_CHUNK : Nat := 0x004E4942

-- m 番目のチャンクの条件: type_0 = JSON、m ≥ 1 で JSON でない、BIN は m = 1 のみ
-- MUST-160, MUST-161: JSON チャンクは最初に 1 つ、BIN チャンクは 2 番目に 1 つまで
def chunkOk (c : Chunk) (m : Nat) : Prop :=
  (m = 0 → c.type = JSON_CHUNK) ∧ (1 ≤ m → c.type ≠ JSON_CHUNK) ∧ (c.type = BIN_CHUNK → m = 1)

instance (c : Chunk) (m : Nat) : Decidable (chunkOk c m) := by unfold chunkOk; infer_instance

def chunksOk (cs : List Chunk) : Prop := ∀ m (h : m < cs.length), chunkOk cs[m] m

instance (cs : List Chunk) : Decidable (chunksOk cs) := by unfold chunksOk; infer_instance

-- bin_len = Some(len_1) if k ≥ 2 ∧ type_1 = BIN else None
def binLenOf (cs : List Chunk) : Option Nat :=
  match cs[1]? with
  | some c => if c.type = BIN_CHUNK then some c.len else none
  | none => none

-- チャンク列から (JSON の開始位置, JSON の長さ, bin_len)
def chunkResult : Option (List Chunk) → Option (Nat × Nat × Option Nat)
  | some (c0 :: rest) =>
    if chunksOk (c0 :: rest) then some (c0.pos + 8, c0.len, binLenOf (c0 :: rest)) else none
  | _ => none

-- glb_spec(s)
-- MUST-158: GLB の magic、glTF 4.4: GLB ヘッダー
def glbSpec (s : List U8) : Option (List U8 × Option Nat) :=
  if 12 ≤ s.length ∧ u32le s 0 = 0x46546C67 ∧ u32le s 4 = 2 ∧ 12 ≤ u32le s 8 ∧ u32le s 8 ≤ s.length then
    (chunkResult (chunksFrom s (u32le s 8) 12)).map (fun (st, len, bin) => ((s.drop st).take len, bin))
  else none

theorem chunksFrom_step (s : List U8) (L p : Nat) (h : p < L)
    (hc : p + 8 ≤ L ∧ u32le s p % 4 = 0 ∧ p + 8 + u32le s p ≤ L) :
    chunksFrom s L p = (chunksFrom s L (p + 8 + u32le s p)).map (chunkAt s p :: ·) := by
  rw [chunksFrom]; simp [h, hc]

theorem chunksFrom_bad (s : List U8) (L p : Nat) (h : p < L)
    (hc : ¬ (p + 8 ≤ L ∧ u32le s p % 4 = 0 ∧ p + 8 + u32le s p ≤ L)) :
    chunksFrom s L p = none := by
  rw [chunksFrom]; simp only [h, ↓reduceIte, hc]

theorem chunksFrom_end (s : List U8) (L : Nat) : chunksFrom s L L = some [] := by
  rw [chunksFrom]; simp

theorem chunkResult_bad (o : Option (List Chunk)) (pre : List Chunk) (c : Chunk)
    (h : ¬ chunkOk c pre.length) : chunkResult ((o.map (c :: ·)).map (pre ++ ·)) = none := by
  rcases o with _ | rest
  · rfl
  · simp only [Option.map_some]
    cases hl : pre ++ c :: rest with
    | nil => simp at hl
    | cons c0 r =>
      simp only [chunkResult, ite_eq_right_iff, reduceCtorEq, imp_false]
      intro hok
      rw [← hl] at hok
      have := hok pre.length (by simp)
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] at this
      exact h this

theorem chunksOk_append (pre : List Chunk) (c : Chunk) (h1 : chunksOk pre) (h2 : chunkOk c pre.length) :
    chunksOk (pre ++ [c]) := by
  intro m hm
  simp only [List.length_append, List.length_singleton] at hm
  rcases Nat.lt_or_ge m pre.length with h | h
  · rw [List.getElem_append_left h]; exact h1 m h
  · have : m = pre.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    exact h2

theorem binLenOf_append (pre : List Chunk) (c : Chunk) :
    binLenOf (pre ++ [c]) =
      if pre.length = 1 ∧ c.type = BIN_CHUNK then some c.len else binLenOf pre := by
  unfold binLenOf
  rcases pre with _ | ⟨a, _ | ⟨b, r⟩⟩ <;> simp

-- scan_chunks のループ不変条件: pre は位置 12 から pos までに読んだチャンク列
def scanInv (s : List U8) (L : Nat) (json : Option (Usize × Usize)) (bin : Option U64)
    (pos : Nat) (index : Nat) (pre : List Chunk) : Prop :=
  chunksFrom s L 12 = (chunksFrom s L pos).map (pre ++ ·) ∧
  index = pre.length ∧ 8 * pre.length + 12 ≤ pos ∧ pos ≤ L ∧ chunksOk pre ∧
  json.map (fun p => (p.1.val, p.2.val)) = pre.head?.map (fun c => (c.pos + 8, c.len)) ∧
  bin.map (·.val) = binLenOf pre

theorem scanInv_malformed {s L json bin pos index pre} (h : scanInv s L json bin pos index pre)
    (hp : pos < L) (hc : ¬ (pos + 8 ≤ L ∧ u32le s pos % 4 = 0 ∧ pos + 8 + u32le s pos ≤ L)) :
    none = chunkResult (chunksFrom s L 12) := by
  rw [h.1, chunksFrom_bad _ _ _ hp hc]; rfl

theorem scanInv_bad {s L json bin pos index pre} (h : scanInv s L json bin pos index pre)
    (hp : pos < L) (hc : pos + 8 ≤ L ∧ u32le s pos % 4 = 0 ∧ pos + 8 + u32le s pos ≤ L)
    (hk : ¬ chunkOk (chunkAt s pos) pre.length) :
    none = chunkResult (chunksFrom s L 12) := by
  rw [h.1, chunksFrom_step _ _ _ hp hc, chunkResult_bad _ _ _ hk]

theorem scanInv_next {s L json bin pos index pre} (h : scanInv s L json bin pos index pre)
    (hp : pos < L) (hc : pos + 8 ≤ L ∧ u32le s pos % 4 = 0 ∧ pos + 8 + u32le s pos ≤ L)
    (hk : chunkOk (chunkAt s pos) pre.length) (json' : Option (Usize × Usize)) (bin' : Option U64)
    (hj : json'.map (fun p => (p.1.val, p.2.val)) =
      (pre ++ [chunkAt s pos]).head?.map (fun c => (c.pos + 8, c.len)))
    (hb : bin'.map (·.val) = binLenOf (pre ++ [chunkAt s pos])) (pos' : Nat) (index' : Nat)
    (hpos' : pos' = pos + 8 + u32le s pos) (hidx' : index' = index + 1) :
    ∃ pre', scanInv s L json' bin' pos' index' pre' := by
  obtain ⟨h12, hidx, hlen, hpos, hok, _, _⟩ := h
  refine ⟨pre ++ [chunkAt s pos], ?_, ?_, ?_, ?_, chunksOk_append _ _ hok hk, hj, hb⟩
  · rw [h12, chunksFrom_step _ _ _ hp hc, hpos', Option.map_map]
    congr 1
    funext l
    simp
  · simp [hidx', hidx]
  · simp only [List.length_append, List.length_singleton]; omega
  · omega

theorem scanInv_end_none {s L bin pos index pre} (h : scanInv s L none bin pos index pre)
    (hp : ¬ pos < L) : none = chunkResult (chunksFrom s L 12) := by
  obtain ⟨h12, _, _, hpos, _, hj, _⟩ := h
  have : pos = L := by omega
  subst this
  rw [h12, chunksFrom_end]
  cases pre with
  | nil => rfl
  | cons c r => simp at hj

theorem scanInv_end_some {s L p bin pos index pre} (h : scanInv s L (some p) bin pos index pre)
    (hp : ¬ pos < L) :
    some (p.1.val, p.2.val, bin.map (·.val)) = chunkResult (chunksFrom s L 12) := by
  obtain ⟨h12, _, _, hpos, hok, hj, hb⟩ := h
  have : pos = L := by omega
  subst this
  rw [h12, chunksFrom_end]
  cases pre with
  | nil => simp at hj
  | cons c r =>
    simp only [Option.map_some, List.append_nil, chunkResult, hok, ↓reduceIte, ← hb]
    simp only [List.head?_cons, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hj
    rw [hj.1, hj.2]

theorem chunk_hc (s : Slice U8) (total pos i i3 i4 len : Usize) (hi : i.val = total.val - pos.val)
    (h8 : ¬ i < 8#usize) (h3 : ¬(i3 != 0#usize) = true) (hi3 : i3.val = len.val % 4)
    (hi4 : i4.val = i.val - 8) (h4 : ¬ i4 < len) (hlv : len.val = u32le s.val pos.val) :
    pos.val + 8 ≤ total.val ∧ u32le s.val pos.val % 4 = 0 ∧
      pos.val + 8 + u32le s.val pos.val ≤ total.val := by
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h3
  subst h3
  simp only [UScalar.lt_equiv, not_lt] at h8 h4
  simp only [UScalar.ofNatCore_val_eq] at hi3 h8
  omega

-- MUST-159, MUST-160, MUST-161: チャンクの長さと順序
@[step]
theorem scan_chunks_loop_spec (s : Slice U8) (total : Usize) (json : Option (Usize × Usize))
    (bin : Option U64) (pos : Usize) (index : Usize)
    (hT : total.val ≤ s.length) (hT32 : total.val ≤ U32.max)
    (hinv : ∃ pre, scanInv s.val total.val json bin pos.val index.val pre) :
    glb.scan_chunks_loop s total json bin pos index ⦃ r =>
      r.map (fun x => (x.1.val, x.2.1.val, x.2.2.map (·.val))) =
        chunkResult (chunksFrom s.val total.val 12) ⦄ := by
  obtain ⟨pre, hI⟩ := hinv
  have hI' := hI
  obtain ⟨h12, hidx, hlen, hpos, hok, hjson, hbin⟩ := hI'
  unfold glb.scan_chunks_loop
  step*
  all_goals try (simp only [Option.map_none]; exact scanInv_malformed hI (by agrind) (by agrind))
  all_goals try (have hlv : len.val = u32le s.val pos.val := by
                   rw [len_post, U32.cast_Usize_val_eq, i1_post])
  all_goals try (have hkv : kind.val = u32le s.val (pos.val + 4) := by rw [kind_post, i2_post])
  all_goals try (have hkn : (kind = 1313821514#u32) = (kind.val = 1313821514) := by simp [UScalar.eq_equiv])
  all_goals try (have hkb : (kind = 5130562#u32) = (kind.val = 5130562) := by simp [UScalar.eq_equiv])
  all_goals try (have hi0 : (index = 0#usize) = (index.val = 0) := by simp [UScalar.eq_equiv])
  all_goals try (have hi1 : (index = 1#usize) = (index.val = 1) := by simp [UScalar.eq_equiv])
  all_goals try (have hc := chunk_hc s total pos i i3 i4 len i_post ‹_› ‹_› i3_post i4_post ‹_› hlv)
  all_goals try simp only [bne_iff_ne, ne_eq, Decidable.not_not, hkn, hkb, hi0, hi1] at *
  · simp only [Option.map_none]
    apply scanInv_bad hI (by agrind) hc
    simp only [chunkOk, chunkAt, JSON_CHUNK, BIN_CHUNK]
    agrind
  · apply scanInv_next hI (by agrind) hc (by simp only [chunkOk, chunkAt, JSON_CHUNK, BIN_CHUNK]; omega)
    · have : pre = [] := by apply List.eq_nil_of_length_eq_zero; agrind
      subst this; simp only [List.nil_append, List.head?_cons, Option.map_some, chunkAt]; agrind
    · rw [binLenOf_append]; simp only [show pre.length ≠ 1 by agrind, false_and, ↓reduceIte, hbin]
    · agrind
    · agrind
  · simp only [Option.map_none]
    apply scanInv_bad hI (by agrind) hc
    simp only [chunkOk, chunkAt, JSON_CHUNK, BIN_CHUNK]
    agrind
  · simp only [Option.map_none]
    apply scanInv_bad hI (by agrind) hc
    simp only [chunkOk, chunkAt, JSON_CHUNK, BIN_CHUNK]
    agrind
  · apply scanInv_next hI (by agrind) hc (by simp only [chunkOk, chunkAt, JSON_CHUNK, BIN_CHUNK]; omega)
    · simp only [List.head?_append, hjson]
      have : pre ≠ [] := by intro h; subst h; agrind
      cases pre with
      | nil => contradiction
      | cons c r => rfl
    · rw [binLenOf_append]
      simp only [show pre.length = 1 by agrind, chunkAt, true_and, Option.map_some]
      have : u32le s.val (pos.val + 4) = BIN_CHUNK := by simp only [BIN_CHUNK]; agrind
      simp only [this, ↓reduceIte, bin_len1_post, usize_cast_u64_val, hlv]
    · agrind
    · agrind
  · apply scanInv_next hI (by agrind) hc (by simp only [chunkOk, chunkAt, JSON_CHUNK, BIN_CHUNK]; omega)
    · simp only [List.head?_append, hjson]
      have : pre ≠ [] := by intro h; subst h; agrind
      cases pre with
      | nil => contradiction
      | cons c r => rfl
    · rw [binLenOf_append]
      have : u32le s.val (pos.val + 4) ≠ BIN_CHUNK := by simp only [BIN_CHUNK]; agrind
      simp only [chunkAt, this, and_false, ↓reduceIte, hbin]
    · agrind
    · agrind
  · simp only [Option.map_none]
    rw [‹json = none›] at hI
    exact scanInv_end_none hI (by agrind)
  · rw [‹json = some _›] at hI
    rename_i p _
    obtain ⟨a, b⟩ := p
    step*
    exact scanInv_end_some hI (by agrind)
termination_by total.val - pos.val
decreasing_by all_goals scalar_decr_tac

theorem chunksFrom_head (s : List U8) (L p : Nat) (c : Chunk) (rest : List Chunk)
    (h : chunksFrom s L p = some (c :: rest)) : c.pos = p ∧ p + 8 + c.len ≤ L := by
  rw [chunksFrom] at h
  by_cases hp : p < L
  · by_cases hc : p + 8 ≤ L ∧ u32le s p % 4 = 0 ∧ p + 8 + u32le s p ≤ L
    · simp only [hp, hc, ↓reduceIte, and_self] at h
      cases hr : chunksFrom s L (p + 8 + u32le s p) <;> rw [hr] at h <;> simp at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, hc.2.2⟩
    · simp [hp, hc] at h
  · simp only [hp, ↓reduceIte] at h
    split at h <;> simp at h

theorem chunkResult_bound (s : List U8) (L : Nat) (st len : Nat) (bin : Option Nat)
    (h : chunkResult (chunksFrom s L 12) = some (st, len, bin)) : st + len ≤ L := by
  cases hc : chunksFrom s L 12 with
  | none => rw [hc] at h; simp [chunkResult] at h
  | some cs =>
    rw [hc] at h
    cases cs with
    | nil => simp [chunkResult] at h
    | cons c rest =>
      have := chunksFrom_head s L 12 c rest hc
      simp only [chunkResult] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp at h

@[step]
theorem copy_range_loop_spec (s : Slice U8) (e : Usize) (out : alloc.vec.Vec U8) (k : Usize)
    (he : e.val ≤ s.length) (hk : k.val ≤ e.val) (hl : out.val.length + (e.val - k.val) ≤ Usize.max) :
    glb.copy_range_loop s e out k ⦃ r => r.val = out.val ++ (s.val.take e.val).drop k.val ⦄ := by
  unfold glb.copy_range_loop
  step*
  · agrind
  · rw [List.drop_eq_getElem_cons (by simp; agrind), r_post, out1_post, k1_post, i_post,
      List.getElem_take]
    simp
  · rw [List.drop_eq_nil_of_le (by rw [List.length_take]; agrind), List.append_nil]
termination_by e.val - k.val
decreasing_by all_goals scalar_decr_tac

-- is_glb: 先頭 4 バイトが glTF
def isGlbSpec (s : List U8) : Prop := s.take 4 = [103#u8, 108#u8, 84#u8, 70#u8]

theorem isGlbSpec_iff (l : List U8) : isGlbSpec l ↔ ∃ h : 4 ≤ l.length,
    l[0] = 103#u8 ∧ l[1] = 108#u8 ∧ l[2] = 84#u8 ∧ l[3] = 70#u8 := by
  simp only [isGlbSpec]
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩⟩ <;> simp

@[step]
theorem is_glb_spec (s : Slice U8) : glb.is_glb s ⦃ b => b = true ↔ isGlbSpec s.val ⦄ := by
  unfold glb.is_glb
  rw [isGlbSpec_iff]
  step*

-- MUST-158, MUST-159, MUST-160, MUST-161: GLB の magic とチャンクの規則、glTF 4.4: GLB コンテナ
/-- G1: parse_glb(s) は glb_spec(s) と等しい -/
@[step]
theorem parse_glb_spec (s : Slice U8) :
    glb.parse_glb s ⦃ r => r.map (fun c => (c.json.val, c.bin_len.map (·.val))) = glbSpec s.val ⦄ := by
  unfold glb.parse_glb glb.scan_chunks
  step*
  all_goals try simp only [bne_iff_ne, ne_eq, Decidable.not_not] at *
  all_goals try (have htv : total.val = u32le s.val 8 := by rw [total_post, U32.cast_Usize_val_eq, i3_post])
  · simp only [Option.map_none, glbSpec]; split_ifs <;> first | rfl | (exfalso; agrind)
  · simp only [Option.map_none, glbSpec]; split_ifs <;> first | rfl | (exfalso; simp only [UScalar.eq_equiv] at *; agrind)
  · simp only [Option.map_none, glbSpec]; split_ifs <;> first | rfl | (exfalso; simp only [UScalar.eq_equiv] at *; agrind)
  · simp only [Option.map_none, glbSpec]; split_ifs <;> first | rfl | (exfalso; agrind)
  · simp only [Option.map_none, glbSpec]; split_ifs <;> first | rfl | (exfalso; agrind)
  · refine ⟨[], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · agrind
    · simp [chunksOk]
    · simp
    · simp [binLenOf]
  · simp only [Option.map_none, glbSpec]
    split_ifs
    · rw [← htv, ← o_post]; simp_all
    · exfalso; simp only [UScalar.eq_equiv] at *; agrind
  · rename_i t _ _ _
    obtain ⟨a, b, c⟩ := t
    have ho := o_post
    rw [‹o = some _›] at ho
    have hb := chunkResult_bound _ _ _ _ _ ho.symm
    simp only at hb
    step*
    · simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.length_nil]; agrind
    simp only [Option.map_some, glbSpec]
    split_ifs
    swap
    · exfalso; simp only [UScalar.eq_equiv] at *; agrind
    rw [← htv, ← ho]
    simp only [Option.map_some, v_post, List.drop_take, i5_post, Option.some.injEq,
      Prod.mk.injEq, and_true]
    simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append, Nat.add_sub_cancel_left]

end LoadGltf
