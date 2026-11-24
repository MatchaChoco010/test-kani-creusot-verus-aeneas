import LoadGltf.Json.String

open Aeneas Aeneas.Std Result

namespace LoadGltf

set_option linter.unusedSimpArgs false


/-! ## J.1 抽象値 -/

inductive JsonS where
  | null
  | bool (b : Bool)
  | num (neg : Bool) (int frac : List Nat) (eneg : Bool) (exp : List Nat)
  | str (b : List Nat)
  | arr (vs : List JsonS)
  | obj (ms : List (List Nat × JsonS))
deriving Inhabited

def isWs (b : Nat) : Bool := b = 0x20 || b = 0x09 || b = 0x0A || b = 0x0D

-- skip_ws(s, i)
-- RFC 8259 §2: 空白
def skipWs (s : List U8) (i : Nat) : Nat :=
  if h : i < s.length then (if isWs s[i].val then skipWs s (i + 1) else i) else i
termination_by s.length - i

-- s[i..i+|lit|] = lit
def litAt (s : List U8) (i : Nat) (lit : List Nat) : Bool := ((s.drop i).take lit.length).map (·.val) == lit

-- ws の後に閉じ括弧 c があればその次の位置
def closeAt (s : List U8) (c k : Nat) : Option Nat :=
  if byteAt s (skipWs s k) = some c then some (skipWs s k + 1) else none

-- メンバの "key" ws : ws (キー, 値の開始位置)
def keyAt (s : List U8) (j : Nat) : Option (List Nat × Nat) :=
  if byteAt s j = some 0x22 then
    (strAt s (j + 1)).bind fun p =>
      if byteAt s (skipWs s p.2) = some 0x3A then some (p.1, skipWs s (skipWs s p.2 + 1)) else none
  else none

-- value(s, i, d) の符号化: s の位置 i から予算 d で v が読めるとき、その終了位置。
-- v についての構造的再帰。value(s,i,d) = some (v, k) ⇔ valueEnd s i d v = some k (一意性は valueEnd_det)。
mutual
def valueEnd (s : List U8) (i d : Nat) : JsonS → Option Nat
  | .null => if litAt s i [0x6E, 0x75, 0x6C, 0x6C] then some (i + 4) else none
  | .bool true => if litAt s i [0x74, 0x72, 0x75, 0x65] then some (i + 4) else none
  | .bool false => if litAt s i [0x66, 0x61, 0x6C, 0x73, 0x65] then some (i + 5) else none
  | .num neg I F en E => (numAt s i).bind fun p => if p.1 = (neg, I, F, en, E) then some p.2 else none
  | .str b =>
    if byteAt s i = some 0x22 then (strAt s (i + 1)).bind fun p => if p.1 = b then some p.2 else none
    else none
  | .arr [] => if d ≠ 0 ∧ byteAt s i = some 0x5B then closeAt s 0x5D (i + 1) else none
  | .arr (v :: vs) => if d ≠ 0 ∧ byteAt s i = some 0x5B then elemsEnd s (skipWs s (i + 1)) (d - 1) (v :: vs) else none
  | .obj [] => if d ≠ 0 ∧ byteAt s i = some 0x7B then closeAt s 0x7D (i + 1) else none
  | .obj (m :: ms) => if d ≠ 0 ∧ byteAt s i = some 0x7B then membersEnd s (skipWs s (i + 1)) (d - 1) (m :: ms) else none

-- 空でない要素列 value (ws , ws value)* ws ]
def elemsEnd (s : List U8) (j d : Nat) : List JsonS → Option Nat
  | [] => none
  | [v] => (valueEnd s j d v).bind (closeAt s 0x5D)
  | v :: w :: ws => (valueEnd s j d v).bind fun k =>
    if byteAt s (skipWs s k) = some 0x2C then elemsEnd s (skipWs s (skipWs s k + 1)) d (w :: ws) else none

-- 空でないメンバ列 "key" ws : ws value (ws , ws member)* ws }
def membersEnd (s : List U8) (j d : Nat) : List (List Nat × JsonS) → Option Nat
  | [] => none
  | [(key, v)] => (keyAt s j).bind fun p => if p.1 = key then (valueEnd s p.2 d v).bind (closeAt s 0x7D) else none
  | (key, v) :: m :: ms => (keyAt s j).bind fun p =>
    if p.1 = key then
      (valueEnd s p.2 d v).bind fun k =>
        if byteAt s (skipWs s k) = some 0x2C then membersEnd s (skipWs s (skipWs s k + 1)) d (m :: ms) else none
    else none
end

-- BOM (EF BB BF) を読み飛ばし、空白を読み飛ばした開始位置
def jsonStart (s : List U8) : Nat :=
  skipWs s (if byteAt s 0 = some 0xEF ∧ byteAt s 1 = some 0xBB ∧ byteAt s 2 = some 0xBF then 3 else 0)

-- json_text(s) = some v
def JsonTextIs (s : List U8) (v : JsonS) : Prop :=
  ∃ k, valueEnd s (jsonStart s) 128 v = some k ∧ skipWs s k = s.length

-- json_text(s)
noncomputable def jsonText (s : List U8) : Option JsonS :=
  open Classical in if h : ∃ v, JsonTextIs s v then some (Classical.choose h) else none

/-! ## アリーナ表現と抽象値の対応 -/

def json.number.Number.toS (n : json.number.Number) : JsonS :=
  .num n.negative (n.int_digits.val.map (·.val)) (n.frac_digits.val.map (·.val)) n.exp_negative
    (n.exp_digits.val.map (·.val))

-- tree(nodes, id): 子の添字は親より小さい (docWf の下では if の else 側は使われない)
def treeN (nodes : List json.JsonNode) (id : Nat) : JsonS :=
  match nodes[id]? with
  | none => .null
  | some .Null => .null
  | some (.Bool b) => .bool b
  | some (.Number n) => n.toS
  | some (.String b) => .str (b.val.map (·.val))
  | some (.Array items) =>
    .arr (items.val.map fun c => if _h : c.val < id then treeN nodes c.val else .null)
  | some (.Object ms) =>
    .obj (ms.val.map fun m => (m.key.val.map (·.val),
      if _h : m.value.val < id then treeN nodes m.value.val else .null))
termination_by id

def tree (doc : json.JsonDoc) (id : Nat) : JsonS := treeN doc.nodes.val id

-- 節点 id の整形条件: 子の添字 < id、Number は Number.wf
def nodeWf (id : Nat) : json.JsonNode → Prop
  | .Array items => ∀ c ∈ items.val, c.val < id
  | .Object ms => ∀ m ∈ ms.val, m.value.val < id
  | .Number n => n.wf
  | _ => True

def nodesWf (nodes : List json.JsonNode) : Prop := ∀ i (h : i < nodes.length), nodeWf i nodes[i]

def docWf (doc : json.JsonDoc) : Prop := doc.root.val < doc.nodes.val.length ∧ nodesWf doc.nodes.val

theorem litAt_head {s : List U8} {i a : Nat} {l : List Nat} (h : litAt s i (a :: l) = true) :
    byteAt s i = some a := by
  simp only [litAt, beq_iff_eq, List.length_cons] at h
  unfold byteAt
  have hh : s[i]? = (s.drop i).head? := by rw [List.head?_drop]
  rw [hh]
  cases hd : s.drop i with
  | nil => simp [hd] at h
  | cons x xs => simp [hd] at h; simp [h.1]

theorem strAt_bound {s : List U8} {i : Nat} {b : List Nat} {k : Nat} (h : strAt s i = some (b, k)) :
    i < k ∧ k ≤ s.length := by
  cases hb : byteAt s i with
  | none => rw [strAt_of_none hb] at h; cases h
  | some c =>
    have hi := byteAt_some' hb
    rw [strAt_of_some hb] at h
    split_ifs at h
    · simp at h; omega
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs, j⟩, hj, ⟨b', k'⟩, hk, he⟩ := h
      simp at he; obtain ⟨_, rfl⟩ := he
      have := escAt_lt hj
      have := strAt_bound hk
      simp at this; omega
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨b', k'⟩, hk, he⟩ := h
      simp at he; obtain ⟨_, rfl⟩ := he
      have := strAt_bound hk; omega
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨b', k'⟩, hk, he⟩ := h
      simp at he; obtain ⟨_, rfl⟩ := he
      have := strAt_bound hk; omega
termination_by s.length - i
decreasing_by all_goals omega

-- 値の先頭バイトの種類
def startsOk : JsonS → Nat → Prop
  | .null, b => b = 0x6E
  | .bool true, b => b = 0x74
  | .bool false, b => b = 0x66
  | .num .., b => b = 0x2D ∨ (0x30 ≤ b ∧ b ≤ 0x39)
  | .str _, b => b = 0x22
  | .arr _, b => b = 0x5B
  | .obj _, b => b = 0x7B

theorem numAt_start {s : List U8} {i : Nat} {p k} (h : numAt s i = some (p, k)) :
    ∃ b, byteAt s i = some b ∧ (b = 0x2D ∨ (0x30 ≤ b ∧ b ≤ 0x39)) := by
  unfold numAt at h
  by_cases hm : byteAt s i = some 0x2D
  · exact ⟨_, hm, Or.inl rfl⟩
  · simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff] at h
    obtain ⟨ip, hip, _⟩ := h
    unfold intPart at hip
    split at hip
    · cases hip
    · rename_i c hc
      split at hip
      · rename_i hd
        simp [isDigit] at hd
        exact ⟨c, hc, Or.inr hd⟩
      · cases hip

theorem closeAt_some {s : List U8} {c k r : Nat} (h : closeAt s c k = some r) :
    byteAt s (skipWs s k) = some c ∧ r = skipWs s k + 1 := by
  unfold closeAt at h; split at h <;> simp_all

theorem valueEnd_start {s : List U8} {i d : Nat} {v : JsonS} {k : Nat} (h : valueEnd s i d v = some k) :
    ∃ b, byteAt s i = some b ∧ startsOk v b := by
  cases v with
  | null => simp only [valueEnd] at h; split at h <;> simp_all [startsOk]; exact litAt_head ‹_›
  | bool b =>
    cases b <;> simp only [valueEnd] at h <;> split at h <;> simp_all [startsOk] <;> exact litAt_head ‹_›
  | num =>
    simp only [valueEnd, Option.bind_eq_some_iff] at h
    obtain ⟨⟨p, k'⟩, hp, _⟩ := h
    exact numAt_start hp
  | str => simp only [valueEnd] at h; split at h <;> simp_all [startsOk]
  | arr vs => cases vs <;> simp only [valueEnd] at h <;> split at h <;> simp_all [startsOk]
  | obj ms => cases ms <;> simp only [valueEnd] at h <;> split at h <;> simp_all [startsOk]

theorem elemsEnd_start {s : List U8} {j d : Nat} {vs : List JsonS} {k : Nat} (h : elemsEnd s j d vs = some k) :
    ∃ b, byteAt s j = some b ∧ b ≠ 0x5D ∧ vs ≠ [] := by
  have hv : ∃ v k1, valueEnd s j d v = some k1 := by
    match vs with
    | [] => simp [elemsEnd] at h
    | [v] =>
      simp only [elemsEnd, Option.bind_eq_some_iff] at h
      obtain ⟨k1, hk1, _⟩ := h; exact ⟨v, k1, hk1⟩
    | v :: w :: ws =>
      simp only [elemsEnd, Option.bind_eq_some_iff] at h
      obtain ⟨k1, hk1, _⟩ := h; exact ⟨v, k1, hk1⟩
  obtain ⟨v, k1, hk1⟩ := hv
  obtain ⟨b, hb, hs⟩ := valueEnd_start hk1
  refine ⟨b, hb, ?_, by rintro rfl; simp [elemsEnd] at h⟩
  cases v <;> (try rename_i bb; cases bb) <;> simp [startsOk] at hs <;> omega

theorem membersEnd_start {s : List U8} {j d : Nat} {ms : List (List Nat × JsonS)} {k : Nat}
    (h : membersEnd s j d ms = some k) : byteAt s j = some 0x22 ∧ ms ≠ [] := by
  have hk : ∃ p, keyAt s j = some p := by
    match ms with
    | [] => simp [membersEnd] at h
    | [(key, v)] =>
      simp only [membersEnd, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, _⟩ := h; exact ⟨p, hp⟩
    | (key, v) :: m :: ms =>
      simp only [membersEnd, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, _⟩ := h; exact ⟨p, hp⟩
  obtain ⟨p, hp⟩ := hk
  refine ⟨?_, by rintro rfl; simp [membersEnd] at h⟩
  unfold keyAt at hp; split at hp <;> simp_all

theorem startsOk_kind {v v' : JsonS} {b : Nat} (h : startsOk v b) (h' : startsOk v' b) :
    (v = .null ∧ v' = .null) ∨ (∃ x, v = .bool x ∧ v' = .bool x) ∨
    (∃ a b c d e a' b' c' d' e', v = .num a b c d e ∧ v' = .num a' b' c' d' e') ∨
    (∃ x y, v = .str x ∧ v' = .str y) ∨ (∃ x y, v = .arr x ∧ v' = .arr y) ∨ (∃ x y, v = .obj x ∧ v' = .obj y) := by
  rcases v with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;> rcases v' with _ | ⟨_ | _⟩ | _ | _ | _ | _ <;>
    simp only [startsOk] at h h' <;> simp <;> omega

-- 空でない列の閉じ方: ] (最後) と , (続き) は排他
theorem close_vs_comma {s : List U8} {k c r : Nat} (hc : c ≠ 0x2C) (h : closeAt s c k = some r)
    (h' : byteAt s (skipWs s k) = some 0x2C) : False := by
  obtain ⟨h1, _⟩ := closeAt_some h; rw [h1] at h'; cases h'; exact hc rfl

theorem cond_of {c : Prop} [Decidable c] {x : Option Nat} {k : Nat} (h : (if c then x else none) = some k) : c := by
  by_contra hc; simp [hc] at h

mutual
theorem valueEnd_det {s : List U8} : ∀ {i d : Nat} (v v' : JsonS) {k k' : Nat},
    valueEnd s i d v = some k → valueEnd s i d v' = some k' → v = v' ∧ k = k'
  | i, d, v, v', k, k', h, h' => by
    obtain ⟨b, hb, hs⟩ := valueEnd_start h
    obtain ⟨b', hb', hs'⟩ := valueEnd_start h'
    rw [hb] at hb'; cases hb'
    rcases startsOk_kind hs hs' with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨a, b, c, d, e, a', b', c', d', e', rfl, rfl⟩ |
      ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩ | ⟨x, y, rfl, rfl⟩
    · simp only [valueEnd] at h h'; split at h <;> simp_all
    · cases x <;> simp only [valueEnd] at h h' <;> split at h <;> simp_all
    · simp only [valueEnd, Option.bind_eq_some_iff] at h h'
      obtain ⟨p, hp, hp2⟩ := h
      obtain ⟨p', hp', hp2'⟩ := h'
      rw [hp] at hp'; cases hp'
      split at hp2 <;> split at hp2' <;> simp_all
    · simp only [startsOk] at hs; subst hs
      simp only [valueEnd, hb, ↓reduceIte, Option.bind_eq_some_iff] at h h'
      obtain ⟨p, hp, hp2⟩ := h
      obtain ⟨p', hp', hp2'⟩ := h'
      rw [hp] at hp'; cases hp'
      split at hp2 <;> split at hp2' <;> simp_all
    · match x, y with
      | [], [] =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'; simp_all
      | [], w :: ws =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'
        obtain ⟨_, hb2, hn, _⟩ := elemsEnd_start h'
        obtain ⟨h3, _⟩ := closeAt_some h
        simp_all
      | w :: ws, [] =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'
        obtain ⟨_, hb2, hn, _⟩ := elemsEnd_start h
        obtain ⟨h3, _⟩ := closeAt_some h'
        simp_all
      | w :: ws, w' :: ws' =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'
        have := elemsEnd_det (w :: ws) (w' :: ws') h h'
        simp_all
    · match x, y with
      | [], [] =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'; simp_all
      | [], w :: ws =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'
        obtain ⟨hb2, _⟩ := membersEnd_start h'
        obtain ⟨h3, _⟩ := closeAt_some h
        simp_all
      | w :: ws, [] =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'
        obtain ⟨hb2, _⟩ := membersEnd_start h
        obtain ⟨h3, _⟩ := closeAt_some h'
        simp_all
      | w :: ws, w' :: ws' =>
        have hc := cond_of h
        simp only [valueEnd, ite_eq_left hc] at h h'
        have := membersEnd_det (w :: ws) (w' :: ws') h h'
        simp_all

theorem elemsEnd_det {s : List U8} : ∀ {j d : Nat} (vs vs' : List JsonS) {k k' : Nat},
    elemsEnd s j d vs = some k → elemsEnd s j d vs' = some k' → vs = vs' ∧ k = k'
  | j, d, [], _, k, k', h, h' => by simp [elemsEnd] at h
  | j, d, _ :: _, [], k, k', h, h' => by simp [elemsEnd] at h'
  | j, d, [v], [v'], k, k', h, h' => by
    simp only [elemsEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    simp_all
  | j, d, [v], v' :: w' :: ws', k, k', h, h' => by
    simp only [elemsEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    exact (close_vs_comma (by decide) h ‹_›).elim
  | j, d, v :: w :: ws, [v'], k, k', h, h' => by
    simp only [elemsEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    split at h <;> try cases h
    exact (close_vs_comma (by decide) h' ‹_›).elim
  | j, d, v :: w :: ws, v' :: w' :: ws', k, k', h, h' => by
    simp only [elemsEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    split at h <;> try cases h
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    have := elemsEnd_det (w :: ws) (w' :: ws') h h'
    simp_all

theorem membersEnd_det {s : List U8} : ∀ {j d : Nat} (ms ms' : List (List Nat × JsonS)) {k k' : Nat},
    membersEnd s j d ms = some k → membersEnd s j d ms' = some k' → ms = ms' ∧ k = k'
  | j, d, [], _, k, k', h, h' => by simp [membersEnd] at h
  | j, d, _ :: _, [], k, k', h, h' => by simp [membersEnd] at h'
  | j, d, [(key, v)], [(key', v')], k, k', h, h' => by
    simp only [membersEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨p', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    split at h <;> try cases h
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    simp only [Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    simp_all
  | j, d, [(key, v)], (key', v') :: m' :: ms', k, k', h, h' => by
    simp only [membersEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨p', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    split at h <;> try cases h
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    simp only [Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    exact (close_vs_comma (by decide) h ‹_›).elim
  | j, d, (key, v) :: m :: ms, [(key', v')], k, k', h, h' => by
    simp only [membersEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨p', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    split at h <;> try cases h
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    simp only [Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    split at h <;> try cases h
    exact (close_vs_comma (by decide) h' ‹_›).elim
  | j, d, (key, v) :: m :: ms, (key', v') :: m' :: ms', k, k', h, h' => by
    simp only [membersEnd, Option.bind_eq_some_iff] at h h'
    obtain ⟨p, hp, h⟩ := h
    obtain ⟨p', hp', h'⟩ := h'
    rw [hp] at hp'; cases hp'
    split at h <;> try cases h
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    simp only [Option.bind_eq_some_iff] at h h'
    obtain ⟨k1, hk1, h⟩ := h
    obtain ⟨k2, hk2, h'⟩ := h'
    obtain ⟨rfl, rfl⟩ := valueEnd_det v v' hk1 hk2
    split at h <;> try cases h
    split at h' <;> (try cases h') <;> (try (exfalso; simp_all; done))
    have := membersEnd_det (m :: ms) (m' :: ms') h h'
    simp_all
end

theorem jsonTextIs_det {s : List U8} {v v' : JsonS} (h : JsonTextIs s v) (h' : JsonTextIs s v') : v = v' := by
  obtain ⟨k, hk, _⟩ := h
  obtain ⟨k', hk', _⟩ := h'
  exact (valueEnd_det v v' hk hk').1

theorem jsonText_eq_some {s : List U8} {v : JsonS} : jsonText s = some v ↔ JsonTextIs s v := by
  unfold jsonText
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact Classical.choose_spec h
    · intro hv; exact jsonTextIs_det (Classical.choose_spec h) hv
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro hv; exact h ⟨v, hv⟩

theorem jsonText_eq_none {s : List U8} : jsonText s = none ↔ ∀ v, ¬ JsonTextIs s v := by
  unfold jsonText
  split
  · rename_i h; simp only [reduceCtorEq, false_iff, not_forall, not_not]; exact h
  · rename_i h; simp only [true_iff]; intro v hv; exact h ⟨v, hv⟩

@[step]
theorem is_ws_spec (b : U8) : json.is_ws b ⦃ r => r = isWs b.val ⦄ := by
  unfold json.is_ws isWs
  step*

@[step]
theorem skip_ws_loop_spec (s : Slice U8) (j : Usize) :
    json.skip_ws_loop s j ⦃ r => r.val = skipWs s.val j.val ⦄ := by
  unfold json.skip_ws_loop
  step*
  all_goals rw [skipWs]
  · rw [dite_eq_left (by scalar_tac)]; simp_all
  · rw [dite_eq_left (by scalar_tac)]; simp_all
  · rw [dite_eq_right (by scalar_tac)]
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

theorem litAt_nil (s : List U8) (j : Nat) : litAt s j [] = true := by simp [litAt]

theorem litAt_cons {s : List U8} {j : Nat} (a : Nat) (l : List Nat) (h : j < s.length) :
    litAt s j (a :: l) = (decide (byteD s j = a) && litAt s (j + 1) l) := by
  simp only [litAt, List.length_cons, List.drop_eq_getElem_cons h, List.take_succ_cons, List.map_cons,
    getElem_val_eq_byteD, List.cons_beq_cons, beq_iff_eq, Nat.add_comm j 1, List.drop_drop]
  by_cases hb : byteD s j = a <;> simp [hb, Nat.add_comm]

theorem litAt_short {s : List U8} {j : Nat} {l : List Nat} (hl : 0 < l.length) (h : s.length < j + l.length) :
    litAt s j l = false := by
  simp only [litAt, beq_eq_false_iff_ne, ne_eq]
  intro he
  have := congrArg List.length he
  simp at this; omega

@[step]
theorem parse_literal_loop_spec (s lit : Slice U8) (i k : Usize) (hk : k.val ≤ lit.length)
    (hb : i.val + lit.length ≤ s.length) :
    json.parse_literal_loop s i lit k ⦃ r => r.map (·.val) =
      if litAt s.val (i.val + k.val) ((lit.val.drop k.val).map (·.val)) then some (i.val + lit.length) else none ⦄ := by
  unfold json.parse_literal_loop
  have hidx := index_u8_spec s
  have hidx' := index_u8_spec lit
  step*
  all_goals try (
    have hkl : k.val < lit.val.length := by scalar_tac
    have hd : (lit.val.drop k.val).map (·.val) = byteD lit.val k.val :: (lit.val.drop (k.val + 1)).map (·.val) := by
      rw [List.drop_eq_getElem_cons hkl, List.map_cons, getElem_val_eq_byteD]
    rw [hd, litAt_cons _ _ (by scalar_tac)])
  · simp_all [UScalar.neq_to_neq_val]
  · rw [r_post]
    simp_all [UScalar.neq_to_neq_val, Nat.add_assoc]
  · rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simp_all [litAt_nil]
termination_by lit.length - k.val
decreasing_by all_goals scalar_decr_tac

theorem litAt_bound {s : List U8} {j : Nat} {l : List Nat} (hl : 0 < l.length) (h : litAt s j l = true) :
    j + l.length ≤ s.length := by
  simp only [litAt, beq_iff_eq] at h
  have := congrArg List.length h
  simp at this; omega

@[step]
theorem parse_literal_spec (s lit : Slice U8) (i : Usize) (hl : 0 < lit.length) :
    json.parse_literal s i lit ⦃ r => r.map (·.val) =
      if litAt s.val i.val (lit.val.map (·.val)) then some (i.val + lit.length) else none ⦄ := by
  unfold json.parse_literal
  step*
  · rw [litAt_short (by simp; scalar_tac) (by simp; scalar_tac)]; rfl
  · rw [litAt_short (by simp; scalar_tac) (by simp; scalar_tac)]; rfl
  · simpa using r_post

-- 葉 (配列・オブジェクト以外) の節点の値
def leafS : json.JsonNode → JsonS
  | .Null => .null
  | .Bool b => .bool b
  | .Number n => n.toS
  | .String b => .str (b.val.map (·.val))
  | .Array _ => .null
  | .Object _ => .null

def isLeaf : json.JsonNode → Prop
  | .Array _ => False
  | .Object _ => False
  | _ => True

theorem treeN_leaf {nodes : List json.JsonNode} {id : Nat} {n : json.JsonNode} (h : nodes[id]? = some n) (hl : isLeaf n) :
    treeN nodes id = leafS n := by
  rw [treeN, h]
  cases n <;> simp_all [isLeaf, leafS]

-- '[' '{' 以外で始まる値の場合分け
theorem valueEnd_leaf_cases {s : List U8} {i d : Nat} {v : JsonS} {k c : Nat} (hv : valueEnd s i d v = some k)
    (hb : byteAt s i = some c) (h1 : c ≠ 0x5B) (h2 : c ≠ 0x7B) :
    (c = 0x22 ∧ ∃ b, v = .str b ∧ strAt s (i + 1) = some (b, k)) ∨
    (c = 0x74 ∧ v = .bool true ∧ litAt s i [0x74, 0x72, 0x75, 0x65] = true) ∨
    (c = 0x66 ∧ v = .bool false ∧ litAt s i [0x66, 0x61, 0x6C, 0x73, 0x65] = true) ∨
    (c = 0x6E ∧ v = .null ∧ litAt s i [0x6E, 0x75, 0x6C, 0x6C] = true) ∨
    ((c = 0x2D ∨ (0x30 ≤ c ∧ c ≤ 0x39)) ∧ ∃ p, numAt s i = some (p, k)) := by
  obtain ⟨b, hb', hs⟩ := valueEnd_start hv
  rw [hb] at hb'; cases hb'
  cases v with
  | null => simp only [valueEnd] at hv; split at hv <;> simp_all [startsOk]
  | bool x => cases x <;> simp only [valueEnd] at hv <;> split at hv <;> simp_all [startsOk]
  | num neg I F en E =>
    simp only [valueEnd, Option.bind_eq_some_iff] at hv
    obtain ⟨⟨p, k'⟩, hp, hp2⟩ := hv
    split at hp2
    · simp only [Option.some.injEq] at hp2; subst hp2
      right; right; right; right
      exact ⟨by simpa [startsOk] using hs, p, hp⟩
    · cases hp2
  | str x =>
    simp only [valueEnd, hb] at hv
    simp only [startsOk] at hs; subst hs
    simp only [↓reduceIte, Option.bind_eq_some_iff] at hv
    obtain ⟨⟨b', k'⟩, hp, hp2⟩ := hv
    split at hp2
    · simp only [Option.some.injEq] at hp2; subst hp2
      rename_i hbb; simp only at hbb; subst hbb
      left; exact ⟨rfl, b', rfl, hp⟩
    · cases hp2
  | arr => simp [startsOk] at hs; omega
  | obj => simp [startsOk] at hs; omega

@[step]
theorem parse_scalar_spec (s : Slice U8) (i : Usize) (h : i.val < s.length) :
    json.parse_scalar s i ⦃ r => match r with
      | none => byteD s.val i.val ≠ 0x5B → byteD s.val i.val ≠ 0x7B → ∀ d v, valueEnd s.val i.val d v = none
      | some (node, k) => isLeaf node ∧ (∀ id, nodeWf id node) ∧ i.val < k.val ∧ k.val ≤ s.length ∧
          ∀ d, valueEnd s.val i.val d (leafS node) = some k.val ⦄ := by
  unfold json.parse_scalar
  have hidx := index_u8_spec s
  have hb : byteAt s.val i.val = some (byteD s.val i.val) := byteAt_eq_byteD h
  step*
  all_goals clear hidx
  all_goals first
    | (intro h1 h2 d v
       cases hv : valueEnd s.val i.val d v with
       | none => rfl
       | some k =>
         exfalso
         rcases valueEnd_leaf_cases hv hb h1 h2 with ⟨hc, b, rfl, hs⟩ | ⟨hc, rfl, hl⟩ | ⟨hc, rfl, hl⟩ |
           ⟨hc, rfl, hl⟩ | ⟨hc, p, hp⟩ <;>
         simp_all [isDigit, UScalar.eq_equiv, UScalar.ofNatCore_val_eq, Bool.and_eq_false_iff,
           decide_eq_false_iff_not] <;> omega)
    | (rcases p with ⟨v, j⟩
       have hs : strAt s.val (i.val + 1) = some (v.val.map (·.val), j.val) := by
         rw [← i1_post]
         cases hh : strAt s.val i1.val <;> simp_all [vec_new_val]
       have := strAt_bound hs
       simp_all [isLeaf, nodeWf, leafS, valueEnd, UScalar.eq_equiv] <;> omega)
    | (rcases p with ⟨n, j⟩
       simp_all [isLeaf, nodeWf, leafS, valueEnd, json.number.Number.toS, json.number.Number.toParts]; done)
    | (simp_all [isLeaf, nodeWf, leafS, valueEnd]
       have := litAt_bound (by simp) o_post.1
       simp at this; omega)
    | (intro h1 h2 d v
       cases hv : valueEnd s.val i.val d v with
       | none => rfl
       | some k =>
         exfalso
         rcases valueEnd_leaf_cases hv hb h1 h2 with ⟨hc, b, rfl, hs⟩ | ⟨hc, rfl, hl⟩ | ⟨hc, rfl, hl⟩ |
           ⟨hc, rfl, hl⟩ | ⟨hc, p, hp⟩
         all_goals first
           | (simp only [isDigit] at *
              simp_all [UScalar.eq_equiv, UScalar.ofNatCore_val_eq, Bool.and_eq_false_iff,
                decide_eq_false_iff_not]; done)
           | (simp only [isDigit] at *
              subst b_post
              simp only [Bool.and_eq_true, decide_eq_true_eq] at *
              simp_all [UScalar.eq_equiv, UScalar.ofNatCore_val_eq]))

-- RFC 8259 §2: 空白
theorem skip_ws_spec (s : Slice U8) (i : Usize) : json.skip_ws s i ⦃ r => r.val = skipWs s.val i.val ⦄ :=
  skip_ws_loop_spec s i

/-! アリーナ (tree / nodesWf) の補題 -/

theorem getElem?_prefix {α} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : Nat} (hi : i < l₁.length) :
    l₂[i]? = l₁[i]? := by
  obtain ⟨t, rfl⟩ := h
  exact List.getElem?_append_left hi

theorem treeN_prefix {l₁ l₂ : List json.JsonNode} (h : l₁ <+: l₂) :
    ∀ id, id < l₁.length → treeN l₂ id = treeN l₁ id := by
  intro id
  induction id using Nat.strong_induction_on with
  | _ id ih =>
    intro hid
    rw [treeN, treeN, getElem?_prefix h hid]
    split
    all_goals try rfl
    · congr 1
      apply List.map_congr_left
      intro c _
      split
      · exact ih _ ‹_› (by omega)
      · rfl
    · congr 1
      apply List.map_congr_left
      intro m _
      congr 1
      split
      · exact ih _ ‹_› (by omega)
      · rfl

theorem treeN_arr {nodes : List json.JsonNode} {id : Nat} {v : alloc.vec.Vec Usize}
    (h : nodes[id]? = some (.Array v)) (hw : ∀ c ∈ v.val, c.val < id) :
    treeN nodes id = .arr (v.val.map fun c => treeN nodes c.val) := by
  rw [treeN, h]
  simp only [JsonS.arr.injEq]
  apply List.map_congr_left
  intro c hc
  rw [dite_eq_left (hw c hc)]

theorem treeN_obj {nodes : List json.JsonNode} {id : Nat} {v : alloc.vec.Vec json.Member}
    (h : nodes[id]? = some (.Object v)) (hw : ∀ m ∈ v.val, m.value.val < id) :
    treeN nodes id = .obj (v.val.map fun m => (m.key.val.map (·.val), treeN nodes m.value.val)) := by
  rw [treeN, h]
  simp only [JsonS.obj.injEq]
  apply List.map_congr_left
  intro m hm
  rw [dite_eq_left (hw m hm)]

theorem nodesWf_push {l : List json.JsonNode} {n : json.JsonNode} (h : nodesWf l) (hn : nodeWf l.length n) :
    nodesWf (l ++ [n]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i l.length with h' | h'
  · rw [List.getElem_append_left h']; exact h i h'
  · have : i = l.length := by omega
    subst this
    simpa using hn

theorem nodesWf_get {l : List json.JsonNode} (h : nodesWf l) {i : Nat} {n : json.JsonNode} (hi : l[i]? = some n) :
    nodeWf i n := by
  have hlt : i < l.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have := h i hlt
  rw [List.getElem?_eq_getElem hlt] at hi
  cases hi; exact this

/-! J1: parse_value と parse_json -/

theorem valueEnd_oob {s : List U8} {i d : Nat} {v : JsonS} (h : s.length ≤ i) : valueEnd s i d v = none := by
  cases hv : valueEnd s i d v with
  | none => rfl
  | some k =>
    obtain ⟨b, hb, _⟩ := valueEnd_start hv
    have := byteAt_some' hb; omega

theorem elemsEnd_single (s : List U8) (j d : Nat) (v : JsonS) :
    elemsEnd s j d [v] = (valueEnd s j d v).bind (closeAt s 0x5D) := by simp [elemsEnd]

theorem elemsEnd_cons2 (s : List U8) (j d : Nat) (v w : JsonS) (ws : List JsonS) :
    elemsEnd s j d (v :: w :: ws) = (valueEnd s j d v).bind fun k =>
      if byteAt s (skipWs s k) = some 0x2C then elemsEnd s (skipWs s (skipWs s k + 1)) d (w :: ws) else none := by
  simp [elemsEnd]

theorem membersEnd_single (s : List U8) (j d : Nat) (key : List Nat) (v : JsonS) :
    membersEnd s j d [(key, v)] =
      (keyAt s j).bind fun p => if p.1 = key then (valueEnd s p.2 d v).bind (closeAt s 0x7D) else none := by
  simp [membersEnd]

theorem membersEnd_cons2 (s : List U8) (j d : Nat) (key : List Nat) (v : JsonS) (m : List Nat × JsonS)
    (ms : List (List Nat × JsonS)) :
    membersEnd s j d ((key, v) :: m :: ms) = (keyAt s j).bind fun p =>
      if p.1 = key then
        (valueEnd s p.2 d v).bind fun k =>
          if byteAt s (skipWs s k) = some 0x2C then membersEnd s (skipWs s (skipWs s k + 1)) d (m :: ms) else none
      else none := by
  simp [membersEnd]

theorem skipWs_ge (s : List U8) (i : Nat) : i ≤ skipWs s i := by
  rw [skipWs]; split
  · split
    · have := skipWs_ge s (i + 1); omega
    · omega
  · omega
termination_by s.length - i

theorem skipWs_le (s : List U8) (i : Nat) (h : i ≤ s.length) : skipWs s i ≤ s.length := by
  rw [skipWs]; split
  · split
    · exact skipWs_le s (i + 1) (by omega)
    · omega
  · omega
termination_by s.length - i

-- skip_ws の仕様 (範囲付き): step* に局所仮定として渡す
theorem skip_ws_spec' (s : Slice U8) :
    ∀ x : Usize, json.skip_ws s x ⦃ r => r.val = skipWs s.val x.val ∧ x.val ≤ r.val ∧
      (x.val ≤ s.length → r.val ≤ s.length) ⦄ := by
  intro x
  apply WP.spec_mono (skip_ws_loop_spec s x)
  intro r hr
  rw [hr]; exact ⟨rfl, skipWs_ge _ _, skipWs_le _ _⟩

theorem elemsEnd_head {s : List U8} {j d : Nat} {v : JsonS} {rest : List JsonS} {r : Nat}
    (h : elemsEnd s j d (v :: rest) = some r) : ∃ k, valueEnd s j d v = some k := by
  cases rest with
  | nil => rw [elemsEnd_single, Option.bind_eq_some_iff] at h; obtain ⟨k, hk, _⟩ := h; exact ⟨k, hk⟩
  | cons w ws => rw [elemsEnd_cons2, Option.bind_eq_some_iff] at h; obtain ⟨k, hk, _⟩ := h; exact ⟨k, hk⟩

theorem elemsEnd_split {s : List U8} {j d : Nat} {v0 v : JsonS} {k : Nat} {rest : List JsonS} {r : Nat}
    (h0 : valueEnd s j d v0 = some k) (h : elemsEnd s j d (v :: rest) = some r) :
    (rest = [] ∧ byteAt s (skipWs s k) = some 0x5D) ∨
    (byteAt s (skipWs s k) = some 0x2C ∧ elemsEnd s (skipWs s (skipWs s k + 1)) d rest = some r) := by
  obtain ⟨k', hk'⟩ := elemsEnd_head h
  obtain ⟨-, rfl⟩ := valueEnd_det v v0 hk' h0
  cases rest with
  | nil =>
    rw [elemsEnd_single, hk', Option.bind_some] at h
    exact Or.inl ⟨rfl, (closeAt_some h).1⟩
  | cons w ws =>
    rw [elemsEnd_cons2, hk', Option.bind_some] at h
    split at h
    · exact Or.inr ⟨‹_›, h⟩
    · cases h

theorem elemsEnd_build_single {s : List U8} {j d : Nat} {v : JsonS} {k : Nat} (h0 : valueEnd s j d v = some k)
    (hc : byteAt s (skipWs s k) = some 0x5D) : elemsEnd s j d [v] = some (skipWs s k + 1) := by
  rw [elemsEnd_single, h0, Option.bind_some, closeAt, ite_eq_left hc]

theorem elemsEnd_build_cons {s : List U8} {j d : Nat} {v : JsonS} {k : Nat} {rest : List JsonS} {r : Nat}
    (h0 : valueEnd s j d v = some k) (hc : byteAt s (skipWs s k) = some 0x2C)
    (hr : elemsEnd s (skipWs s (skipWs s k + 1)) d rest = some r) : elemsEnd s j d (v :: rest) = some r := by
  cases rest with
  | nil => simp [elemsEnd] at hr
  | cons w ws => rw [elemsEnd_cons2, h0, Option.bind_some, ite_eq_left hc, hr]

-- parse_value の事後条件
def PVPost (s : Slice U8) (i : Usize) (d : Nat) (nodes : alloc.vec.Vec json.JsonNode)
    (r : Option (Usize × Usize)) (nodes' : alloc.vec.Vec json.JsonNode) : Prop :=
  nodes.val <+: nodes'.val ∧ nodesWf nodes'.val ∧ match r with
  | none => ∀ v, valueEnd s.val i.val d v = none
  | some (id, k) => nodes.val.length ≤ id.val ∧ id.val + 1 = nodes'.val.length ∧ i.val < k.val ∧
      k.val ≤ s.length ∧ nodes'.val.length ≤ k.val ∧ valueEnd s.val i.val d (treeN nodes'.val id.val) = some k.val

-- 予算 d' での parse_value の仕様 (帰納法の仮定)
def PVSpec (s : Slice U8) (d' : Usize) : Prop :=
  ∀ (i : Usize) (nodes : alloc.vec.Vec json.JsonNode), nodesWf nodes.val → nodes.val.length ≤ i.val →
    json.parse_value s i d' nodes ⦃ p => PVPost s i d'.val nodes p.1 p.2 ⦄

theorem keyAt_eq {s : List U8} {j : Nat} {kb : List Nat} {e : Nat} (hq : byteAt s j = some 0x22)
    (hs : strAt s (j + 1) = some (kb, e)) (hc : byteAt s (skipWs s e) = some 0x3A) :
    keyAt s j = some (kb, skipWs s (skipWs s e + 1)) := by
  simp [keyAt, hq, hs, hc]

theorem keyAt_some {s : List U8} {j : Nat} {p : List Nat × Nat} (h : keyAt s j = some p) :
    byteAt s j = some 0x22 ∧ ∃ e, strAt s (j + 1) = some (p.1, e) ∧ byteAt s (skipWs s e) = some 0x3A ∧
      p.2 = skipWs s (skipWs s e + 1) := by
  unfold keyAt at h
  split at h
  · rename_i hq
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨kb, e⟩, hs, h⟩ := h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact ⟨hq, e, hs, ‹_›, rfl⟩
    · cases h
  · cases h

theorem membersEnd_head {s : List U8} {j d : Nat} {key : List Nat} {v : JsonS} {rest : List (List Nat × JsonS)}
    {r : Nat} (h : membersEnd s j d ((key, v) :: rest) = some r) :
    ∃ p, keyAt s j = some p ∧ p.1 = key ∧ ∃ k, valueEnd s p.2 d v = some k := by
  cases rest with
  | nil =>
    rw [membersEnd_single, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    split at h
    · rw [Option.bind_eq_some_iff] at h; obtain ⟨k, hk, _⟩ := h; exact ⟨p, hp, ‹_›, k, hk⟩
    · cases h
  | cons m ms =>
    rw [membersEnd_cons2, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    split at h
    · rw [Option.bind_eq_some_iff] at h; obtain ⟨k, hk, _⟩ := h; exact ⟨p, hp, ‹_›, k, hk⟩
    · cases h

theorem membersEnd_split {s : List U8} {j d : Nat} {key0 : List Nat} {p2 : Nat} {v0 : JsonS} {k : Nat}
    {key : List Nat} {v : JsonS} {rest : List (List Nat × JsonS)} {r : Nat}
    (hkey : keyAt s j = some (key0, p2)) (h0 : valueEnd s p2 d v0 = some k)
    (h : membersEnd s j d ((key, v) :: rest) = some r) :
    (rest = [] ∧ byteAt s (skipWs s k) = some 0x7D) ∨
    (byteAt s (skipWs s k) = some 0x2C ∧ membersEnd s (skipWs s (skipWs s k + 1)) d rest = some r) := by
  obtain ⟨p, hp, hpk, k', hk'⟩ := membersEnd_head h
  rw [hkey] at hp; cases hp
  obtain ⟨-, rfl⟩ := valueEnd_det v v0 hk' h0
  cases rest with
  | nil =>
    rw [membersEnd_single, hkey, Option.bind_some, ite_eq_left hpk, hk', Option.bind_some] at h
    exact Or.inl ⟨rfl, (closeAt_some h).1⟩
  | cons m ms =>
    rw [membersEnd_cons2, hkey, Option.bind_some, ite_eq_left hpk, hk', Option.bind_some] at h
    split at h
    · exact Or.inr ⟨‹_›, h⟩
    · cases h

theorem membersEnd_build_single {s : List U8} {j d : Nat} {key : List Nat} {p2 : Nat} {v : JsonS} {k : Nat}
    (hkey : keyAt s j = some (key, p2)) (h0 : valueEnd s p2 d v = some k)
    (hc : byteAt s (skipWs s k) = some 0x7D) : membersEnd s j d [(key, v)] = some (skipWs s k + 1) := by
  rw [membersEnd_single, hkey, Option.bind_some, ite_eq_left rfl, h0, Option.bind_some, closeAt, ite_eq_left hc]

theorem membersEnd_build_cons {s : List U8} {j d : Nat} {key : List Nat} {p2 : Nat} {v : JsonS} {k : Nat}
    {rest : List (List Nat × JsonS)} {r : Nat}
    (hkey : keyAt s j = some (key, p2)) (h0 : valueEnd s p2 d v = some k)
    (hc : byteAt s (skipWs s k) = some 0x2C)
    (hr : membersEnd s (skipWs s (skipWs s k + 1)) d rest = some r) : membersEnd s j d ((key, v) :: rest) = some r := by
  cases rest with
  | nil => simp [membersEnd] at hr
  | cons m ms => rw [membersEnd_cons2, hkey, Option.bind_some, ite_eq_left rfl, h0, Option.bind_some, ite_eq_left hc, hr]

theorem parse_value_loop2_spec (s : Slice U8) (depth : Usize) (nodes : alloc.vec.Vec json.JsonNode)
    (members : alloc.vec.Vec json.Member) (j : Usize)
    (ih : ∀ d' : Usize, d'.val + 1 = depth.val → PVSpec s d') (hd : 0 < depth.val)
    (hwf : nodesWf nodes.val) (hlen : nodes.val.length ≤ j.val)
    (hit : ∀ m ∈ members.val, m.value.val < nodes.val.length) (hil : members.val.length ≤ nodes.val.length) :
    json.parse_value_loop2 s depth nodes members j ⦃ p =>
      nodes.val <+: p.2.val ∧ nodesWf p.2.val ∧ match p.1 with
      | none => ∀ ms, membersEnd s.val j.val (depth.val - 1) ms = none
      | some (id, k) => nodes.val.length ≤ id.val ∧ id.val + 1 = p.2.val.length ∧ j.val < k.val ∧
          k.val ≤ s.length ∧ p.2.val.length ≤ k.val ∧
          ∃ v new, p.2.val[id.val]? = some (.Object v) ∧ v.val = members.val ++ new ∧
            membersEnd s.val j.val (depth.val - 1)
              (new.map fun m => (m.key.val.map (·.val), treeN p.2.val m.value.val)) = some k.val ⦄ := by
  unfold json.parse_value_loop2
  have hsk := skip_ws_spec' s
  have hidx := index_u8_spec s
  have hps := parse_string_spec s
  have ih2 : ∀ d' : Usize, d'.val + 1 = depth.val → ∀ (i : Usize) (nodes : alloc.vec.Vec json.JsonNode),
      nodesWf nodes.val → nodes.val.length ≤ i.val →
      json.parse_value s i d' nodes ⦃ p => PVPost s i d'.val nodes p.1 p.2 ⦄ := ih
  step*
  · -- 入力の終わり
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    rintro (_ | ⟨⟨key, v⟩, rest⟩)
    · rfl
    · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨p, hp, -⟩ := membersEnd_head he
        have := byteAt_some' (keyAt_some hp).1; scalar_tac
  · -- " でない
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    rintro (_ | ⟨⟨key, v⟩, rest⟩)
    · rfl
    · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨p, hp, -⟩ := membersEnd_head he
        have h1 := (keyAt_some hp).1
        rw [byteAt_eq_byteD (by scalar_tac)] at h1
        simp_all [UScalar.neq_to_neq_val]
  · -- キーの文字列が不正
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    rintro (_ | ⟨⟨key, v⟩, rest⟩)
    · rfl
    · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨p, hp, -⟩ := membersEnd_head he
        obtain ⟨_, e, hs, _⟩ := keyAt_some hp
        simp_all
  · obtain ⟨kb, e⟩ := p
    have hq : byteAt s.val j.val = some 0x22 := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.neq_to_neq_val]
    have hstr : strAt s.val (j.val + 1) = some (kb.val.map (·.val), e.val) := by simp_all
    have hsb := strAt_bound hstr
    step*
    · -- キーの後で入力の終わり
      refine ⟨List.prefix_refl _, hwf, ?_⟩
      rintro (_ | ⟨⟨key, v⟩, rest⟩)
      · rfl
      · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
        | none => rfl
        | some r =>
          obtain ⟨p, hp, -⟩ := membersEnd_head he
          obtain ⟨_, e', hs, hc, _⟩ := keyAt_some hp
          rw [hstr] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
          have := byteAt_some' hc; scalar_tac
    · -- : がない
      refine ⟨List.prefix_refl _, hwf, ?_⟩
      rintro (_ | ⟨⟨key, v⟩, rest⟩)
      · rfl
      · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
        | none => rfl
        | some r =>
          obtain ⟨p, hp, -⟩ := membersEnd_head he
          obtain ⟨_, e', hs, hc, _⟩ := keyAt_some hp
          rw [hstr] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
          rw [← j1_post, byteAt_eq_byteD (by scalar_tac)] at hc
          simp_all [UScalar.neq_to_neq_val]
    · -- 値の解析に失敗
      simp only [PVPost] at o1_post
      obtain ⟨hpre, hwf1, ho⟩ := o1_post
      rename_i ho1
      rw [ho1] at ho
      refine ⟨hpre, hwf1, ?_⟩
      rintro (_ | ⟨⟨key, v⟩, rest⟩)
      · rfl
      · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
        | none => rfl
        | some r =>
          obtain ⟨p, hp, -, k, hk⟩ := membersEnd_head he
          obtain ⟨_, e', hs, hc, hp2⟩ := keyAt_some hp
          rw [hstr] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
          rw [hp2, ← j1_post, ← i5_post, ← j2_post, show depth.val - 1 = i6.val by scalar_tac, ho v] at hk
          cases hk
    · obtain ⟨id, k1⟩ := p1
      simp only [PVPost] at o1_post
      obtain ⟨hpre, hwf1, ho⟩ := o1_post
      rename_i ho1
      rw [ho1] at ho
      obtain ⟨hid0, hid1, hk1, hk2, hk3, hv⟩ := ho
      have hpl := hpre.length_le
      have hkey : keyAt s.val j.val = some (kb.val.map (·.val), j2.val) := by
        rw [keyAt_eq hq hstr (by rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.neq_to_neq_val]),
          j2_post, i5_post, j1_post]
      rw [show i6.val = depth.val - 1 by scalar_tac] at hv
      step*
      · -- 値の後で入力の終わり
        refine ⟨hpre, hwf1, ?_⟩
        rintro (_ | ⟨⟨key, v⟩, rest⟩)
        · rfl
        · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
          | none => rfl
          | some r =>
            exfalso
            rcases membersEnd_split hkey hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;>
            · rw [← j3_post] at hb; have := byteAt_some' hb; scalar_tac
      · intro m hm
        simp only [members1_post, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have := hit m hm; omega
        · simp; omega
      · simp only [members1_post, List.length_append, List.length_singleton]; omega
      · -- , の後の再帰
        have hpre2 := p_post
        have hr := p_post2
        refine ⟨hpre.trans hpre2, p_post1, ?_⟩
        obtain ⟨r1, nodes'⟩ := p
        simp only at hr hpre2 ⊢
        rcases r1 with _ | ⟨id', k'⟩
        · rintro (_ | ⟨⟨key, v⟩, rest⟩)
          · rfl
          · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
            | none => rfl
            | some r =>
              exfalso
              have hb2 : byteAt s.val (skipWs s.val k1.val) = some 0x2C := by
                rw [← j3_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
              rcases membersEnd_split hkey hv he with ⟨_, hb⟩ | ⟨_, hr3⟩
              · rw [hb] at hb2; cases hb2
              · rw [← j3_post, ← i9_post, ← j4_post, hr] at hr3; cases hr3
        · obtain ⟨h1, h2, h3, h4, h5, v', new', hv1, hv2, hv3⟩ := hr
          refine ⟨by omega, h2, by omega, h4, h5, v', { key := kb, value := id } :: new', hv1,
            by simp [hv2, members1_post], ?_⟩
          have ht : treeN nodes'.val id.val = treeN nodes1.val id.val := treeN_prefix hpre2 _ (by omega)
          simp only [List.map_cons]
          refine membersEnd_build_cons hkey (k := k1.val) (by rw [ht]; exact hv) ?_ ?_
          · rw [← j3_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
          · rw [← j3_post, ← i9_post, ← j4_post]; exact hv3
      · -- } で閉じる
        have hn2 : nodes2.val.length = nodes1.val.length + 1 := by simp [nodes2_post]
        have hi10 : i10.val = nodes1.val.length := by simp_all
        refine ⟨hpre.trans (by rw [nodes2_post]; exact List.prefix_append _ _), ?_, by omega, by omega,
          by scalar_tac, by scalar_tac, by scalar_tac, members1, [{ key := kb, value := id }], ?_,
          by simp [members1_post], ?_⟩
        · rw [nodes2_post]
          apply nodesWf_push hwf1
          intro m hm
          simp only [members1_post, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · have := hit m hm; omega
          · simp; omega
        · rw [hi10, nodes2_post]; simp
        · have ht : treeN nodes2.val id.val = treeN nodes1.val id.val :=
            treeN_prefix (by rw [nodes2_post]; exact List.prefix_append _ _) _ (by omega)
          simp only [List.map_cons, List.map_nil]
          rw [show i11.val = skipWs s.val k1.val + 1 by rw [i11_post, j3_post]]
          refine membersEnd_build_single hkey (by rw [ht]; exact hv) ?_
          rw [← j3_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
      · -- その他のバイト
        refine ⟨hpre, hwf1, ?_⟩
        rintro (_ | ⟨⟨key, v⟩, rest⟩)
        · rfl
        · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
          | none => rfl
          | some r =>
            exfalso
            have hb2 : byteAt s.val (skipWs s.val k1.val) = some i8.val := by
              rw [← j3_post, byteAt_eq_byteD (by scalar_tac), i8_post]
            rcases membersEnd_split hkey hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;> rw [hb] at hb2 <;> simp at hb2 <;>
              simp_all [UScalar.eq_equiv]
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

theorem parse_value_loop0_spec (s : Slice U8) (depth : Usize) (nodes : alloc.vec.Vec json.JsonNode)
    (items : alloc.vec.Vec Usize) (j : Usize)
    (ih : ∀ d' : Usize, d'.val + 1 = depth.val → PVSpec s d') (hd : 0 < depth.val)
    (hwf : nodesWf nodes.val) (hlen : nodes.val.length ≤ j.val)
    (hit : ∀ c ∈ items.val, c.val < nodes.val.length) (hil : items.val.length ≤ nodes.val.length) :
    json.parse_value_loop0 s depth nodes items j ⦃ p =>
      nodes.val <+: p.2.val ∧ nodesWf p.2.val ∧ match p.1 with
      | none => ∀ vs, elemsEnd s.val j.val (depth.val - 1) vs = none
      | some (id, k) => nodes.val.length ≤ id.val ∧ id.val + 1 = p.2.val.length ∧ j.val < k.val ∧
          k.val ≤ s.length ∧ p.2.val.length ≤ k.val ∧
          ∃ v new, p.2.val[id.val]? = some (.Array v) ∧ v.val = items.val ++ new ∧
            elemsEnd s.val j.val (depth.val - 1) (new.map fun c => treeN p.2.val c.val) = some k.val ⦄ := by
  unfold json.parse_value_loop0
  step as ⟨d1, hd1⟩
  have ih' := ih d1 (by scalar_tac)
  unfold PVSpec at ih'
  step as ⟨o, nodes1, ho⟩
  simp only [PVPost] at ho
  obtain ⟨hpre, hwf1, ho⟩ := ho
  rcases o with _ | ⟨id, k⟩
  · -- 要素の解析に失敗
    simp only [WP.spec_ok]
    refine ⟨hpre, hwf1, ?_⟩
    intro vs
    cases vs with
    | nil => rfl
    | cons v rest =>
      cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨k', hk'⟩ := elemsEnd_head he
        rw [show depth.val - 1 = d1.val by scalar_tac, ho v] at hk'
        cases hk'
  · obtain ⟨hid0, hid1, hk1, hk2, hk3, hv⟩ := ho
    have hsk := skip_ws_spec' s
    have hidx := index_u8_spec s
    have hpl := hpre.length_le
    rw [show d1.val = depth.val - 1 by scalar_tac] at hv
    step*
    · -- 要素の後で入力の終わり
      refine ⟨hpre, hwf1, ?_⟩
      intro vs
      cases vs with
      | nil => rfl
      | cons v rest =>
        cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
        | none => rfl
        | some r =>
          exfalso
          rcases elemsEnd_split hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;>
          · rw [← j1_post] at hb; have := byteAt_some' hb; scalar_tac
    · intro c hc
      simp only [items1_post, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · have := hit c hc; omega
      · omega
    · simp only [items1_post, List.length_append, List.length_singleton]; omega
    · -- , の後の再帰
      have hpre2 := p_post
      have hr := p_post2
      refine ⟨hpre.trans hpre2, p_post1, ?_⟩
      obtain ⟨r1, nodes'⟩ := p
      simp only at hr hpre2 ⊢
      rcases r1 with _ | ⟨id', k'⟩
      · intro vs
        cases vs with
        | nil => rfl
        | cons v rest =>
          cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
          | none => rfl
          | some r =>
            exfalso
            have hb2 : byteAt s.val (skipWs s.val k.val) = some 0x2C := by
              rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
            rcases elemsEnd_split hv he with ⟨_, hb⟩ | ⟨_, hr3⟩
            · rw [hb] at hb2; cases hb2
            · rw [← j1_post, ← i3_post, ← j2_post, hr] at hr3; cases hr3
      · obtain ⟨h1, h2, h3, h4, h5, v', new', hv1, hv2, hv3⟩ := hr
        refine ⟨by omega, h2, by omega, h4, h5, v', id :: new', hv1, by simp [hv2, items1_post], ?_⟩
        have ht : treeN nodes'.val id.val = treeN nodes1.val id.val := treeN_prefix hpre2 _ (by omega)
        simp only [List.map_cons]
        refine elemsEnd_build_cons (k := k.val) (by rw [ht]; exact hv) ?_ ?_
        · rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
        · rw [← j1_post, ← i3_post, ← j2_post]; exact hv3
    · -- ] で閉じる
      have hn2 : nodes2.val.length = nodes1.val.length + 1 := by simp [nodes2_post]
      have hi4 : i4.val = nodes1.val.length := by simp_all
      refine ⟨hpre.trans (by rw [nodes2_post]; exact List.prefix_append _ _), ?_, by omega, by omega,
        by scalar_tac, by scalar_tac, by scalar_tac, items1, [id], ?_, by simp [items1_post], ?_⟩
      · rw [nodes2_post]
        apply nodesWf_push hwf1
        intro c hc
        simp only [items1_post, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · have := hit c hc; omega
        · omega
      · rw [hi4, nodes2_post]; simp
      · have ht : treeN nodes2.val id.val = treeN nodes1.val id.val :=
          treeN_prefix (by rw [nodes2_post]; exact List.prefix_append _ _) _ (by omega)
        simp only [List.map_cons, List.map_nil]
        rw [show i5.val = skipWs s.val k.val + 1 by rw [i5_post, j1_post]]
        refine elemsEnd_build_single (by rw [ht]; exact hv) ?_
        rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    · -- その他のバイト
      refine ⟨hpre, hwf1, ?_⟩
      intro vs
      cases vs with
      | nil => rfl
      | cons v rest =>
        cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
        | none => rfl
        | some r =>
          exfalso
          have hb2 : byteAt s.val (skipWs s.val k.val) = some i2.val := by
            rw [← j1_post, byteAt_eq_byteD (by scalar_tac), i2_post]
          rcases elemsEnd_split hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;> rw [hb] at hb2 <;> simp at hb2 <;>
            simp_all [UScalar.eq_equiv]
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

-- loop1 / loop3 は loop0 / loop2 と同じ本体 (生成コードで別関数)
theorem parse_value_loop1_spec (s : Slice U8) (depth : Usize) (nodes : alloc.vec.Vec json.JsonNode)
    (items : alloc.vec.Vec Usize) (j : Usize)
    (ih : ∀ d' : Usize, d'.val + 1 = depth.val → PVSpec s d') (hd : 0 < depth.val)
    (hwf : nodesWf nodes.val) (hlen : nodes.val.length ≤ j.val)
    (hit : ∀ c ∈ items.val, c.val < nodes.val.length) (hil : items.val.length ≤ nodes.val.length) :
    json.parse_value_loop1 s depth nodes items j ⦃ p =>
      nodes.val <+: p.2.val ∧ nodesWf p.2.val ∧ match p.1 with
      | none => ∀ vs, elemsEnd s.val j.val (depth.val - 1) vs = none
      | some (id, k) => nodes.val.length ≤ id.val ∧ id.val + 1 = p.2.val.length ∧ j.val < k.val ∧
          k.val ≤ s.length ∧ p.2.val.length ≤ k.val ∧
          ∃ v new, p.2.val[id.val]? = some (.Array v) ∧ v.val = items.val ++ new ∧
            elemsEnd s.val j.val (depth.val - 1) (new.map fun c => treeN p.2.val c.val) = some k.val ⦄ := by
  unfold json.parse_value_loop1
  step as ⟨d1, hd1⟩
  have ih' := ih d1 (by scalar_tac)
  unfold PVSpec at ih'
  step as ⟨o, nodes1, ho⟩
  simp only [PVPost] at ho
  obtain ⟨hpre, hwf1, ho⟩ := ho
  rcases o with _ | ⟨id, k⟩
  · -- 要素の解析に失敗
    simp only [WP.spec_ok]
    refine ⟨hpre, hwf1, ?_⟩
    intro vs
    cases vs with
    | nil => rfl
    | cons v rest =>
      cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨k', hk'⟩ := elemsEnd_head he
        rw [show depth.val - 1 = d1.val by scalar_tac, ho v] at hk'
        cases hk'
  · obtain ⟨hid0, hid1, hk1, hk2, hk3, hv⟩ := ho
    have hsk := skip_ws_spec' s
    have hidx := index_u8_spec s
    have hpl := hpre.length_le
    rw [show d1.val = depth.val - 1 by scalar_tac] at hv
    step*
    · -- 要素の後で入力の終わり
      refine ⟨hpre, hwf1, ?_⟩
      intro vs
      cases vs with
      | nil => rfl
      | cons v rest =>
        cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
        | none => rfl
        | some r =>
          exfalso
          rcases elemsEnd_split hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;>
          · rw [← j1_post] at hb; have := byteAt_some' hb; scalar_tac
    · intro c hc
      simp only [items1_post, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · have := hit c hc; omega
      · omega
    · simp only [items1_post, List.length_append, List.length_singleton]; omega
    · -- , の後の再帰
      have hpre2 := p_post
      have hr := p_post2
      refine ⟨hpre.trans hpre2, p_post1, ?_⟩
      obtain ⟨r1, nodes'⟩ := p
      simp only at hr hpre2 ⊢
      rcases r1 with _ | ⟨id', k'⟩
      · intro vs
        cases vs with
        | nil => rfl
        | cons v rest =>
          cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
          | none => rfl
          | some r =>
            exfalso
            have hb2 : byteAt s.val (skipWs s.val k.val) = some 0x2C := by
              rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
            rcases elemsEnd_split hv he with ⟨_, hb⟩ | ⟨_, hr3⟩
            · rw [hb] at hb2; cases hb2
            · rw [← j1_post, ← i3_post, ← j2_post, hr] at hr3; cases hr3
      · obtain ⟨h1, h2, h3, h4, h5, v', new', hv1, hv2, hv3⟩ := hr
        refine ⟨by omega, h2, by omega, h4, h5, v', id :: new', hv1, by simp [hv2, items1_post], ?_⟩
        have ht : treeN nodes'.val id.val = treeN nodes1.val id.val := treeN_prefix hpre2 _ (by omega)
        simp only [List.map_cons]
        refine elemsEnd_build_cons (k := k.val) (by rw [ht]; exact hv) ?_ ?_
        · rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
        · rw [← j1_post, ← i3_post, ← j2_post]; exact hv3
    · -- ] で閉じる
      have hn2 : nodes2.val.length = nodes1.val.length + 1 := by simp [nodes2_post]
      have hi4 : i4.val = nodes1.val.length := by simp_all
      refine ⟨hpre.trans (by rw [nodes2_post]; exact List.prefix_append _ _), ?_, by omega, by omega,
        by scalar_tac, by scalar_tac, by scalar_tac, items1, [id], ?_, by simp [items1_post], ?_⟩
      · rw [nodes2_post]
        apply nodesWf_push hwf1
        intro c hc
        simp only [items1_post, List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · have := hit c hc; omega
        · omega
      · rw [hi4, nodes2_post]; simp
      · have ht : treeN nodes2.val id.val = treeN nodes1.val id.val :=
          treeN_prefix (by rw [nodes2_post]; exact List.prefix_append _ _) _ (by omega)
        simp only [List.map_cons, List.map_nil]
        rw [show i5.val = skipWs s.val k.val + 1 by rw [i5_post, j1_post]]
        refine elemsEnd_build_single (by rw [ht]; exact hv) ?_
        rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    · -- その他のバイト
      refine ⟨hpre, hwf1, ?_⟩
      intro vs
      cases vs with
      | nil => rfl
      | cons v rest =>
        cases he : elemsEnd s.val j.val (depth.val - 1) (v :: rest) with
        | none => rfl
        | some r =>
          exfalso
          have hb2 : byteAt s.val (skipWs s.val k.val) = some i2.val := by
            rw [← j1_post, byteAt_eq_byteD (by scalar_tac), i2_post]
          rcases elemsEnd_split hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;> rw [hb] at hb2 <;> simp at hb2 <;>
            simp_all [UScalar.eq_equiv]
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

theorem parse_value_loop3_spec (s : Slice U8) (depth : Usize) (nodes : alloc.vec.Vec json.JsonNode)
    (members : alloc.vec.Vec json.Member) (j : Usize)
    (ih : ∀ d' : Usize, d'.val + 1 = depth.val → PVSpec s d') (hd : 0 < depth.val)
    (hwf : nodesWf nodes.val) (hlen : nodes.val.length ≤ j.val)
    (hit : ∀ m ∈ members.val, m.value.val < nodes.val.length) (hil : members.val.length ≤ nodes.val.length) :
    json.parse_value_loop3 s depth nodes members j ⦃ p =>
      nodes.val <+: p.2.val ∧ nodesWf p.2.val ∧ match p.1 with
      | none => ∀ ms, membersEnd s.val j.val (depth.val - 1) ms = none
      | some (id, k) => nodes.val.length ≤ id.val ∧ id.val + 1 = p.2.val.length ∧ j.val < k.val ∧
          k.val ≤ s.length ∧ p.2.val.length ≤ k.val ∧
          ∃ v new, p.2.val[id.val]? = some (.Object v) ∧ v.val = members.val ++ new ∧
            membersEnd s.val j.val (depth.val - 1)
              (new.map fun m => (m.key.val.map (·.val), treeN p.2.val m.value.val)) = some k.val ⦄ := by
  unfold json.parse_value_loop3
  have hsk := skip_ws_spec' s
  have hidx := index_u8_spec s
  have hps := parse_string_spec s
  have ih2 : ∀ d' : Usize, d'.val + 1 = depth.val → ∀ (i : Usize) (nodes : alloc.vec.Vec json.JsonNode),
      nodesWf nodes.val → nodes.val.length ≤ i.val →
      json.parse_value s i d' nodes ⦃ p => PVPost s i d'.val nodes p.1 p.2 ⦄ := ih
  step*
  · -- 入力の終わり
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    rintro (_ | ⟨⟨key, v⟩, rest⟩)
    · rfl
    · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨p, hp, -⟩ := membersEnd_head he
        have := byteAt_some' (keyAt_some hp).1; scalar_tac
  · -- " でない
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    rintro (_ | ⟨⟨key, v⟩, rest⟩)
    · rfl
    · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨p, hp, -⟩ := membersEnd_head he
        have h1 := (keyAt_some hp).1
        rw [byteAt_eq_byteD (by scalar_tac)] at h1
        simp_all [UScalar.neq_to_neq_val]
  · -- キーの文字列が不正
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    rintro (_ | ⟨⟨key, v⟩, rest⟩)
    · rfl
    · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
      | none => rfl
      | some r =>
        obtain ⟨p, hp, -⟩ := membersEnd_head he
        obtain ⟨_, e, hs, _⟩ := keyAt_some hp
        simp_all
  · obtain ⟨kb, e⟩ := p
    have hq : byteAt s.val j.val = some 0x22 := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.neq_to_neq_val]
    have hstr : strAt s.val (j.val + 1) = some (kb.val.map (·.val), e.val) := by simp_all
    have hsb := strAt_bound hstr
    step*
    · -- キーの後で入力の終わり
      refine ⟨List.prefix_refl _, hwf, ?_⟩
      rintro (_ | ⟨⟨key, v⟩, rest⟩)
      · rfl
      · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
        | none => rfl
        | some r =>
          obtain ⟨p, hp, -⟩ := membersEnd_head he
          obtain ⟨_, e', hs, hc, _⟩ := keyAt_some hp
          rw [hstr] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
          have := byteAt_some' hc; scalar_tac
    · -- : がない
      refine ⟨List.prefix_refl _, hwf, ?_⟩
      rintro (_ | ⟨⟨key, v⟩, rest⟩)
      · rfl
      · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
        | none => rfl
        | some r =>
          obtain ⟨p, hp, -⟩ := membersEnd_head he
          obtain ⟨_, e', hs, hc, _⟩ := keyAt_some hp
          rw [hstr] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
          rw [← j1_post, byteAt_eq_byteD (by scalar_tac)] at hc
          simp_all [UScalar.neq_to_neq_val]
    · -- 値の解析に失敗
      simp only [PVPost] at o1_post
      obtain ⟨hpre, hwf1, ho⟩ := o1_post
      rename_i ho1
      rw [ho1] at ho
      refine ⟨hpre, hwf1, ?_⟩
      rintro (_ | ⟨⟨key, v⟩, rest⟩)
      · rfl
      · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
        | none => rfl
        | some r =>
          obtain ⟨p, hp, -, k, hk⟩ := membersEnd_head he
          obtain ⟨_, e', hs, hc, hp2⟩ := keyAt_some hp
          rw [hstr] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨-, rfl⟩ := hs
          rw [hp2, ← j1_post, ← i5_post, ← j2_post, show depth.val - 1 = i6.val by scalar_tac, ho v] at hk
          cases hk
    · obtain ⟨id, k1⟩ := p1
      simp only [PVPost] at o1_post
      obtain ⟨hpre, hwf1, ho⟩ := o1_post
      rename_i ho1
      rw [ho1] at ho
      obtain ⟨hid0, hid1, hk1, hk2, hk3, hv⟩ := ho
      have hpl := hpre.length_le
      have hkey : keyAt s.val j.val = some (kb.val.map (·.val), j2.val) := by
        rw [keyAt_eq hq hstr (by rw [← j1_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.neq_to_neq_val]),
          j2_post, i5_post, j1_post]
      rw [show i6.val = depth.val - 1 by scalar_tac] at hv
      step*
      · -- 値の後で入力の終わり
        refine ⟨hpre, hwf1, ?_⟩
        rintro (_ | ⟨⟨key, v⟩, rest⟩)
        · rfl
        · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
          | none => rfl
          | some r =>
            exfalso
            rcases membersEnd_split hkey hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;>
            · rw [← j3_post] at hb; have := byteAt_some' hb; scalar_tac
      · intro m hm
        simp only [members1_post, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · have := hit m hm; omega
        · simp; omega
      · simp only [members1_post, List.length_append, List.length_singleton]; omega
      · -- , の後の再帰
        have hpre2 := p_post
        have hr := p_post2
        refine ⟨hpre.trans hpre2, p_post1, ?_⟩
        obtain ⟨r1, nodes'⟩ := p
        simp only at hr hpre2 ⊢
        rcases r1 with _ | ⟨id', k'⟩
        · rintro (_ | ⟨⟨key, v⟩, rest⟩)
          · rfl
          · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
            | none => rfl
            | some r =>
              exfalso
              have hb2 : byteAt s.val (skipWs s.val k1.val) = some 0x2C := by
                rw [← j3_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
              rcases membersEnd_split hkey hv he with ⟨_, hb⟩ | ⟨_, hr3⟩
              · rw [hb] at hb2; cases hb2
              · rw [← j3_post, ← i9_post, ← j4_post, hr] at hr3; cases hr3
        · obtain ⟨h1, h2, h3, h4, h5, v', new', hv1, hv2, hv3⟩ := hr
          refine ⟨by omega, h2, by omega, h4, h5, v', { key := kb, value := id } :: new', hv1,
            by simp [hv2, members1_post], ?_⟩
          have ht : treeN nodes'.val id.val = treeN nodes1.val id.val := treeN_prefix hpre2 _ (by omega)
          simp only [List.map_cons]
          refine membersEnd_build_cons hkey (k := k1.val) (by rw [ht]; exact hv) ?_ ?_
          · rw [← j3_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
          · rw [← j3_post, ← i9_post, ← j4_post]; exact hv3
      · -- } で閉じる
        have hn2 : nodes2.val.length = nodes1.val.length + 1 := by simp [nodes2_post]
        have hi10 : i10.val = nodes1.val.length := by simp_all
        refine ⟨hpre.trans (by rw [nodes2_post]; exact List.prefix_append _ _), ?_, by omega, by omega,
          by scalar_tac, by scalar_tac, by scalar_tac, members1, [{ key := kb, value := id }], ?_,
          by simp [members1_post], ?_⟩
        · rw [nodes2_post]
          apply nodesWf_push hwf1
          intro m hm
          simp only [members1_post, List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | rfl
          · have := hit m hm; omega
          · simp; omega
        · rw [hi10, nodes2_post]; simp
        · have ht : treeN nodes2.val id.val = treeN nodes1.val id.val :=
            treeN_prefix (by rw [nodes2_post]; exact List.prefix_append _ _) _ (by omega)
          simp only [List.map_cons, List.map_nil]
          rw [show i11.val = skipWs s.val k1.val + 1 by rw [i11_post, j3_post]]
          refine membersEnd_build_single hkey (by rw [ht]; exact hv) ?_
          rw [← j3_post, byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
      · -- その他のバイト
        refine ⟨hpre, hwf1, ?_⟩
        rintro (_ | ⟨⟨key, v⟩, rest⟩)
        · rfl
        · cases he : membersEnd s.val j.val (depth.val - 1) ((key, v) :: rest) with
          | none => rfl
          | some r =>
            exfalso
            have hb2 : byteAt s.val (skipWs s.val k1.val) = some i8.val := by
              rw [← j3_post, byteAt_eq_byteD (by scalar_tac), i8_post]
            rcases membersEnd_split hkey hv he with ⟨_, hb⟩ | ⟨hb, _⟩ <;> rw [hb] at hb2 <;> simp at hb2 <;>
              simp_all [UScalar.eq_equiv]
termination_by s.length - j.val
decreasing_by all_goals scalar_decr_tac

theorem startsOk_arr {v : JsonS} (h : startsOk v 0x5B) : ∃ vs, v = .arr vs := by
  rcases v with _ | ⟨_ | _⟩ | _ | _ | vs | _ <;> simp [startsOk] at h ⊢

theorem startsOk_obj {v : JsonS} (h : startsOk v 0x7B) : ∃ ms, v = .obj ms := by
  rcases v with _ | ⟨_ | _⟩ | _ | _ | _ | ms <;> simp [startsOk] at h ⊢

theorem valueEnd_arr_none {s : List U8} {i d : Nat} (hb : byteAt s i = some 0x5B)
    (h1 : d ≠ 0 → closeAt s 0x5D (i + 1) = none)
    (h2 : d ≠ 0 → ∀ vs, elemsEnd s (skipWs s (i + 1)) (d - 1) vs = none) : ∀ v, valueEnd s i d v = none := by
  intro v
  cases hv : valueEnd s i d v with
  | none => rfl
  | some k =>
    exfalso
    obtain ⟨b, hb', hs⟩ := valueEnd_start hv
    rw [hb] at hb'; cases hb'
    obtain ⟨vs, rfl⟩ := startsOk_arr hs
    cases vs with
    | nil =>
      simp only [valueEnd] at hv
      split at hv
      · rename_i hc; rw [h1 hc.1] at hv; cases hv
      · cases hv
    | cons w ws =>
      simp only [valueEnd] at hv
      split at hv
      · rename_i hc; rw [h2 hc.1] at hv; cases hv
      · cases hv

theorem valueEnd_obj_none {s : List U8} {i d : Nat} (hb : byteAt s i = some 0x7B)
    (h1 : d ≠ 0 → closeAt s 0x7D (i + 1) = none)
    (h2 : d ≠ 0 → ∀ ms, membersEnd s (skipWs s (i + 1)) (d - 1) ms = none) : ∀ v, valueEnd s i d v = none := by
  intro v
  cases hv : valueEnd s i d v with
  | none => rfl
  | some k =>
    exfalso
    obtain ⟨b, hb', hs⟩ := valueEnd_start hv
    rw [hb] at hb'; cases hb'
    obtain ⟨ms, rfl⟩ := startsOk_obj hs
    cases ms with
    | nil =>
      simp only [valueEnd] at hv
      split at hv
      · rename_i hc; rw [h1 hc.1] at hv; cases hv
      · cases hv
    | cons w ws =>
      simp only [valueEnd] at hv
      split at hv
      · rename_i hc; rw [h2 hc.1] at hv; cases hv
      · cases hv

theorem closeAt_none {s : List U8} {c k : Nat} (h : byteAt s (skipWs s k) ≠ some c) : closeAt s c k = none := by
  simp [closeAt, h]

theorem arr_of_loop {s : List U8} {i d : Nat} {nodes' : List json.JsonNode} {id k : Nat} {v : alloc.vec.Vec Usize}
    {new : List Usize} (hb : byteAt s i = some 0x5B) (hd : d ≠ 0) (hwf : nodesWf nodes')
    (hv1 : nodes'[id]? = some (.Array v)) (hv2 : v.val = [] ++ new)
    (hv3 : elemsEnd s (skipWs s (i + 1)) (d - 1) (new.map fun c => treeN nodes' c.val) = some k) :
    valueEnd s i d (treeN nodes' id) = some k := by
  rw [treeN_arr hv1 (nodesWf_get hwf hv1), hv2, List.nil_append]
  obtain ⟨_, _, _, hne⟩ := elemsEnd_start hv3
  cases new with
  | nil => simp at hne
  | cons w ws =>
    simp only [List.map_cons] at hv3 ⊢
    simp only [valueEnd, hb, hd, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hv3]

theorem obj_of_loop {s : List U8} {i d : Nat} {nodes' : List json.JsonNode} {id k : Nat} {v : alloc.vec.Vec json.Member}
    {new : List json.Member} (hb : byteAt s i = some 0x7B) (hd : d ≠ 0) (hwf : nodesWf nodes')
    (hv1 : nodes'[id]? = some (.Object v)) (hv2 : v.val = [] ++ new)
    (hv3 : membersEnd s (skipWs s (i + 1)) (d - 1)
      (new.map fun m => (m.key.val.map (·.val), treeN nodes' m.value.val)) = some k) :
    valueEnd s i d (treeN nodes' id) = some k := by
  rw [treeN_obj hv1 (nodesWf_get hwf hv1), hv2, List.nil_append]
  have hne := (membersEnd_start hv3).2
  cases new with
  | nil => simp at hne
  | cons w ws =>
    simp only [List.map_cons] at hv3 ⊢
    simp only [valueEnd, hb, hd, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hv3]

set_option maxHeartbeats 2000000 in
theorem parse_value_body (s : Slice U8) (depth : Usize) (ihD : ∀ d' : Usize, d'.val + 1 = depth.val → PVSpec s d') :
    PVSpec s depth := by
  intro i nodes hwf hlen
  unfold json.parse_value
  have hsk := skip_ws_spec' s
  have hidx := index_u8_spec s
  have hl0 := fun nodes items j => parse_value_loop0_spec s depth nodes items j ihD
  have hl1 := fun nodes items j => parse_value_loop1_spec s depth nodes items j ihD
  have hl2 := fun nodes members j => parse_value_loop2_spec s depth nodes members j ihD
  have hl3 := fun nodes members j => parse_value_loop3_spec s depth nodes members j ihD
  step*
  all_goals try simp only [PVPost]
  · -- 入力の終わり
    exact ⟨List.prefix_refl _, hwf, fun v => valueEnd_oob (by scalar_tac)⟩
  · -- [ で予算 0
    have hb : byteAt s.val i.val = some 0x5B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    exact ⟨List.prefix_refl _, hwf, valueEnd_arr_none hb (fun h => absurd (by simp) h) (fun h => absurd (by simp) h)⟩
  · -- 空配列
    have hb : byteAt s.val i.val = some 0x5B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    have hd0 : depth.val ≠ 0 := by scalar_tac
    have hn1 : nodes1.val.length = nodes.val.length + 1 := by simp [nodes1_post]
    have hi6 : i6.val = nodes.val.length := by simp_all
    refine ⟨by rw [nodes1_post]; exact List.prefix_append _ _, ?_, by omega, by omega, by scalar_tac,
      by scalar_tac, by scalar_tac, ?_⟩
    · rw [nodes1_post]; exact nodesWf_push hwf (by simp [nodeWf])
    · rw [treeN_arr (v := alloc.vec.Vec.new Usize) (by rw [hi6, nodes1_post]; simp) (by simp)]
      simp only [vec_new_val, List.map_nil, valueEnd, hb, hd0, ne_eq, not_false_eq_true, and_self, ↓reduceIte, closeAt]
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post], i7_post, byteAt_eq_byteD (by scalar_tac)]
      simp_all [UScalar.eq_equiv]
  · intro c hc; simp [vec_new_val] at hc
  · -- 配列 (loop0)
    have hb : byteAt s.val i.val = some 0x5B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    have hd0 : depth.val ≠ 0 := by scalar_tac
    refine ⟨p_post, p_post1, ?_⟩
    have hr := p_post2
    obtain ⟨r1, nodes'⟩ := p
    simp only at hr ⊢
    rcases r1 with _ | ⟨id, k⟩
    · refine valueEnd_arr_none hb (fun _ => closeAt_none ?_) (fun _ => by rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hr)
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post], byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    · obtain ⟨h1, h2, h3, h4, h5, v, new, hv1, hv2, hv3⟩ := hr
      refine ⟨h1, h2, by scalar_tac, h4, h5, arr_of_loop hb hd0 p_post1 hv1 (by simpa using hv2) ?_⟩
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hv3
  · intro c hc; simp [vec_new_val] at hc
  · -- 配列 (loop1)
    have hb : byteAt s.val i.val = some 0x5B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    have hd0 : depth.val ≠ 0 := by scalar_tac
    refine ⟨p_post, p_post1, ?_⟩
    have hr := p_post2
    obtain ⟨r1, nodes'⟩ := p
    simp only at hr ⊢
    rcases r1 with _ | ⟨id, k⟩
    · refine valueEnd_arr_none hb (fun _ => closeAt_none ?_) (fun _ => by rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hr)
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post], byteAt_ge (by scalar_tac)]; simp
    · obtain ⟨h1, h2, h3, h4, h5, v, new, hv1, hv2, hv3⟩ := hr
      refine ⟨h1, h2, by scalar_tac, h4, h5, arr_of_loop hb hd0 p_post1 hv1 (by simpa using hv2) ?_⟩
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hv3
  · -- { で予算 0
    have hb : byteAt s.val i.val = some 0x7B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    exact ⟨List.prefix_refl _, hwf, valueEnd_obj_none hb (fun h => absurd (by simp) h) (fun h => absurd (by simp) h)⟩
  · -- 空オブジェクト
    have hb : byteAt s.val i.val = some 0x7B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    have hd0 : depth.val ≠ 0 := by scalar_tac
    have hn1 : nodes1.val.length = nodes.val.length + 1 := by simp [nodes1_post]
    have hi6 : i6.val = nodes.val.length := by simp_all
    refine ⟨by rw [nodes1_post]; exact List.prefix_append _ _, ?_, by omega, by omega, by scalar_tac,
      by scalar_tac, by scalar_tac, ?_⟩
    · rw [nodes1_post]; exact nodesWf_push hwf (by simp [nodeWf])
    · rw [treeN_obj (v := alloc.vec.Vec.new json.Member) (by rw [hi6, nodes1_post]; simp) (by simp)]
      simp only [vec_new_val, List.map_nil, valueEnd, hb, hd0, ne_eq, not_false_eq_true, and_self, ↓reduceIte, closeAt]
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post], i7_post, byteAt_eq_byteD (by scalar_tac)]
      simp_all [UScalar.eq_equiv]
  · intro c hc; simp [vec_new_val] at hc
  · -- オブジェクト (loop2)
    have hb : byteAt s.val i.val = some 0x7B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    have hd0 : depth.val ≠ 0 := by scalar_tac
    refine ⟨p_post, p_post1, ?_⟩
    have hr := p_post2
    obtain ⟨r1, nodes'⟩ := p
    simp only at hr ⊢
    rcases r1 with _ | ⟨id, k⟩
    · refine valueEnd_obj_none hb (fun _ => closeAt_none ?_) (fun _ => by rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hr)
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post], byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    · obtain ⟨h1, h2, h3, h4, h5, v, new, hv1, hv2, hv3⟩ := hr
      refine ⟨h1, h2, by scalar_tac, h4, h5, obj_of_loop hb hd0 p_post1 hv1 (by simpa using hv2) ?_⟩
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hv3
  · intro c hc; simp [vec_new_val] at hc
  · -- オブジェクト (loop3)
    have hb : byteAt s.val i.val = some 0x7B := by
      rw [byteAt_eq_byteD (by scalar_tac)]; simp_all [UScalar.eq_equiv]
    have hd0 : depth.val ≠ 0 := by scalar_tac
    refine ⟨p_post, p_post1, ?_⟩
    have hr := p_post2
    obtain ⟨r1, nodes'⟩ := p
    simp only at hr ⊢
    rcases r1 with _ | ⟨id, k⟩
    · refine valueEnd_obj_none hb (fun _ => closeAt_none ?_) (fun _ => by rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hr)
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post], byteAt_ge (by scalar_tac)]; simp
    · obtain ⟨h1, h2, h3, h4, h5, v, new, hv1, hv2, hv3⟩ := hr
      refine ⟨h1, h2, by scalar_tac, h4, h5, obj_of_loop hb hd0 p_post1 hv1 (by simpa using hv2) ?_⟩
      rw [show skipWs s.val (i.val + 1) = j.val by rw [j_post, i2_post]]; exact hv3
  · -- スカラー失敗
    refine ⟨List.prefix_refl _, hwf, ?_⟩
    have := o_post
    rw [‹o = none›] at this
    exact this (by simp_all [UScalar.eq_equiv]) (by simp_all [UScalar.eq_equiv]) _
  · -- スカラー成功
    have ho := o_post
    obtain ⟨node, k⟩ := p
    rw [‹o = some (node, k)›] at ho
    obtain ⟨hl, hnw, hk1, hk2, hv⟩ := ho
    step*
    try simp only [PVPost]
    have hn1 : nodes1.val.length = nodes.val.length + 1 := by simp [nodes1_post]
    have hi3 : i3.val = nodes.val.length := by simp_all
    refine ⟨by rw [nodes1_post]; exact List.prefix_append _ _, ?_, by omega, by omega, hk1, hk2, by omega, ?_⟩
    · rw [nodes1_post]; exact nodesWf_push hwf (hnw _)
    · rw [treeN_leaf (by rw [hi3, nodes1_post]; simp) hl]; exact hv _

theorem parse_value_spec_all : ∀ (n : Nat) (s : Slice U8) (depth : Usize), depth.val = n → PVSpec s depth
  | 0, s, depth, _ => parse_value_body s depth (fun d' hd' => by omega)
  | n + 1, s, depth, h => parse_value_body s depth (fun d' hd' => parse_value_spec_all n s d' (by omega))

/-- parse_value: nodes には追加のみ、結果のアリーナは整形 (子の添字 < 親の添字、Number は wf)、
    成功時は valueEnd (文法) と一致、失敗時は文法上どの値も読めない -/
@[step]
theorem parse_value_spec (s : Slice U8) (i depth : Usize) (nodes : alloc.vec.Vec json.JsonNode)
    (hwf : nodesWf nodes.val) (hlen : nodes.val.length ≤ i.val) :
    json.parse_value s i depth nodes ⦃ p => PVPost s i depth.val nodes p.1 p.2 ⦄ :=
  parse_value_spec_all _ s depth rfl i nodes hwf hlen

-- skipWs は「i 以上で j = |s| または ¬ws(s[j]) となる最小の j」(SPEC J.2 の skip_ws)
theorem skipWs_least (s : List U8) (i : Nat) (h : i ≤ s.length) :
    i ≤ skipWs s i ∧ skipWs s i ≤ s.length ∧
    (∀ hj : skipWs s i < s.length, isWs s[skipWs s i].val = false) ∧
    ∀ q, i ≤ q → q < skipWs s i → ∃ hq : q < s.length, isWs s[q].val = true := by
  rw [skipWs]
  split
  · rename_i hi
    split
    · rename_i hw
      obtain ⟨h1, h2, h3, h4⟩ := skipWs_least s (i + 1) (by omega)
      refine ⟨by omega, h2, h3, fun q hq1 hq2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hq1 with rfl | hq1
      · exact ⟨hi, hw⟩
      · exact h4 q hq1 hq2
    · rename_i hw
      simp only [Bool.not_eq_true] at hw
      exact ⟨le_refl _, h, fun _ => hw, fun q hq1 hq2 => by omega⟩
  · refine ⟨le_refl _, h, fun hj => by omega, fun q hq1 hq2 => by omega⟩
termination_by s.length - i

theorem jsonStart_eq (s : List U8) : jsonStart s =
    skipWs s (if 3 ≤ s.length ∧ byteD s 0 = 0xEF ∧ byteD s 1 = 0xBB ∧ byteD s 2 = 0xBF then 3 else 0) := by
  unfold jsonStart
  congr 1
  by_cases h : 3 ≤ s.length
  · rw [byteAt_eq_byteD (by omega), byteAt_eq_byteD (by omega), byteAt_eq_byteD (by omega)]
    simp [h]
  · rw [byteAt_ge (s := s) (i := 2) (by omega)]; simp [h]

theorem max_depth_val : json.MAX_DEPTH.val = 128 := by
  unfold json.MAX_DEPTH; rfl

/-- J1 -/
@[step]
theorem parse_json_spec (s : Slice U8) :
    json.parse_json s ⦃ r => match r with
      | none => jsonText s.val = none
      | some doc => jsonText s.val = some (tree doc doc.root.val) ∧ docWf doc ⦄ := by
  unfold json.parse_json
  simp only [bind_ite_res]
  have hsk := skip_ws_spec' s
  have hidx := index_u8_spec s
  step*
  iterate 3 (all_goals try (simp only [bind_ite_res]; step*))
  all_goals try (intro i hi; simp [vec_new_val] at hi; done)
  all_goals
    have hst : i2.val = jsonStart s.val := by
      rw [i2_post, jsonStart_eq]; congr 1
      split_ifs <;> simp_all [UScalar.eq_equiv]
    simp only [PVPost, vec_new_val, max_depth_val] at o_post
    obtain ⟨hpre0, hwf1, ho⟩ := o_post
    rename_i ho1
    rw [ho1] at ho
  all_goals first
    | (simp only at ho
       rw [jsonText_eq_none]
       rintro v ⟨k, hk, -⟩
       rw [← hst, ho v] at hk; cases hk)
    | (obtain ⟨root, j⟩ := p
       simp only at ho
       obtain ⟨-, hr1, hr2, hr3, -, hv⟩ := ho
       step*
       · refine ⟨jsonText_eq_some.mpr ⟨j.val, by rw [← hst]; exact hv, by simp_all⟩, ?_, hwf1⟩
         simp only; omega
       · rw [jsonText_eq_none]
         rintro v ⟨k, hk, hks⟩
         rw [← hst] at hk
         obtain ⟨-, rfl⟩ := valueEnd_det _ _ hk hv
         simp_all)

end LoadGltf
