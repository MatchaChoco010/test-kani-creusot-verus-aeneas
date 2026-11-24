import LoadGltf.Glb
import LoadGltf.Read.Mod
import LoadGltf.Validate.Mod

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! JSON テキストの値の節点数はテキストの長さ以下 -/

theorem keyAt_lt {s : List U8} {j : Nat} {p : List Nat × Nat} (h : keyAt s j = some p) : j < p.2 := by
  obtain ⟨-, e, hs, -, he⟩ := keyAt_some h
  have := (strAt_bound hs).1
  have := skipWs_ge s e
  have := skipWs_ge s (skipWs s e + 1)
  omega

theorem closeAt_gt {s : List U8} {c k r : Nat} (h : closeAt s c k = some r) : k < r := by
  obtain ⟨-, rfl⟩ := closeAt_some h
  have := skipWs_ge s k; omega

mutual
theorem valueEnd_size {s : List U8} : ∀ {i d : Nat} (v : JsonS) {k : Nat},
    valueEnd s i d v = some k → i + jsonSize v ≤ k
  | i, d, .null, k, h => by
    simp only [valueEnd] at h; split at h <;> simp_all [jsonSize] <;> omega
  | i, d, .bool b, k, h => by
    cases b <;> simp only [valueEnd] at h <;> split at h <;> simp_all [jsonSize] <;> omega
  | i, d, .num .., k, h => by
    simp only [valueEnd, Option.bind_eq_some_iff] at h
    obtain ⟨⟨p, k'⟩, hp, h2⟩ := h
    split at h2 <;> simp at h2
    have := (numAt_some hp).1
    simp [jsonSize]; omega
  | i, d, .str b, k, h => by
    simp only [valueEnd] at h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨b', k'⟩, hp, h2⟩ := h
      split at h2 <;> simp at h2
      have := (strAt_bound hp).1
      simp [jsonSize]; omega
    · cases h
  | i, d, .arr [], k, h => by
    simp only [valueEnd] at h
    split at h
    · have := closeAt_gt h; simp [jsonSize, listSize]; omega
    · cases h
  | i, d, .arr (v :: vs), k, h => by
    simp only [valueEnd] at h
    split at h
    · have := elemsEnd_size (v :: vs) h
      have := skipWs_ge s (i + 1)
      simp only [jsonSize]; omega
    · cases h
  | i, d, .obj [], k, h => by
    simp only [valueEnd] at h
    split at h
    · have := closeAt_gt h; simp [jsonSize, memSize]; omega
    · cases h
  | i, d, .obj (m :: ms), k, h => by
    simp only [valueEnd] at h
    split at h
    · have := membersEnd_size (m :: ms) h
      have := skipWs_ge s (i + 1)
      simp only [jsonSize]; omega
    · cases h

theorem elemsEnd_size {s : List U8} : ∀ {j d : Nat} (vs : List JsonS) {k : Nat},
    elemsEnd s j d vs = some k → j + listSize vs ≤ k
  | j, d, [], k, h => by simp [elemsEnd] at h
  | j, d, [v], k, h => by
    simp only [elemsEnd, Option.bind_eq_some_iff] at h
    obtain ⟨k1, hk1, h⟩ := h
    have := valueEnd_size v hk1
    have := closeAt_gt h
    simp [listSize]; omega
  | j, d, v :: w :: ws, k, h => by
    simp only [elemsEnd, Option.bind_eq_some_iff] at h
    obtain ⟨k1, hk1, h⟩ := h
    split at h
    · have := valueEnd_size v hk1
      have := elemsEnd_size (w :: ws) h
      have := skipWs_ge s k1
      have := skipWs_ge s (skipWs s k1 + 1)
      simp only [listSize] at *; omega
    · cases h

theorem membersEnd_size {s : List U8} : ∀ {j d : Nat} (ms : List (List Nat × JsonS)) {k : Nat},
    membersEnd s j d ms = some k → j + memSize ms ≤ k
  | j, d, [], k, h => by simp [membersEnd] at h
  | j, d, [(key, v)], k, h => by
    simp only [membersEnd, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨k1, hk1, h⟩ := h
      have := keyAt_lt hp
      have := valueEnd_size v hk1
      have := closeAt_gt h
      simp [memSize]; omega
    · cases h
  | j, d, (key, v) :: m :: ms, k, h => by
    simp only [membersEnd, Option.bind_eq_some_iff] at h
    obtain ⟨p, hp, h⟩ := h
    split at h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨k1, hk1, h⟩ := h
      split at h
      · have := keyAt_lt hp
        have := valueEnd_size v hk1
        have := membersEnd_size (m :: ms) h
        have := skipWs_ge s k1
        have := skipWs_ge s (skipWs s k1 + 1)
        simp only [memSize] at *; omega
      · cases h
    · cases h
end

theorem jsonText_size {s : List U8} {v : JsonS} (h : jsonText s = some v) : jsonSize v ≤ s.length := by
  obtain ⟨k, hk, hs⟩ := jsonText_eq_some.mp h
  have := valueEnd_size v hk
  have := skipWs_ge s k
  omega

/-! ## T1: parse_gltf -/

-- T1 の仕様: GLB なら glb_spec、JSON テキストなら json_text_spec、読めれば read_spec (R1/R2)
def ParseGltfSpec (s : List U8) (r : core.result.Result model.Gltf model.GltfError) : Prop :=
  (isGlbSpec s →
    (r = .Err .Glb ↔ glbSpec s = none) ∧
    ∀ c, glbSpec s = some c → (r = .Err .Json ↔ jsonText c.1 = none) ∧
      ∀ j, jsonText c.1 = some j → ReadPost j true c.2 r) ∧
  (¬ isGlbSpec s →
    (r = .Err .Json ↔ jsonText s = none) ∧ ∀ j, jsonText s = some j → ReadPost j false none r)

theorem readPost_ne {j : JsonS} {glb : Bool} {bin : Option Nat} {r : core.result.Result model.Gltf model.GltfError}
    (h : ReadPost j glb bin r) : r ≠ .Err .Glb ∧ r ≠ .Err .Json := by
  constructor <;> (rintro rfl; exact h)

/-- T1 -/
@[step]
theorem parse_gltf_spec (bytes : Slice U8) : parse_gltf bytes ⦃ r => ParseGltfSpec bytes.val r ⦄ := by
  unfold parse_gltf
  step*
  all_goals subst_vars
  · -- GLB コンテナが不正
    have hg : glbSpec bytes.val = none := by rw [← o_post]; rfl
    refine ⟨fun _ => ⟨by simp [hg], fun c hc => by rw [hg] at hc; cases hc⟩, fun h => absurd (b_post.mp rfl) h⟩
  · -- JSON チャンクが不正
    have hg : glbSpec bytes.val = some (c.json.val, c.bin_len.map (·.val)) := by rw [← o_post]; rfl
    simp only at o1_post
    refine ⟨fun _ => ⟨by simp [hg], fun c' hc => ?_⟩, fun h => absurd (b_post.mp rfl) h⟩
    rw [hg] at hc; cases hc
    simp only [vec_deref_val] at o1_post
    exact ⟨by simp [o1_post], fun j hj => by rw [o1_post] at hj; cases hj⟩
  · simp only at o1_post
    have := jsonText_size o1_post.1
    have := c.json.deref.property
    scalar_tac
  · have hg : glbSpec bytes.val = some (c.json.val, c.bin_len.map (·.val)) := by rw [← o_post]; rfl
    simp only [vec_deref_val] at o1_post
    obtain ⟨hne1, hne2⟩ := readPost_ne r_post
    refine ⟨fun _ => ⟨by simp [hg, hne1], fun c' hc => ?_⟩, fun h => absurd (b_post.mp rfl) h⟩
    rw [hg] at hc; cases hc
    refine ⟨by simp [o1_post.1, hne2], fun j' hj => ?_⟩
    rw [o1_post.1] at hj; cases hj
    exact r_post
  · simp only at o_post
    refine ⟨fun h => absurd (b_post.mpr h) ‹_›, fun _ => ⟨by simp [o_post], fun j hj => by rw [o_post] at hj; cases hj⟩⟩
  · simp only at o_post
    have := jsonText_size o_post.1
    have := bytes.property
    scalar_tac
  · simp only at o_post
    obtain ⟨hne1, hne2⟩ := readPost_ne r_post
    refine ⟨fun h => absurd (b_post.mpr h) ‹_›, fun _ => ⟨by simp [o_post.1, hne2], fun j' hj => ?_⟩⟩
    rw [o_post.1] at hj; cases hj
    exact r_post

/-! ## T3: load_gltf -/

-- T3 の仕様: parse_gltf の仕様 (T1) を満たす結果 p について、Ok(g) ⇔ p = Ok(g) ∧ valid(g)。誤りは T1/T2 のとおり伝わる
def LoadGltfSpec (s : List U8) (r : core.result.Result model.Gltf model.GltfError) : Prop :=
  ∃ p, ParseGltfSpec s p ∧ match p with
    | .Err e => r = .Err e
    | .Ok g => (∀ g', r = .Ok g' ↔ g' = g ∧ valid g) ∧
        (r = .Err .Unsupported → refsOk g ∧ ¬ supportedSpec g) ∧
        (r = .Err .Invalid → ¬ refsOk g ∨ (supportedSpec g ∧ ¬ rulesSpec g)) ∧
        r ≠ .Err .Glb ∧ r ≠ .Err .Json

/-- T3 -/
@[step]
theorem load_gltf_spec (bytes : Slice U8) : load_gltf bytes ⦃ r => LoadGltfSpec bytes.val r ⦄ := by
  unfold load_gltf
  step*
  all_goals subst_vars
  · refine ⟨_, r_post, fun g' => ⟨fun h => ?_, fun ⟨h, _⟩ => by rw [h]⟩, by simp, by simp, by simp, by simp⟩
    cases h; exact ⟨rfl, r1_post.mp rfl⟩
  · refine ⟨_, r_post, fun g' => ⟨fun h => (by cases h), fun ⟨_, hv⟩ => absurd (r1_post.mpr hv) (by simp)⟩,
      ?_, ?_, ?_, ?_⟩ <;> rcases e with _ | _ | _ | _ <;> simp_all
  · exact ⟨_, r_post, rfl⟩

/-! ## T4: process の事前条件 valid(g) -/

/-- T4: valid(g) のもとで process は失敗しない (massert は validate の Ok で成り立つ) -/
@[step]
theorem process_spec (g : model.Gltf) (h : valid g) : process g ⦃ _ => True ⦄ := by
  unfold process
  step*
  split
  · step*
  · exact absurd (r_post.mpr h) (by simp_all)

/-! ## T5: render -/

/-- T5: render(bytes) は load_gltf が Ok なら Ok(())、Err(e) ならそのまま Err(e) -/
theorem render_spec (bytes : Slice U8) :
    render bytes ⦃ r => ∃ l, LoadGltfSpec bytes.val l ∧ (r = .Ok () ↔ ∃ g, l = .Ok g) ∧
      ∀ e, l = .Err e → r = .Err e ⦄ := by
  unfold render
  step*
  all_goals subst_vars
  · -- process の事前条件: load_gltf の Ok から valid
    obtain ⟨p, hp, hm⟩ := r_post
    rcases p with g' | e
    · obtain ⟨he, hv⟩ := (hm.1 g).mp rfl
      rw [he]; exact hv
    · cases hm
  exact ⟨_, r_post, by simp, by simp⟩

/-! ## T6: render_unvalidated

render_unvalidated は parse_gltf の結果をそのまま process に渡す。process の事前条件 (debug_assert! の massert) は
validate g = Ok () (valid g) を要するが、parse_gltf の仕様 (T1) はそれを与えない。下の証明は
`⊢ valid g` (process_spec の事前条件) で止まり、process を展開すると validate g = Err e の分岐で massert の
`⊢ false = true` が残る。

-- 証明失敗: process の massert は validate g = Ok () を要するが、parse_gltf の事後条件からは導けない
theorem render_unvalidated_spec (bytes : Slice U8) :
    render_unvalidated bytes ⦃ r => ∃ p, ParseGltfSpec bytes.val p ∧ (r = .Ok () ↔ ∃ g, p = .Ok g) ∧
      ∀ e, p = .Err e → r = .Err e ⦄ := by
  unfold render_unvalidated
  step*
  all_goals subst_vars
  all_goals try exact ⟨_, r_post, by simp, by simp⟩
-/

end LoadGltf
