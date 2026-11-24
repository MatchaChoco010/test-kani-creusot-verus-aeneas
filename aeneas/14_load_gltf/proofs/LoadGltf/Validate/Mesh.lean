import LoadGltf.Json.Number
import LoadGltf.Validate.Refs

open Aeneas Aeneas.Std Result

namespace LoadGltf

-- 文字列リテラルのバイト列
def lit (s : String) : List U8 := s.toList.map (fun c => ⟨BitVec.ofNat 8 c.toNat⟩)

/-! ## 属性のセマンティクス (adoc 1626–1700) -/

abbrev isDigitByte (c : U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

-- 集合番号: 先頭 0 なし (0 自身を除く) の 1–9 桁の十進数
-- MUST-060, MUST-061, MUST-062: 集合の番号は先頭 0 なしの 9 桁以下の 10 進数
def setIndexSpec (d : List U8) : Option Nat :=
  if 1 ≤ d.length ∧ d.length ≤ 9 ∧ (∀ c ∈ d, isDigitByte c) ∧ (d.head? = some 48#u8 → d.length = 1)
  then some (digitsVal (d.map (fun c => c.val - 48)))
  else none

-- 種類の番号は実装の定数 SEM_* に合わせる: OTHER 0, POSITION 1, NORMAL 2, TANGENT 3,
-- TEXCOORD 4, COLOR 5, JOINTS 6, WEIGHTS 7, INVALID 8
def withSet (kind : Nat) (d : List U8) : Nat × Nat :=
  match setIndexSpec d with
  | some n => (kind, n)
  | none => (8, 0)

-- MUST-063: TEXCOORD_ などの後ろは正しい集合の番号
def semanticSpec (nm : List U8) : Nat × Nat :=
  if nm = lit "POSITION" then (1, 0)
  else if nm = lit "NORMAL" then (2, 0)
  else if nm = lit "TANGENT" then (3, 0)
  else if lit "TEXCOORD_" <+: nm then withSet 4 (nm.drop 9)
  else if lit "COLOR_" <+: nm then withSet 5 (nm.drop 6)
  else if lit "JOINTS_" <+: nm then withSet 6 (nm.drop 7)
  else if lit "WEIGHTS_" <+: nm then withSet 7 (nm.drop 8)
  else (0, 0)

-- 各セマンティクスで許される型 (adoc 1645, 1922)。morph はモーフターゲットでの使用
-- MUST-059, MUST-086: 属性とモーフターゲットの型の表
def attrTypeOk (kind : Nat) (a : model.Accessor) (morph : Bool) : Prop :=
  if kind = 0 then True
  else a.is_matrix = false ∧
    (if kind = 1 ∨ kind = 2 then a.components.val = 3 ∧ isFloat32 a
    else if kind = 3 then a.components.val = (if morph then 3 else 4) ∧ isFloat32 a
    else if kind = 4 then a.components.val = 2 ∧ (isFloat32 a ∨ isUnorm816 a ∨ (morph = true ∧ isSnorm816 a))
    else if kind = 5 then (a.components.val = 3 ∨ a.components.val = 4) ∧
      (isFloat32 a ∨ isUnorm816 a ∨ (morph = true ∧ isSnorm816 a))
    else if kind = 6 then morph = false ∧ a.components.val = 4 ∧ a.normalized = false ∧
      (a.component_type.val = 5121 ∨ a.component_type.val = 5123)
    else if kind = 7 then morph = false ∧ a.components.val = 4 ∧ (isFloat32 a ∨ isUnorm816 a)
    else False)

def hasSem (attrs : List model.Attribute) (kind set : Nat) : Prop :=
  ∃ x ∈ attrs, semanticSpec x.name.val = (kind, set)

def hasName (attrs : List model.Attribute) (nm : List U8) : Prop := ∃ x ∈ attrs, x.name.val = nm

-- M2 の各属性の条件。attrs は同じ属性集合、base はプリミティブの属性、count は最初の属性の count
-- MUST-057, MUST-063, MUST-064, MUST-066, MUST-069, MUST-083, MUST-088, MUST-089, MUST-091: 属性ごとの規則
def attrOk (g : model.Gltf) (attrs : List model.Attribute) (x : model.Attribute) (morph : Bool) (base : List model.Attribute)
    (count : Nat) : Prop :=
  let a := g.accessors.val[x.accessor.val]!
  let k := (semanticSpec x.name.val).1
  let n := (semanticSpec x.name.val).2
  k ≠ 8 ∧ attrTypeOk k a morph ∧ a.count.val = count ∧ (morph = true → hasName base x.name.val) ∧
  (k = 1 → a.min_len ≠ none ∧ a.max_len ≠ none) ∧
  (4 ≤ k ∧ k ≤ 7 ∧ 0 < n → hasSem attrs k (n - 1)) ∧
  (k = 6 → hasSem attrs 7 n) ∧ (k = 7 → hasSem attrs 6 n)

-- morph_count(mesh)
def morphCount (m : model.Mesh) : Nat :=
  match m.primitives.val.find? (fun p => p.targets.val ≠ []) with
  | some p => p.targets.val.length
  | none => 0

-- M4 のモード別の頂点数の条件
-- MUST-075, MUST-076, MUST-077, MUST-078, MUST-079, MUST-080, MUST-081: モード別の頂点数
def vertexCountOk (mode n : Nat) : Prop :=
  0 < n ∧ (mode = 1 → n % 2 = 0) ∧ (mode = 2 ∨ mode = 3 → 2 ≤ n) ∧ (mode = 4 → n % 3 = 0) ∧
  (5 ≤ mode → 3 ≤ n)

-- M3
-- MUST-071: インデックスは SCALAR の符号なし整数
def indexAccessorOk (a : model.Accessor) : Prop :=
  a.components.val = 1 ∧ a.is_matrix = false ∧ a.normalized = false ∧
  (a.component_type.val = 5121 ∨ a.component_type.val = 5123 ∨ a.component_type.val = 5125)

-- M1–M5 (プリミティブごと)
-- MUST-084, MUST-124: モーフターゲットの数、テクスチャの TEXCOORD
def primitiveOk (g : model.Gltf) (p : model.Primitive) (morph : Nat) : Prop :=
  p.attributes.val ≠ [] ∧ (p.targets.val ≠ [] → p.targets.val.length = morph) ∧
  let count := (g.accessors.val[(p.attributes.val[0]!).accessor.val]!).count.val
  (∀ x ∈ p.attributes.val, attrOk g p.attributes.val x false p.attributes.val count) ∧
  (∀ t ∈ p.targets.val, ∀ x ∈ t.val, attrOk g t.val x true p.attributes.val count) ∧
  (∀ ix, p.indices = some ix → indexAccessorOk (g.accessors.val[ix.val]!)) ∧
  vertexCountOk p.mode.val (match p.indices with
    | some ix => (g.accessors.val[ix.val]!).count.val
    | none => count) ∧
  (∀ m, p.material = some m → ∀ ti ∈ textureInfos (g.materials.val[m.val]!),
    hasSem p.attributes.val 4 ti.tex_coord.val)

-- M1–M5 (メッシュごと)
-- MUST-085: mesh.weights の長さ = モーフターゲットの数
def meshOk (g : model.Gltf) (m : model.Mesh) : Prop :=
  (∀ w, m.weights_len = some w → w.val = morphCount m) ∧ ∀ p ∈ m.primitives.val, primitiveOk g p (morphCount m)

def meshesOk (g : model.Gltf) : Prop := ∀ m ∈ g.meshes.val, meshOk g m

theorem lit_eq (s : String) (l : List U8) (h : lit s = l) : lit s = l := h

@[step]
theorem starts_with_loop_spec (s : alloc.vec.Vec U8) (p : Slice U8) (i : Usize)
    (hl : p.length ≤ s.val.length) (hi : i.val ≤ p.length) :
    validate.mesh.starts_with_loop s p i ⦃ r => r = true ↔ forallIdx p.val.length i.val (fun q => s.val[q]? = p.val[q]?) ⦄ := by
  unfold validate.mesh.starts_with_loop
  step*
  · simp only [Bool.false_eq_true, false_iff, forallIdx, not_forall]
    refine ⟨i.val, Nat.le_refl _, by scalar_tac, ?_⟩
    rw [List.getElem?_eq_getElem (by scalar_tac), List.getElem?_eq_getElem (by scalar_tac)]
    simp_all
  · rw [r_post, i4_post, forallIdx_step_slice (i := i) ‹_›,
      List.getElem?_eq_getElem (by scalar_tac : i.val < s.val.length),
      List.getElem?_eq_getElem (by scalar_tac : i.val < p.val.length)]
    simp_all [UScalar.eq_equiv]
  · simp [forallIdx_end_slice ‹_›]
termination_by p.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem starts_with_spec (s : alloc.vec.Vec U8) (p : Slice U8) :
    validate.mesh.starts_with s p ⦃ r => r = true ↔ p.val <+: s.val ⦄ := by
  unfold validate.mesh.starts_with
  step*
  · simp only [Bool.false_eq_true, false_iff]
    intro h; have := h.length_le; scalar_tac
  · rw [r_post, forallIdx_zero, List.prefix_iff_eq_take]
    constructor
    · intro h
      apply List.ext_getElem?
      intro q
      by_cases hq : q < p.val.length
      · rw [← h q hq, List.getElem?_take]; simp [hq]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · intro h q hq
      rw [h, List.getElem?_take]; simp [hq]

theorem digitsVal_cons (d : Nat) (l : List Nat) : digitsVal (d :: l) = d * 10 ^ l.length + digitsVal l := by
  have := digitsVal_append [d] l
  simp only [List.cons_append, List.nil_append] at this
  rw [this]; simp [digitsVal]

@[step]
theorem decimal_digits_loop_spec (s : alloc.vec.Vec U8) (v : U64) (i : Usize)
    (hi : i.val ≤ s.val.length) (h9 : s.val.length - i.val ≤ 9)
    (hv : v.val < 10 ^ (9 - (s.val.length - i.val))) :
    validate.mesh.decimal_digits_loop s v i ⦃ r => match r with
      | some x => (∀ c ∈ s.val.drop i.val, isDigitByte c) ∧
          x.val = v.val * 10 ^ (s.val.length - i.val) + digitsVal ((s.val.drop i.val).map (fun c => c.val - 48))
      | none => ¬ ∀ c ∈ s.val.drop i.val, isDigitByte c ⦄ := by
  unfold validate.mesh.decimal_digits_loop
  have hmx : (10 : Nat) ^ 9 ≤ U64.max := by simp [U64.max_eq]
  have hp9 : 10 ^ (9 - (s.val.length - i.val)) ≤ 10 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
  step*
  all_goals simp only [UScalar.lt_equiv, GT.gt, not_lt, UScalar.ofNatCore_val_eq] at *
  all_goals first
    | omega
    | (rw [List.drop_eq_getElem_cons (by scalar_tac)]
       simp only [List.mem_cons, forall_eq_or_imp, isDigitByte, not_and]
       intro h; exfalso; subst_vars; omega)
    | (have h0 : s.val.length - i.val = 0 := by scalar_tac
       rw [List.drop_eq_nil_of_le (by scalar_tac), h0]; simp [digitsVal])
    | (have h5 : i5.val = i4.val := by rw [i5_post]; exact U8.cast_U64_val_eq _
       have hr : 9 - (s.val.length - i6.val) = (9 - (s.val.length - i.val)) + 1 := by scalar_tac
       rw [hr, pow_succ]; omega)
    | (have h5 : i5.val = i4.val := by rw [i5_post]; exact U8.cast_U64_val_eq _
       have hlt : i.val < s.val.length := by scalar_tac
       have hd := List.drop_eq_getElem_cons hlt
       have hr : s.val.length - i.val = (s.val.length - (i.val + 1)) + 1 := by omega
       rw [i6_post] at r_post
       rcases r with _ | x <;> simp only at r_post ⊢
       · rw [hd]; simp only [List.mem_cons, forall_eq_or_imp, not_and]
         intro _; exact r_post
       · obtain ⟨hall, hx⟩ := r_post
         refine ⟨?_, ?_⟩
         · rw [hd]; simp only [List.mem_cons, forall_eq_or_imp]
           exact ⟨⟨by rw [← i2_post]; omega, by rw [← i2_post]; omega⟩, hall⟩
         · rw [hx, hd, List.map_cons, digitsVal_cons, List.length_map, List.length_drop, hr, pow_succ,
             v1_post, i3_post, h5, i4_post, ← i2_post]
           ring_nf)
termination_by s.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem decimal_digits_spec (s : alloc.vec.Vec U8) (start : Usize)
    (hi : start.val ≤ s.val.length) (h9 : s.val.length - start.val ≤ 9) :
    validate.mesh.decimal_digits s start ⦃ r => match r with
      | some x => (∀ c ∈ s.val.drop start.val, isDigitByte c) ∧
          x.val = digitsVal ((s.val.drop start.val).map (fun c => c.val - 48))
      | none => ¬ ∀ c ∈ s.val.drop start.val, isDigitByte c ⦄ := by
  unfold validate.mesh.decimal_digits
  have : 0 < 10 ^ (9 - (s.val.length - start.val)) := by positivity
  step*

theorem head_drop {α} (l : List α) (k : Nat) (h : k < l.length) : (l.drop k).head? = some l[k] := by
  rw [List.head?_drop, List.getElem?_eq_getElem h]

-- MUST-060, MUST-061, MUST-062: 集合の番号は先頭 0 なしの 9 桁以下の 10 進数
@[step]
theorem parse_set_index_spec (s : alloc.vec.Vec U8) (start : Usize) (hi : start.val ≤ s.val.length) :
    validate.mesh.parse_set_index s start ⦃ r => r.map (·.val) = setIndexSpec (s.val.drop start.val) ⦄ := by
  unfold validate.mesh.parse_set_index setIndexSpec
  have hlen : (s.val.drop start.val).length = s.val.length - start.val := List.length_drop
  step*
  all_goals simp only [UScalar.eq_equiv, UScalar.lt_equiv, GT.gt, UScalar.ofNatCore_val_eq,
    alloc.vec.Vec.len_val, Option.map_none] at *
  · rw [ite_eq_right (by scalar_tac)]
  · rw [ite_eq_right (by scalar_tac)]
  · rw [ite_eq_right]
    rintro ⟨-, -, -, h⟩
    have := h (by rw [head_drop _ _ (by scalar_tac)]; congr 1; apply UScalar.eq_equiv _ _ |>.mpr; simp_all)
    scalar_tac
  · rcases r with _ | x <;> simp only at r_post
    · rw [ite_eq_right (by tauto)]; rfl
    · rw [ite_eq_left ⟨by scalar_tac, by scalar_tac, r_post.1, fun _ => by scalar_tac⟩, ← r_post.2]; rfl
  · rcases r with _ | x <;> simp only at r_post
    · rw [ite_eq_right (by tauto)]; rfl
    · have hz : (s.val.drop start.val).head? = some 48#u8 → (s.val.drop start.val).length = 1 := by
        intro h; exfalso; rw [head_drop _ _ (by scalar_tac)] at h
        simp only [Option.some.injEq] at h
        apply ‹¬ i1.val = 48›
        rw [i1_post, h]; rfl
      rw [ite_eq_left ⟨by scalar_tac, by scalar_tac, r_post.1, hz⟩, ← r_post.2]
      rfl

theorem sem_consts : validate.mesh.SEM_OTHER = 0#u64 ∧ validate.mesh.SEM_POSITION = 1#u64 ∧ validate.mesh.SEM_NORMAL = 2#u64 ∧ validate.mesh.SEM_TANGENT = 3#u64 ∧
    validate.mesh.SEM_TEXCOORD = 4#u64 ∧ validate.mesh.SEM_COLOR = 5#u64 ∧ validate.mesh.SEM_JOINTS = 6#u64 ∧ validate.mesh.SEM_WEIGHTS = 7#u64 ∧
    validate.mesh.SEM_INVALID = 8#u64 := by
  unfold validate.mesh.SEM_OTHER validate.mesh.SEM_POSITION validate.mesh.SEM_NORMAL validate.mesh.SEM_TANGENT validate.mesh.SEM_TEXCOORD validate.mesh.SEM_COLOR validate.mesh.SEM_JOINTS validate.mesh.SEM_WEIGHTS validate.mesh.SEM_INVALID
  simp

-- MUST-063: TEXCOORD_ などの後ろは正しい集合の番号
@[step]
theorem semantic_spec (nm : alloc.vec.Vec U8) :
    validate.mesh.semantic nm ⦃ r => (r.1.val, r.2.val) = semanticSpec nm.val ⦄ := by
  unfold validate.mesh.semantic semanticSpec
  have l1 : lit "POSITION" = [80#u8, 79#u8, 83#u8, 73#u8, 84#u8, 73#u8, 79#u8, 78#u8] := rfl
  have l2 : lit "NORMAL" = [78#u8, 79#u8, 82#u8, 77#u8, 65#u8, 76#u8] := rfl
  have l3 : lit "TANGENT" = [84#u8, 65#u8, 78#u8, 71#u8, 69#u8, 78#u8, 84#u8] := rfl
  have l4 : lit "TEXCOORD_" = [84#u8, 69#u8, 88#u8, 67#u8, 79#u8, 79#u8, 82#u8, 68#u8, 95#u8] := rfl
  have l5 : lit "COLOR_" = [67#u8, 79#u8, 76#u8, 79#u8, 82#u8, 95#u8] := rfl
  have l6 : lit "JOINTS_" = [74#u8, 79#u8, 73#u8, 78#u8, 84#u8, 83#u8, 95#u8] := rfl
  have l7 : lit "WEIGHTS_" = [87#u8, 69#u8, 73#u8, 71#u8, 72#u8, 84#u8, 83#u8, 95#u8] := rfl
  have hc := sem_consts
  step*
  all_goals (simp only [l1, l2, l3, l4, l5, l6, l7] at *)
  all_goals simp_all [withSet]
  all_goals first
    | (rw [← o_post]; done)
    | (have := (‹_ <+: _›).length_le; simp_all)

-- MUST-059, MUST-086: 属性とモーフターゲットの型の表
@[step]
theorem attribute_type_ok_spec (kind : U64) (a : model.Accessor) (morph : Bool) :
    validate.mesh.attribute_type_ok kind a morph ⦃ r => r = true ↔ attrTypeOk kind.val a morph ⦄ := by
  unfold validate.mesh.attribute_type_ok attrTypeOk
  have hc := sem_consts
  cases morph <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_tc_ok] <;> step* <;>
    simp_all [UScalar.eq_equiv] <;> agrind

@[step]
theorem has_semantic_loop_spec (attrs : alloc.vec.Vec model.Attribute) (kind set : U64) (i : Usize)
    (hi : i.val ≤ attrs.val.length) :
    validate.mesh.has_semantic_loop attrs kind set i ⦃ r => r = false ↔
      forallFrom attrs.val i.val (fun x => semanticSpec x.name.val ≠ (kind.val, set.val)) ⦄ := by
  unfold validate.mesh.has_semantic_loop
  loop_auto [UScalar.eq_equiv]
termination_by attrs.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem has_semantic_spec (attrs : alloc.vec.Vec model.Attribute) (kind set : U64) :
    validate.mesh.has_semantic attrs kind set ⦃ r => r = true ↔ hasSem attrs.val kind.val set.val ⦄ := by
  unfold validate.mesh.has_semantic hasSem
  step*
  rw [← Bool.not_eq_false, r_post, forallFrom_zero]
  simp

@[step]
theorem has_name_loop_spec (attrs : alloc.vec.Vec model.Attribute) (nm : alloc.vec.Vec U8) (i : Usize)
    (hi : i.val ≤ attrs.val.length) :
    validate.mesh.has_name_loop attrs nm i ⦃ r => r = false ↔ forallFrom attrs.val i.val (fun x => x.name.val ≠ nm.val) ⦄ := by
  unfold validate.mesh.has_name_loop
  loop_auto
termination_by attrs.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem has_name_spec (attrs : alloc.vec.Vec model.Attribute) (nm : alloc.vec.Vec U8) :
    validate.mesh.has_name attrs nm ⦃ r => r = true ↔ hasName attrs.val nm.val ⦄ := by
  unfold validate.mesh.has_name hasName
  step*
  rw [← Bool.not_eq_false, r_post, forallFrom_zero]
  simp

-- MUST-057, MUST-063, MUST-064, MUST-066, MUST-069, MUST-083, MUST-088, MUST-089, MUST-091: 属性ごとの規則
set_option maxHeartbeats 2000000 in
@[step]
theorem attribute_ok_spec (g : model.Gltf) (attrs : alloc.vec.Vec model.Attribute) (i : Usize) (morph : Bool)
    (base : alloc.vec.Vec model.Attribute) (count : U64) (hi : i.val < attrs.val.length)
    (ha : attrs.val[i.val].accessor.val < g.accessors.val.length) :
    validate.mesh.attribute_ok g attrs i morph base count ⦃ r => r = true ↔
      attrOk g attrs.val attrs.val[i.val] morph base.val count.val ⦄ := by
  unfold validate.mesh.attribute_ok attrOk
  have hc := sem_consts
  have hm := mod_numBits_of_lt ha (by scalar_tac)
  step*
  all_goals (try (rw [hm]; exact ha))
  all_goals (try simp_all [UScalar.eq_equiv])
  all_goals (simp only [← kind_post]; simp_all [Option.isSome_iff_ne_none])
  all_goals (intros; omega)

@[step]
theorem attributes_ok_loop_spec (g : model.Gltf) (attrs : alloc.vec.Vec model.Attribute) (morph : Bool) (base : alloc.vec.Vec model.Attribute) (count : U64) (i : Usize) (ha : ∀ x ∈ attrs.val, x.accessor.val < g.accessors.val.length) (hi : i.val ≤ attrs.val.length) :
    validate.mesh.attributes_ok_loop g attrs morph base count i ⦃ r => r = true ↔
      forallFrom attrs.val i.val (fun x => attrOk g attrs.val (x) morph base.val count.val) ⦄ := by
  unfold validate.mesh.attributes_ok_loop
  loop_auto
termination_by attrs.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem attributes_ok_spec (g : model.Gltf) (attrs : alloc.vec.Vec model.Attribute) (morph : Bool) (base : alloc.vec.Vec model.Attribute) (count : U64) (ha : ∀ x ∈ attrs.val, x.accessor.val < g.accessors.val.length) :
    validate.mesh.attributes_ok g attrs morph base count ⦃ r => r = true ↔ ∀ x ∈ attrs.val, attrOk g attrs.val (x) morph base.val count.val ⦄ := by
  unfold validate.mesh.attributes_ok
  step*
  simp_all [forallFrom_zero]

@[step]
theorem targets_ok_loop_spec (g : model.Gltf) (p : model.Primitive) (count : U64) (t : Usize) (ha : ∀ t ∈ p.targets.val, ∀ y ∈ t.val, y.accessor.val < g.accessors.val.length) (hi : t.val ≤ p.targets.val.length) :
    validate.mesh.targets_ok_loop g p count t ⦃ r => r = true ↔
      forallFrom p.targets.val t.val (fun x => ∀ y ∈ (x).val, attrOk g (x).val y true p.attributes.val count.val) ⦄ := by
  unfold validate.mesh.targets_ok_loop
  have ha' : ∀ j (h : j < p.targets.val.length), ∀ y ∈ p.targets.val[j].val,
      y.accessor.val < g.accessors.val.length := fun j h => ha _ (List.getElem_mem h)
  loop_auto
termination_by p.targets.val.length - t.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem targets_ok_spec (g : model.Gltf) (p : model.Primitive) (count : U64) (ha : ∀ t ∈ p.targets.val, ∀ y ∈ t.val, y.accessor.val < g.accessors.val.length) :
    validate.mesh.targets_ok g p count ⦃ r => r = true ↔ ∀ x ∈ p.targets.val, ∀ y ∈ (x).val, attrOk g (x).val y true p.attributes.val count.val ⦄ := by
  unfold validate.mesh.targets_ok
  step*
  simp_all [forallFrom_zero]

-- 先頭から最初にターゲットを持つプリミティブのターゲット数
def morphCountOf (l : List model.Primitive) : Nat :=
  match l.find? (fun p => p.targets.val ≠ []) with
  | some p => p.targets.val.length
  | none => 0

@[step]
theorem morph_target_count_loop_spec (m : model.Mesh) (i : Usize) (hi : i.val ≤ m.primitives.val.length) :
    validate.mesh.morph_target_count_loop m i ⦃ r => r.val = morphCountOf (m.primitives.val.drop i.val) ⦄ := by
  unfold validate.mesh.morph_target_count_loop
  step*
  · rw [List.drop_eq_getElem_cons (by scalar_tac)]
    simp_all [morphCountOf, List.find?_cons, ← List.length_pos_iff_ne_nil]
  · rw [List.drop_eq_getElem_cons (by scalar_tac), r_post]
    simp_all [morphCountOf, List.find?_cons, ← List.length_pos_iff_ne_nil]
  · rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simp [morphCountOf]
termination_by m.primitives.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem morph_target_count_spec (m : model.Mesh) : validate.mesh.morph_target_count m ⦃ r => r.val = morphCount m ⦄ := by
  unfold validate.mesh.morph_target_count morphCount
  step*
  simp_all [morphCountOf]

-- MUST-075, MUST-076, MUST-077, MUST-078, MUST-079, MUST-080, MUST-081: モード別の頂点数
@[step]
theorem vertex_count_ok_spec (mode n : U64) :
    validate.mesh.vertex_count_ok mode n ⦃ r => r = true ↔ vertexCountOk mode.val n.val ⦄ := by
  unfold validate.mesh.vertex_count_ok vertexCountOk
  step* <;> simp_all [UScalar.eq_equiv] <;> agrind

@[step]
theorem texcoord_ok_spec (t : Option model.TextureInfo) (attrs : alloc.vec.Vec model.Attribute) :
    validate.mesh.texcoord_ok t attrs ⦃ r => r = true ↔ ∀ ti, t = some ti → hasSem attrs.val 4 ti.tex_coord.val ⦄ := by
  unfold validate.mesh.texcoord_ok
  have hc := sem_consts
  rcases t with _ | ti <;> step* <;> simp_all

-- MUST-124: テクスチャを使うなら TEXCOORD がある
@[step]
theorem material_texcoords_ok_spec (mat : model.Material) (attrs : alloc.vec.Vec model.Attribute) :
    validate.mesh.material_texcoords_ok mat attrs ⦃ r => r = true ↔
      ∀ ti ∈ textureInfos mat, hasSem attrs.val 4 ti.tex_coord.val ⦄ := by
  unfold validate.mesh.material_texcoords_ok textureInfos
  step* <;> simp_all [List.mem_filterMap, or_imp, forall_and, @eq_comm _ (some _)]

-- MUST-071: インデックスは SCALAR の符号なし整数
@[step]
theorem index_accessor_ok_spec (a : model.Accessor) : validate.mesh.index_accessor_ok a ⦃ r => r = true ↔ indexAccessorOk a ⦄ := by
  unfold validate.mesh.index_accessor_ok indexAccessorOk
  step* <;> simp_all [UScalar.eq_equiv] <;> agrind

-- MUST-084: モーフターゲットの数は等しい
set_option maxHeartbeats 4000000 in
@[step]
theorem primitive_ok_spec (g : model.Gltf) (p : model.Primitive) (targets : U64) (hr : primitiveRefsOk g p) :
    validate.mesh.primitive_ok g p targets ⦃ r => r = true ↔ primitiveOk g p targets.val ⦄ := by
  unfold validate.mesh.primitive_ok primitiveOk
  obtain ⟨h1, h2, h3, h4⟩ := hr
  have hlA : g.accessors.val.length ≤ Usize.max := by scalar_tac
  have hlM : g.materials.val.length ≤ Usize.max := by scalar_tac
  have hA0 : ∀ h : 0 < p.attributes.val.length,
      (p.attributes.val[0]).accessor.val % 2 ^ System.Platform.numBits = (p.attributes.val[0]).accessor.val ∧
      (p.attributes.val[0]).accessor.val < g.accessors.val.length := fun h =>
    have := h1 _ (List.getElem_mem h); ⟨mod_numBits_of_lt this hlA, this⟩
  have hb0 : ∀ h : 0 < p.attributes.val.length, p.attributes.val[0]! = p.attributes.val[0] :=
    fun h => getElem!_pos p.attributes.val 0 h
  by_cases hne : p.attributes.val = []
  · step* <;> simp_all
  have h0 : 0 < p.attributes.val.length := List.length_pos_iff_ne_nil.mpr hne
  rw [hb0 h0]
  obtain ⟨hm0, hl0⟩ := hA0 h0
  rcases hix : p.indices with _ | ix <;> rcases hmat : p.material with _ | m <;>
    simp only [hix, hmat, optLt, reduceCtorEq, false_imp_iff, forall_const,
      Option.some.injEq, forall_eq'] at h3 h4 ⊢
  all_goals (try rw [getElem!_pos g.accessors.val ix.val h3])
  all_goals (try rw [getElem!_pos g.materials.val m.val h4])
  all_goals (try have hmi := mod_numBits_of_lt h3 hlA)
  all_goals (try have hmm := mod_numBits_of_lt h4 hlM)
  all_goals step*
  all_goals (try simp_all [UScalar.eq_equiv])
  all_goals (intro h; simp_all)

@[step]
theorem primitives_ok_loop_spec (g : model.Gltf) (mesh : model.Mesh) (targets : U64) (j : Usize) (hr : ∀ p ∈ mesh.primitives.val, primitiveRefsOk g p) (hi : j.val ≤ mesh.primitives.val.length) :
    validate.mesh.primitives_ok_loop g mesh targets j ⦃ r => r = true ↔
      forallFrom mesh.primitives.val j.val (fun x => primitiveOk g (x) targets.val) ⦄ := by
  unfold validate.mesh.primitives_ok_loop
  have hr' : ∀ j (h : j < mesh.primitives.val.length), primitiveRefsOk g mesh.primitives.val[j] :=
    fun j h => hr _ (List.getElem_mem h)
  loop_auto
termination_by mesh.primitives.val.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem primitives_ok_spec (g : model.Gltf) (mesh : model.Mesh) (targets : U64) (hr : ∀ p ∈ mesh.primitives.val, primitiveRefsOk g p) :
    validate.mesh.primitives_ok g mesh targets ⦃ r => r = true ↔ ∀ x ∈ mesh.primitives.val, primitiveOk g (x) targets.val ⦄ := by
  unfold validate.mesh.primitives_ok
  step*
  simp_all [forallFrom_zero]

-- MUST-085: mesh.weights の長さ = モーフターゲットの数
@[step]
theorem mesh_ok_spec (g : model.Gltf) (mesh : model.Mesh) (hr : ∀ p ∈ mesh.primitives.val, primitiveRefsOk g p) :
    validate.mesh.mesh_ok g mesh ⦃ r => r = true ↔ meshOk g mesh ⦄ := by
  unfold validate.mesh.mesh_ok meshOk
  rcases hw : mesh.weights_len with _ | w <;> step* <;> simp_all [UScalar.eq_equiv]

@[step]
theorem meshes_ok_loop_spec (g : model.Gltf) (i : Usize) (hr : meshRefsOk g) (hi : i.val ≤ g.meshes.val.length) :
    validate.mesh.meshes_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.meshes.val i.val (fun x => meshOk g (x)) ⦄ := by
  unfold validate.mesh.meshes_ok_loop
  have hr' : ∀ j (h : j < g.meshes.val.length), ∀ p ∈ (g.meshes.val[j]).primitives.val,
      primitiveRefsOk g p := fun j h => hr _ (List.getElem_mem h)
  loop_auto
termination_by g.meshes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem meshes_ok_spec (g : model.Gltf) (hr : meshRefsOk g) :
    validate.mesh.meshes_ok g ⦃ r => r = true ↔ meshesOk g ⦄ := by
  unfold validate.mesh.meshes_ok meshesOk
  step*
  simp_all [forallFrom_zero]

end LoadGltf
