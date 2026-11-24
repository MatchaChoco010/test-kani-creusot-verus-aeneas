import LoadGltf.Validate.Refs

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## アクセサの役割 -/

-- 属性アクセサ (プリミティブの属性またはモーフターゲットの属性)
def attrAcc (g : model.Gltf) (i : Nat) : Prop :=
  ∃ m ∈ g.meshes.val, ∃ p ∈ m.primitives.val,
    (∃ x ∈ p.attributes.val, x.accessor.val = i) ∨ (∃ t ∈ p.targets.val, ∃ x ∈ t.val, x.accessor.val = i)

-- インデックスアクセサ
def idxAcc (g : model.Gltf) (i : Nat) : Prop :=
  ∃ m ∈ g.meshes.val, ∃ p ∈ m.primitives.val, p.indices.map (·.val) = some i

-- 逆バインド行列アクセサ
def ibmAcc (g : model.Gltf) (i : Nat) : Prop := ∃ sk ∈ g.skins.val, sk.inverse_bind_matrices.map (·.val) = some i

theorem getD_set_true (l : List Bool) (c j : Nat) (hc : c < l.length) :
    (l.set c true).getD j false = true ↔ j = c ∨ l.getD j false = true := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : c = j
  · subst h; simp [hc]
  · simp [h, Ne.symm h]

@[step]
theorem mark_attributes_loop_spec (roles : alloc.vec.Vec Bool) (attrs : alloc.vec.Vec model.Attribute) (i : Usize)
    (ha : ∀ x ∈ attrs.val, x.accessor.val < roles.val.length) (hi : i.val ≤ attrs.val.length) :
    validate.data.mark_attributes_loop roles attrs i ⦃ r => r.val.length = roles.val.length ∧
      ∀ j, r.val.getD j false = true ↔ roles.val.getD j false = true ∨
        ∃ x ∈ attrs.val.drop i.val, x.accessor.val = j ⦄ := by
  unfold validate.data.mark_attributes_loop
  step*
  · subst a_post
    rw [i2_post, u64_cast_usize_val _ (by have := ha _ (List.getElem_mem (usize_lt_len ‹_›)); scalar_tac)]
    exact ha _ (List.getElem_mem (usize_lt_len ‹_›))
  · intro x hx; rw [index_mut_back_post]; simp only [alloc.vec.Vec.set_val_eq, List.length_set]; exact ha x hx
  · have hk := usize_lt_len ‹i < attrs.len›
    have hb := ha _ (List.getElem_mem hk)
    have hi2 : i2.val = (attrs.val[i.val]).accessor.val := by
      rw [i2_post, a_post]; exact u64_cast_usize_val _ (by scalar_tac)
    rw [index_mut_back_post, alloc.vec.Vec.set_val_eq, hi2] at r_post r_post1
    refine ⟨by simp_all, fun j => ?_⟩
    rw [r_post1 j, getD_set_true _ _ _ hb, i3_post, List.drop_eq_getElem_cons hk]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h
  · intro j; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
termination_by attrs.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mark_attributes_spec (roles : alloc.vec.Vec Bool) (attrs : alloc.vec.Vec model.Attribute)
    (ha : ∀ x ∈ attrs.val, x.accessor.val < roles.val.length) :
    validate.data.mark_attributes roles attrs ⦃ r => r.val.length = roles.val.length ∧
      ∀ j, r.val.getD j false = true ↔ roles.val.getD j false = true ∨ ∃ x ∈ attrs.val, x.accessor.val = j ⦄ := by
  unfold validate.data.mark_attributes
  step*
  simp_all

@[step]
theorem mark_primitive_loop_spec (v : alloc.vec.Vec Bool) (ts : alloc.vec.Vec (alloc.vec.Vec model.Attribute))
    (t : Usize) (ha : ∀ tt ∈ ts.val, ∀ x ∈ tt.val, x.accessor.val < v.val.length) (ht : t.val ≤ ts.val.length) :
    validate.data.mark_primitive_loop v ts t ⦃ r => r.val.length = v.val.length ∧
      ∀ j, r.val.getD j false = true ↔ v.val.getD j false = true ∨
        ∃ tt ∈ ts.val.drop t.val, ∃ x ∈ tt.val, x.accessor.val = j ⦄ := by
  unfold validate.data.mark_primitive_loop
  step*
  all_goals first
  | (subst v2_post; exact ha _ (List.getElem_mem (usize_lt_len ‹_›)))
  | (have hk := usize_lt_len ‹t < ts.len›
     refine ⟨by simp_all, fun j => ?_⟩
     rw [r_post1 j, v3_post1 j, t1_post, List.drop_eq_getElem_cons hk, v2_post]
     simp only [List.mem_cons, exists_eq_or_imp, or_assoc])
  | (intro j; rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp)
termination_by ts.val.length - t.val
decreasing_by all_goals scalar_decr_tac

-- 役割の配列の更新: 各配列に集合 A, I, B の要素が加わる
def RolesRel (r r' : validate.data.Roles) (A I B : Nat → Prop) : Prop :=
  r'.attribute.val.length = r.attribute.val.length ∧ r'.index.val.length = r.index.val.length ∧
  r'.ibm.val.length = r.ibm.val.length ∧
  ∀ j, (r'.attribute.val.getD j false = true ↔ r.attribute.val.getD j false = true ∨ A j) ∧
    (r'.index.val.getD j false = true ↔ r.index.val.getD j false = true ∨ I j) ∧
    (r'.ibm.val.getD j false = true ↔ r.ibm.val.getD j false = true ∨ B j)

def primAttr (p : model.Primitive) (j : Nat) : Prop :=
  (∃ x ∈ p.attributes.val, x.accessor.val = j) ∨ (∃ t ∈ p.targets.val, ∃ x ∈ t.val, x.accessor.val = j)

def primIdx (p : model.Primitive) (j : Nat) : Prop := p.indices.map (·.val) = some j

@[step]
theorem mark_primitive_spec (r : validate.data.Roles) (p : model.Primitive) (n : Nat)
    (hl : r.attribute.val.length = n ∧ r.index.val.length = n)
    (hp : (∀ x ∈ p.attributes.val, x.accessor.val < n) ∧ (∀ t ∈ p.targets.val, ∀ x ∈ t.val, x.accessor.val < n) ∧
      optLt p.indices n) :
    validate.data.mark_primitive r p ⦃ r' => RolesRel r r' (primAttr p) (primIdx p) (fun _ => False) ⦄ := by
  unfold validate.data.mark_primitive RolesRel primAttr primIdx
  obtain ⟨hl1, hl2⟩ := hl
  obtain ⟨h1, h2, h3⟩ := hp
  rcases hi : p.indices with _ | ix <;> simp only [optLt, hi] at h3
  · step*
    refine ⟨by simp_all, fun j => ⟨?_, by simp, by simp⟩⟩
    rw [v1_post1, v_post1]; simp only [List.drop_zero, or_assoc]
  · have h3' := h3 ix rfl
    have hiv : (UScalar.cast .Usize ix).val = ix.val := u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq r.index; omega)
    step*
    all_goals first
    | (rw [i_post, hiv]; omega)
    | (rw [index_mut_back_post, alloc.vec.Vec.set_val_eq, i_post, hiv]
       refine ⟨by simp_all, by simp, fun j => ⟨?_, ?_, by simp⟩⟩
       · rw [v1_post1, v_post1]; simp only [List.drop_zero, or_assoc]
       · rw [getD_set_true _ _ _ (by omega)]; simp only [Option.map_some, Option.some.injEq]; tauto)

theorem RolesRel.trans {r r1 r2 : validate.data.Roles} {A I B A' I' B' : Nat → Prop} (h1 : RolesRel r r1 A I B)
    (h2 : RolesRel r1 r2 A' I' B') : RolesRel r r2 (fun j => A j ∨ A' j) (fun j => I j ∨ I' j) (fun j => B j ∨ B' j) := by
  obtain ⟨a1, b1, c1, d1⟩ := h1
  obtain ⟨a2, b2, c2, d2⟩ := h2
  refine ⟨by omega, by omega, by omega, fun j => ⟨?_, ?_, ?_⟩⟩
  · rw [(d2 j).1, (d1 j).1]; tauto
  · rw [(d2 j).2.1, (d1 j).2.1]; tauto
  · rw [(d2 j).2.2, (d1 j).2.2]; tauto

theorem RolesRel.refl (r : validate.data.Roles) : RolesRel r r (fun _ => False) (fun _ => False) (fun _ => False) := by
  simp [RolesRel]

theorem RolesRel.congr {r r' : validate.data.Roles} {A I B A' I' B' : Nat → Prop} (h : RolesRel r r' A I B)
    (ha : ∀ j, A j ↔ A' j) (hi : ∀ j, I j ↔ I' j) (hb : ∀ j, B j ↔ B' j) : RolesRel r r' A' I' B' := by
  obtain ⟨a, b, c, d⟩ := h
  exact ⟨a, b, c, fun j => by rw [← ha, ← hi, ← hb]; exact d j⟩

@[step]
theorem mark_mesh_loop_spec (r : validate.data.Roles) (m : model.Mesh) (j : Usize) (n : Nat)
    (hl : r.attribute.val.length = n ∧ r.index.val.length = n)
    (hp : ∀ p ∈ m.primitives.val, (∀ x ∈ p.attributes.val, x.accessor.val < n) ∧
      (∀ t ∈ p.targets.val, ∀ x ∈ t.val, x.accessor.val < n) ∧ optLt p.indices n)
    (hj : j.val ≤ m.primitives.val.length) :
    validate.data.mark_mesh_loop r m j ⦃ r' => RolesRel r r' (fun k => ∃ p ∈ m.primitives.val.drop j.val, primAttr p k)
      (fun k => ∃ p ∈ m.primitives.val.drop j.val, primIdx p k) (fun _ => False) ⦄ := by
  unfold validate.data.mark_mesh_loop
  step*
  · subst p_post; exact hp _ (List.getElem_mem _)
  · have hk := usize_lt_len ‹j < m.primitives.len›
    apply (r1_post.trans r'_post).congr <;> intro k <;>
      simp only [j1_post, List.drop_eq_getElem_cons hk, List.mem_cons, exists_eq_or_imp, p_post, or_false]
  · apply (RolesRel.refl r).congr <;> intro k <;> (try rw [List.drop_eq_nil_of_le (by scalar_tac)]) <;> simp
termination_by m.primitives.val.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mark_mesh_spec (r : validate.data.Roles) (m : model.Mesh) (n : Nat)
    (hl : r.attribute.val.length = n ∧ r.index.val.length = n)
    (hp : ∀ p ∈ m.primitives.val, (∀ x ∈ p.attributes.val, x.accessor.val < n) ∧
      (∀ t ∈ p.targets.val, ∀ x ∈ t.val, x.accessor.val < n) ∧ optLt p.indices n) :
    validate.data.mark_mesh r m ⦃ r' => RolesRel r r' (fun k => ∃ p ∈ m.primitives.val, primAttr p k)
      (fun k => ∃ p ∈ m.primitives.val, primIdx p k) (fun _ => False) ⦄ := by
  unfold validate.data.mark_mesh
  step*
  simp_all

@[step]
theorem mark_meshes_loop_spec (r : validate.data.Roles) (g : model.Gltf) (i : Usize)
    (hl : r.attribute.val.length = g.accessors.val.length ∧ r.index.val.length = g.accessors.val.length)
    (hr : meshRefsOk g) (hi : i.val ≤ g.meshes.val.length) :
    validate.data.mark_meshes_loop r g i ⦃ r' => RolesRel r r'
      (fun k => ∃ m ∈ g.meshes.val.drop i.val, ∃ p ∈ m.primitives.val, primAttr p k)
      (fun k => ∃ m ∈ g.meshes.val.drop i.val, ∃ p ∈ m.primitives.val, primIdx p k) (fun _ => False) ⦄ := by
  unfold validate.data.mark_meshes_loop
  step*
  · subst m_post
    intro p hp
    have := hr _ (List.getElem_mem (usize_lt_len ‹_›)) p hp
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  · have hk := usize_lt_len ‹i < g.meshes.len›
    apply (r1_post.trans r'_post).congr <;> intro k <;>
      simp only [i2_post, List.drop_eq_getElem_cons hk, List.mem_cons, exists_eq_or_imp, m_post, or_false]
  · apply (RolesRel.refl r).congr <;> intro k <;> (try rw [List.drop_eq_nil_of_le (by scalar_tac)]) <;> simp
termination_by g.meshes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mark_meshes_spec (r : validate.data.Roles) (g : model.Gltf)
    (hl : r.attribute.val.length = g.accessors.val.length ∧ r.index.val.length = g.accessors.val.length)
    (hr : meshRefsOk g) :
    validate.data.mark_meshes r g ⦃ r' => RolesRel r r' (fun k => ∃ m ∈ g.meshes.val, ∃ p ∈ m.primitives.val, primAttr p k)
      (fun k => ∃ m ∈ g.meshes.val, ∃ p ∈ m.primitives.val, primIdx p k) (fun _ => False) ⦄ := by
  unfold validate.data.mark_meshes
  step*
  simp_all

@[step]
theorem mark_skins_loop_spec (r : validate.data.Roles) (g : model.Gltf) (i : Usize)
    (hl : r.ibm.val.length = g.accessors.val.length) (hr : skinRefsOk g) (hi : i.val ≤ g.skins.val.length) :
    validate.data.mark_skins_loop r g i ⦃ r' => RolesRel r r' (fun _ => False) (fun _ => False)
      (fun k => ∃ sk ∈ g.skins.val.drop i.val, sk.inverse_bind_matrices.map (·.val) = some k) ⦄ := by
  unfold validate.data.mark_skins_loop
  step*
  · have hk := usize_lt_len ‹i < g.skins.len›
    have hsr := (hr _ (List.getElem_mem hk)).2.2
    subst s_post
    rcases h : (g.skins.val[i.val]).inverse_bind_matrices with _ | m <;> simp only [h, optLt] at hsr ⊢
    · step*
      apply r'_post.congr <;> intro k <;>
        simp only [i2_post, List.drop_eq_getElem_cons hk, List.mem_cons, exists_eq_or_imp, h, false_or,
          Option.map_none, reduceCtorEq]
    · have hm := hsr m rfl
      have hiv : (UScalar.cast .Usize m).val = m.val := u64_cast_usize_val _ (by have := alloc.vec.Vec.len_ineq g.accessors; omega)
      step*
      obtain ⟨x1, x2⟩ := x
      simp only at x_post x_post1 ⊢
      subst x_post1
      have hiu := congrArg (·.val) ‹_ = UScalar.cast UScalarTy.Usize m›
      simp only [hiv] at hiu
      step*
      · refine (RolesRel.trans (r := r) (r1 := { «attribute» := r.attribute, index := r.index, ibm := r.ibm.set x true }) (A := fun _ => False) (I := fun _ => False) (B := fun k => k = m.val)
          ⟨rfl, rfl, by simp, fun j => ⟨by simp, by simp, ?_⟩⟩ r'_post).congr ?_ ?_ ?_
        · simp only [alloc.vec.Vec.set_val_eq]
          rw [getD_set_true _ _ _ (by rw [hiu]; omega), hiu]
          tauto
        · intro k; simp
        · intro k; simp
        · intro k
          simp only [i2_post, List.drop_eq_getElem_cons hk, List.mem_cons, exists_eq_or_imp, h,
            Option.map_some, Option.some.injEq]
          constructor <;> rintro (h1 | h1) <;> simp_all
  · apply (RolesRel.refl r).congr <;> intro k <;> (try rw [List.drop_eq_nil_of_le (by scalar_tac)]) <;> simp
termination_by g.skins.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mark_skins_spec (r : validate.data.Roles) (g : model.Gltf) (hl : r.ibm.val.length = g.accessors.val.length)
    (hr : skinRefsOk g) :
    validate.data.mark_skins r g ⦃ r' => RolesRel r r' (fun _ => False) (fun _ => False) (ibmAcc g) ⦄ := by
  unfold validate.data.mark_skins ibmAcc
  step*
  simp_all

@[step]
theorem false_vec_loop_spec (n : Usize) (v : alloc.vec.Vec Bool) (i : Usize)
    (hv : v.val = List.replicate i.val false) (hi : i.val ≤ n.val) :
    validate.data.false_vec_loop n v i ⦃ r => r.val = List.replicate n.val false ⦄ := by
  unfold validate.data.false_vec_loop
  step*
  rw [v1_post, hv, i1_post, List.replicate_succ']
termination_by n.val - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem false_vec_spec (n : Usize) : validate.data.false_vec n ⦃ r => r.val = List.replicate n.val false ⦄ := by
  unfold validate.data.false_vec
  step*
  simp

@[step]
theorem zero_vec_loop_spec (n : Usize) (v : alloc.vec.Vec U64) (i : Usize)
    (hv : v.val = List.replicate i.val 0#u64) (hi : i.val ≤ n.val) :
    validate.data.zero_vec_loop n v i ⦃ r => r.val = List.replicate n.val 0#u64 ⦄ := by
  unfold validate.data.zero_vec_loop
  step*
  rw [v1_post, hv, i1_post, List.replicate_succ']
termination_by n.val - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem zero_vec_spec (n : Usize) : validate.data.zero_vec n ⦃ r => r.val = List.replicate n.val 0#u64 ⦄ := by
  unfold validate.data.zero_vec
  step*
  simp

-- 役割の配列がアクセサの役割を表す
def RolesOk (g : model.Gltf) (r : validate.data.Roles) : Prop :=
  r.attribute.val.length = g.accessors.val.length ∧ r.index.val.length = g.accessors.val.length ∧
  r.ibm.val.length = g.accessors.val.length ∧
  ∀ j, (r.attribute.val.getD j false = true ↔ attrAcc g j) ∧ (r.index.val.getD j false = true ↔ idxAcc g j) ∧
    (r.ibm.val.getD j false = true ↔ ibmAcc g j)

@[step]
theorem accessor_roles_spec (g : model.Gltf) (hm : meshRefsOk g) (hs : skinRefsOk g) :
    validate.data.accessor_roles g ⦃ r => RolesOk g r ⦄ := by
  unfold validate.data.accessor_roles
  step*
  obtain ⟨a1, b1, c1, d1⟩ := RolesRel.trans ‹RolesRel { «attribute» := v, index := v, ibm := v } _ _ _ _› r_post
  refine ⟨by simp_all, by simp_all, by simp_all, fun j => ?_⟩
  have hz : ∀ n j, (List.replicate n false).getD j false = false := by
    intro n j; simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  have e1 := d1 j
  simp only [v_post, hz, Bool.false_eq_true, false_or, or_false] at e1
  rw [e1.1, e1.2.1, e1.2.2]
  simp only [attrAcc, idxAcc, primAttr, primIdx]
  simp

/-! ## バッファビューの用途 (SPEC B の attr/idx/ibm/anim/sparse/image と attr_count) -/

-- アクセサ k の bufferView が b
def accView (g : model.Gltf) (k b : Nat) : Prop := (g.accessors.val[k]!).buffer_view.map (·.val) = some b

instance (g : model.Gltf) (k b : Nat) : Decidable (accView g k b) := by unfold accView; infer_instance

def attrView (g : model.Gltf) (b : Nat) : Prop := ∃ k < g.accessors.val.length, attrAcc g k ∧ accView g k b

def idxView (g : model.Gltf) (b : Nat) : Prop := ∃ k < g.accessors.val.length, idxAcc g k ∧ accView g k b

def ibmView (g : model.Gltf) (b : Nat) : Prop := ∃ k < g.accessors.val.length, ibmAcc g k ∧ accView g k b

def animView (g : model.Gltf) (b : Nat) : Prop :=
  ∃ an ∈ g.animations.val, ∃ s ∈ an.samplers.val, accView g s.input.val b ∨ accView g s.output.val b

def sparseView (g : model.Gltf) (b : Nat) : Prop :=
  ∃ a ∈ g.accessors.val, ∃ s, a.sparse = some s ∧ (s.indices_buffer_view.val = b ∨ s.values_buffer_view.val = b)

def imageView (g : model.Gltf) (b : Nat) : Prop := ∃ im ∈ g.images.val, im.buffer_view.map (·.val) = some b

-- MUST-027: bufferView を使うアクセサーがある
def accessorView (g : model.Gltf) (b : Nat) : Prop := ∃ k < g.accessors.val.length, accView g k b

-- MUST-038: bufferView を使う頂点属性でないアクセサーがある
def nonAttrView (g : model.Gltf) (b : Nat) : Prop := ∃ k < g.accessors.val.length, ¬ attrAcc g k ∧ accView g k b

-- attr_count(b): bufferView = b である属性アクセサの個数
-- MUST-029, MUST-039: bufferView を使う頂点属性アクセサーの数
open Classical in
noncomputable def attrCount (g : model.Gltf) (b : Nat) : Nat :=
  (List.range g.accessors.val.length).countP (fun k => decide (attrAcc g k ∧ accView g k b))

-- view_use の結果が各用途を表す
def ViewUseOk (g : model.Gltf) (u : validate.data.ViewUse) : Prop :=
  u.attribute.val.length = g.buffer_views.val.length ∧ u.attribute_count.val.length = g.buffer_views.val.length ∧
  u.index.val.length = g.buffer_views.val.length ∧ u.ibm.val.length = g.buffer_views.val.length ∧
  u.sparse.val.length = g.buffer_views.val.length ∧ u.image.val.length = g.buffer_views.val.length ∧
  u.animation.val.length = g.buffer_views.val.length ∧ u.accessor.val.length = g.buffer_views.val.length ∧
  u.non_attribute.val.length = g.buffer_views.val.length ∧
  ∀ b, (u.attribute.val.getD b false = true ↔ attrView g b) ∧
    (u.attribute_count.val.getD b 0#u64).val = attrCount g b ∧
    (u.index.val.getD b false = true ↔ idxView g b) ∧ (u.ibm.val.getD b false = true ↔ ibmView g b) ∧
    (u.sparse.val.getD b false = true ↔ sparseView g b) ∧ (u.image.val.getD b false = true ↔ imageView g b) ∧
    (u.animation.val.getD b false = true ↔ animView g b) ∧
    (u.accessor.val.getD b false = true ↔ accessorView g b) ∧
    (u.non_attribute.val.getD b false = true ↔ nonAttrView g b)

/-! ## B1–B4 -/

-- 命題の列のうち高々 1 つが成り立つ
def atMostOne (ps : List Prop) : Prop := ps.Pairwise (fun p q => ¬ (p ∧ q))

-- バッファビュー bv の規則。attr..image, acc, nonAttr は用途、attrCnt は attr_count
-- MUST-025, MUST-026, MUST-027, MUST-028, MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039: bufferView の規則 B1–B4
-- MUST-046, MUST-050, MUST-070, MUST-072, MUST-090, MUST-098, MUST-110, MUST-142, MUST-146: 用途ごとの byteStride / target
def bufferViewRules (g : model.Gltf) (bv : model.BufferView) (attr idx ibm anim sparse image acc nonAttr : Prop)
    (attrCnt : Nat) : Prop :=
  -- B1
  0 < bv.byte_length.val ∧
  bv.byte_offset.val + bv.byte_length.val ≤ (g.buffers.val[bv.buffer.val]!).byte_length.val ∧
  -- B2'
  ((attr ∨ idx ∨ ibm ∨ image) → atMostOne [attr, idx, ibm, anim ∨ sparse, image]) ∧
  (image → ¬ acc ∧ ¬ sparse) ∧
  -- B3'
  (bv.byte_stride = none → attrCnt < 2) ∧
  (∀ st, bv.byte_stride = some st → 4 ≤ st.val ∧ st.val ≤ 252 ∧ st.val % 4 = 0 ∧ st.val ≤ bv.byte_length.val ∧
    ¬ idx ∧ ¬ ibm ∧ ¬ (anim ∨ sparse) ∧ ¬ image ∧ ¬ nonAttr ∧ ∀ t, bv.target = some t → t.val ≠ 34963) ∧
  -- B4
  (∀ t, bv.target = some t → ¬ (attr ∧ t.val ≠ 34962) ∧ ¬ (idx ∧ t.val ≠ 34963) ∧ ¬ ibm ∧ ¬ (anim ∨ sparse) ∧ ¬ image)

-- B1–B4 (すべてのバッファビュー)
def bufferViewsOk (g : model.Gltf) : Prop :=
  ∀ b (hb : b < g.buffer_views.val.length), bufferViewRules g g.buffer_views.val[b] (attrView g b) (idxView g b)
    (ibmView g b) (animView g b) (sparseView g b) (imageView g b) (accessorView g b) (nonAttrView g b) (attrCount g b)

/-! ## AC1–AC3 -/

-- 成分のバイト数 (5120, 5121 → 1; 5122, 5123 → 2; 5125, 5126 → 4)
def componentSize (ct : Nat) : Nat := if ct = 5120 ∨ ct = 5121 then 1 else if ct = 5122 ∨ ct = 5123 then 2 else 4

-- 行列の行数 (= 列数): MAT2, MAT3, MAT4
def matRows (c : Nat) : Nat := if c = 4 then 2 else if c = 9 then 3 else 4

-- 4 の倍数への切り上げ
def roundUp4 (x : Nat) : Nat := (x + 3) / 4 * 4

-- 要素のバイト数 (行列は列ごとに 4 バイト境界に揃える, adoc 1266)
def elementSize (a : model.Accessor) : Nat :=
  if a.is_matrix then matRows a.components.val * roundUp4 (componentSize a.component_type.val * matRows a.components.val)
  else a.components.val * componentSize a.component_type.val

-- AC1
-- MUST-035, MUST-053: normalized の型、min / max の長さ
def accessorBasicOk (a : model.Accessor) : Prop :=
  0 < a.count.val ∧ ¬ (a.normalized = true ∧ (a.component_type.val = 5125 ∨ a.component_type.val = 5126)) ∧
  (∀ n, a.min_len = some n → n.val = a.components.val) ∧ (∀ n, a.max_len = some n → n.val = a.components.val)

-- AC2 (isAttr: 属性アクセサである)
-- MUST-034, MUST-036, MUST-037, MUST-040, MUST-041, MUST-042: アクセサーの配置
def accessorViewOk (g : model.Gltf) (a : model.Accessor) (isAttr : Prop) : Prop :=
  (a.buffer_view = none → a.byte_offset = none) ∧
  ∀ b, a.buffer_view = some b →
    let bv := g.buffer_views.val[b.val]!
    let off := (a.byte_offset.map (·.val)).getD 0
    let cs := componentSize a.component_type.val
    let stride := (bv.byte_stride.map (·.val)).getD (elementSize a)
    off % cs = 0 ∧ bv.byte_offset.val % cs = 0 ∧
    (∀ st, bv.byte_stride = some st → elementSize a ≤ st.val ∧ st.val % cs = 0) ∧
    (isAttr → off % 4 = 0 ∧ (cs % 4 = 0 ∨ bv.byte_stride ≠ none)) ∧
    off + (a.count.val - 1) * stride + elementSize a ≤ bv.byte_length.val

-- AC3
-- MUST-044, MUST-045, MUST-047, MUST-048, MUST-051, MUST-052: sparse の規則
def sparseOk (g : model.Gltf) (a : model.Accessor) : Prop :=
  ∀ s, a.sparse = some s →
    let cs := componentSize a.component_type.val
    let isz := componentSize s.indices_component_type.val
    let ib := g.buffer_views.val[s.indices_buffer_view.val]!
    let vb := g.buffer_views.val[s.values_buffer_view.val]!
    0 < s.count.val ∧ s.count.val ≤ a.count.val ∧
    (s.indices_component_type.val = 5121 ∨ s.indices_component_type.val = 5123 ∨
      s.indices_component_type.val = 5125) ∧
    s.indices_byte_offset.val % isz = 0 ∧ ib.byte_offset.val % isz = 0 ∧
    s.values_byte_offset.val % cs = 0 ∧ vb.byte_offset.val % cs = 0 ∧
    s.indices_byte_offset.val + s.count.val * isz ≤ ib.byte_length.val ∧
    s.values_byte_offset.val + s.count.val * elementSize a ≤ vb.byte_length.val

-- AC1–AC3 (すべてのアクセサ)
def accessorsOk (g : model.Gltf) : Prop :=
  ∀ i (h : i < g.accessors.val.length), accessorBasicOk g.accessors.val[i] ∧
    accessorViewOk g g.accessors.val[i] (attrAcc g i) ∧ sparseOk g g.accessors.val[i]

@[step]
theorem lift_checked_add_spec (x y : U64) :
    lift (U64.checked_add x y) ⦃ r => (r = none ↔ U64.max < x.val + y.val) ∧
      ∀ z, r = some z → z.val = x.val + y.val ⦄ := by
  have := U64.checked_add_bv_spec x y
  simp only [lift, WP.spec_ok]
  rcases h : U64.checked_add x y with _ | z <;> simp_all

@[step]
theorem lift_checked_mul_spec (x y : U64) :
    lift (U64.checked_mul x y) ⦃ r => (r = none ↔ U64.max < x.val * y.val) ∧
      ∀ z, r = some z → z.val = x.val * y.val ⦄ := by
  have := U64.checked_mul_bv_spec x y
  simp only [lift, WP.spec_ok]
  rcases h : U64.checked_mul x y with _ | z <;> simp_all

theorem getD_set_eq {α} (l : List α) (c j : Nat) (x d : α) (hc : c < l.length) :
    (l.set c x).getD j d = if c = j then x else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : c = j
  · subst h; simp [hc]
  · simp [h]

theorem count_step_le (c : List U64) (b i : Nat) (x : U64) (hc : ∀ j, (c.getD j 0#u64).val ≤ i)
    (hb : b < c.length) (hx : x.val ≤ (c[b]).val + 1) : ∀ j, ((c.set b x).getD j 0#u64).val ≤ i + 1 := by
  intro j
  rw [getD_set_eq _ _ _ _ _ hb]
  split
  · have := hc b; rw [List.getD_eq_getElem _ _ hb] at this; omega
  · have := hc j; omega

theorem drop_cons_iff {α} {l : List α} {i : Nat} (hi : i < l.length) (P : α → Prop) :
    (∃ x ∈ l.drop i, P x) ↔ P l[i] ∨ ∃ x ∈ l.drop (i + 1), P x := by
  rw [List.drop_eq_getElem_cons hi]; simp only [List.mem_cons, exists_eq_or_imp]

@[step]
theorem mark_image_views_loop_spec (u : validate.data.ViewUse) (g : model.Gltf) (i : Usize) (hr : imageRefsOk g)
    (hl : u.image.val.length = g.buffer_views.val.length) (hi : i.val ≤ g.images.val.length) :
    validate.data.mark_image_views_loop u g i ⦃ r => ∃ v, r = { u with image := v } ∧ v.val.length = u.image.val.length ∧
      ∀ j, v.val.getD j false = true ↔ u.image.val.getD j false = true ∨
        ∃ im ∈ g.images.val.drop i.val, im.buffer_view.map (·.val) = some j ⦄ := by
  unfold validate.data.mark_image_views_loop
  step*
  · subst i2_post
    have hk := usize_lt_len ‹i < g.images.len›
    have hrb := hr _ (List.getElem_mem hk)
    rcases hb : (g.images.val[i.val]).buffer_view with _ | bv
    · simp only [hb]
      step*
      refine ⟨v, r_post, r_post1, fun j => ?_⟩
      rw [r_post2, i3_post, drop_cons_iff hk, hb]; simp
    · simp only [hb]
      have hbv := hrb bv hb
      have hc : (UScalar.cast .Usize bv).val = bv.val := u64_cast_usize_val _ (by scalar_tac)
      step as ⟨c, hc'⟩
      rw [hc'] at *
      step*
      obtain ⟨x1, x2⟩ := x
      simp only at x_post x_post1 ⊢
      subst x_post1
      step*
      refine ⟨v, r_post, by simp_all, fun j => ?_⟩
      rw [r_post2, i3_post, drop_cons_iff hk, hb, alloc.vec.Vec.set_val_eq,
        getD_set_true _ _ _ (by rw [hc]; omega), hc]
      simp only [Option.map_some, Option.some.injEq]
      tauto
  · refine ⟨u.image, rfl, rfl, fun j => ?_⟩
    rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
termination_by g.images.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mark_accessor_view_spec (v : alloc.vec.Vec Bool) (g : model.Gltf) (k : U64) (hk : k.val < g.accessors.val.length)
    (hb : optLt (g.accessors.val[k.val]).buffer_view v.val.length) :
    validate.data.mark_accessor_view v g k ⦃ r => r.val.length = v.val.length ∧
      ∀ j, r.val.getD j false = true ↔ v.val.getD j false = true ∨ accView g k.val j ⦄ := by
  unfold validate.data.mark_accessor_view accView
  rw [getElem!_pos g.accessors.val k.val hk]
  have hc : (UScalar.cast .Usize k).val = k.val := u64_cast_usize_val _ (by scalar_tac)
  step*
  all_goals (have ha : a = g.accessors.val[k.val] := (by rw [a_post]; exact getElem_idx_eq (by rw [i_post]; exact hc) _ _))
  all_goals subst ha
  · simp_all
  · have hbv := hb _ ‹_›
    rw [i1_post, u64_cast_usize_val _ (by scalar_tac)]; scalar_tac
  · have hbv := hb _ ‹_›
    have hc2 := u64_cast_usize_val bv (by scalar_tac)
    rw [index_mut_back_post, alloc.vec.Vec.set_val_eq]
    refine ⟨by simp, fun j => ?_⟩
    rw [getD_set_true _ _ _ (by rw [i1_post, hc2]; omega), i1_post, hc2, ‹(g.accessors.val[k.val]).buffer_view = some bv›]
    simp only [Option.map_some, Option.some.injEq]
    tauto

@[step]
theorem mark_animation_views_loop_spec (u : validate.data.ViewUse) (g : model.Gltf) (an : model.Animation) (s : Usize)
    (hs : ∀ x ∈ an.samplers.val, x.input.val < g.accessors.val.length ∧ x.output.val < g.accessors.val.length)
    (ha : ∀ a ∈ g.accessors.val, optLt a.buffer_view g.buffer_views.val.length)
    (hl : u.animation.val.length = g.buffer_views.val.length) (hi : s.val ≤ an.samplers.val.length) :
    validate.data.mark_animation_views_loop u g an s ⦃ r => ∃ v, r = { u with animation := v } ∧
      v.val.length = u.animation.val.length ∧
      ∀ j, v.val.getD j false = true ↔ u.animation.val.getD j false = true ∨
        ∃ x ∈ an.samplers.val.drop s.val, accView g x.input.val j ∨ accView g x.output.val j ⦄ := by
  unfold validate.data.mark_animation_views_loop
  have hs' : ∀ q (h : q < an.samplers.val.length), (an.samplers.val[q]).input.val < g.accessors.val.length ∧
      (an.samplers.val[q]).output.val < g.accessors.val.length := fun q h => hs _ (List.getElem_mem h)
  have ha' : ∀ q (h : q < g.accessors.val.length), optLt (g.accessors.val[q]).buffer_view g.buffer_views.val.length :=
    fun q h => ha _ (List.getElem_mem h)
  step*
  · have hk := usize_lt_len ‹s < an.samplers.len›
    refine ⟨_, r_post, by simp_all, fun j => ?_⟩
    rw [r_post2, s1_post, drop_cons_iff hk, v1_post1, v_post1, as_post]
    simp only [or_assoc]
  · refine ⟨u.animation, rfl, rfl, fun j => ?_⟩
    rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
termination_by an.samplers.val.length - s.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mark_animations_views_loop_spec (u : validate.data.ViewUse) (g : model.Gltf) (i : Usize) (hr : animationRefsOk g)
    (ha : ∀ a ∈ g.accessors.val, optLt a.buffer_view g.buffer_views.val.length)
    (hl : u.animation.val.length = g.buffer_views.val.length) (hi : i.val ≤ g.animations.val.length) :
    validate.data.mark_animations_views_loop u g i ⦃ r => ∃ v, r = { u with animation := v } ∧
      v.val.length = u.animation.val.length ∧
      ∀ j, v.val.getD j false = true ↔ u.animation.val.getD j false = true ∨
        ∃ an ∈ g.animations.val.drop i.val, ∃ x ∈ an.samplers.val, accView g x.input.val j ∨ accView g x.output.val j ⦄ := by
  unfold validate.data.mark_animations_views_loop
  step*
  · subst a_post; exact (hr _ (List.getElem_mem (usize_lt_len ‹_›))).2
  · have hk := usize_lt_len ‹i < g.animations.len›
    subst u1_post
    refine ⟨_, r_post, by simp_all, fun j => ?_⟩
    rw [r_post2, i2_post, drop_cons_iff hk, u1_post2, a_post]
    simp only [List.drop_zero, or_assoc]
  · refine ⟨u.animation, rfl, rfl, fun j => ?_⟩
    rw [List.drop_eq_nil_of_le (by scalar_tac)]; simp
termination_by g.animations.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem lift_saturating_add_spec (a b : U64) :
    lift (core.num.U64.saturating_add a b) ⦃ r => r.val = min U64.max (a.val + b.val) ⦄ := by
  simp only [lift, WP.spec_ok]; exact saturating_add_val a b

-- mark_accessor_views のループの事後条件 (i 以降のアクセサを処理した結果)
def AccLoopPost (g : model.Gltf) (roles : validate.data.Roles) (i : Nat) (u r : validate.data.ViewUse) : Prop :=
  r.image = u.image ∧ r.animation = u.animation ∧
  r.attribute.val.length = u.attribute.val.length ∧ r.attribute_count.val.length = u.attribute_count.val.length ∧
  r.index.val.length = u.index.val.length ∧ r.ibm.val.length = u.ibm.val.length ∧
  r.sparse.val.length = u.sparse.val.length ∧ r.accessor.val.length = u.accessor.val.length ∧
  r.non_attribute.val.length = u.non_attribute.val.length ∧
  ∀ j, (r.attribute.val.getD j false = true ↔ u.attribute.val.getD j false = true ∨
      ∃ k, i ≤ k ∧ k < g.accessors.val.length ∧ roles.attribute.val.getD k false = true ∧ accView g k j) ∧
    (r.attribute_count.val.getD j 0#u64).val = (u.attribute_count.val.getD j 0#u64).val +
      (List.range' i (g.accessors.val.length - i)).countP
        (fun k => roles.attribute.val.getD k false && decide (accView g k j)) ∧
    (r.index.val.getD j false = true ↔ u.index.val.getD j false = true ∨
      ∃ k, i ≤ k ∧ k < g.accessors.val.length ∧ roles.index.val.getD k false = true ∧ accView g k j) ∧
    (r.ibm.val.getD j false = true ↔ u.ibm.val.getD j false = true ∨
      ∃ k, i ≤ k ∧ k < g.accessors.val.length ∧ roles.ibm.val.getD k false = true ∧ accView g k j) ∧
    (r.sparse.val.getD j false = true ↔ u.sparse.val.getD j false = true ∨
      ∃ a ∈ g.accessors.val.drop i, ∃ s, a.sparse = some s ∧
        (s.indices_buffer_view.val = j ∨ s.values_buffer_view.val = j)) ∧
    (r.accessor.val.getD j false = true ↔ u.accessor.val.getD j false = true ∨
      ∃ k, i ≤ k ∧ k < g.accessors.val.length ∧ accView g k j) ∧
    (r.non_attribute.val.getD j false = true ↔ u.non_attribute.val.getD j false = true ∨
      ∃ k, i ≤ k ∧ k < g.accessors.val.length ∧ ¬ roles.attribute.val.getD k false = true ∧ accView g k j)

-- ループ本体 1 回分 (アクセサ i) の効果
def AccStep (g : model.Gltf) (roles : validate.data.Roles) (i : Nat) (u u2 : validate.data.ViewUse) : Prop :=
  u2.image = u.image ∧ u2.animation = u.animation ∧
  u2.attribute.val.length = u.attribute.val.length ∧ u2.attribute_count.val.length = u.attribute_count.val.length ∧
  u2.index.val.length = u.index.val.length ∧ u2.ibm.val.length = u.ibm.val.length ∧
  u2.sparse.val.length = u.sparse.val.length ∧ u2.accessor.val.length = u.accessor.val.length ∧
  u2.non_attribute.val.length = u.non_attribute.val.length ∧
  ∀ j, (u2.attribute.val.getD j false = true ↔ u.attribute.val.getD j false = true ∨
      (roles.attribute.val.getD i false = true ∧ accView g i j)) ∧
    (u2.attribute_count.val.getD j 0#u64).val = (u.attribute_count.val.getD j 0#u64).val +
      (if roles.attribute.val.getD i false = true ∧ accView g i j then 1 else 0) ∧
    (u2.index.val.getD j false = true ↔ u.index.val.getD j false = true ∨
      (roles.index.val.getD i false = true ∧ accView g i j)) ∧
    (u2.ibm.val.getD j false = true ↔ u.ibm.val.getD j false = true ∨
      (roles.ibm.val.getD i false = true ∧ accView g i j)) ∧
    (u2.sparse.val.getD j false = true ↔ u.sparse.val.getD j false = true ∨
      ∃ s, (g.accessors.val[i]!).sparse = some s ∧
        (s.indices_buffer_view.val = j ∨ s.values_buffer_view.val = j)) ∧
    (u2.accessor.val.getD j false = true ↔ u.accessor.val.getD j false = true ∨ accView g i j) ∧
    (u2.non_attribute.val.getD j false = true ↔ u.non_attribute.val.getD j false = true ∨
      (¬ roles.attribute.val.getD i false = true ∧ accView g i j))

theorem exists_ge_step {P : Nat → Prop} {i n : Nat} (hi : i < n) :
    (∃ k, i ≤ k ∧ k < n ∧ P k) ↔ P i ∨ ∃ k, i + 1 ≤ k ∧ k < n ∧ P k := by
  constructor
  · rintro ⟨k, h1, h2, h3⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact Or.inl h3
    · exact Or.inr ⟨k, h1, h2, h3⟩
  · rintro (h | ⟨k, h1, h2, h3⟩)
    · exact ⟨i, Nat.le_refl _, hi, h⟩
    · exact ⟨k, by omega, h2, h3⟩

theorem AccLoopPost.step {g : model.Gltf} {roles : validate.data.Roles} {i : Nat} {u u2 r : validate.data.ViewUse}
    (hi : i < g.accessors.val.length) (h1 : AccStep g roles i u u2) (h2 : AccLoopPost g roles (i + 1) u2 r) :
    AccLoopPost g roles i u r := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a9, a10, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b9, b10, b8⟩ := h2
  refine ⟨by rw [b1, a1], by rw [b2, a2], by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    fun j => ?_⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := a8 j
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := b8 j
  have hr : List.range' i (g.accessors.val.length - i) = i :: List.range' (i + 1) (g.accessors.val.length - (i + 1)) := by
    rw [show g.accessors.val.length - i = (g.accessors.val.length - (i + 1)) + 1 by omega, List.range'_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [d1, c1, exists_ge_step hi]; simp only [or_assoc]
  · rw [d2, c2, hr, List.countP_cons]
    by_cases h : roles.attribute.val.getD i false = true ∧ accView g i j
    · simp only [h, and_self, ↓reduceIte, Bool.and_true, decide_true]; omega
    · simp only [h, ↓reduceIte]
      have : (roles.attribute.val.getD i false && decide (accView g i j)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases h' : roles.attribute.val.getD i false = true
        · exact Or.inr (fun h'' => h ⟨h', h''⟩)
        · exact Or.inl (by simpa using h')
      simp only [this, Bool.false_eq_true, ↓reduceIte]; omega
  · rw [d3, c3, exists_ge_step hi]; simp only [or_assoc]
  · rw [d4, c4, exists_ge_step hi]; simp only [or_assoc]
  · rw [d5, c5, drop_cons_iff hi, getElem!_pos g.accessors.val i hi]; simp only [or_assoc]
  · rw [d6, c6, exists_ge_step (P := fun k => accView g k j) hi]; simp only [or_assoc]
  · rw [d7, c7, exists_ge_step (P := fun k => ¬ roles.attribute.val.getD k false = true ∧ accView g k j) hi]
    simp only [or_assoc]

theorem AccLoopPost.done {g : model.Gltf} {roles : validate.data.Roles} {i : Nat} {u : validate.data.ViewUse} (hi : g.accessors.val.length ≤ i) :
    AccLoopPost g roles i u u := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [iff_self_or]; rintro ⟨k, h1, h2, -⟩; omega
  · simp [show g.accessors.val.length - i = 0 by omega]
  · simp only [iff_self_or]; rintro ⟨k, h1, h2, -⟩; omega
  · simp only [iff_self_or]; rintro ⟨k, h1, h2, -⟩; omega
  · rw [List.drop_eq_nil_of_le hi]; simp
  · simp only [iff_self_or]; rintro ⟨k, h1, h2, -⟩; omega
  · simp only [iff_self_or]; rintro ⟨k, h1, h2, -⟩; omega

set_option maxHeartbeats 4000000 in
@[step]
theorem mark_accessor_views_loop_spec (u : validate.data.ViewUse) (g : model.Gltf) (roles : validate.data.Roles) (i : Usize)
    (ha : ∀ a ∈ g.accessors.val, optLt a.buffer_view g.buffer_views.val.length ∧
      sparseRefsOk a.sparse g.buffer_views.val.length)
    (hro : roles.attribute.val.length = g.accessors.val.length ∧ roles.index.val.length = g.accessors.val.length ∧
      roles.ibm.val.length = g.accessors.val.length)
    (hl : u.attribute.val.length = g.buffer_views.val.length ∧
      u.attribute_count.val.length = g.buffer_views.val.length ∧ u.index.val.length = g.buffer_views.val.length ∧
      u.ibm.val.length = g.buffer_views.val.length ∧ u.sparse.val.length = g.buffer_views.val.length ∧
      u.accessor.val.length = g.buffer_views.val.length ∧ u.non_attribute.val.length = g.buffer_views.val.length)
    (hc : ∀ j, (u.attribute_count.val.getD j 0#u64).val ≤ i.val) (hi : i.val ≤ g.accessors.val.length) :
    validate.data.mark_accessor_views_loop u g roles i ⦃ r => AccLoopPost g roles i.val u r ⦄ := by
  unfold validate.data.mark_accessor_views_loop
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hl
  obtain ⟨o1, o2, o3⟩ := hro
  step*
  · subst a_post
    have hk := usize_lt_len ‹i < g.accessors.len›
    obtain ⟨hbv, hsp⟩ := ha _ (List.getElem_mem hk)
    have hmax : i.val + 1 ≤ U64.max := by
      have := alloc.vec.Vec.len_ineq g.accessors; have := usize_max_le_u64; omega
    have hri1 : i.val < roles.attribute.val.length := by omega
    have hri2 : i.val < roles.index.val.length := by omega
    have hri3 : i.val < roles.ibm.val.length := by omega
    rcases hb : (g.accessors.val[i.val]).buffer_view with _ | bv <;>
    rcases hs : (g.accessors.val[i.val]).sparse with _ | sp <;> simp only [hb, hs] at hbv hsp ⊢
    all_goals (try have hbl := hbv bv rfl)
    all_goals (try have hcb : (UScalar.cast .Usize bv).val = bv.val := u64_cast_usize_val _ (by scalar_tac))
    all_goals (try obtain ⟨hsl1, hsl2⟩ := hsp sp rfl)
    all_goals (try have hcs1 : (UScalar.cast .Usize sp.indices_buffer_view).val = sp.indices_buffer_view.val :=
      u64_cast_usize_val _ (by scalar_tac))
    all_goals (try have hcs2 : (UScalar.cast .Usize sp.values_buffer_view).val = sp.values_buffer_view.val :=
      u64_cast_usize_val _ (by scalar_tac))
    all_goals step*
    repeat' (first | (split <;> step*) | (have _hx := x.2; clear _hx; obtain ⟨x1, x2⟩ := x; simp only at x_post x_post1 ⊢; subst x_post1; step*))
    all_goals try (
      show ∀ _, _ ;
      subst_vars
      rw [i2_post]
      first
      | (intro j; have := hc j; simp only at *; omega)
      | (simp only [alloc.vec.Vec.set_val_eq]
         simp only [hcb] at *
         exact count_step_le _ _ _ _ hc (by omega) (by omega)))
    all_goals (
       refine AccLoopPost.step hk ?_ (by rw [i2_post] at r_post; exact r_post)
       subst_vars
       refine ⟨rfl, rfl, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
         fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
       all_goals simp only [accView, getElem!_pos g.accessors.val i.val hk, hb, hs, alloc.vec.Vec.set_val_eq,
         List.length_set, List.getD_eq_getElem _ _ hri1, List.getD_eq_getElem _ _ hri2,
         List.getD_eq_getElem _ _ hri3, Option.map_some, Option.map_none]
       all_goals (try simp only [hcb] at *)
       all_goals (try simp only [hcs1, hcs2] at *)
       all_goals (try simp (disch := ((try simp only [List.length_set]); omega)) only [getD_set_true, getD_set_eq])
       all_goals (try simp_all)
       all_goals first
       | tauto
       | (split
          · rename_i hj; subst hj
            have h1 := hc bv.val
            have hbl2 : bv.val < u.attribute_count.val.length := by omega
            simp only [List.getElem?_eq_getElem hbl2, Option.getD_some] at h1 ⊢
            omega
          · simp))
  · exact AccLoopPost.done (by scalar_tac)
termination_by g.accessors.val.length - i.val
decreasing_by all_goals scalar_decr_tac

-- MUST-026, MUST-027, MUST-029, MUST-038, MUST-039, MUST-046, MUST-050: bufferView の用途
/-- view_use はバッファビューの各用途を計算する -/
@[step]
theorem view_use_spec (g : model.Gltf) (roles : validate.data.Roles) (hr : refsOk g) (hro : RolesOk g roles) :
    validate.data.view_use g roles ⦃ u => ViewUseOk g u ⦄ := by
  unfold validate.data.view_use
  obtain ⟨-, -, -, -, hacc, -, -, himg, -, -, hanim⟩ := hr
  obtain ⟨o1, o2, o3, ho⟩ := hro
  have ha : ∀ a ∈ g.accessors.val, optLt a.buffer_view g.buffer_views.val.length ∧
      sparseRefsOk a.sparse g.buffer_views.val.length := fun a h => ⟨(hacc a h).2.1, (hacc a h).2.2⟩
  have ha2 : ∀ a ∈ g.accessors.val, optLt a.buffer_view g.buffer_views.val.length := fun a h => (ha a h).1
  have hz : ∀ n j, (List.replicate n false).getD j false = false := by
    intro n j; simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  have hz0 : ∀ n j, (List.replicate n 0#u64).getD j 0#u64 = 0#u64 := by
    intro n j; simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  step as ⟨v0, hv0⟩
  step as ⟨c0, hc0⟩
  step as ⟨u0, hu0⟩
  step as ⟨u1, w1, hu1, hw1, hw1'⟩
  step as ⟨u2, w2, hu2, hw2, hw2'⟩
  · obtain ⟨p1, p2, p3, p4, p5, p6, p7, p9, p10, p8⟩ := hu0
    subst hu1 hu2
    simp only at p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hw1 hw1' hw2 hw2' ⊢
    refine ⟨by simp_all, by simp_all, by simp_all, by simp_all, by simp_all, by simp_all, by simp_all, by simp_all,
      by simp_all, fun b => ?_⟩
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := p8 b
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [q1, hv0, hz]; simp only [Bool.false_eq_true, false_or, attrView]
      constructor
      · rintro ⟨k, -, hk, h1, h2⟩; exact ⟨k, hk, ((ho k).1).mp h1, h2⟩
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, Nat.zero_le _, hk, ((ho k).1).mpr h1, h2⟩
    · rw [q2, hc0, hz0, attrCount, Nat.sub_zero, ← List.range_eq_range']
      simp only [UScalar.ofNatCore_val_eq, zero_add]
      apply List.countP_congr
      intro k _
      simp only [Bool.and_eq_true, decide_eq_true_eq, (ho k).1]
    · rw [q3, hv0, hz]; simp only [Bool.false_eq_true, false_or, idxView]
      constructor
      · rintro ⟨k, -, hk, h1, h2⟩; exact ⟨k, hk, ((ho k).2.1).mp h1, h2⟩
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, Nat.zero_le _, hk, ((ho k).2.1).mpr h1, h2⟩
    · rw [q4, hv0, hz]; simp only [Bool.false_eq_true, false_or, ibmView]
      constructor
      · rintro ⟨k, -, hk, h1, h2⟩; exact ⟨k, hk, ((ho k).2.2).mp h1, h2⟩
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, Nat.zero_le _, hk, ((ho k).2.2).mpr h1, h2⟩
    · rw [q5, hv0, hz]; simp [sparseView]
    · rw [hw1', p1, hv0, hz]; simp [imageView]
    · rw [hw2', p2, hv0, hz]; simp [animView]
    · rw [q6, hv0, hz]; simp only [Bool.false_eq_true, false_or, accessorView]
      constructor
      · rintro ⟨k, -, hk, h⟩; exact ⟨k, hk, h⟩
      · rintro ⟨k, hk, h⟩; exact ⟨k, Nat.zero_le _, hk, h⟩
    · rw [q7, hv0, hz]; simp only [Bool.false_eq_true, false_or, nonAttrView]
      constructor
      · rintro ⟨k, -, hk, h1, h2⟩; exact ⟨k, hk, fun h => h1 (((ho k).1).mpr h), h2⟩
      · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, Nat.zero_le _, hk, fun h => h1 (((ho k).1).mp h), h2⟩

theorem opt_ne_some_iff (o : Option U64) (n : U64) : ¬ o = some n ↔ ∀ t, o = some t → t.val ≠ n.val := by
  rcases o with _ | t
  · simp
  · simp only [Option.some.injEq, forall_eq']; rw [UScalar.eq_equiv]

-- MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039: byteStride の規則
@[step]
theorem stride_ok_spec (bv : model.BufferView) (cnt : U64) (nv : Bool) :
    validate.data.stride_ok bv cnt nv ⦃ r => r = true ↔ (bv.byte_stride = none → cnt.val < 2) ∧
      (∀ st, bv.byte_stride = some st → 4 ≤ st.val ∧ st.val ≤ 252 ∧ st.val % 4 = 0 ∧
        st.val ≤ bv.byte_length.val ∧ nv = false ∧ ∀ t, bv.target = some t → t.val ≠ 34963) ⦄ := by
  unfold validate.data.stride_ok
  rcases h : bv.byte_stride with _ | st <;> step* <;> simp_all [opt_ne_some_iff]

-- MUST-028, MUST-070, MUST-090: target の規則
@[step]
theorem target_ok_spec (t : Option U64) (a i o : Bool) :
    validate.data.target_ok t a i o ⦃ r => r = true ↔ ∀ x, t = some x →
      ¬ (a = true ∧ x.val ≠ 34962) ∧ ¬ (i = true ∧ x.val ≠ 34963) ∧ o = false ⦄ := by
  unfold validate.data.target_ok
  rcases t with _ | x <;> step*

-- MUST-036: アクセサーは bufferView に収まる
@[step]
theorem fits_spec (offset count stride size limit : U64) (hc : 0 < count.val) :
    validate.data.fits offset count stride size limit ⦃ r => r = true ↔
      offset.val + (count.val - 1) * stride.val + size.val ≤ limit.val ⦄ := by
  unfold validate.data.fits
  have := limit.hBounds
  step*

theorem vec_index_ok {α} (v : alloc.vec.Vec α) (i : Usize) (h : i.val < v.val.length) :
    v.index_usize i = ok (v.val[i.val]) := by
  unfold alloc.vec.Vec.index_usize
  have : v[i.val]? = some v.val[i.val] := by
    simp only [alloc.vec.Vec.getElem?_Nat_eq]; exact List.getElem?_eq_getElem h
  rw [this]

theorem ite_ok {α} (c : Prop) [Decidable c] (a b : α) :
    (if c then (ok a : Result α) else ok b) = ok (if c then a else b) := by split <;> rfl

theorem nv_false (i m o im : Bool) :
    (if i = true then true else if m = true then true else if o = true then true else im) = false ↔
      i = false ∧ m = false ∧ o = false ∧ im = false := by
  cases i <;> cases m <;> cases o <;> cases im <;> simp

theorem img1_false (m o im : Bool) :
    (if m = true then true else if o = true then true else im) = false ↔ m = false ∧ o = false ∧ im = false := by
  cases m <;> cases o <;> cases im <;> simp

theorem other_iff (n s : Bool) : (n = true ∨ s = true) ↔ (if n = true then true else s) = true := by
  cases n <;> simp

-- B2 の「高々 1 つ」の判定
theorem one_kind_iff (a i m o im : Bool) :
    (if a = true then decide (a.toNat + i.toNat + m.toNat + o.toNat + im.toNat ≤ 1) else
      if i = true then decide (a.toNat + i.toNat + m.toNat + o.toNat + im.toNat ≤ 1) else
      if m = true then decide (a.toNat + i.toNat + m.toNat + o.toNat + im.toNat ≤ 1) else
      if im = true then decide (a.toNat + i.toNat + m.toNat + o.toNat + im.toNat ≤ 1) else true) = true ↔
    ((a = true ∨ i = true ∨ m = true ∨ im = true) →
      atMostOne [a = true, i = true, m = true, o = true, im = true]) := by
  simp only [atMostOne, List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, List.Pairwise.nil]
  cases a <;> cases i <;> cases m <;> cases o <;> cases im <;> simp

-- MUST-025, MUST-026, MUST-027, MUST-028, MUST-029, MUST-030, MUST-031, MUST-032, MUST-033, MUST-038, MUST-039: bufferView の規則 B1–B4
-- MUST-046, MUST-050, MUST-070, MUST-072, MUST-090, MUST-098, MUST-110, MUST-142, MUST-146: 用途ごとの byteStride / target
set_option maxHeartbeats 8000000 in
@[step]
theorem buffer_view_ok_spec (g : model.Gltf) (u : validate.data.ViewUse) (b : Usize) (hb : b.val < g.buffer_views.val.length)
    (hbuf : (g.buffer_views.val[b.val]).buffer.val < g.buffers.val.length)
    (hl : u.attribute.val.length = g.buffer_views.val.length ∧
      u.attribute_count.val.length = g.buffer_views.val.length ∧ u.index.val.length = g.buffer_views.val.length ∧
      u.ibm.val.length = g.buffer_views.val.length ∧ u.sparse.val.length = g.buffer_views.val.length ∧
      u.image.val.length = g.buffer_views.val.length ∧ u.animation.val.length = g.buffer_views.val.length ∧
      u.accessor.val.length = g.buffer_views.val.length ∧ u.non_attribute.val.length = g.buffer_views.val.length) :
    validate.data.buffer_view_ok g u b ⦃ r => r = true ↔ bufferViewRules g g.buffer_views.val[b.val]
      (u.attribute.val.getD b.val false = true) (u.index.val.getD b.val false = true)
      (u.ibm.val.getD b.val false = true)
      (u.animation.val.getD b.val false = true) (u.sparse.val.getD b.val false = true)
      (u.image.val.getD b.val false = true) (u.accessor.val.getD b.val false = true)
      (u.non_attribute.val.getD b.val false = true) (u.attribute_count.val.getD b.val 0#u64).val ⦄ := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hl
  have hbm := mod_numBits_of_lt hbuf (alloc.vec.Vec.len_ineq g.buffers)
  unfold validate.data.buffer_view_ok
  simp only [alloc.vec.Vec.index_slice_index]
  simp only [vec_index_ok _ _ hb, vec_index_ok _ _ (show b.val < u.attribute.val.length by omega),
    vec_index_ok _ _ (show b.val < u.index.val.length by omega),
    vec_index_ok _ _ (show b.val < u.ibm.val.length by omega),
    vec_index_ok _ _ (show b.val < u.sparse.val.length by omega),
    vec_index_ok _ _ (show b.val < u.image.val.length by omega),
    vec_index_ok _ _ (show b.val < u.animation.val.length by omega),
    vec_index_ok _ _ (show b.val < u.accessor.val.length by omega),
    vec_index_ok _ _ (show b.val < u.non_attribute.val.length by omega),
    vec_index_ok _ _ (show b.val < u.attribute_count.val.length by omega), bind_tc_ok, ite_ok]
  simp only [List.getD_eq_getElem _ _ (show b.val < u.attribute.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.attribute_count.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.index.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.ibm.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.sparse.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.image.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.animation.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.accessor.val.length by omega),
    List.getD_eq_getElem _ _ (show b.val < u.non_attribute.val.length by omega),
    getElem!_pos g.buffers.val (g.buffer_views.val[b.val]).buffer.val hbuf]
  have hcv : (UScalar.cast .Usize (g.buffer_views.val[b.val]).buffer).val = (g.buffer_views.val[b.val]).buffer.val :=
    u64_cast_usize_val _ (by scalar_tac)
  unfold bufferViewRules atMostOne
  generalize u.attribute_count.val[b.val] = cnt
  cases u.attribute.val[b.val] <;> cases u.index.val[b.val] <;> cases u.ibm.val[b.val] <;>
    cases u.animation.val[b.val] <;> cases u.sparse.val[b.val] <;> cases u.image.val[b.val] <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.pairwise_cons, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true, List.Pairwise.nil, true_or, or_true, or_false, false_or,
      not_true_eq_false, not_false_eq_true, and_false, false_and, true_and, and_self, true_implies,
      false_implies, not_and, not_false_eq_true, imp_false]
  all_goals step*
  all_goals (repeat' (split <;> step*))
  all_goals (
    subst_vars
    try (have hx := getElem_idx_eq hcv (by scalar_tac) hbuf; rw [hx] at *)
    try simp_all [UScalar.le_equiv, UScalar.lt_equiv])

-- ループ用: 用途の配列で与えた規則
def bvRulesAt (g : model.Gltf) (u : validate.data.ViewUse) (q : Nat) : Prop :=
  ∀ h : q < g.buffer_views.val.length, bufferViewRules g g.buffer_views.val[q]
    (u.attribute.val.getD q false = true) (u.index.val.getD q false = true) (u.ibm.val.getD q false = true)
    (u.animation.val.getD q false = true) (u.sparse.val.getD q false = true)
    (u.image.val.getD q false = true) (u.accessor.val.getD q false = true) (u.non_attribute.val.getD q false = true)
    (u.attribute_count.val.getD q 0#u64).val

@[step]
theorem buffer_views_ok_loop_spec (g : model.Gltf) (u : validate.data.ViewUse) (b : Usize) (hr : bufferViewRefsOk g)
    (hu : ViewUseOk g u) (hb : b.val ≤ g.buffer_views.val.length) :
    validate.data.buffer_views_ok_loop g u b ⦃ r => r = true ↔ forallIdx g.buffer_views.val.length b.val (bvRulesAt g u) ⦄ := by
  unfold validate.data.buffer_views_ok_loop
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, -⟩ := id hu
  have hr' : ∀ q (h : q < g.buffer_views.val.length), (g.buffer_views.val[q]).buffer.val < g.buffers.val.length :=
    fun q h => hr _ (List.getElem_mem h)
  by_cases hlt : b < g.buffer_views.len
  · have hb' : b.val < g.buffer_views.val.length := by scalar_tac
    have e : bvRulesAt g u b.val ↔ bufferViewRules g g.buffer_views.val[b.val]
        (u.attribute.val.getD b.val false = true) (u.index.val.getD b.val false = true)
        (u.ibm.val.getD b.val false = true)
        (u.animation.val.getD b.val false = true) (u.sparse.val.getD b.val false = true)
        (u.image.val.getD b.val false = true) (u.accessor.val.getD b.val false = true)
        (u.non_attribute.val.getD b.val false = true) (u.attribute_count.val.getD b.val 0#u64).val := by
      simp only [bvRulesAt, hb', forall_true_left]
    simp only [hlt, ↓reduceIte]
    step as ⟨b1, hb1⟩
    split
    · step*
      rw [r_post, forallIdx_step_vec hlt, e, ← hb1]; simp_all
    · rw [forallIdx_step_vec hlt, e, ← hb1]; simp_all
  · simp only [hlt, ↓reduceIte, WP.spec_ok, true_iff]
    rw [forallIdx_end_vec hlt]; trivial
termination_by g.buffer_views.val.length - b.val
decreasing_by all_goals scalar_decr_tac

/-- B1–B4 -/
@[step]
theorem buffer_views_ok_spec (g : model.Gltf) (u : validate.data.ViewUse) (hr : bufferViewRefsOk g) (hu : ViewUseOk g u) :
    validate.data.buffer_views_ok g u ⦃ r => r = true ↔ bufferViewsOk g ⦄ := by
  unfold validate.data.buffer_views_ok
  step*
  rw [r_post, forallIdx_zero]
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := hu
  simp only [bvRulesAt, bufferViewsOk]
  apply forall_congr'; intro q
  constructor
  · intro hq hq'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h q
    have := hq hq' hq'
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9] at this
    exact this
  · intro hq hq' hq''
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h q
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact hq hq''

@[step]
theorem component_size_spec (ct : U64) : validate.data.component_size ct ⦃ r => r.val = componentSize ct.val ⦄ := by
  unfold validate.data.component_size componentSize
  step*

theorem componentSize_pos (ct : Nat) : 0 < componentSize ct := by
  unfold componentSize; split_ifs <;> omega

theorem componentSize_le (ct : Nat) : componentSize ct ≤ 4 := by
  unfold componentSize; split_ifs <;> omega

@[step]
theorem element_size_spec (a : model.Accessor) (h : accessorShapeOk a) :
    validate.data.element_size a ⦃ r => r.val = elementSize a ⦄ := by
  unfold validate.data.element_size elementSize matRows roundUp4 accessorShapeOk at *
  have := componentSize_le a.component_type.val
  step*
  repeat' (split <;> step*)

theorem elementSize_le (a : model.Accessor) (h : accessorShapeOk a) : elementSize a ≤ 64 := by
  unfold elementSize matRows roundUp4
  have h4 := componentSize_le a.component_type.val
  unfold accessorShapeOk at h
  cases hm : a.is_matrix
  · have h1 : a.components.val ≤ 4 := (h.2 hm).2
    have := Nat.mul_le_mul h1 h4
    simp only [Bool.false_eq_true, ↓reduceIte]; omega
  · simp only [↓reduceIte]; split_ifs <;> omega

-- MUST-034, MUST-036, MUST-037, MUST-040, MUST-041, MUST-042: アクセサーの配置
set_option maxHeartbeats 2000000 in
@[step]
theorem accessor_view_ok_spec (g : model.Gltf) (a : model.Accessor) (isAttr : Bool) (hc : 0 < a.count.val)
    (hs : accessorShapeOk a) (hb : optLt a.buffer_view g.buffer_views.val.length) :
    validate.data.accessor_view_ok g a isAttr ⦃ r => r = true ↔ accessorViewOk g a (isAttr = true) ⦄ := by
  unfold validate.data.accessor_view_ok accessorViewOk
  have hcs := componentSize_pos a.component_type.val
  have hcs4 := componentSize_le a.component_type.val
  have hes := elementSize_le a hs
  rcases hbv : a.buffer_view with _ | b
  · step*; simp [Option.isNone_iff_eq_none]
  · have hbl := hb b hbv
    have hcv : (UScalar.cast .Usize b).val = b.val := u64_cast_usize_val _ (by scalar_tac)
    simp only [reduceCtorEq, false_imp_iff, true_and, Option.some.injEq, forall_eq',
      getElem!_pos g.buffer_views.val b.val hbl]
    step*
    repeat' (split <;> step*)
    all_goals (
      subst_vars
      try (have hx := getElem_idx_eq hcv (by scalar_tac) hbl; rw [hx] at *)
      try simp_all [UScalar.le_equiv, UScalar.lt_equiv]
      try simp_all [UScalar.eq_equiv])

theorem add_pred_mul_add (a c x : Nat) (h : 0 < c) : a + (c - 1) * x + x = a + c * x := by
  obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
  simp [Nat.add_mul, Nat.add_assoc]

-- MUST-044, MUST-045, MUST-047, MUST-048, MUST-051, MUST-052: sparse の規則
set_option maxHeartbeats 4000000 in
@[step]
theorem sparse_ok_spec (g : model.Gltf) (a : model.Accessor) (hs : accessorShapeOk a)
    (hr : sparseRefsOk a.sparse g.buffer_views.val.length) :
    validate.data.sparse_ok g a ⦃ r => r = true ↔ sparseOk g a ⦄ := by
  unfold validate.data.sparse_ok sparseOk
  have hcs := componentSize_pos a.component_type.val
  have hes := elementSize_le a hs
  rcases hsp : a.sparse with _ | sp
  · step*
  · obtain ⟨h1, h2⟩ := hr sp hsp
    have hc1 : (UScalar.cast .Usize sp.indices_buffer_view).val = sp.indices_buffer_view.val :=
      u64_cast_usize_val _ (by scalar_tac)
    have hc2 : (UScalar.cast .Usize sp.values_buffer_view).val = sp.values_buffer_view.val :=
      u64_cast_usize_val _ (by scalar_tac)
    simp only [reduceCtorEq, false_imp_iff, true_and, Option.some.injEq, forall_eq',
      getElem!_pos g.buffer_views.val sp.indices_buffer_view.val h1,
      getElem!_pos g.buffer_views.val sp.values_buffer_view.val h2]
    step*
    all_goals (
      subst_vars
      try (have hx := getElem_idx_eq hc1 (by scalar_tac) h1; rw [hx] at *; clear hx)
      try (have hx := getElem_idx_eq hc2 (by scalar_tac) h2; rw [hx] at *; clear hx)
      try simp_all [UScalar.le_equiv, UScalar.lt_equiv, componentSize]
      try simp_all [UScalar.eq_equiv])
    all_goals (
      by_cases hpos : 0 < sp.count.val
      · (try simp only [add_pred_mul_add _ _ _ hpos] at *); simp_all; try omega
      · simp_all)

-- MUST-053: min / max の長さ = 成分数
@[step]
theorem bounds_len_ok_spec (l : Option U64) (c : U64) :
    validate.data.bounds_len_ok l c ⦃ r => r = true ↔ ∀ n, l = some n → n.val = c.val ⦄ := by
  unfold validate.data.bounds_len_ok
  rcases l with _ | n <;> step* <;> simp [UScalar.eq_equiv]

-- MUST-035, MUST-053: normalized の型、min / max の長さ
set_option maxHeartbeats 2000000 in
@[step]
theorem accessor_ok_spec (g : model.Gltf) (roles : validate.data.Roles) (i : Usize) (hi : i.val < g.accessors.val.length)
    (hr : accessorRefsOk g) (hro : roles.attribute.val.length = g.accessors.val.length) :
    validate.data.accessor_ok g roles i ⦃ r => r = true ↔ accessorBasicOk g.accessors.val[i.val] ∧
      accessorViewOk g g.accessors.val[i.val] (roles.attribute.val.getD i.val false = true) ∧
      sparseOk g g.accessors.val[i.val] ⦄ := by
  unfold validate.data.accessor_ok accessorBasicOk
  obtain ⟨h1, h2, h3⟩ := hr _ (List.getElem_mem hi)
  rw [List.getD_eq_getElem _ _ (by omega)]
  step*
  all_goals (try simp_all [UScalar.eq_equiv])

-- ループ用: 役割の配列で与えた AC1–AC3
def accRulesAt (g : model.Gltf) (roles : validate.data.Roles) (q : Nat) : Prop :=
  ∀ h : q < g.accessors.val.length, accessorBasicOk g.accessors.val[q] ∧
    accessorViewOk g g.accessors.val[q] (roles.attribute.val.getD q false = true) ∧ sparseOk g g.accessors.val[q]

@[step]
theorem accessors_ok_loop_spec (g : model.Gltf) (roles : validate.data.Roles) (i : Usize) (hr : accessorRefsOk g)
    (hro : roles.attribute.val.length = g.accessors.val.length) (hi : i.val ≤ g.accessors.val.length) :
    validate.data.accessors_ok_loop g roles i ⦃ r => r = true ↔ forallIdx g.accessors.val.length i.val (accRulesAt g roles) ⦄ := by
  unfold validate.data.accessors_ok_loop
  by_cases hlt : i < g.accessors.len
  · have hi' : i.val < g.accessors.val.length := by scalar_tac
    have e : accRulesAt g roles i.val ↔ accessorBasicOk g.accessors.val[i.val] ∧
        accessorViewOk g g.accessors.val[i.val] (roles.attribute.val.getD i.val false = true) ∧
        sparseOk g g.accessors.val[i.val] := by
      simp only [accRulesAt, hi', forall_true_left]
    simp only [hlt, ↓reduceIte]
    step as ⟨b1, hb1⟩
    split
    · step*
      rw [r_post, forallIdx_step_vec hlt, e, ← hb1]; simp_all
    · rw [forallIdx_step_vec hlt, e, ← hb1]; simp_all
  · simp only [hlt, ↓reduceIte, WP.spec_ok, true_iff]
    rw [forallIdx_end_vec hlt]; trivial
termination_by g.accessors.val.length - i.val
decreasing_by all_goals scalar_decr_tac

/-- AC1–AC3 -/
@[step]
theorem accessors_ok_spec (g : model.Gltf) (roles : validate.data.Roles) (hr : accessorRefsOk g) (hro : RolesOk g roles) :
    validate.data.accessors_ok g roles ⦃ r => r = true ↔ accessorsOk g ⦄ := by
  unfold validate.data.accessors_ok
  obtain ⟨o1, -, -, ho⟩ := hro
  step*
  rw [r_post, forallIdx_zero]
  simp only [accRulesAt, accessorsOk]
  apply forall_congr'; intro q
  rw [(ho q).1]
  constructor
  · intro h hq; exact h hq hq
  · intro h hq _; exact h hq

/-- data_ok: B1–B4 と AC1–AC3 -/
@[step]
theorem data_ok_spec (g : model.Gltf) (hr : refsOk g) : validate.data.data_ok g ⦃ r => r = true ↔ bufferViewsOk g ∧ accessorsOk g ⦄ := by
  unfold validate.data.data_ok
  have hr' := hr
  obtain ⟨-, -, -, hm, hacc, hbv, -, -, -, hs, -⟩ := hr'
  step*

end LoadGltf
