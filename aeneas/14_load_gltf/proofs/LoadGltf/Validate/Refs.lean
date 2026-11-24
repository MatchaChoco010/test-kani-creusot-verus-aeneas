import LoadGltf.Validate.Util

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## V.0 refs_ok: すべての添字が範囲内で、アクセサの形が正しい -/

-- マテリアルの textureInfo の一覧
def textureInfos (m : model.Material) : List model.TextureInfo :=
  [m.base_color_texture, m.metallic_roughness_texture, m.normal_texture, m.occlusion_texture,
    m.emissive_texture].filterMap id

-- 行列なら 4, 9, 16 成分、それ以外は 1..4 成分
def accessorShapeOk (a : model.Accessor) : Prop :=
  (a.is_matrix = true → a.components.val = 4 ∨ a.components.val = 9 ∨ a.components.val = 16) ∧
  (a.is_matrix = false → 1 ≤ a.components.val ∧ a.components.val ≤ 4)

def primitiveRefsOk (g : model.Gltf) (p : model.Primitive) : Prop :=
  (∀ x ∈ p.attributes.val, x.accessor.val < g.accessors.val.length) ∧
  (∀ t ∈ p.targets.val, ∀ x ∈ t.val, x.accessor.val < g.accessors.val.length) ∧
  optLt p.indices g.accessors.val.length ∧ optLt p.material g.materials.val.length

def sparseRefsOk (s : Option model.Sparse) (n : Nat) : Prop :=
  ∀ sp, s = some sp → sp.indices_buffer_view.val < n ∧ sp.values_buffer_view.val < n

def sceneRefsOk (g : model.Gltf) : Prop := ∀ sc ∈ g.scenes.val, ∀ n ∈ sc.nodes.val, n.val < g.nodes.val.length

def nodeRefsOk (g : model.Gltf) : Prop :=
  ∀ nd ∈ g.nodes.val, (∀ c ∈ nd.children.val, c.val < g.nodes.val.length) ∧
    optLt nd.mesh g.meshes.val.length ∧ optLt nd.camera g.cameras.val.length ∧
    optLt nd.skin g.skins.val.length

def meshRefsOk (g : model.Gltf) : Prop := ∀ m ∈ g.meshes.val, ∀ p ∈ m.primitives.val, primitiveRefsOk g p

def accessorRefsOk (g : model.Gltf) : Prop :=
  ∀ a ∈ g.accessors.val, accessorShapeOk a ∧ optLt a.buffer_view g.buffer_views.val.length ∧
    sparseRefsOk a.sparse g.buffer_views.val.length

def bufferViewRefsOk (g : model.Gltf) : Prop := ∀ bv ∈ g.buffer_views.val, bv.buffer.val < g.buffers.val.length

def textureRefsOk (g : model.Gltf) : Prop :=
  ∀ t ∈ g.textures.val, optLt t.sampler g.samplers_len.val ∧ optLt t.source g.images.val.length

def imageRefsOk (g : model.Gltf) : Prop := ∀ im ∈ g.images.val, optLt im.buffer_view g.buffer_views.val.length

def materialRefsOk (g : model.Gltf) : Prop :=
  ∀ m ∈ g.materials.val, ∀ ti ∈ textureInfos m, ti.index.val < g.textures.val.length

def skinRefsOk (g : model.Gltf) : Prop :=
  ∀ sk ∈ g.skins.val, (∀ j ∈ sk.joints.val, j.val < g.nodes.val.length) ∧
    optLt sk.skeleton g.nodes.val.length ∧ optLt sk.inverse_bind_matrices g.accessors.val.length

def animationRefsOk (g : model.Gltf) : Prop :=
  ∀ an ∈ g.animations.val,
    (∀ ch ∈ an.channels.val, ch.sampler.val < an.samplers.val.length ∧ optLt ch.node g.nodes.val.length) ∧
    (∀ s ∈ an.samplers.val, s.input.val < g.accessors.val.length ∧ s.output.val < g.accessors.val.length)

-- refs_ok(g)
-- MUST-014: すべての添字が範囲内
def refsOk (g : model.Gltf) : Prop :=
  optLt g.scene g.scenes.val.length ∧ sceneRefsOk g ∧ nodeRefsOk g ∧ meshRefsOk g ∧
  accessorRefsOk g ∧ bufferViewRefsOk g ∧ textureRefsOk g ∧ imageRefsOk g ∧ materialRefsOk g ∧
  skinRefsOk g ∧ animationRefsOk g

@[step]
theorem scene_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.scenes.val.length) :
    validate.refs.scene_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.scenes.val i.val (fun x => ∀ n ∈ (x).nodes.val, n.val < g.nodes.val.length) ⦄ := by
  unfold validate.refs.scene_refs_ok_loop
  loop_auto
termination_by g.scenes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem scene_refs_ok_spec (g : model.Gltf) :
    validate.refs.scene_refs_ok g ⦃ r => r = true ↔ sceneRefsOk g ⦄ := by
  unfold validate.refs.scene_refs_ok sceneRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem node_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.nodes.val.length) :
    validate.refs.node_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.nodes.val i.val (fun x => (∀ c ∈ (x).children.val, c.val < g.nodes.val.length) ∧ optLt (x).mesh g.meshes.val.length ∧ optLt (x).camera g.cameras.val.length ∧ optLt (x).skin g.skins.val.length) ⦄ := by
  unfold validate.refs.node_refs_ok_loop
  loop_auto
termination_by g.nodes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem node_refs_ok_spec (g : model.Gltf) :
    validate.refs.node_refs_ok g ⦃ r => r = true ↔ nodeRefsOk g ⦄ := by
  unfold validate.refs.node_refs_ok nodeRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem attributes_less_loop_spec (attrs : alloc.vec.Vec model.Attribute) (n : Usize) (i : Usize) (hi : i.val ≤ attrs.val.length) :
    validate.refs.attributes_less_loop attrs n i ⦃ r => r = true ↔
      forallFrom attrs.val i.val (fun x => (x).accessor.val < n.val) ⦄ := by
  unfold validate.refs.attributes_less_loop
  loop_auto
termination_by attrs.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem attributes_less_spec (attrs : alloc.vec.Vec model.Attribute) (n : Usize) :
    validate.refs.attributes_less attrs n ⦃ r => r = true ↔ ∀ x ∈ attrs.val, (x).accessor.val < n.val ⦄ := by
  unfold validate.refs.attributes_less
  step*
  simp_all [forallFrom_zero]

@[step]
theorem targets_less_loop_spec (targets : alloc.vec.Vec (alloc.vec.Vec model.Attribute)) (n : Usize) (i : Usize) (hi : i.val ≤ targets.val.length) :
    validate.refs.targets_less_loop targets n i ⦃ r => r = true ↔
      forallFrom targets.val i.val (fun x => ∀ y ∈ (x).val, y.accessor.val < n.val) ⦄ := by
  unfold validate.refs.targets_less_loop
  loop_auto
termination_by targets.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem targets_less_spec (targets : alloc.vec.Vec (alloc.vec.Vec model.Attribute)) (n : Usize) :
    validate.refs.targets_less targets n ⦃ r => r = true ↔ ∀ x ∈ targets.val, ∀ y ∈ (x).val, y.accessor.val < n.val ⦄ := by
  unfold validate.refs.targets_less
  step*
  simp_all [forallFrom_zero]

@[step]
theorem texture_info_less_spec (t : Option model.TextureInfo) (n : Usize) :
    validate.refs.texture_info_less t n ⦃ r => r = true ↔ ∀ ti, t = some ti → ti.index.val < n.val ⦄ := by
  unfold validate.refs.texture_info_less
  step_auto

@[step]
theorem primitive_refs_ok_loop_spec (g : model.Gltf) (m : model.Mesh) (j : Usize) (hi : j.val ≤ m.primitives.val.length) :
    validate.refs.primitive_refs_ok_loop g m j ⦃ r => r = true ↔
      forallFrom m.primitives.val j.val (fun x => primitiveRefsOk g (x)) ⦄ := by
  unfold validate.refs.primitive_refs_ok_loop
  loop_auto [primitiveRefsOk]
termination_by m.primitives.val.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem primitive_refs_ok_spec (g : model.Gltf) (m : model.Mesh) :
    validate.refs.primitive_refs_ok g m ⦃ r => r = true ↔ ∀ x ∈ m.primitives.val, primitiveRefsOk g (x) ⦄ := by
  unfold validate.refs.primitive_refs_ok
  step*
  simp_all [forallFrom_zero]

@[step]
theorem mesh_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.meshes.val.length) :
    validate.refs.mesh_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.meshes.val i.val (fun x => ∀ p ∈ (x).primitives.val, primitiveRefsOk g p) ⦄ := by
  unfold validate.refs.mesh_refs_ok_loop
  loop_auto
termination_by g.meshes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem mesh_refs_ok_spec (g : model.Gltf) :
    validate.refs.mesh_refs_ok g ⦃ r => r = true ↔ meshRefsOk g ⦄ := by
  unfold validate.refs.mesh_refs_ok meshRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem sparse_refs_ok_spec (s : Option model.Sparse) (n : Usize) :
    validate.refs.sparse_refs_ok s n ⦃ r => r = true ↔ sparseRefsOk s n.val ⦄ := by
  unfold validate.refs.sparse_refs_ok sparseRefsOk
  step* <;> simp_all

@[step]
theorem accessor_shape_ok_spec (a : model.Accessor) :
    validate.refs.accessor_shape_ok a ⦃ r => r = true ↔ accessorShapeOk a ⦄ := by
  unfold validate.refs.accessor_shape_ok accessorShapeOk
  step_auto

@[step]
theorem accessor_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.accessors.val.length) :
    validate.refs.accessor_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.accessors.val i.val (fun x => accessorShapeOk (x) ∧ optLt (x).buffer_view g.buffer_views.val.length ∧ sparseRefsOk (x).sparse g.buffer_views.val.length) ⦄ := by
  unfold validate.refs.accessor_refs_ok_loop
  loop_auto
termination_by g.accessors.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem accessor_refs_ok_spec (g : model.Gltf) :
    validate.refs.accessor_refs_ok g ⦃ r => r = true ↔ accessorRefsOk g ⦄ := by
  unfold validate.refs.accessor_refs_ok accessorRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem buffer_view_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.buffer_views.val.length) :
    validate.refs.buffer_view_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.buffer_views.val i.val (fun x => (x).buffer.val < g.buffers.val.length) ⦄ := by
  unfold validate.refs.buffer_view_refs_ok_loop
  loop_auto
termination_by g.buffer_views.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem buffer_view_refs_ok_spec (g : model.Gltf) :
    validate.refs.buffer_view_refs_ok g ⦃ r => r = true ↔ bufferViewRefsOk g ⦄ := by
  unfold validate.refs.buffer_view_refs_ok bufferViewRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem texture_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.textures.val.length) :
    validate.refs.texture_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.textures.val i.val (fun x => optLt (x).sampler g.samplers_len.val ∧ optLt (x).source g.images.val.length) ⦄ := by
  unfold validate.refs.texture_refs_ok_loop
  loop_auto
termination_by g.textures.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem texture_refs_ok_spec (g : model.Gltf) :
    validate.refs.texture_refs_ok g ⦃ r => r = true ↔ textureRefsOk g ⦄ := by
  unfold validate.refs.texture_refs_ok textureRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem image_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.images.val.length) :
    validate.refs.image_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.images.val i.val (fun x => optLt (x).buffer_view g.buffer_views.val.length) ⦄ := by
  unfold validate.refs.image_refs_ok_loop
  loop_auto
termination_by g.images.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem image_refs_ok_spec (g : model.Gltf) :
    validate.refs.image_refs_ok g ⦃ r => r = true ↔ imageRefsOk g ⦄ := by
  unfold validate.refs.image_refs_ok imageRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem material_refs_ok_loop_spec (v : alloc.vec.Vec model.Material) (nt i : Usize) (hi : i.val ≤ v.val.length) :
    validate.refs.material_refs_ok_loop v nt i ⦃ r => r = true ↔
      forallFrom v.val i.val (fun m => ∀ ti ∈ textureInfos m, ti.index.val < nt.val) ⦄ := by
  unfold validate.refs.material_refs_ok_loop
  loop_auto [textureInfos]
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem material_refs_ok_spec (g : model.Gltf) : validate.refs.material_refs_ok g ⦃ r => r = true ↔ materialRefsOk g ⦄ := by
  unfold validate.refs.material_refs_ok materialRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem skin_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.skins.val.length) :
    validate.refs.skin_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.skins.val i.val (fun x => (∀ k ∈ (x).joints.val, k.val < g.nodes.val.length) ∧ optLt (x).skeleton g.nodes.val.length ∧ optLt (x).inverse_bind_matrices g.accessors.val.length) ⦄ := by
  unfold validate.refs.skin_refs_ok_loop
  loop_auto
termination_by g.skins.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem skin_refs_ok_spec (g : model.Gltf) :
    validate.refs.skin_refs_ok g ⦃ r => r = true ↔ skinRefsOk g ⦄ := by
  unfold validate.refs.skin_refs_ok skinRefsOk
  step*
  simp_all [forallFrom_zero]

@[step]
theorem channel_refs_ok_loop_spec (g : model.Gltf) (an : model.Animation) (c : Usize) (hi : c.val ≤ an.channels.val.length) :
    validate.refs.channel_refs_ok_loop g an c ⦃ r => r = true ↔
      forallFrom an.channels.val c.val (fun x => (x).sampler.val < an.samplers.val.length ∧ optLt (x).node g.nodes.val.length) ⦄ := by
  unfold validate.refs.channel_refs_ok_loop
  loop_auto
termination_by an.channels.val.length - c.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem channel_refs_ok_spec (g : model.Gltf) (an : model.Animation) :
    validate.refs.channel_refs_ok g an ⦃ r => r = true ↔ ∀ x ∈ an.channels.val, (x).sampler.val < an.samplers.val.length ∧ optLt (x).node g.nodes.val.length ⦄ := by
  unfold validate.refs.channel_refs_ok
  step*
  simp_all [forallFrom_zero]

@[step]
theorem animation_sampler_refs_ok_loop_spec (g : model.Gltf) (an : model.Animation) (s : Usize) (hi : s.val ≤ an.samplers.val.length) :
    validate.refs.animation_sampler_refs_ok_loop g an s ⦃ r => r = true ↔
      forallFrom an.samplers.val s.val (fun x => (x).input.val < g.accessors.val.length ∧ (x).output.val < g.accessors.val.length) ⦄ := by
  unfold validate.refs.animation_sampler_refs_ok_loop
  loop_auto
termination_by an.samplers.val.length - s.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem animation_sampler_refs_ok_spec (g : model.Gltf) (an : model.Animation) :
    validate.refs.animation_sampler_refs_ok g an ⦃ r => r = true ↔ ∀ x ∈ an.samplers.val, (x).input.val < g.accessors.val.length ∧ (x).output.val < g.accessors.val.length ⦄ := by
  unfold validate.refs.animation_sampler_refs_ok
  step*
  simp_all [forallFrom_zero]

@[step]
theorem animation_refs_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.animations.val.length) :
    validate.refs.animation_refs_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.animations.val i.val (fun x => (∀ ch ∈ (x).channels.val, ch.sampler.val < (x).samplers.val.length ∧ optLt ch.node g.nodes.val.length) ∧ (∀ s ∈ (x).samplers.val, s.input.val < g.accessors.val.length ∧ s.output.val < g.accessors.val.length)) ⦄ := by
  unfold validate.refs.animation_refs_ok_loop
  loop_auto
termination_by g.animations.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem animation_refs_ok_spec (g : model.Gltf) :
    validate.refs.animation_refs_ok g ⦃ r => r = true ↔ animationRefsOk g ⦄ := by
  unfold validate.refs.animation_refs_ok animationRefsOk
  step*
  simp_all [forallFrom_zero]

-- MUST-014: すべての添字が範囲内
/-- refs_in_range(g) ⇔ refs_ok(g) -/
@[step]
theorem refs_in_range_spec (g : model.Gltf) : validate.refs.refs_in_range g ⦃ r => r = true ↔ refsOk g ⦄ := by
  unfold validate.refs.refs_in_range refsOk
  step*

end LoadGltf
