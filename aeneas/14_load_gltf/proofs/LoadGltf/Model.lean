import LoadGltf.Common

open Aeneas Aeneas.Std Result

namespace LoadGltf

@[step]
theorem bytes_eq_loop_spec (a b : Slice U8) (i : Usize) (hl : b.length = a.length) (hi : i.val ≤ a.length) :
    model.bytes_eq_loop a b i ⦃ r => r = true ↔ forallIdx a.val.length i.val (fun q => a.val[q]? = b.val[q]?) ⦄ := by
  unfold model.bytes_eq_loop
  step*
  · simp only [Bool.false_eq_true, false_iff]
    intro h
    have := h i.val (Nat.le_refl _) (by scalar_tac)
    simp only at this
    rw [List.getElem?_eq_getElem (by scalar_tac), List.getElem?_eq_getElem (by scalar_tac)] at this
    simp_all
  · rw [r_post, i4_post, forallIdx_step_slice (i := i) ‹_›,
      List.getElem?_eq_getElem (by scalar_tac : i.val < a.val.length),
      List.getElem?_eq_getElem (by scalar_tac : i.val < b.val.length)]
    simp_all [UScalar.eq_equiv]
  · simp [forallIdx_end_slice ‹_›]
termination_by a.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem bytes_eq_spec (a b : Slice U8) : model.bytes_eq a b ⦃ r => r = true ↔ a.val = b.val ⦄ := by
  unfold model.bytes_eq
  step*
  rw [r_post]
  · rw [forallIdx_zero, List.ext_getElem?_iff]
    constructor
    · intro h q
      by_cases hq : q < a.val.length
      · exact h q hq
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by scalar_tac)]
    · intro h q _; exact h q

theorem camera_consts : model.CAMERA_PERSPECTIVE = 1#u64 ∧ model.CAMERA_ORTHOGRAPHIC = 2#u64 := by
  unfold model.CAMERA_PERSPECTIVE model.CAMERA_ORTHOGRAPHIC; simp

deriving instance Inhabited for model.Accessor

deriving instance Inhabited for model.Material

deriving instance Inhabited for model.Mesh

deriving instance Inhabited for model.Attribute

deriving instance Inhabited for model.Node

deriving instance Inhabited for model.Skin

@[step]
theorem opt_eq_spec (a b : Option U64) : model.opt_eq a b ⦃ r => r = true ↔ a = b ⦄ := by
  unfold model.opt_eq
  rcases a with _ | x <;> rcases b with _ | y <;> step* <;> simp

deriving instance Inhabited for model.Channel

deriving instance Inhabited for model.AnimationSampler

theorem anim_consts : model.PATH_TRANSLATION = 1#u64 ∧ model.PATH_ROTATION = 2#u64 ∧ model.PATH_SCALE = 3#u64 ∧
    model.PATH_WEIGHTS = 4#u64 ∧ model.KIND_OTHER = 0#u64 ∧ model.INTERP_LINEAR = 0#u64 ∧ model.INTERP_STEP = 1#u64 ∧
    model.INTERP_CUBICSPLINE = 2#u64 := by
  unfold model.PATH_TRANSLATION model.PATH_ROTATION model.PATH_SCALE model.PATH_WEIGHTS model.KIND_OTHER model.INTERP_LINEAR model.INTERP_STEP
    model.INTERP_CUBICSPLINE
  simp

deriving instance Inhabited for model.BufferView

deriving instance Inhabited for model.Buffer

abbrev Bytes := List Nat

-- 文書中に現れた拡張名の列
abbrev Exts := List Bytes

/-! モデル (コードの型の Nat / List 版) -/

structure TextureInfoS where
  index : Nat
  tex_coord : Nat

structure MaterialS where
  base_color_texture : Option TextureInfoS
  metallic_roughness_texture : Option TextureInfoS
  normal_texture : Option TextureInfoS
  occlusion_texture : Option TextureInfoS
  emissive_texture : Option TextureInfoS

structure AttributeS where
  «name» : Bytes
  accessor : Nat

structure PrimitiveS where
  attributes : List AttributeS
  indices : Option Nat
  material : Option Nat
  mode : Nat
  targets : List (List AttributeS)

structure MeshS where
  primitives : List PrimitiveS
  weights_len : Option Nat

structure NodeS where
  children : List Nat
  mesh : Option Nat
  camera : Option Nat
  skin : Option Nat
  has_matrix : Bool
  has_trs : Bool
  weights_len : Option Nat

structure SceneS where
  nodes : List Nat

structure SparseS where
  count : Nat
  indices_buffer_view : Nat
  indices_byte_offset : Nat
  indices_component_type : Nat
  values_buffer_view : Nat
  values_byte_offset : Nat

structure AccessorS where
  buffer_view : Option Nat
  byte_offset : Option Nat
  component_type : Nat
  normalized : Bool
  count : Nat
  components : Nat
  is_matrix : Bool
  min_len : Option Nat
  max_len : Option Nat
  sparse : Option SparseS

structure BufferViewS where
  buffer : Nat
  byte_offset : Nat
  byte_length : Nat
  byte_stride : Option Nat
  target : Option Nat

structure BufferS where
  byte_length : Nat
  uri : Option Bytes

structure ImageS where
  uri : Option Bytes
  buffer_view : Option Nat
  has_mime_type : Bool

structure TextureS where
  sampler : Option Nat
  source : Option Nat

structure CameraS where
  kind : Nat
  has_perspective : Bool
  has_orthographic : Bool

structure SkinS where
  joints : List Nat
  skeleton : Option Nat
  inverse_bind_matrices : Option Nat

structure ChannelS where
  sampler : Nat
  node : Option Nat
  path : Nat

structure AnimationSamplerS where
  input : Nat
  output : Nat
  interpolation : Nat

structure AnimationS where
  channels : List ChannelS
  samplers : List AnimationSamplerS

structure GltfS where
  version_major : Nat
  version_minor : Nat
  min_version : Option (Nat × Nat)
  extensions_used : List Bytes
  extensions_required : List Bytes
  scene : Option Nat
  scenes : List SceneS
  nodes : List NodeS
  meshes : List MeshS
  accessors : List AccessorS
  buffer_views : List BufferViewS
  buffers : List BufferS
  materials : List MaterialS
  textures : List TextureS
  images : List ImageS
  samplers_len : Nat
  cameras : List CameraS
  skins : List SkinS
  animations : List AnimationS
  extensions_present : Exts
  is_glb : Bool
  glb_bin_len : Option Nat

/-! コードの値からモデルへ -/

def bs (v : alloc.vec.Vec U8) : Bytes := v.val.map (·.val)

def ov (o : Option U64) : Option Nat := o.map (·.val)

def model.TextureInfo.toS (t : model.TextureInfo) : TextureInfoS := ⟨t.index.val, t.tex_coord.val⟩

def model.Material.toS (m : model.Material) : MaterialS :=
  ⟨m.base_color_texture.map (·.toS), m.metallic_roughness_texture.map (·.toS), m.normal_texture.map (·.toS),
    m.occlusion_texture.map (·.toS), m.emissive_texture.map (·.toS)⟩

def model.Attribute.toS (a : model.Attribute) : AttributeS := ⟨bs a.«name», a.accessor.val⟩

def attrsS (v : alloc.vec.Vec model.Attribute) : List AttributeS := v.val.map (·.toS)

def model.Primitive.toS (p : model.Primitive) : PrimitiveS :=
  ⟨attrsS p.attributes, ov p.indices, ov p.material, p.mode.val, p.targets.val.map attrsS⟩

def model.Mesh.toS (m : model.Mesh) : MeshS := ⟨m.primitives.val.map (·.toS), ov m.weights_len⟩

def model.Node.toS (n : model.Node) : NodeS :=
  ⟨n.children.val.map (·.val), ov n.mesh, ov n.camera, ov n.skin, n.has_matrix, n.has_trs, ov n.weights_len⟩

def model.Scene.toS (s : model.Scene) : SceneS := ⟨s.nodes.val.map (·.val)⟩

def model.Sparse.toS (s : model.Sparse) : SparseS :=
  ⟨s.count.val, s.indices_buffer_view.val, s.indices_byte_offset.val, s.indices_component_type.val,
    s.values_buffer_view.val, s.values_byte_offset.val⟩

def model.Accessor.toS (a : model.Accessor) : AccessorS :=
  ⟨ov a.buffer_view, ov a.byte_offset, a.component_type.val, a.normalized, a.count.val, a.components.val,
    a.is_matrix, ov a.min_len, ov a.max_len, a.sparse.map (·.toS)⟩

def model.BufferView.toS (b : model.BufferView) : BufferViewS :=
  ⟨b.buffer.val, b.byte_offset.val, b.byte_length.val, ov b.byte_stride, ov b.target⟩

def model.Buffer.toS (b : model.Buffer) : BufferS := ⟨b.byte_length.val, b.uri.map bs⟩

def model.Image.toS (i : model.Image) : ImageS := ⟨i.uri.map bs, ov i.buffer_view, i.has_mime_type⟩

def model.Texture.toS (t : model.Texture) : TextureS := ⟨ov t.sampler, ov t.source⟩

def model.Camera.toS (c : model.Camera) : CameraS := ⟨c.kind.val, c.has_perspective, c.has_orthographic⟩

def model.Skin.toS (s : model.Skin) : SkinS := ⟨s.joints.val.map (·.val), ov s.skeleton, ov s.inverse_bind_matrices⟩

def model.Channel.toS (c : model.Channel) : ChannelS := ⟨c.sampler.val, ov c.node, c.path.val⟩

def model.AnimationSampler.toS (s : model.AnimationSampler) : AnimationSamplerS := ⟨s.input.val, s.output.val, s.interpolation.val⟩

def model.Animation.toS (a : model.Animation) : AnimationS := ⟨a.channels.val.map (·.toS), a.samplers.val.map (·.toS)⟩

def model.Gltf.toS (g : model.Gltf) : GltfS :=
  ⟨g.version_major.val, g.version_minor.val, g.min_version.map (fun p => (p.1.val, p.2.val)),
    g.extensions_used.val.map bs, g.extensions_required.val.map bs, ov g.scene, g.scenes.val.map (·.toS),
    g.nodes.val.map (·.toS), g.meshes.val.map (·.toS), g.accessors.val.map (·.toS),
    g.buffer_views.val.map (·.toS), g.buffers.val.map (·.toS), g.materials.val.map (·.toS),
    g.textures.val.map (·.toS), g.images.val.map (·.toS), g.samplers_len.val, g.cameras.val.map (·.toS),
    g.skins.val.map (·.toS), g.animations.val.map (·.toS), g.extensions_present.val.map bs, g.is_glb,
    ov g.glb_bin_len⟩

def kb (s : Slice U8) : Bytes := s.val.map (·.val)

@[simp] theorem kb_deref (v : alloc.vec.Vec U8) : kb v.deref = bs v := by simp [kb, bs]

@[simp] theorem kind_other_val : model.KIND_OTHER.val = 0 := by unfold model.KIND_OTHER; rfl

@[simp] theorem camera_perspective_val : model.CAMERA_PERSPECTIVE.val = 1 := by unfold model.CAMERA_PERSPECTIVE; rfl

@[simp] theorem camera_orthographic_val : model.CAMERA_ORTHOGRAPHIC.val = 2 := by unfold model.CAMERA_ORTHOGRAPHIC; rfl

@[simp] theorem path_translation_val : model.PATH_TRANSLATION.val = 1 := by unfold model.PATH_TRANSLATION; rfl

@[simp] theorem path_rotation_val : model.PATH_ROTATION.val = 2 := by unfold model.PATH_ROTATION; rfl

@[simp] theorem path_scale_val : model.PATH_SCALE.val = 3 := by unfold model.PATH_SCALE; rfl

@[simp] theorem path_weights_val : model.PATH_WEIGHTS.val = 4 := by unfold model.PATH_WEIGHTS; rfl

@[simp] theorem interp_linear_val : model.INTERP_LINEAR.val = 0 := by unfold model.INTERP_LINEAR; rfl

@[simp] theorem interp_step_val : model.INTERP_STEP.val = 1 := by unfold model.INTERP_STEP; rfl

@[simp] theorem interp_cubicspline_val : model.INTERP_CUBICSPLINE.val = 2 := by unfold model.INTERP_CUBICSPLINE; rfl

end LoadGltf
