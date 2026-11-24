import LoadGltf.Read.Objects

open Aeneas Aeneas.Std Result

namespace LoadGltf

-- 省略可能な配列プロパティ (無ければ空)
def listE {α} (ms : Members) (k : Bytes) (f : JsonS → Option (α × Exts)) : Option (List α × Exts) :=
  (opt ms k arrS).bind fun o => match o with
    | none => some ([], [])
    | some xs => allE f xs

-- MUST-002, MUST-009: asset.version は必須
def rAsset (ms : Members) : Option (((Nat × Nat) × Option (Nat × Nat)) × Exts) := do
  let e ← extsS ms
  let _ ← opt ms (key "copyright") strS
  let _ ← opt ms (key "generator") strS
  let ver ← (req ms (key "version") strS).bind versionS
  let mv ← (opt ms (key "minVersion") strS).bind fun o => match o with
    | none => some none
    | some s => (versionS s).map some
  pure ((ver, mv), e)

-- 各プロパティの読み取り結果からモデルを組み立てる
def mkGltf (asset : ((Nat × Nat) × Option (Nat × Nat)) × Exts) (used required : List Bytes) (scene : Option Nat)
    (scenes : List SceneS × Exts) (nodes : List NodeS × Exts) (meshes : List MeshS × Exts)
    (accessors : List AccessorS × Exts) (bvs : List BufferViewS × Exts) (buffers : List BufferS × Exts)
    (materials : List MaterialS × Exts) (textures : List TextureS × Exts) (images : List ImageS × Exts)
    (samplers : List Unit × Exts) (cameras : List CameraS × Exts) (skins : List SkinS × Exts)
    (anims : List AnimationS × Exts) (e0 : Exts) (glb : Bool) (bin : Option Nat) : GltfS :=
  ⟨asset.1.1.1, asset.1.1.2, asset.1.2, used, required, scene, scenes.1, nodes.1, meshes.1, accessors.1, bvs.1,
    buffers.1, materials.1, textures.1, images.1, samplers.1.length, cameras.1, skins.1, anims.1,
    e0 ++ asset.2 ++ scenes.2 ++ nodes.2 ++ meshes.2 ++ accessors.2 ++ bvs.2 ++ buffers.2 ++ materials.2 ++
      textures.2 ++ images.2 ++ samplers.2 ++ cameras.2 ++ skins.2 ++ anims.2, glb, bin⟩

-- ルート (u = false が read_spec)
-- MUST-008: asset は必須
def readG (u : Bool) (j : JsonS) (glb : Bool) (bin : Option Nat) : Option GltfS := do
  let ms ← objS j
  let e0 ← extsS ms
  let asset ← reqObjE ms (key "asset") rAsset
  let used ← listP ms (key "extensionsUsed") strS
  let required ← listP ms (key "extensionsRequired") strS
  let scene ← opt ms (key "scene") uintS
  let scenes ← listE ms (key "scenes") rScene
  let nodes ← listE ms (key "nodes") rNode
  let meshes ← listE ms (key "meshes") rMesh
  let accessors ← listE ms (key "accessors") (rAccessor u)
  let bvs ← listE ms (key "bufferViews") rBufferView
  let buffers ← listE ms (key "buffers") rBuffer
  let materials ← listE ms (key "materials") rMaterial
  let textures ← listE ms (key "textures") rTexture
  let images ← listE ms (key "images") rImage
  let samplers ← listE ms (key "samplers") rSampler
  let cameras ← listE ms (key "cameras") rCamera
  let skins ← listE ms (key "skins") rSkin
  let anims ← listE ms (key "animations") (rAnimation u)
  pure (mkGltf asset used required scene scenes nodes meshes accessors bvs buffers materials textures images
    samplers cameras skins anims e0 glb bin)

-- read_spec(j, is_glb, bin_len)
def readSpec (j : JsonS) (glb : Bool) (bin : Option Nat) : Option GltfS := readG false j glb bin

-- j は (U) 以外の規則に違反する: (U) の場合を受け入れても読めない
def violatesRule (j : JsonS) (glb : Bool) (bin : Option Nat) : Prop := readG true j glb bin = none

-- j は (U) の場合を含む
def hasU (j : JsonS) : Prop :=
  ∃ ms, j = .obj ms ∧
    ((∃ xs, lookup ms (key "accessors") = some (.arr xs) ∧ ∃ a ∈ xs, accU a) ∨
     (∃ xs, lookup ms (key "animations") = some (.arr xs) ∧ ∃ a ∈ xs, animU a))

/-! R1/R2 の事後条件 -/

-- R1: extensions_present 以外のフィールドが等しく、extensions_present は同じ拡張名を含む
def agrees (g : model.Gltf) (g' : GltfS) : Prop :=
  g.toS = { g' with extensions_present := g.toS.extensions_present } ∧
  ∀ x, x ∈ g.toS.extensions_present ↔ x ∈ g'.extensions_present

def ReadPost (j : JsonS) (glb : Bool) (bin : Option Nat) (r : core.result.Result model.Gltf model.GltfError) : Prop :=
  match r with
  | .Ok g => ∃ g', readSpec j glb bin = some g' ∧ agrees g g'
  | .Err .Unsupported => hasU j ∧ readSpec j glb bin = none
  | .Err .Invalid => violatesRule j glb bin ∧ readSpec j glb bin = none
  | .Err _ => False

/-! 文字列の配列とルートの配列プロパティ -/

@[step]
theorem strings_of_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize) (hw : nodesWf d.val) (hi : i.val ≤ a.val.length)
    (ho : out.val.length ≤ i.val) :
    read.strings_of_loop d a out i ⦃ r => (resO r).map (fun v => v.val.map bs) =
      (List.mapM strS ((elemsOf d a).drop i.val)).map (out.val.map bs ++ ·) ⦄ := by
  unfold read.strings_of_loop
  step*
  all_goals try (simp [vec_new_val]; done)
  elem_tac
  all_goals simp_all [List.mapM_cons, nodeS, strS, json.number.Number.toS, bs, Function.comp_def, vec_new_val]
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem read_string_array_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.read_string_array d o key ⦃ r => listP (msOf d o) (kb key) strS = (resO r).map (fun v => v.val.map bs) ⦄ := by
  unfold read.read_string_array read.strings_of
  step*
  all_goals subst_vars
  all_goals simp_all [listP, opt_arrOf, vec_new_val, usize_zero_val]

-- ルートの配列プロパティの後始末
set_option hygiene false in
macro "list_tac" : tactic => `(tactic| (
  all_goals subst_vars
  all_goals keys_norm
  all_goals try (have hz := szO_of_opt_arr r_post; rw [hz] at hb)
  all_goals try (obtain ⟨pr, pe⟩ := p; rcases pr with _ | ⟨_ | _ | _ | _⟩ <;> simp only at p_post ⊢)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Ok _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Err _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Ok _›)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Err _›)
  all_goals try (rcases e with _ | _ | _ | _ <;> simp only at *)
  norm_posts'
  all_goals clear_markers
  all_goals simp_each [usize_zero_val, List.drop_zero, vec_new_val, List.nil_append, List.map_nil]
  all_goals try omega
  all_goals simp [*, listE]
  all_goals try omega))

@[step]
theorem read_scenes_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Scene) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_scenes_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rScene ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Scene.toS = out.val.map model.Scene.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rScene ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_scenes_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_scenes_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "scenes")) ≤ Usize.max) :
    read.read_scenes d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "scenes") rScene = some (xs.val.map model.Scene.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "scenes"))
      | .Err .Invalid => listE (msOf d o) (key "scenes") rScene = none
      | .Err _ => False ⦄ := by
  unfold read.read_scenes read.read_scenes_items
  step_more
  list_tac

@[step]
theorem read_nodes_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Node) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_nodes_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rNode ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Node.toS = out.val.map model.Node.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rNode ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_nodes_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_nodes_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "nodes")) ≤ Usize.max) :
    read.read_nodes d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "nodes") rNode = some (xs.val.map model.Node.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "nodes"))
      | .Err .Invalid => listE (msOf d o) (key "nodes") rNode = none
      | .Err _ => False ⦄ := by
  unfold read.read_nodes read.read_nodes_items
  step_more
  list_tac

@[step]
theorem read_meshes_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Mesh) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_meshes_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rMesh ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Mesh.toS = out.val.map model.Mesh.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rMesh ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_meshes_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_meshes_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "meshes")) ≤ Usize.max) :
    read.read_meshes d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "meshes") rMesh = some (xs.val.map model.Mesh.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "meshes"))
      | .Err .Invalid => listE (msOf d o) (key "meshes") rMesh = none
      | .Err _ => False ⦄ := by
  unfold read.read_meshes read.read_meshes_items
  step_more
  list_tac

@[step]
theorem read_buffer_views_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.BufferView) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_buffer_views_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rBufferView ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.BufferView.toS = out.val.map model.BufferView.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rBufferView ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_buffer_views_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_buffer_views_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "bufferViews")) ≤ Usize.max) :
    read.read_buffer_views d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "bufferViews") rBufferView = some (xs.val.map model.BufferView.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "bufferViews"))
      | .Err .Invalid => listE (msOf d o) (key "bufferViews") rBufferView = none
      | .Err _ => False ⦄ := by
  unfold read.read_buffer_views read.read_buffer_views_items
  step_more
  list_tac

@[step]
theorem read_buffers_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Buffer) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_buffers_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rBuffer ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Buffer.toS = out.val.map model.Buffer.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rBuffer ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_buffers_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_buffers_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "buffers")) ≤ Usize.max) :
    read.read_buffers d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "buffers") rBuffer = some (xs.val.map model.Buffer.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "buffers"))
      | .Err .Invalid => listE (msOf d o) (key "buffers") rBuffer = none
      | .Err _ => False ⦄ := by
  unfold read.read_buffers read.read_buffers_items
  step_more
  list_tac

@[step]
theorem read_materials_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Material) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_materials_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rMaterial ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Material.toS = out.val.map model.Material.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rMaterial ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_materials_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_materials_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "materials")) ≤ Usize.max) :
    read.read_materials d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "materials") rMaterial = some (xs.val.map model.Material.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "materials"))
      | .Err .Invalid => listE (msOf d o) (key "materials") rMaterial = none
      | .Err _ => False ⦄ := by
  unfold read.read_materials read.read_materials_items
  step_more
  list_tac

@[step]
theorem read_textures_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Texture) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_textures_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rTexture ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Texture.toS = out.val.map model.Texture.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rTexture ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_textures_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_textures_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "textures")) ≤ Usize.max) :
    read.read_textures d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "textures") rTexture = some (xs.val.map model.Texture.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "textures"))
      | .Err .Invalid => listE (msOf d o) (key "textures") rTexture = none
      | .Err _ => False ⦄ := by
  unfold read.read_textures read.read_textures_items
  step_more
  list_tac

@[step]
theorem read_images_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Image) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_images_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rImage ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Image.toS = out.val.map model.Image.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rImage ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_images_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_images_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "images")) ≤ Usize.max) :
    read.read_images d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "images") rImage = some (xs.val.map model.Image.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "images"))
      | .Err .Invalid => listE (msOf d o) (key "images") rImage = none
      | .Err _ => False ⦄ := by
  unfold read.read_images read.read_images_items
  step_more
  list_tac

@[step]
theorem read_cameras_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Camera) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_cameras_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rCamera ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Camera.toS = out.val.map model.Camera.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rCamera ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_cameras_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_cameras_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "cameras")) ≤ Usize.max) :
    read.read_cameras d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "cameras") rCamera = some (xs.val.map model.Camera.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "cameras"))
      | .Err .Invalid => listE (msOf d o) (key "cameras") rCamera = none
      | .Err _ => False ⦄ := by
  unfold read.read_cameras read.read_cameras_items
  step_more
  list_tac

@[step]
theorem read_skins_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Skin) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_skins_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rSkin ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Skin.toS = out.val.map model.Skin.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rSkin ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.read_skins_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_skins_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "skins")) ≤ Usize.max) :
    read.read_skins d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, listE (msOf d o) (key "skins") rSkin = some (xs.val.map model.Skin.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "skins"))
      | .Err .Invalid => listE (msOf d o) (key "skins") rSkin = none
      | .Err _ => False ⦄ := by
  unfold read.read_skins read.read_skins_items
  step_more
  list_tac

@[step]
theorem read_accessors_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Accessor) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_accessors_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, (∀ u, allE (rAccessor u) ((elemsOf d a).drop i.val) = some (ys, e)) ∧
          xs.val.map model.Accessor.toS = out.val.map model.Accessor.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => ∀ u, allE (rAccessor u) ((elemsOf d a).drop i.val) = none
      | .Err .Unsupported => allE (rAccessor false) ((elemsOf d a).drop i.val) = none ∧
          ∃ s ∈ (elemsOf d a).drop i.val, accU s
      | .Err _ => False ⦄ := by
  unfold read.read_accessors_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_accessors_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "accessors")) ≤ Usize.max) :
    read.read_accessors d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, (∀ u, listE (msOf d o) (key "accessors") (rAccessor u) = some (xs.val.map model.Accessor.toS, e)) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "accessors"))
      | .Err .Invalid => ∀ u, listE (msOf d o) (key "accessors") (rAccessor u) = none
      | .Err .Unsupported => listE (msOf d o) (key "accessors") (rAccessor false) = none ∧
          ∃ xs, lookup (msOf d o) (key "accessors") = some (.arr xs) ∧ ∃ s ∈ xs, accU s
      | .Err _ => False ⦄ := by
  unfold read.read_accessors read.read_accessors_items
  step_more
  list_tac
  all_goals exact ⟨_, opt_arr_some r_post, _, ‹_ ∈ _›, ‹accU _›⟩

@[step]
theorem read_animations_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Animation) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.read_animations_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, (∀ u, allE (rAnimation u) ((elemsOf d a).drop i.val) = some (ys, e)) ∧
          xs.val.map model.Animation.toS = out.val.map model.Animation.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => ∀ u, allE (rAnimation u) ((elemsOf d a).drop i.val) = none
      | .Err .Unsupported => allE (rAnimation false) ((elemsOf d a).drop i.val) = none ∧
          ∃ s ∈ (elemsOf d a).drop i.val, animU s
      | .Err _ => False ⦄ := by
  unfold read.read_animations_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_animations_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "animations")) ≤ Usize.max) :
    read.read_animations d o ext ⦃ p => match p.1 with
      | .Ok xs => ∃ e, (∀ u, listE (msOf d o) (key "animations") (rAnimation u) = some (xs.val.map model.Animation.toS, e)) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "animations"))
      | .Err .Invalid => ∀ u, listE (msOf d o) (key "animations") (rAnimation u) = none
      | .Err .Unsupported => listE (msOf d o) (key "animations") (rAnimation false) = none ∧
          ∃ xs, lookup (msOf d o) (key "animations") = some (.arr xs) ∧ ∃ s ∈ xs, animU s
      | .Err _ => False ⦄ := by
  unfold read.read_animations read.read_animations_items
  step_more
  list_tac
  all_goals exact ⟨_, opt_arr_some r_post, _, ‹_ ∈ _›, ‹animU _›⟩

theorem allE_length {α} (f : JsonS → Option (α × Exts)) :
    ∀ (l : List JsonS) (ys : List α) (e : Exts), allE f l = some (ys, e) → ys.length = l.length
  | [], ys, e, h => by simp [allE] at h; simp [← h.1]
  | v :: vs, ys, e, h => by
    simp only [allE, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨x, e1⟩, _, ⟨xs, e2⟩, h2, h3⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h3
    rw [← h3.1]; simp [allE_length f vs xs e2 h2]

@[step]
theorem check_sampler_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.check_sampler_items_loop d a ext i ⦃ p => match p.1 with
      | .Ok _ => ∃ e ys, allE rSampler ((elemsOf d a).drop i.val) = some (ys, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => allE rSampler ((elemsOf d a).drop i.val) = none
      | .Err _ => False ⦄ := by
  unfold read.check_sampler_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_samplers_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "samplers")) ≤ Usize.max) :
    read.read_samplers d o ext ⦃ p => match p.1 with
      | .Ok n => ∃ e ys, listE (msOf d o) (key "samplers") rSampler = some (ys, e) ∧ n.val = ys.length ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "samplers"))
      | .Err .Invalid => listE (msOf d o) (key "samplers") rSampler = none
      | .Err _ => False ⦄ := by
  unfold read.read_samplers read.check_sampler_items
  step_more
  list_tac
  all_goals (have hlen := allE_length _ _ _ _ ‹allE rSampler _ = some _›
             simp [elemsOf] at hlen; constructor <;> omega)

-- do 記法の bind を Option.bind に直さずに簡約する (Option.bind_congr' による指数的な simp を避ける)
theorem obind_some {α β} (a : α) (f : α → Option β) : (bind (some a) f : Option β) = f a := rfl

theorem obind_none {α β} (f : α → Option β) : (bind none f : Option β) = none := rfl

theorem opure {α} (a : α) : (pure a : Option α) = some a := rfl

theorem obind_assoc {α β γ} (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (bind (bind x f) g : Option γ) = bind x (fun a => bind (f a) g) := by cases x <;> rfl

theorem ojoin_some {α} (a : Option α) : (some a).join = a := rfl

theorem ojoin_none {α} : (none : Option (Option α)).join = none := rfl

theorem bind'_some {α β} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

theorem bind'_none {α β} (f : α → Option β) : (none : Option α).bind f = none := rfl

/-! read_gltf -/

@[simp] theorem bss_new : bss (alloc.vec.Vec.new (alloc.vec.Vec U8)) = [] := rfl

theorem map_bs_eq_bss (v : alloc.vec.Vec (alloc.vec.Vec U8)) : v.val.map bs = bss v := rfl

-- 仕様の読み取りとの完全な対応 (extensions_present も同じ順序で一致)
def ReadCore (j : JsonS) (glb : Bool) (bin : Option Nat) (r : core.result.Result model.Gltf model.GltfError) : Prop :=
  match r with
  | .Ok g => ∀ u, readG u j glb bin = some g.toS
  | .Err .Invalid => ∀ u, readG u j glb bin = none
  | .Err .Unsupported => readG false j glb bin = none ∧ hasU j
  | .Err _ => False

set_option maxHeartbeats 40000000 in
theorem read_gltf_core (doc : json.JsonDoc) (glb : Bool) (bin : Option U64) (hw : nodesWf doc.nodes.val)
    (hb : jsonSize (jt doc.nodes doc.root) ≤ Usize.max) :
    read.read_gltf doc glb bin ⦃ r => match r with
      | .Ok g => ∀ u, readG u (jt doc.nodes doc.root) glb (ov bin) = some g.toS
      | .Err .Invalid => ∀ u, readG u (jt doc.nodes doc.root) glb (ov bin) = none
      | .Err .Unsupported => readG false (jt doc.nodes doc.root) glb (ov bin) = none ∧ hasU (jt doc.nodes doc.root)
      | .Err _ => False ⦄ := by
  obtain ⟨nodes, root⟩ := doc
  simp only at hw hb ⊢
  unfold read.read_gltf
  step_more
  all_goals try (rcases p with ⟨p1, p2⟩; step_more)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Ok _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Err _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Ok _›)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Err _›)
  all_goals try (rcases e with _ | _ | _ | _ <;> simp only at *)
  all_goals subst_vars
  all_goals keys_norm
  all_goals try (have hz := szO_of_opt_obj r2_post; have hs2 := szO_le (msOf nodes a) (key "extensions"))
  norm_posts'
  all_goals try (sum_of (msOf nodes o), [key "extensions", key "asset", key "scenes", key "nodes", key "meshes",
    key "accessors", key "bufferViews", key "buffers", key "materials", key "textures", key "images",
    key "samplers", key "cameras", key "skins", key "animations"])
  all_goals clear_markers
  all_goals try rw [r_post] at hb
  all_goals try simp only [jsonSize] at hb
  all_goals try rw [hz] at hsum
  all_goals simp_each [vec_new_val, List.length_nil]
  all_goals try omega
  all_goals simp_each [jt, usize_zero_val, List.drop_zero, vec_new_val, List.nil_append]
  all_goals try intro u
  all_goals simp only [*, readG, reqObjE, rAsset, req_opt, objS_obj, obind_some, obind_none, opure, ojoin_some,
    ojoin_none, bind'_some, bind'_none, true_and, obind_assoc, Option.map_some, Option.map_none]
  all_goals try (simp only [Option.some.injEq]; simp [mkGltf, model.Gltf.toS, map_bs_eq_bss, *, List.append_assoc]; done)
  all_goals try (exact ⟨_, rfl, Or.inl ⟨_, ‹lookup _ (key "accessors") = _›, _, ‹_ ∈ _›, ‹accU _›⟩⟩)
  all_goals exact ⟨_, rfl, Or.inr ⟨_, ‹lookup _ (key "animations") = _›, _, ‹_ ∈ _›, ‹animU _›⟩⟩

/-! ## R1/R2: read_gltf -/

theorem gltfS_with_ext (g : GltfS) : { g with extensions_present := g.extensions_present } = g := by
  cases g; rfl

-- MUST-002, MUST-008, MUST-009: asset と asset.version は必須
/-- R1/R2: read_gltf(j, is_glb, bin) は read_spec と一致する (extensions_present は集合として)。
Err Unsupported は (U) の場合を含むとき、Err Invalid は (U) 以外の規則に違反するときだけ。Glb/Json は返さない -/
@[step]
theorem read_gltf_spec (doc : json.JsonDoc) (glb : Bool) (bin : Option U64) (hw : docWf doc)
    (hs : jsonSize (tree doc doc.root.val) ≤ Usize.max) :
    read.read_gltf doc glb bin ⦃ r => ReadPost (tree doc doc.root.val) glb (bin.map (·.val)) r ⦄ := by
  apply WP.spec_mono (read_gltf_core doc glb bin hw.2 hs)
  intro r h
  have hj : jt doc.nodes doc.root = tree doc doc.root.val := rfl
  rw [hj] at h
  simp only [ov] at h
  unfold ReadPost readSpec violatesRule
  rcases r with g | (_ | _ | _ | _)
  · exact ⟨g.toS, h false, (gltfS_with_ext _).symm, fun _ => Iff.rfl⟩
  · exact h.elim
  · exact h.elim
  · exact ⟨h true, h false⟩
  · exact ⟨h.2, h.1⟩

end LoadGltf
