import LoadGltf.Read.Access

open Aeneas Aeneas.Std Result

namespace LoadGltf

-- 既定値つきプロパティ
def dflt {α} (ms : List (Bytes × JsonS)) (k : Bytes) (f : JsonS → Option α) (x : α) : Option α :=
  (opt ms k f).map (·.getD x)

-- 配列プロパティ (無ければ空)
def listP {α} (ms : List (Bytes × JsonS)) (k : Bytes) (f : JsonS → Option α) : Option (List α) :=
  (opt ms k (arrOf f)).map (·.getD [])

def allE {α} (f : JsonS → Option (α × Exts)) : List JsonS → Option (List α × Exts)
  | [] => some ([], [])
  | v :: vs => do
    let (x, e1) ← f v
    let (xs, e2) ← allE f vs
    pure (x :: xs, e1 ++ e2)

-- 省略可能なプロパティ (値の読み手 f)
def optE {α} (ms : Members) (k : Bytes) (f : JsonS → Option (α × Exts)) : Option (Option α × Exts) :=
  match lookup ms k with
  | none => some (none, [])
  | some v => (f v).map fun p => (some p.1, p.2)

-- 省略可能なオブジェクトのプロパティ (メンバー列の読み手 f)
def optObjE {α} (ms : Members) (k : Bytes) (f : Members → Option (α × Exts)) : Option (Option α × Exts) :=
  (opt ms k objS).bind fun o => match o with
    | none => some (none, [])
    | some m => (f m).map fun p => (some p.1, p.2)

-- 必須のオブジェクトのプロパティ
def reqObjE {α} (ms : Members) (k : Bytes) (f : Members → Option (α × Exts)) : Option (α × Exts) :=
  (req ms k objS).bind f

-- 必須の配列プロパティ (各要素を f で読む)
def reqArrE {α} (ms : Members) (k : Bytes) (f : JsonS → Option (α × Exts)) : Option (List α × Exts) :=
  (req ms k arrS).bind (allE f)

/-! オブジェクトごとの規則 (R 節の表) -/

-- textureInfo: index (uint, 必須), texCoord (uint, 既定 0)。extra のキーは number
def rTexInfo (extra : List Bytes) (v : JsonS) : Option (TextureInfoS × Exts) := do
  let ms ← objS v
  let e ← extsS ms
  let index ← req ms (key "index") uintS
  let tc ← dflt ms (key "texCoord") uintS 0
  let _ ← extra.mapM fun k => opt ms k numS
  pure (⟨index, tc⟩, e)

def rPbr (ms : Members) : Option ((Option TextureInfoS × Option TextureInfoS) × Exts) := do
  let e ← extsS ms
  let _ ← opt ms (key "baseColorFactor") (numArrN 4)
  let _ ← opt ms (key "metallicFactor") numS
  let _ ← opt ms (key "roughnessFactor") numS
  let (bc, e1) ← optE ms (key "baseColorTexture") (rTexInfo [])
  let (mr, e2) ← optE ms (key "metallicRoughnessTexture") (rTexInfo [])
  pure ((bc, mr), e ++ e1 ++ e2)

def rMaterial (v : JsonS) : Option (MaterialS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let (pbr, e1) ← optObjE ms (key "pbrMetallicRoughness") rPbr
  let (nt, e2) ← optE ms (key "normalTexture") (rTexInfo [key "scale"])
  let (ot, e3) ← optE ms (key "occlusionTexture") (rTexInfo [key "strength"])
  let (et, e4) ← optE ms (key "emissiveTexture") (rTexInfo [])
  let _ ← opt ms (key "emissiveFactor") (numArrN 3)
  let _ ← opt ms (key "alphaMode") strS
  let _ ← opt ms (key "alphaCutoff") numS
  let _ ← opt ms (key "doubleSided") boolS
  pure (⟨(pbr.map (·.1)).join, (pbr.map (·.2)).join, nt, ot, et⟩, e ++ e1 ++ e2 ++ e3 ++ e4)

def attrOf (m : Bytes × JsonS) : Option AttributeS := (uintS m.2).map fun a => ⟨m.1, a⟩

-- attributes / targets の 1 つ: オブジェクトで、上書きされないメンバーの値はすべて uint
-- MUST-058, MUST-082: attributes と targets の要素は名前 → アクセサーの平らな対応
def attrMap (allowEmpty : Bool) (v : JsonS) : Option (List AttributeS) := do
  let ms ← objS v
  if ms = [] ∧ allowEmpty = false then none
  else (lastOnes ms).mapM attrOf

def rPrimitive (v : JsonS) : Option (PrimitiveS × Exts) := do
  let ms ← objS v
  let e ← extsS ms
  let attrs ← req ms (key "attributes") (attrMap false)
  let indices ← opt ms (key "indices") uintS
  let material ← opt ms (key "material") uintS
  let mode ← dflt ms (key "mode") uintS 4
  let targets ← listP ms (key "targets") (attrMap true)
  pure (⟨attrs, indices, material, mode, targets⟩, e)

def rMesh (v : JsonS) : Option (MeshS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let (prims, e1) ← reqArrE ms (key "primitives") rPrimitive
  let w ← opt ms (key "weights") numArr
  pure (⟨prims, w⟩, e ++ e1)

def rNode (v : JsonS) : Option (NodeS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let children ← listP ms (key "children") uintS
  let mesh ← opt ms (key "mesh") uintS
  let camera ← opt ms (key "camera") uintS
  let skin ← opt ms (key "skin") uintS
  let m ← opt ms (key "matrix") (numArrN 16)
  let t ← opt ms (key "translation") (numArrN 3)
  let r ← opt ms (key "rotation") (numArrN 4)
  let s ← opt ms (key "scale") (numArrN 3)
  let w ← opt ms (key "weights") numArr
  pure (⟨children, mesh, camera, skin, m.isSome, t.isSome || r.isSome || s.isSome, w⟩, e)

def rScene (v : JsonS) : Option (SceneS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let nodes ← listP ms (key "nodes") uintS
  pure (⟨nodes⟩, e)

-- accessor.type → (成分数, 行列か)
def typeComponents (t : Bytes) : Option (Nat × Bool) :=
  if t = key "SCALAR" then some (1, false)
  else if t = key "VEC2" then some (2, false)
  else if t = key "VEC3" then some (3, false)
  else if t = key "VEC4" then some (4, false)
  else if t = key "MAT2" then some (4, true)
  else if t = key "MAT3" then some (9, true)
  else if t = key "MAT4" then some (16, true)
  else none

-- u = true は (U) の場合を受け入れる読み方 (規則違反の判定用)
def accType (u : Bool) (t : Bytes) : Option (Nat × Bool) :=
  match typeComponents t with
  | some c => some c
  | none => if u then some (0, false) else none

def rSparseIdx (ms : Members) : Option ((Nat × Nat × Nat) × Exts) := do
  let e ← extsS ms
  let bv ← req ms (key "bufferView") uintS
  let bo ← dflt ms (key "byteOffset") uintS 0
  let ct ← req ms (key "componentType") uintS
  pure ((bv, bo, ct), e)

def rSparseVal (ms : Members) : Option ((Nat × Nat) × Exts) := do
  let e ← extsS ms
  let bv ← req ms (key "bufferView") uintS
  let bo ← dflt ms (key "byteOffset") uintS 0
  pure ((bv, bo), e)

-- MUST-043: sparse の count / indices / values は必須
def rSparse (v : JsonS) : Option (SparseS × Exts) := do
  let ms ← objS v
  let e ← extsS ms
  let count ← req ms (key "count") uintS
  let ((ib, io, ict), e1) ← reqObjE ms (key "indices") rSparseIdx
  let ((vb, vo), e2) ← reqObjE ms (key "values") rSparseVal
  pure (⟨count, ib, io, ict, vb, vo⟩, e ++ e1 ++ e2)

def rAccessor (u : Bool) (v : JsonS) : Option (AccessorS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let bv ← opt ms (key "bufferView") uintS
  let bo ← opt ms (key "byteOffset") uintS
  let ct ← req ms (key "componentType") uintS
  let nz ← dflt ms (key "normalized") boolS false
  let count ← req ms (key "count") uintS
  let (comps, isM) ← (req ms (key "type") strS).bind (accType u)
  let mn ← opt ms (key "min") numArr
  let mx ← opt ms (key "max") numArr
  let (sp, e1) ← optE ms (key "sparse") rSparse
  pure (⟨bv, bo, ct, nz, count, comps, isM, mn, mx, sp⟩, e ++ e1)

def rBufferView (v : JsonS) : Option (BufferViewS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let b ← req ms (key "buffer") uintS
  let bo ← dflt ms (key "byteOffset") uintS 0
  let bl ← req ms (key "byteLength") uintS
  let st ← opt ms (key "byteStride") uintS
  let tg ← opt ms (key "target") uintS
  pure (⟨b, bo, bl, st, tg⟩, e)

def rBuffer (v : JsonS) : Option (BufferS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let bl ← req ms (key "byteLength") uintS
  let uri ← opt ms (key "uri") strS
  pure (⟨bl, uri⟩, e)

def rImage (v : JsonS) : Option (ImageS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let uri ← opt ms (key "uri") strS
  let bv ← opt ms (key "bufferView") uintS
  let mt ← opt ms (key "mimeType") strS
  pure (⟨uri, bv, mt.isSome⟩, e)

def rTexture (v : JsonS) : Option (TextureS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let s ← opt ms (key "sampler") uintS
  let src ← opt ms (key "source") uintS
  pure (⟨s, src⟩, e)

def rSampler (v : JsonS) : Option (Unit × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let _ ← opt ms (key "magFilter") uintS
  let _ ← opt ms (key "minFilter") uintS
  let _ ← opt ms (key "wrapS") uintS
  let _ ← opt ms (key "wrapT") uintS
  pure ((), e)

def rPerspective (ms : Members) : Option (Unit × Exts) := do
  let e ← extsS ms
  let _ ← opt ms (key "aspectRatio") numS
  let _ ← req ms (key "yfov") numS
  let _ ← opt ms (key "zfar") numS
  let _ ← req ms (key "znear") numS
  pure ((), e)

def rOrthographic (ms : Members) : Option (Unit × Exts) := do
  let e ← extsS ms
  let _ ← req ms (key "xmag") numS
  let _ ← req ms (key "ymag") numS
  let _ ← req ms (key "zfar") numS
  let _ ← req ms (key "znear") numS
  pure ((), e)

-- camera.type: perspective = 1, orthographic = 2, それ以外 (独自の型) = 0
def cameraKind (t : Bytes) : Nat :=
  if t = key "perspective" then 1 else if t = key "orthographic" then 2 else 0

-- MUST-132: camera.type は必須
def rCamera (v : JsonS) : Option (CameraS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let t ← req ms (key "type") strS
  let (p, e1) ← optObjE ms (key "perspective") rPerspective
  let (o, e2) ← optObjE ms (key "orthographic") rOrthographic
  pure (⟨cameraKind t, p.isSome, o.isSome⟩, e ++ e1 ++ e2)

-- MUST-095: skin.joints は必須
def rSkin (v : JsonS) : Option (SkinS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let joints ← req ms (key "joints") (arrOf uintS)
  let sk ← opt ms (key "skeleton") uintS
  let ibm ← opt ms (key "inverseBindMatrices") uintS
  pure (⟨joints, sk, ibm⟩, e)

-- target.path: translation = 1, rotation = 2, scale = 3, weights = 4, それ以外 (独自) = 0
def pathCode (p : Bytes) : Nat :=
  if p = key "translation" then 1 else if p = key "rotation" then 2
  else if p = key "scale" then 3 else if p = key "weights" then 4 else 0

def rTarget (ms : Members) : Option ((Option Nat × Nat) × Exts) := do
  let e ← extsS ms
  let node ← opt ms (key "node") uintS
  let p ← req ms (key "path") strS
  pure ((node, pathCode p), e)

def rChannel (v : JsonS) : Option (ChannelS × Exts) := do
  let ms ← objS v
  let e ← extsS ms
  let s ← req ms (key "sampler") uintS
  let ((node, path), e1) ← reqObjE ms (key "target") rTarget
  pure (⟨s, node, path⟩, e ++ e1)

-- interpolation: LINEAR = 0, STEP = 1, CUBICSPLINE = 2, それ以外は (U)
def interpCode (s : Bytes) : Option Nat :=
  if s = key "LINEAR" then some 0 else if s = key "STEP" then some 1
  else if s = key "CUBICSPLINE" then some 2 else none

def interpS (u : Bool) (s : Bytes) : Option Nat :=
  match interpCode s with
  | some c => some c
  | none => if u then some 0 else none

def rAnimSampler (u : Bool) (v : JsonS) : Option (AnimationSamplerS × Exts) := do
  let ms ← objS v
  let e ← extsS ms
  let i ← req ms (key "input") uintS
  let o ← req ms (key "output") uintS
  let ip ← (opt ms (key "interpolation") strS).bind fun o => match o with
    | none => some 0
    | some s => interpS u s
  pure (⟨i, o, ip⟩, e)

def rAnimation (u : Bool) (v : JsonS) : Option (AnimationS × Exts) := do
  let ms ← objS v
  let e ← childS ms
  let (chs, e1) ← reqArrE ms (key "channels") rChannel
  let (sps, e2) ← reqArrE ms (key "samplers") (rAnimSampler u)
  pure (⟨chs, sps⟩, e ++ e1 ++ e2)

-- バージョンの片側: 0 | [1-9][0-9]{0,8}
def verPart (p : Bytes) : Option Nat :=
  if p ≠ [] ∧ p.length ≤ 9 ∧ (∀ c ∈ p, isDigit c = true) ∧ (1 < p.length → p.head? ≠ some 0x30) then
    some (digitsVal (p.map (· - 0x30)))
  else none

-- ^(0|[1-9][0-9]{0,8})\.(0|[1-9][0-9]{0,8})$
-- MUST-010: version / minVersion は <major>.<minor> の形
def versionS (s : Bytes) : Option (Nat × Nat) :=
  if 0x2E ∈ s then do
    let a ← verPart (s.take (s.idxOf 0x2E))
    let b ← verPart (s.drop (s.idxOf 0x2E + 1))
    pure (a, b)
  else none

/-! (U) の場合: 未知の accessor.type、未知の animation sampler interpolation -/

def accU (v : JsonS) : Prop :=
  ∃ ms t, v = .obj ms ∧ lookup ms (key "type") = some (.str t) ∧ typeComponents t = none

def sampU (v : JsonS) : Prop :=
  ∃ ms s, v = .obj ms ∧ lookup ms (key "interpolation") = some (.str s) ∧ interpCode s = none

def animU (v : JsonS) : Prop :=
  ∃ ms xs, v = .obj ms ∧ lookup ms (key "samplers") = some (.arr xs) ∧ ∃ s ∈ xs, sampU s

-- step* の注釈 [> let x ← f <] を消す
open Lean Elab Tactic Meta in
elab "clear_markers" : tactic => do
  let goal ← getMainGoal
  let mut g := goal
  for d in (← goal.getDecl).lctx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type).getAppFn.isConstOf ``Aeneas.Step.prettyMonadEq then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

@[simp] theorem resO_ok {α ε} (x : α) : resO (.Ok x : core.result.Result α ε) = some x := rfl

@[simp] theorem resO_err {α ε} (e : ε) : resO (.Err e : core.result.Result α ε) = none := rfl

-- step* が束縛中の if / match で止まったときに続ける
macro "step_more" : tactic => `(tactic| (
  step*
  iterate 4 (all_goals try (split <;> step*))))

/-! 予算: 異なるキーの値の大きさの和はメンバーの値の大きさの和以下 -/

theorem lookup_concat (ms : Members) (m : Bytes × JsonS) (k : Bytes) :
    lookup (ms ++ [m]) k = if m.1 = k then some m.2 else lookup ms k := by
  simp only [lookup, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.find?_cons, beq_iff_eq]
  split <;> simp_all

theorem memSize_concat (ms : Members) (m : Bytes × JsonS) : memSize (ms ++ [m]) = memSize ms + jsonSize m.2 := by
  induction ms with
  | nil => simp [memSize]
  | cons x xs ih => simp [memSize, ih]; omega

theorem sum_upd (ks : List Bytes) (hks : ks.Nodup) (a : Bytes) (c : Nat) (f : Bytes → Nat) :
    (ks.map fun k => if a = k then c else f k).sum ≤ (ks.map f).sum + c := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [List.nodup_cons] at hks
    simp only [List.map_cons, List.sum_cons]
    by_cases h : a = k
    · subst h
      have : (ks.map fun k => if a = k then c else f k) = ks.map f := by
        apply List.map_congr_left; intro x hx
        have : a ≠ x := fun e => hks.1 (by rw [e]; exact hx)
        rw [if_neg this]
      rw [if_pos rfl, this]; omega
    · rw [if_neg h]; have := ih hks.2; omega

theorem sum_lookup_le (ms : Members) (ks : List Bytes) (hks : ks.Nodup) :
    (ks.map fun k => szO (lookup ms k)).sum ≤ memSize ms := by
  induction ms using List.reverseRecOn with
  | nil => simp [lookup, szO, memSize]
  | append_singleton ms m ih =>
    rw [memSize_concat]
    have : (ks.map fun k => szO (lookup (ms ++ [m]) k)) =
        ks.map fun k => if m.1 = k then jsonSize m.2 else szO (lookup ms k) := by
      apply List.map_congr_left; intro k _; rw [lookup_concat]; split <;> rfl
    rw [this]
    have := sum_upd ks hks m.1 (jsonSize m.2) (fun k => szO (lookup ms k))
    omega

theorem objS_some {v : JsonS} {ms : Members} (h : objS v = some ms) : v = .obj ms := by
  cases v <;> simp_all [objS]

def extraKeys (extra : U64) : List Bytes :=
  if extra = 1#u64 then [key "scale"] else if extra = 2#u64 then [key "strength"] else []

theorem objS_eq_some_iff {v : JsonS} {ms : Members} : objS v = some ms ↔ v = .obj ms := by
  cases v <;> simp [objS]

-- 事後条件を整理する
macro "norm_posts" : tactic => `(tactic| (
  all_goals try simp only [resO, Option.map_some, Option.map_none, objS_eq_some_iff] at *
  all_goals try (casesm* (∃ _, _), (_ ∧ _))))

@[step]
theorem read_texture_info_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize) (extra : U64)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_texture_info d id extra ext ⦃ p => match p.1 with
      | .Ok t => ∃ e, rTexInfo (extraKeys extra) (jt d id) = some (t.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rTexInfo (extraKeys extra) (jt d id) = none ⦄ := by
  unfold read.objects.read_texture_info
  step_more
  all_goals subst_vars
  all_goals keys_norm
  norm_posts
  all_goals try (have hsum := sum_lookup_le (msOf d o) [key "extensions"] (by decide)
                 simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum)
  all_goals try omega
  all_goals simp_all [rTexInfo, extraKeys, jsonSize, model.TextureInfo.toS, dflt, objS, ov]
  all_goals omega

/-! 各オブジェクトの読み取り -/

macro "norm_posts'" : tactic => `(tactic| (
  all_goals simp_each [resO_ok, resO_err, Option.map_some, Option.map_none, objS_eq_some_iff]
  all_goals try (casesm* (∃ _, _), (_ ∧ _))))

set_option hygiene false in
macro "sum_of" ms:term "," ks:term : tactic => `(tactic| (
  have hsum := sum_lookup_le $ms $ks (by decide)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum))

set_option hygiene false in
macro "reader_prep" "(" ks:term ")" : tactic => `(tactic| (
  all_goals subst_vars
  all_goals keys_norm
  norm_posts'
  all_goals try (sum_of (msOf d o), $ks)
  all_goals clear_markers
  all_goals try rw [r_post] at hb
  all_goals try simp only [jsonSize] at hb))

set_option hygiene false in
macro "reader_fin" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  all_goals try omega
  all_goals simp_each [jt, usize_zero_val, List.drop_zero, vec_new_val, List.nil_append]
  all_goals simp (config := {decide := true}) [*, objS_obj, ov, jsonSize, dflt, isSome_ite_bool, $ls,*]
  all_goals try omega))

set_option hygiene false in
macro "reader_close" "(" ks:term ")" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  reader_prep ($ks)
  reader_fin [$ls,*]))

theorem opt_arr_some {ms : Members} {k : Bytes} {xs : List JsonS} (h : opt ms k arrS = some (some xs)) :
    lookup ms k = some (.arr xs) := by
  unfold opt at h
  split at h
  · cases h
  · rename_i v hv
    rw [hv]
    cases v <;> simp_all [arrS]
    rename_i l; cases l <;> simp_all

@[simp] theorem isSome_ite_bool (b : Bool) : (if b = true then some () else none).isSome = b := by
  cases b <;> rfl

@[simp] theorem objS_obj (ms : Members) : objS (.obj ms) = some ms := rfl

theorem usize_zero_val : (0#usize : Usize).val = 0 := rfl

theorem szO_of_opt_obj {ms : Members} {k : Bytes} {m : Members} (h : opt ms k objS = some (some m)) :
    szO (lookup ms k) = 1 + memSize m := by
  rw [opt_obj_some h]; rfl

theorem szO_of_opt_arr {ms : Members} {k : Bytes} {xs : List JsonS} (h : opt ms k arrS = some (some xs)) :
    szO (lookup ms k) = 1 + listSize xs := by
  rw [opt_arr_some h]; rfl

theorem szO_le (ms : Members) (k : Bytes) : szO (lookup ms k) ≤ memSize ms := by
  have := sum_lookup_le ms [k] (by simp); simpa using this

-- 配列の要素を読むループの後始末
set_option hygiene false in
macro "items_tac" : tactic => `(tactic| (
  all_goals subst_vars
  all_goals try (obtain ⟨pr, pe⟩ := p; cases pr <;> simp only at p_post ⊢)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Ok _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Err _›; done)
  norm_posts'
  all_goals clear_markers
  all_goals first
    | (simp (disch := scalar_tac) only [elems_drop_end] at *
       simp [allE, listSize])
    | (have hlt : i.val < a.val.length := by scalar_tac
       rw [listSize_drop _ _ _ hlt] at *
       try rw [elems_drop _ _ _ hlt]
       simp only [jt] at *
       try simp only [i3_post] at *
       first
         | omega
         | scalar_tac
         | (simp_all [allE, List.append_assoc] <;> omega))))

@[step]
theorem opt_texture_info_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (extra : U64) (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (kb key)) ≤ Usize.max) :
    read.objects.opt_texture_info d o key extra ext ⦃ p => match p.1 with
      | .Ok t => ∃ e, optE (msOf d o) (kb key) (rTexInfo (extraKeys extra)) = some (t.map model.TextureInfo.toS, e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (kb key))
      | .Err _ => optE (msOf d o) (kb key) (rTexInfo (extraKeys extra)) = none ⦄ := by
  unfold read.objects.opt_texture_info
  step_more
  all_goals subst_vars
  norm_posts'
  all_goals try (simp_all [szO, jt]; done)
  all_goals simp_all [optE, jt, szO]

@[step]
theorem attribute_entries_loop_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (out : alloc.vec.Vec model.Attribute) (i : Usize) (hw : nodesWf d.val) (hi : i.val ≤ o.val.length)
    (ho : out.val.length ≤ i.val) :
    read.objects.attribute_entries_loop d o out i ⦃ r => (resO r).map attrsS =
      ((lastOnes ((msOf d o).drop i.val)).mapM attrOf).map (attrsS out ++ ·) ⦄ := by
  unfold read.objects.attribute_entries_loop
  step_more
  all_goals subst_vars
  all_goals try simp only at o1_post
  all_goals try exact nodesWf_get hw o1_post
  all_goals try scalar_tac
  all_goals first
    | (simp [vec_new_val]; done)
    | (have hd : (msOf d o).drop i.val = [] := by simp only [msOf, List.drop_eq_nil_iff, List.length_map]; scalar_tac
       simp [hd, lastOnes, resO])
    | (have hlt : i.val < o.val.length := by scalar_tac
       rw [lastOnes_drop _ _ _ hlt]
       by_cases hc : ∀ q (hq : q < o.val.length), i.val < q → bs o.val[q].key ≠ bs o.val[i.val].key
       · rw [if_pos hc]
         simp only [List.mapM_cons, attrOf, mS]
         first
           | (rw [treeN_oob o1_post]; simp [uintS, resO])
           | (rw [treeN_node hw o1_post]
              simp only [nodeS]
              first
                | rw [uintS_toS _ _ o2_post]
                | rw [uintS_toS_none _ o2_post]
                | rw [uintS_toS_some _ _ ((o2_post _).mp rfl)]
                | skip
              simp_all [nodeS, uintS, resO, json.number.Number.toS, attrsS, model.Attribute.toS, bs, Function.comp_def])
           | (simp_all [bs]; done)
           | (exfalso; obtain ⟨x, h1, h2, h3⟩ := b_post; exact hc x h2 h1 (by simpa [bs] using h3))
           | (exfalso; have := b_post.mpr hc; simp_all)
       · rw [if_neg hc]
         simp_all [bs])
termination_by o.val.length - i.val
decreasing_by all_goals scalar_decr_tac

-- MUST-058, MUST-082: attributes と targets の要素は名前 → アクセサーの平らな対応
@[step]
theorem read_attribute_map_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize) (allow : Bool) (hw : nodesWf d.val) :
    read.objects.read_attribute_map d id allow ⦃ r => attrMap allow (jt d id) = (resO r).map attrsS ⦄ := by
  unfold read.objects.read_attribute_map
  step_more
  all_goals subst_vars
  norm_posts'
  all_goals try (have h0 : o.val = [] := List.length_eq_zero_iff.mp (by scalar_tac)
                 simp_all [attrMap, objS, msOf]; done)
  all_goals simp_all [attrMap, objS, msOf, attrsS]

@[step]
theorem read_target_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (out : alloc.vec.Vec (alloc.vec.Vec model.Attribute)) (i : Usize) (hw : nodesWf d.val) (hi : i.val ≤ a.val.length)
    (ho : out.val.length ≤ i.val) :
    read.objects.read_target_items_loop d a out i ⦃ r => (resO r).map (fun v => v.val.map attrsS) =
      (((elemsOf d a).drop i.val).mapM (attrMap true)).map (out.val.map attrsS ++ ·) ⦄ := by
  unfold read.objects.read_target_items_loop
  step_more
  all_goals subst_vars
  all_goals try scalar_tac
  all_goals first
    | (simp (disch := scalar_tac) only [elems_drop_end]; simp [resO])
    | (rw [elems_drop _ _ i.val (by scalar_tac)]
       simp_all [resO, jt, Function.comp_def])
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem listSize_drop (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize) (i : Nat) (h : i < a.val.length) :
    listSize ((elemsOf d a).drop i) = jsonSize (treeN d.val a.val[i].val) + listSize ((elemsOf d a).drop (i + 1)) := by
  rw [elems_drop _ _ _ h, listSize]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_primitive_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_primitive d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rPrimitive (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rPrimitive (jt d id) = none ⦄ := by
  unfold read.objects.read_primitive
  step_more
  reader_close ([key "extensions"]) [rPrimitive, model.Primitive.toS, listP, opt_arrOf, attrsS, req]

@[step]
theorem read_primitive_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Primitive) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.objects.read_primitive_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rPrimitive ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Primitive.toS = out.val.map model.Primitive.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err _ => allE rPrimitive ((elemsOf d a).drop i.val) = none ⦄ := by
  unfold read.objects.read_primitive_items_loop
  step_more
  items_tac
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_mesh_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_mesh d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rMesh (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rMesh (jt d id) = none ⦄ := by
  unfold read.objects.read_mesh read.objects.read_primitive_items
  step_more
  reader_prep ([key "extensions", key "primitives"])
  all_goals try (have hz := szO_of_opt_arr r2_post; simp only [hz] at hsum)
  all_goals simp_each [req_opt]
  reader_fin [rMesh, model.Mesh.toS, reqArrE, req_opt]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_node_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_node d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rNode (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rNode (jt d id) = none ⦄ := by
  unfold read.objects.read_node
  step_more
  reader_close ([key "extensions"]) [rNode, model.Node.toS, listP]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_scene_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_scene d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rScene (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rScene (jt d id) = none ⦄ := by
  unfold read.objects.read_scene
  step_more
  reader_close ([key "extensions"]) [rScene, model.Scene.toS, listP]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_buffer_view_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_buffer_view d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rBufferView (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rBufferView (jt d id) = none ⦄ := by
  unfold read.objects.read_buffer_view
  step_more
  reader_close ([key "extensions"]) [rBufferView, model.BufferView.toS]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_buffer_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_buffer d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rBuffer (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rBuffer (jt d id) = none ⦄ := by
  unfold read.objects.read_buffer
  step_more
  reader_close ([key "extensions"]) [rBuffer, model.Buffer.toS]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_image_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_image d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rImage (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rImage (jt d id) = none ⦄ := by
  unfold read.objects.read_image
  step_more
  reader_close ([key "extensions"]) [rImage, model.Image.toS]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_texture_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_texture d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rTexture (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rTexture (jt d id) = none ⦄ := by
  unfold read.objects.read_texture
  step_more
  reader_close ([key "extensions"]) [rTexture, model.Texture.toS]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_sampler_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_sampler d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rSampler (jt d id) = some (x, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rSampler (jt d id) = none ⦄ := by
  unfold read.objects.read_sampler
  step_more
  reader_close ([key "extensions"]) [rSampler, Option.isSome]

-- MUST-095: skin.joints は必須
set_option maxHeartbeats 4000000 in
@[step]
theorem read_skin_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_skin d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rSkin (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rSkin (jt d id) = none ⦄ := by
  unfold read.objects.read_skin
  step_more
  reader_prep ([key "extensions"])
  all_goals simp_each [req_opt]
  reader_fin [rSkin, model.Skin.toS, req_opt]

/-! 文字列の比較と定数 -/

theorem slice_eq_iff_kb (a b : Slice U8) : a.val = b.val ↔ kb a = kb b := bs_inj.symm

-- bytes_eq の結果を key "..." との比較に直す
macro "cmp_norm" : tactic => `(tactic| (
  all_goals simp_each [Bool.not_eq_true]
  all_goals subst_vars
  all_goals simp_each [slice_eq_iff_kb, kb_deref, Bool.false_eq_true, false_iff, true_iff]
  all_goals keys_norm))

@[step]
theorem type_components_spec (t : alloc.vec.Vec U8) :
    read.objects.type_components t ⦃ r => typeComponents (bs t) = r.map (fun p => (p.1.val, p.2)) ⦄ := by
  unfold read.objects.type_components
  step_more
  all_goals subst_vars
  cmp_norm
  all_goals clear_markers
  all_goals simp_all (config := {decide := true}) [typeComponents]

set_option maxHeartbeats 4000000 in
@[step]
theorem check_perspective_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "perspective")) ≤ Usize.max) :
    read.objects.check_perspective d o ext ⦃ p => match p.1 with
      | .Ok b => ∃ e, optObjE (msOf d o) (key "perspective") rPerspective = some ((if b then some () else none), e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "perspective"))
      | .Err _ => optObjE (msOf d o) (key "perspective") rPerspective = none ⦄ := by
  unfold read.objects.check_perspective
  step_more
  all_goals subst_vars
  all_goals keys_norm
  norm_posts'
  all_goals try (have hz := szO_of_opt_obj r_post; rw [hz] at hb; have := szO_le (msOf d p) (key "extensions"))
  all_goals clear_markers
  all_goals try omega
  all_goals simp_each [req_opt]
  all_goals simp [*, optObjE, rPerspective, req_opt, isSome_ite_bool]
  all_goals try omega

set_option maxHeartbeats 4000000 in
@[step]
theorem check_orthographic_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "orthographic")) ≤ Usize.max) :
    read.objects.check_orthographic d o ext ⦃ p => match p.1 with
      | .Ok b => ∃ e, optObjE (msOf d o) (key "orthographic") rOrthographic = some ((if b then some () else none), e) ∧
          bss p.2 = bss ext ++ e ∧ p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "orthographic"))
      | .Err _ => optObjE (msOf d o) (key "orthographic") rOrthographic = none ⦄ := by
  unfold read.objects.check_orthographic
  step_more
  all_goals subst_vars
  all_goals keys_norm
  norm_posts'
  all_goals try (have hz := szO_of_opt_obj r_post; rw [hz] at hb; have := szO_le (msOf d p) (key "extensions"))
  all_goals clear_markers
  all_goals try omega
  all_goals simp_each [req_opt]
  all_goals simp [*, optObjE, rOrthographic, req_opt, isSome_ite_bool]
  all_goals try omega

-- MUST-132: camera.type は必須
set_option maxHeartbeats 4000000 in
@[step]
theorem read_camera_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_camera d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rCamera (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rCamera (jt d id) = none ⦄ := by
  unfold read.objects.read_camera
  step_more
  cmp_norm
  reader_prep ([key "extensions", key "perspective", key "orthographic"])
  all_goals simp_each [req_opt, true_iff, iff_true]
  reader_fin [rCamera, model.Camera.toS, req_opt, cameraKind]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_channel_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_channel d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rChannel (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rChannel (jt d id) = none ⦄ := by
  unfold read.objects.read_channel
  step_more
  cmp_norm
  reader_prep ([key "extensions", key "target"])
  all_goals try (have hz := szO_of_opt_obj r3_post; rw [hz] at hsum; have := szO_le (msOf d t) (key "extensions"))
  all_goals simp_each [req_opt]
  reader_fin [rChannel, model.Channel.toS, req_opt, reqObjE, rTarget, pathCode]

@[step]
theorem read_channel_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.Channel) (i : Usize) (hw : nodesWf d.val)
    (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.objects.read_channel_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, allE rChannel ((elemsOf d a).drop i.val) = some (ys, e) ∧
          xs.val.map model.Channel.toS = out.val.map model.Channel.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err _ => allE rChannel ((elemsOf d a).drop i.val) = none ⦄ := by
  unfold read.objects.read_channel_items_loop
  step_more
  items_tac
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

-- MUST-043: sparse の count / indices / values は必須
set_option maxHeartbeats 4000000 in
@[step]
theorem read_sparse_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_sparse d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rSparse (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rSparse (jt d id) = none ⦄ := by
  unfold read.objects.read_sparse
  step_more
  reader_prep ([key "extensions", key "indices", key "values"])
  all_goals try (have hz := szO_of_opt_obj r3_post; rw [hz] at hsum; have := szO_le (msOf d x) (key "extensions"))
  all_goals try (have hz := szO_of_opt_obj r8_post; rw [hz] at hsum; have := szO_le (msOf d x1) (key "extensions"))
  all_goals simp_each [req_opt]
  reader_fin [rSparse, model.Sparse.toS, req_opt, reqObjE, rSparseIdx, rSparseVal]

theorem opt_str_some {ms : Members} {k : Bytes} {s : Bytes} (h : opt ms k strS = some (some s)) :
    lookup ms k = some (.str s) := by
  unfold opt at h
  split at h
  · cases h
  · rename_i v hv
    cases v <;> simp_all [strS]

set_option maxHeartbeats 4000000 in
@[step]
theorem read_animation_sampler_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_animation_sampler d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, (∀ u, rAnimSampler u (jt d id) = some (x.toS, e)) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err .Invalid => ∀ u, rAnimSampler u (jt d id) = none
      | .Err .Unsupported => rAnimSampler false (jt d id) = none ∧ sampU (jt d id)
      | .Err _ => False ⦄ := by
  unfold read.objects.read_animation_sampler
  step_more
  cmp_norm
  reader_prep ([key "extensions"])
  all_goals try (have hl := opt_str_some r4_post)
  all_goals simp_each [req_opt]
  reader_fin [rAnimSampler, model.AnimationSampler.toS, req_opt, interpS, interpCode, sampU]

-- (U) を含みうる配列の要素を読むループの後始末
set_option hygiene false in
macro "items_tac_u" : tactic => `(tactic| (
  all_goals subst_vars
  all_goals try (obtain ⟨pr, pe⟩ := p; rcases pr with _ | ⟨_ | _ | _ | _⟩ <;> simp only at p_post ⊢)
  all_goals try (rcases e with _ | _ | _ | _ <;> simp only at *)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Ok _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Err _›; done)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Err _›; done)
  norm_posts'
  all_goals clear_markers
  all_goals first
    | (simp (disch := scalar_tac) only [elems_drop_end] at *
       simp [allE, listSize])
    | (have hlt : i.val < a.val.length := by scalar_tac
       rw [listSize_drop _ _ _ hlt] at *
       try rw [elems_drop _ _ _ hlt]
       simp only [jt] at *
       try simp only [i3_post] at *
       first
         | omega
         | scalar_tac
         | (simp_all [allE, List.append_assoc] <;> first | omega | exact Or.inr ⟨_, ‹_›, ‹_›⟩))))

@[step]
theorem read_animation_sampler_items_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (out : alloc.vec.Vec model.AnimationSampler) (i : Usize)
    (hw : nodesWf d.val) (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val)
    (hb : ext.val.length + listSize ((elemsOf d a).drop i.val) ≤ Usize.max) :
    read.objects.read_animation_sampler_items_loop d a ext out i ⦃ p => match p.1 with
      | .Ok xs => ∃ e ys, (∀ u, allE (rAnimSampler u) ((elemsOf d a).drop i.val) = some (ys, e)) ∧
          xs.val.map model.AnimationSampler.toS = out.val.map model.AnimationSampler.toS ++ ys ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + listSize ((elemsOf d a).drop i.val)
      | .Err .Invalid => ∀ u, allE (rAnimSampler u) ((elemsOf d a).drop i.val) = none
      | .Err .Unsupported => allE (rAnimSampler false) ((elemsOf d a).drop i.val) = none ∧
          ∃ s ∈ (elemsOf d a).drop i.val, sampU s
      | .Err _ => False ⦄ := by
  unfold read.objects.read_animation_sampler_items_loop
  step_more
  items_tac_u
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

set_option maxHeartbeats 4000000 in
@[step]
theorem read_animation_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_animation d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, (∀ u, rAnimation u (jt d id) = some (x.toS, e)) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err .Invalid => ∀ u, rAnimation u (jt d id) = none
      | .Err .Unsupported => rAnimation false (jt d id) = none ∧ animU (jt d id)
      | .Err _ => False ⦄ := by
  unfold read.objects.read_animation read.objects.read_channel_items read.objects.read_animation_sampler_items
  step_more
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Err _›)
  all_goals try (cases ‹core.result.Result.Err _ = core.result.Result.Ok _›; done)
  all_goals try (cases ‹core.result.Result.Ok _ = core.result.Result.Err _›; done)
  all_goals try (rcases e with _ | _ | _ | _ <;> simp only at *)
  reader_prep ([key "extensions", key "channels", key "samplers"])
  all_goals try (have hz := szO_of_opt_arr r2_post; rw [hz] at hsum)
  all_goals try (have hz := szO_of_opt_arr r4_post; rw [hz] at hsum)
  all_goals try (have hl := opt_arr_some r4_post)
  all_goals simp_each [req_opt]
  reader_fin [rAnimation, model.Animation.toS, req_opt, reqArrE, animU]
  all_goals exact ⟨_, ‹_ ∈ _›, ‹sampU _›⟩

theorem szO_of_find {d : alloc.vec.Vec json.JsonNode} {o : alloc.vec.Vec json.Member} {k : Bytes} {i : Usize}
    (h : i.val < o.val.length ∧ ∀ d, lookup (msOf d o) k = (o.val[i.val]?).map (fun m => treeN d.val m.value.val)) :
    szO (lookup (msOf d o) k) = jsonSize (treeN d.val (o.val[i.val]'h.1).value.val) := by
  simp only [h.2 d, List.getElem?_eq_getElem h.1, Option.map_some, szO]

set_option maxHeartbeats 8000000 in
@[step]
theorem read_accessor_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_accessor d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, (∀ u, rAccessor u (jt d id) = some (x.toS, e)) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err .Invalid => ∀ u, rAccessor u (jt d id) = none
      | .Err .Unsupported => rAccessor false (jt d id) = none ∧ accU (jt d id)
      | .Err _ => False ⦄ := by
  unfold read.objects.read_accessor
  step_more
  all_goals try (rcases c with ⟨c1, c2⟩; step_more)
  all_goals subst_vars
  all_goals keys_norm
  all_goals try (have hz := szO_of_find (d := d) o4_post)
  reader_prep ([key "extensions", key "sparse"])
  all_goals try (rw [hz] at hsum)
  all_goals try (have hl := opt_str_some r7_post)
  all_goals simp_each [req_opt]
  reader_fin [rAccessor, model.Accessor.toS, accType, accU, optE, req_opt]

theorem extraKeys_0 : extraKeys 0#u64 = [] := by unfold extraKeys; decide

theorem extraKeys_1 : extraKeys 1#u64 = [key "scale"] := by unfold extraKeys; decide

theorem extraKeys_2 : extraKeys 2#u64 = [key "strength"] := by unfold extraKeys; decide

set_option maxHeartbeats 16000000 in
@[step]
theorem read_material_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + jsonSize (jt d id) ≤ Usize.max) :
    read.objects.read_material d id ext ⦃ p => match p.1 with
      | .Ok x => ∃ e, rMaterial (jt d id) = some (x.toS, e) ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + jsonSize (jt d id)
      | .Err _ => rMaterial (jt d id) = none ⦄ := by
  unfold read.objects.read_material
  step_more
  all_goals subst_vars
  all_goals keys_norm
  all_goals try (have hz := szO_of_opt_obj r2_post; have hs2 := sum_lookup_le (msOf d p) [key "extensions",
    key "baseColorTexture", key "metallicRoughnessTexture"] (by decide))
  reader_prep ([key "extensions", key "pbrMetallicRoughness", key "normalTexture", key "occlusionTexture",
    key "emissiveTexture"])
  all_goals try (rw [hz] at hsum; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hs2)
  all_goals simp_each [extraKeys_0, extraKeys_1, extraKeys_2]
  reader_fin [rMaterial, model.Material.toS, optObjE, rPbr]

/-! バージョン文字列 -/

def verDigits (p : Bytes) : Nat := digitsVal (p.map (· - 0x30))

theorem take_drop_cons (l : List Nat) (st i e : Nat) (hi : i < e) (he : e ≤ l.length) (hs : st ≤ i) :
    (l.take (i + 1)).drop st = (l.take i).drop st ++ [l[i]'(by omega)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by omega),
    List.drop_append_of_le_length (by simp; omega)]
  rfl

theorem drop_take_cons (l : List Nat) (i e : Nat) (hi : i < e) (he : e ≤ l.length) :
    (l.take e).drop i = l[i]'(by omega) :: (l.take e).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp

theorem verDigits_lt (p : Bytes) (h : ∀ c ∈ p, isDigit c = true) : verDigits p < 10 ^ p.length := by
  have := digitsVal_lt (p.map (· - 0x30)) (by
    intro d hd; simp only [List.mem_map] at hd; obtain ⟨c, hc, rfl⟩ := hd
    have := h c hc; simp [isDigit] at this; omega)
  simpa [verDigits] using this

set_option maxHeartbeats 4000000 in
theorem pvp_loop_spec (loop : alloc.vec.Vec U8 → Usize → U64 → Usize → Result (Option U64))
    (hloop : ∀ s e v i, loop s e v i = (do
      if i < e then
        let i1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8) s i
        if i1 < 48#u8 then ok none
        else if i1 > 57#u8 then ok none
        else
          let i2 ← v * 10#u64
          let i3 ← i1 - 48#u8
          let i4 ← lift (UScalar.cast .U64 i3)
          let v1 ← i2 + i4
          let i5 ← i + 1#usize
          loop s e v1 i5
      else ok (some v)))
    (s : alloc.vec.Vec U8) (e : Usize) (v : U64) (i : Usize) (st : Nat) (hst : st ≤ i.val)
    (hi : i.val ≤ e.val) (he : e.val ≤ s.val.length) (h9 : e.val - st ≤ 9)
    (hv : v.val = verDigits (((bs s).take i.val).drop st))
    (hd : ∀ c ∈ ((bs s).take i.val).drop st, isDigit c = true) :
    loop s e v i ⦃ r => r.map (·.val) = if (∀ c ∈ ((bs s).take e.val).drop i.val, isDigit c = true)
      then some (verDigits (((bs s).take e.val).drop st)) else none ⦄ := by
  rw [hloop]
  have hlen : (bs s).length = s.val.length := by simp [bs]
  split
  · rename_i hie
    have hie' : i.val < e.val := by scalar_tac
    have hc := drop_take_cons (bs s) i.val e.val hie' (by omega)
    have hsi : (bs s)[i.val]'(by omega) = (s.val[i.val]'(by scalar_tac)).val := by simp [bs]
    step*
    · -- 数字でない (< '0')
      simp only [Option.map_none]
      rw [if_neg]
      rw [hc]; simp only [List.mem_cons, forall_eq_or_imp, not_and_or]; left
      rw [hsi]; simp [isDigit]; scalar_tac
    · simp only [Option.map_none]
      rw [if_neg]
      rw [hc]; simp only [List.mem_cons, forall_eq_or_imp, not_and_or]; left
      rw [hsi]; simp [isDigit]; scalar_tac
    · -- 桁あふれしない
      have := verDigits_lt _ hd
      have hl : (((bs s).take i.val).drop st).length = i.val - st := by simp [hlen]; omega
      rw [hl] at this
      have : 10 ^ (i.val - st) ≤ 10 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      scalar_tac
    · have := verDigits_lt _ hd
      have hl : (((bs s).take i.val).drop st).length = i.val - st := by simp [hlen]; omega
      rw [hl] at this
      have : 10 ^ (i.val - st) ≤ 10 ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      scalar_tac
    · -- 再帰
      apply WP.spec_mono (pvp_loop_spec loop hloop s e v1 i5 st (by scalar_tac) (by scalar_tac) he h9 ?_ ?_)
      · intro r hr
        rw [hr, hc]
        have hdig : isDigit ((bs s)[i.val]'(by omega)) = true := by
          rw [hsi]; simp [isDigit]; constructor <;> scalar_tac
        simp only [List.mem_cons, forall_eq_or_imp, hdig, true_and]
        rw [i5_post]
      · rw [i5_post, take_drop_cons (bs s) st i.val e.val hie' (by omega) hst, verDigits, List.map_append,
          List.map_cons, List.map_nil, digitsVal_concat, ← verDigits, ← hv, hsi]
        scalar_tac
      · rw [i5_post, take_drop_cons (bs s) st i.val e.val hie' (by omega) hst]
        intro c hc'
        simp only [List.mem_append, List.mem_singleton] at hc'
        rcases hc' with hc' | rfl
        · exact hd c hc'
        · rw [hsi]; simp [isDigit]; constructor <;> scalar_tac
  · rename_i hie
    have : i.val = e.val := by scalar_tac
    step*
    simp [this, hv]
termination_by e.val - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem parse_version_part_loop0_spec (s : alloc.vec.Vec U8) (e : Usize) (v : U64) (i : Usize) (st : Nat)
    (hst : st ≤ i.val) (hi : i.val ≤ e.val) (he : e.val ≤ s.val.length) (h9 : e.val - st ≤ 9)
    (hv : v.val = verDigits (((bs s).take i.val).drop st))
    (hd : ∀ c ∈ ((bs s).take i.val).drop st, isDigit c = true) :
    read.objects.parse_version_part_loop0 s e v i ⦃ r => r.map (·.val) = if (∀ c ∈ ((bs s).take e.val).drop i.val, isDigit c = true)
      then some (verDigits (((bs s).take e.val).drop st)) else none ⦄ :=
  pvp_loop_spec read.objects.parse_version_part_loop0 (fun s e v i => by rw [read.objects.parse_version_part_loop0]) s e v i st hst hi he h9 hv hd

@[step]
theorem parse_version_part_loop1_spec (s : alloc.vec.Vec U8) (e : Usize) (v : U64) (i : Usize) (st : Nat)
    (hst : st ≤ i.val) (hi : i.val ≤ e.val) (he : e.val ≤ s.val.length) (h9 : e.val - st ≤ 9)
    (hv : v.val = verDigits (((bs s).take i.val).drop st))
    (hd : ∀ c ∈ ((bs s).take i.val).drop st, isDigit c = true) :
    read.objects.parse_version_part_loop1 s e v i ⦃ r => r.map (·.val) = if (∀ c ∈ ((bs s).take e.val).drop i.val, isDigit c = true)
      then some (verDigits (((bs s).take e.val).drop st)) else none ⦄ :=
  pvp_loop_spec read.objects.parse_version_part_loop1 (fun s e v i => by rw [read.objects.parse_version_part_loop1]) s e v i st hst hi he h9 hv hd

theorem verPart_eq (p : Bytes) (h1 : p ≠ []) (h2 : p.length ≤ 9) (h3 : 1 < p.length → p.head? ≠ some 0x30) :
    verPart p = if (∀ c ∈ p, isDigit c = true) then some (verDigits p) else none := by
  unfold verPart verDigits
  by_cases h : ∀ c ∈ p, isDigit c = true
  · rw [if_pos ⟨h1, h2, h, h3⟩, if_pos h]
  · rw [if_neg (fun hh => h hh.2.2.1), if_neg h]

@[step]
theorem parse_version_part_spec (s : alloc.vec.Vec U8) (start e : Usize) (he : e.val ≤ s.val.length) :
    read.objects.parse_version_part s start e ⦃ r => r.map (·.val) = verPart (((bs s).take e.val).drop start.val) ⦄ := by
  have hlen : (bs s).length = s.val.length := by simp [bs]
  have hpl : (((bs s).take e.val).drop start.val).length = e.val - start.val := by simp [hlen]; omega
  unfold read.objects.parse_version_part
  split
  · rename_i h
    have : ((bs s).take e.val).drop start.val = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [hpl]; scalar_tac
    simp [this, verPart]
  · rename_i h
    have hlt : start.val < e.val := by scalar_tac
    have hc := drop_take_cons (bs s) start.val e.val hlt (by omega)
    have hsi : (bs s)[start.val]'(by omega) = (s.val[start.val]'(by scalar_tac)).val := by simp [bs]
    have hne : ((bs s).take e.val).drop start.val ≠ [] := by rw [hc]; simp
    step
    split
    · step*
      unfold verPart; rw [if_neg (fun hh => by have := hh.2.1; rw [hpl] at this; scalar_tac)]; rfl
    · step
      split
      · rename_i h48
        split
        · rename_i hgt
          step*
          unfold verPart
          rw [if_neg (fun hh => by
            have := hh.2.2.2 (by rw [hpl]; scalar_tac)
            rw [hc] at this; simp only [List.head?_cons, ne_eq, Option.some.injEq] at this
            apply this; rw [hsi]; scalar_tac)]
          rfl
        · apply WP.spec_mono (parse_version_part_loop0_spec s e 0#u64 start start.val (by omega) (by omega) he
            (by scalar_tac) (by simp [verDigits, digitsVal]) (by simp))
          intro r hr
          rw [hr, verPart_eq _ hne (by rw [hpl]; scalar_tac) (by intro h; rw [hpl] at h; scalar_tac)]
      · rename_i h48
        apply WP.spec_mono (parse_version_part_loop1_spec s e 0#u64 start start.val (by omega) (by omega) he
          (by scalar_tac) (by simp [verDigits, digitsVal]) (by simp))
        intro r hr
        rw [hr, verPart_eq _ hne (by rw [hpl]; scalar_tac) ?_]
        intro _; rw [hc]; simp only [List.head?_cons, ne_eq, Option.some.injEq]
        rw [hsi]; intro h'; apply h48; scalar_tac

@[step]
theorem parse_version_loop_spec (s : alloc.vec.Vec U8) (dot : Usize) (hd : dot.val ≤ s.val.length) :
    read.objects.parse_version_loop s dot ⦃ r => dot.val ≤ r.val ∧ r.val ≤ s.val.length ∧
      (∀ j (hj : j < s.val.length), dot.val ≤ j → j < r.val → (s.val[j]).val ≠ 46) ∧
      (∀ hr : r.val < s.val.length, (s.val[r.val]).val = 46) ⦄ := by
  unfold read.objects.parse_version_loop
  step*
  · refine ⟨by omega, by omega, ?_, by assumption⟩
    intro j hj h1 h2
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · intro h; simp_all [bne_iff_ne, ne_eq, UScalar.eq_equiv]
    · exact r_post2 j hj (by scalar_tac) h2
  · refine ⟨le_refl _, by scalar_tac, fun j hj h1 h2 => by omega, fun _ => ?_⟩
    simp_all
  · refine ⟨le_refl _, by scalar_tac, fun j hj h1 h2 => by omega, fun h => by scalar_tac⟩
termination_by s.val.length - dot.val
decreasing_by all_goals scalar_decr_tac

theorem idxOf_eq (l : List Nat) (a i : Nat) (hi : i ≤ l.length)
    (h1 : ∀ j (hj : j < l.length), j < i → l[j] ≠ a) (h2 : ∀ hr : i < l.length, l[i] = a) : l.idxOf a = i := by
  induction l generalizing i with
  | nil => simp at hi; subst hi; simp
  | cons x xs ih =>
    cases i with
    | zero => have := h2 (by simp); simp_all
    | succ k =>
      have hx : x ≠ a := h1 0 (by simp) (by omega)
      rw [List.idxOf_cons_ne _ (by simpa using hx)]
      congr 1
      exact ih k (by simp at hi; omega) (fun j hj h => h1 (j + 1) (by simp; omega) (by omega))
        (fun hr => h2 (by simp; omega))

theorem versionS_none (l : Bytes) (h : ∀ j (hj : j < l.length), l[j] ≠ 46) : versionS l = none := by
  unfold versionS
  rw [if_neg]
  intro hm
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
  exact h j hj he

theorem versionS_of_dot (l : Bytes) (dot : Nat) (hd : dot < l.length) (h46 : l[dot] = 46)
    (hb : ∀ j (hj : j < l.length), j < dot → l[j] ≠ 46) :
    versionS l = (verPart (l.take dot)).bind (fun a => (verPart (l.drop (dot + 1))).map (a, ·)) := by
  have hm : 0x2E ∈ l := by rw [List.mem_iff_getElem]; exact ⟨dot, hd, h46⟩
  have hi : l.idxOf 0x2E = dot := idxOf_eq l 0x2E dot (by omega) hb (fun _ => h46)
  unfold versionS
  rw [if_pos hm, hi]
  cases verPart (l.take dot) <;> cases verPart (l.drop (dot + 1)) <;> rfl

-- MUST-010: version / minVersion の構文
@[step]
theorem parse_version_spec (s : alloc.vec.Vec U8) :
    read.objects.parse_version s ⦃ r => versionS (bs s) = r.map (fun p => (p.1.val, p.2.val)) ⦄ := by
  have hlen : (bs s).length = s.val.length := by simp [bs]
  have hget : ∀ j (hj : j < s.val.length), (bs s)[j]'(by omega) = (s.val[j]).val := by simp [bs]
  unfold read.objects.parse_version
  step*
  · rw [versionS_none]
    · rfl
    · intro j hj; rw [hget j (by omega)]; exact dot_post2 j (by omega) (by omega) (by scalar_tac)
  all_goals have hlt : dot.val < (bs s).length := by scalar_tac
  all_goals rw [versionS_of_dot (bs s) dot.val hlt (by rw [hget]; exact dot_post3 (by omega))
    (fun j hj h => by rw [hget j (by omega)]; exact dot_post2 j (by omega) (by omega) h)]
  all_goals simp only [List.drop_zero, List.take_of_length_le (show (bs s).length ≤ s.len.val by scalar_tac)] at *
  all_goals subst_vars
  all_goals try simp only [i1_post] at *
  all_goals rw [← o_post]
  all_goals try rw [← o1_post]
  all_goals simp

end LoadGltf
