import LoadGltf.Model
import LoadGltf.Json.Mod

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## R. スキーマ対応 read_spec (glTF JSON スキーマの転記) -/

-- ASCII のキー
def key (s : String) : Bytes := s.toList.map Char.toNat

-- lookup(o, k): キーが k に等しい最後のメンバーの値
def lookup (ms : List (Bytes × JsonS)) (k : Bytes) : Option JsonS :=
  (ms.reverse.find? (fun m => m.1 == k)).map (·.2)

-- 後のメンバーに上書きされないメンバー (文書順)
def lastOnes : List (Bytes × JsonS) → List (Bytes × JsonS)
  | [] => []
  | m :: rest => if rest.any (fun m' => m'.1 == m.1) then lastOnes rest else m :: lastOnes rest

-- 数値 Number(neg, I, F, eneg, E) が表す有理数 (N 節)
def numQ (neg : Bool) (I F : List Nat) (eneg : Bool) (E : List Nat) : ℚ :=
  let e : ℤ := if eneg then -(digitsVal E : ℤ) else (digitsVal E : ℤ)
  (-1 : ℚ) ^ neg.toNat * (digitsVal (I ++ F) : ℚ) * (10 : ℚ) ^ (e - (F.length : ℤ))

-- uint: 値が 0 以上 u64::MAX 以下の整数である数値
-- MUST-006, MUST-013: 整数のプロパティは小数部が 0 で、添字は 0 以上
def uintS : JsonS → Option Nat
  | .num neg I F eneg E =>
    let q := numQ neg I F eneg E
    if q.den = 1 ∧ 0 ≤ q ∧ q ≤ (U64.max : ℚ) then some q.num.toNat else none
  | _ => none

def strS : JsonS → Option Bytes
  | .str b => some b
  | _ => none

def boolS : JsonS → Option Bool
  | .bool b => some b
  | _ => none

def objS : JsonS → Option (List (Bytes × JsonS))
  | .obj ms => some ms
  | _ => none

def isObj : JsonS → Bool
  | .obj _ => true
  | _ => false

def isNum : JsonS → Bool
  | .num .. => true
  | _ => false

-- number (値は解釈しない)
def numS (v : JsonS) : Option Unit := if isNum v then some () else none

-- array: 要素 1 個以上 (minItems 1)
def arrS : JsonS → Option (List JsonS)
  | .arr (v :: vs) => some (v :: vs)
  | _ => none

-- 数値の配列 → 長さ
def numArr (v : JsonS) : Option Nat :=
  (arrS v).bind fun xs => if xs.all isNum then some xs.length else none

-- ちょうど n 個の数値の配列
def numArrN (n : Nat) (v : JsonS) : Option Unit :=
  (numArr v).bind fun l => if l = n then some () else none

-- 各要素を f で読む配列
def arrOf {α} (f : JsonS → Option α) (v : JsonS) : Option (List α) := (arrS v).bind (·.mapM f)

-- 省略可能なプロパティ: 無ければ some none、型が違えば none
def opt {α} (ms : List (Bytes × JsonS)) (k : Bytes) (f : JsonS → Option α) : Option (Option α) :=
  match lookup ms k with
  | none => some none
  | some v => (f v).map some

-- 必須プロパティ
def req {α} (ms : List (Bytes × JsonS)) (k : Bytes) (f : JsonS → Option α) : Option α :=
  (lookup ms k).bind f

/-! 拡張名を集めながら読む (値, 訪れた glTFProperty の拡張名) -/

abbrev Members := List (Bytes × JsonS)

-- extensions: あればオブジェクトで、上書きされないメンバーの値はすべてオブジェクト。そのキーが拡張名
def extsS (ms : Members) : Option Exts :=
  (opt ms (key "extensions") objS).bind fun o => match o with
    | none => some []
    | some es => if (lastOnes es).all (fun m => isObj m.2) then some ((lastOnes es).map (·.1)) else none

-- glTFChildOfRootProperty: name は文字列、extensions
def childS (ms : Members) : Option Exts := do
  let _ ← opt ms (key "name") strS
  extsS ms

-- JSON 値の節点数 (読み取り中に集める拡張名の数の上限)
mutual
def jsonSize : JsonS → Nat
  | .arr vs => 1 + listSize vs
  | .obj ms => 1 + memSize ms
  | _ => 1
def listSize : List JsonS → Nat
  | [] => 0
  | v :: vs => jsonSize v + listSize vs
def memSize : List (Bytes × JsonS) → Nat
  | [] => 0
  | m :: ms => jsonSize m.2 + memSize ms
end

/-! 各仮定と目標をそれぞれ simp only する (simp at * が書き換えない仮定があるため) -/

open Lean Elab Tactic Meta in
elab "simp_each " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => withMainContext do
  let stx ← `(tactic| simp only [$ls,*])
  let r ← mkSimpContext stx (eraseLocal := false)
  let goal ← getMainGoal
  let mut fvars := #[]
  for d in (← goal.getDecl).lctx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then fvars := fvars.push d.fvarId
  try
    r.dischargeWrapper.with fun discharge? => do
      let (res?, _) ← simpGoal goal r.ctx r.simprocs discharge? (simplifyTarget := true) (fvarIdsToSimp := fvars)
      match res? with
      | none => replaceMainGoal []
      | some (_, g) => replaceMainGoal [g]
  catch _ => pure ()

/-! アリーナから抽象値へ -/

def jt (d : alloc.vec.Vec json.JsonNode) (id : Usize) : JsonS := treeN d.val id.val

def mS (d : alloc.vec.Vec json.JsonNode) (m : json.Member) : Bytes × JsonS := (bs m.key, treeN d.val m.value.val)

def msOf (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) : List (Bytes × JsonS) := o.val.map (mS d)

def bss (v : alloc.vec.Vec (alloc.vec.Vec U8)) : Exts := v.val.map bs

def resO {α ε} : core.result.Result α ε → Option α
  | .Ok x => some x
  | .Err _ => none

-- 節点の表す値
def nodeS (d : alloc.vec.Vec json.JsonNode) : json.JsonNode → JsonS
  | .Null => .null
  | .Bool b => .bool b
  | .Number n => n.toS
  | .String s => .str (bs s)
  | .Array a => .arr (a.val.map fun c => treeN d.val c.val)
  | .Object m => .obj (msOf d m)

theorem treeN_node {d : alloc.vec.Vec json.JsonNode} (hw : nodesWf d.val) {id : Nat} {n : json.JsonNode}
    (h : d.val[id]? = some n) : treeN d.val id = nodeS d n := by
  have hn := nodesWf_get hw h
  cases n with
  | Array a => exact treeN_arr h hn
  | Object m => exact treeN_obj h hn
  | _ => rw [treeN, h]; rfl

theorem bs_inj {a b : List U8} : a.map (·.val) = b.map (·.val) ↔ a = b := by
  apply List.map_inj_right
  intro x y h; exact UScalar.eq_of_val_eq h

/-! lookup -/

theorem lookup_none {ms : List (Bytes × JsonS)} {k : Bytes} (h : ∀ m ∈ ms, m.1 ≠ k) : lookup ms k = none := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none, List.mem_reverse, beq_iff_eq]
  exact h

theorem lookup_last {ms : List (Bytes × JsonS)} {k : Bytes} {i : Nat} (hi : i < ms.length)
    (hk : ms[i].1 = k) (hl : ∀ q (hq : q < ms.length), i < q → ms[q].1 ≠ k) : lookup ms k = some ms[i].2 := by
  have hs : ms = ms.take i ++ ms[i] :: ms.drop (i + 1) := by simp
  unfold lookup
  generalize hx : ms[i] = x at hk ⊢
  rw [hx] at hs
  rw [hs, List.reverse_append, List.reverse_cons, List.append_assoc, List.find?_append]
  have hn : (ms.drop (i + 1)).reverse.find? (fun m => m.1 == k) = none := by
    simp only [List.find?_eq_none, List.mem_reverse, beq_iff_eq]
    intro m hm
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
    simp only [List.getElem_drop]
    exact hl _ (by simp at hq; omega) (by omega)
  rw [hn]
  simp [hk]

/-! find_member / is_last_member -/

def FindInv (obj : alloc.vec.Vec json.Member) (k : Bytes) (n : Nat) (r : Option Usize) : Prop :=
  match r with
  | none => ∀ q (hq : q < obj.val.length), q < n → bs obj.val[q].key ≠ k
  | some j => ∃ hj : j.val < obj.val.length, j.val < n ∧ bs obj.val[j.val].key = k ∧
      ∀ q (hq : q < obj.val.length), j.val < q → q < n → bs obj.val[q].key ≠ k

@[step]
theorem find_member_loop_spec (obj : alloc.vec.Vec json.Member) (key : Slice U8) (found : Option Usize) (i : Usize)
    (hi : i.val ≤ obj.val.length) (hf : FindInv obj (kb key) i.val found) :
    read.access.find_member_loop obj key found i ⦃ r => FindInv obj (kb key) obj.val.length r ⦄ := by
  unfold read.access.find_member_loop
  step*
  · simp only [bind_ite_res]
    have hb : bs m.key = kb key ↔ b = true := by rw [b_post]; simp [bs, kb, bs_inj, m_post]
    split
    · step*
      refine ⟨by scalar_tac, by scalar_tac, ?_, ?_⟩
      · simp_all
      · intro q hq h1 h2; scalar_tac
    · step*
      cases found with
      | none =>
        intro q hq h1
        rcases Nat.lt_or_ge q i.val with h | h
        · exact hf q hq h
        · have : q = i.val := by scalar_tac
          subst this; simp_all
      | some j =>
        obtain ⟨hj, hj1, hj2, hj3⟩ := hf
        refine ⟨hj, by scalar_tac, hj2, ?_⟩
        intro q hq h1 h2
        rcases Nat.lt_or_ge q i.val with h | h
        · exact hj3 q hq h1 h
        · have : q = i.val := by scalar_tac
          subst this; simp_all
  done
termination_by obj.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem find_member_spec0 (obj : alloc.vec.Vec json.Member) (key : Slice U8) :
    read.access.find_member obj key ⦃ r => FindInv obj (kb key) obj.val.length r ⦄ := by
  unfold read.access.find_member
  step*
  · intro q hq h; scalar_tac

theorem findInv_none {d : alloc.vec.Vec json.JsonNode} {obj : alloc.vec.Vec json.Member} {k : Bytes}
    (h : FindInv obj k obj.val.length none) : lookup (msOf d obj) k = none := by
  apply lookup_none
  intro m hm
  simp only [msOf, List.mem_map] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm'
  exact h q hq hq

theorem findInv_some {d : alloc.vec.Vec json.JsonNode} {obj : alloc.vec.Vec json.Member} {k : Bytes} {j : Usize}
    (h : FindInv obj k obj.val.length (some j)) :
    ∃ hj : j.val < obj.val.length, lookup (msOf d obj) k = some (treeN d.val obj.val[j.val].value.val) := by
  obtain ⟨hj, -, hk, hl⟩ := h
  refine ⟨hj, ?_⟩
  have := lookup_last (ms := msOf d obj) (k := k) (i := j.val) (by simp [msOf, hj])
    (by simp [msOf, mS, hk]) (by intro q hq h1; simp [msOf, mS]; exact hl q (by simpa [msOf] using hq) h1 (by simpa [msOf] using hq))
  simpa [msOf, mS] using this

@[step]
theorem is_last_member_spec (obj : alloc.vec.Vec json.Member) (i : Usize) (hi : i.val < obj.val.length) :
    read.access.is_last_member obj i ⦃ r => r = true ↔ ∀ q (hq : q < obj.val.length), i.val < q → bs obj.val[q].key ≠ bs obj.val[i.val].key ⦄ := by
  unfold read.access.is_last_member
  step*
  · subst_vars
    simp only [Bool.false_eq_true, false_iff, not_forall]
    exact absurd (o_post i.val hi hi) (by simp [kb, bs])
  · subst_vars
    obtain ⟨hj, -, hk, hl⟩ := o_post
    simp only [UScalar.eq_equiv, decide_eq_true_eq]
    constructor
    · rintro h; have : k.val = i.val := by scalar_tac
      intro q hq h1; simpa [kb, bs] using hl q hq (by omega) hq
    · intro h
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (show k.val ≠ i.val from fun e => hne (by scalar_tac)) with h1 | h1
      · exact hl i.val hi h1 hi (by simp [kb, bs])
      · exact h k.val hj h1 (by simp_all [kb, bs])

@[step]
theorem node_at_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize) :
    read.access.node_at d id ⦃ r => match r with
      | none => d.val.length ≤ id.val
      | some n => d.val[id.val]? = some n ⦄ := by
  unfold read.access.node_at
  step*
  simp_all

-- メンバー key の値の節点
def MemberPost (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (k : Bytes)
    (r : core.result.Result (Option json.JsonNode) Unit) : Prop :=
  match r with
  | .Ok none => lookup (msOf d o) k = none
  | .Ok (some n) => ∃ id, d.val[id]? = some n ∧ lookup (msOf d o) k = some (treeN d.val id)
  | .Err _ => lookup (msOf d o) k = some .null

@[step]
theorem member_node_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8) :
    read.access.member_node d o key ⦃ r => MemberPost d o (kb key) r ⦄ := by
  unfold read.access.member_node
  step*
  all_goals subst_vars
  all_goals try simp only at o1_post
  all_goals try simp only [MemberPost]
  all_goals first
    | exact findInv_none o_post
    | (obtain ⟨hj, hl⟩ := findInv_some (d := d) o_post
       exact ⟨_, o1_post, hl⟩)
    | (obtain ⟨hj, hl⟩ := findInv_some (d := d) o_post
       rw [hl]; unfold treeN; simp [List.getElem?_eq_none o1_post])
    | (obtain ⟨hj, -⟩ := o_post; scalar_tac)

-- 見つかったメンバーの値 (どの節点列 d についても)
theorem find_member_spec (obj : alloc.vec.Vec json.Member) (key : Slice U8) :
    read.access.find_member obj key ⦃ r => match r with
      | none => ∀ d, lookup (msOf d obj) (kb key) = none
      | some j => j.val < obj.val.length ∧
          ∀ d, lookup (msOf d obj) (kb key) = (obj.val[j.val]?).map (fun m => treeN d.val m.value.val) ⦄ := by
  apply WP.spec_mono (find_member_spec0 obj key)
  intro r h
  cases r with
  | none => intro d; exact findInv_none h
  | some j =>
    have h' := h
    obtain ⟨hj, -⟩ := h'
    refine ⟨hj, fun d => ?_⟩
    obtain ⟨hj', hl⟩ := findInv_some (d := d) h
    rw [hl, List.getElem?_eq_getElem hj']; rfl

attribute [-step] find_member_spec0

attribute [step] find_member_spec

def nodeOpt {α} (d : alloc.vec.Vec json.JsonNode) (f : JsonS → Option α) :
    core.result.Result (Option json.JsonNode) Unit → Option (Option α)
  | .Ok none => some none
  | .Ok (some n) => (f (nodeS d n)).map some
  | .Err _ => (f .null).map some

theorem opt_member {d : alloc.vec.Vec json.JsonNode} (hw : nodesWf d.val) {o : alloc.vec.Vec json.Member} {k : Bytes}
    {α} (f : JsonS → Option α) {r : core.result.Result (Option json.JsonNode) Unit} (h : MemberPost d o k r) :
    opt (msOf d o) k f = nodeOpt d f r := by
  unfold MemberPost at h
  split at h
  · simp [opt, h, nodeOpt]
  · obtain ⟨id, h1, h2⟩ := h; simp [opt, h2, treeN_node hw h1, nodeOpt]
  · simp [opt, h, nodeOpt]

theorem numQ_toS (n : json.number.Number) :
    numQ n.negative (n.int_digits.val.map (·.val)) (n.frac_digits.val.map (·.val)) n.exp_negative
      (n.exp_digits.val.map (·.val)) = n.q := by
  simp [numQ, json.number.Number.q, json.number.Number.digits, json.number.Number.expVal, List.map_append]

theorem uintS_toS (n : json.number.Number) (o : Option U64) (h : ∀ v : U64, o = some v ↔ n.q = (v.val : ℚ)) :
    uintS n.toS = o.map (·.val) := by
  simp only [uintS, json.number.Number.toS, numQ_toS]
  cases o with
  | some v =>
    have hq := (h v).mp rfl
    rw [hq]
    have : (v.val : ℚ) ≤ (U64.max : ℚ) := by have := v.hBounds; norm_cast; scalar_tac
    simp [this]
  | none =>
    simp only [Option.map_none]
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    have hz : 0 ≤ n.q.num := Rat.num_nonneg.mpr h2
    have hlt : n.q.num.toNat < 2 ^ UScalarTy.U64.numBits := by
      have : (n.q.num : ℚ) = n.q := (Rat.den_eq_one_iff _).mp h1
      have h4 : (n.q.num : ℚ) ≤ (U64.max : ℚ) := by rw [this]; exact h3
      have h5 : n.q.num ≤ (U64.max : ℤ) := by exact_mod_cast h4
      rw [U64.max_eq] at h5
      have : (2 : ℕ) ^ UScalarTy.U64.numBits = 18446744073709551616 := by simp [UScalarTy.numBits]
      rw [this]; omega
    have := (h (UScalar.ofNatCore n.q.num.toNat hlt)).mpr
    simp only [reduceCtorEq] at this
    apply this
    simp only [UScalar.ofNatCore_val_eq]
    have e := (Rat.den_eq_one_iff _).mp h1
    rw [← e]; exact_mod_cast (Int.toNat_of_nonneg hz).symm

theorem uintS_toS_none (n : json.number.Number) (h : ∀ v : U64, ¬ n.q = (v.val : ℚ)) : uintS n.toS = none :=
  uintS_toS n none (by simpa using h)

theorem uintS_toS_some (n : json.number.Number) (v : U64) (h : n.q = (v.val : ℚ)) : uintS n.toS = some v.val := by
  apply uintS_toS n (some v)
  intro w; constructor
  · intro e; cases e; exact h
  · intro e; simp only [Option.some.injEq]; rw [h] at e; exact UScalar.eq_of_val_eq (by exact_mod_cast e)

-- uintS (n.toS) を事後条件から書き換える
set_option hygiene false in
macro "uint_tac" : tactic => `(tactic| (
  all_goals try simp only [nodeS] at *
  all_goals try simp only [List.mapM_cons, nodeS]
  all_goals try (first
    | rw [uintS_toS _ _ o1_post]
    | rw [uintS_toS_none _ o1_post]
    | rw [uintS_toS_some _ _ ((o1_post _).mp rfl)])))

theorem member_num_wf {d : alloc.vec.Vec json.JsonNode} (hw : nodesWf d.val) {o : alloc.vec.Vec json.Member} {k : Bytes}
    {n : json.number.Number} (h : MemberPost d o k (.Ok (some (.Number n)))) : n.wf := by
  obtain ⟨id, h1, -⟩ := h
  exact nodesWf_get hw h1

-- MUST-006, MUST-013: 整数のプロパティは小数部が 0 で、添字は 0 以上
@[step]
theorem get_uint_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_uint d o key ⦃ r => opt (msOf d o) (kb key) uintS = (resO r).map ov ⦄ := by
  unfold read.access.get_uint
  step*
  all_goals subst_vars
  all_goals try exact member_num_wf hw r_post
  all_goals rw [opt_member hw _ r_post]
  all_goals simp only [nodeOpt, nodeS]
  all_goals try simp only [uintS_toS _ _ o1_post]
  all_goals simp [uintS, resO, ov]

@[simp] theorem opt_bind_some {α β} (x : Option α) (f : α → β) : (x.bind fun a => some (f a)) = x.map f := by
  cases x <;> rfl

-- 配列節点の要素の値
def elemsOf (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize) : List JsonS := a.val.map fun c => treeN d.val c.val

@[step]
theorem get_bool_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_bool d o key ⦃ r => opt (msOf d o) (kb key) boolS = resO r ⦄ := by
  unfold read.access.get_bool
  step*
  all_goals subst_vars
  all_goals rw [opt_member hw _ r_post]
  all_goals simp [nodeOpt, nodeS, boolS, resO, json.number.Number.toS]

@[step]
theorem copy_bytes_loop_spec (v out : alloc.vec.Vec U8) (i : Usize) (hi : i.val ≤ v.val.length)
    (ho : out.val = v.val.take i.val) :
    read.access.copy_bytes_loop v out i ⦃ r => r.val = v.val ⦄ := by
  unfold read.access.copy_bytes_loop
  step*
  simp only [out1_post, ho, i3_post, i2_post]
  · rw [List.take_add_one, List.getElem?_eq_getElem (by scalar_tac)]; simp
  · rw [ho, List.take_of_length_le (by scalar_tac)]
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem copy_key_loop_spec (v out : alloc.vec.Vec U8) (i : Usize) (hi : i.val ≤ v.val.length)
    (ho : out.val = v.val.take i.val) :
    read.access.copy_key_loop v out i ⦃ r => r.val = v.val ⦄ := by
  unfold read.access.copy_key_loop
  step*
  simp only [out1_post, ho, i3_post, i2_post]
  · rw [List.take_add_one, List.getElem?_eq_getElem (by scalar_tac)]; simp
  · rw [ho, List.take_of_length_le (by scalar_tac)]
termination_by v.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem get_string_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_string d o key ⦃ r => opt (msOf d o) (kb key) strS = (resO r).map (Option.map bs) ⦄ := by
  unfold read.access.get_string
  step*
  all_goals subst_vars
  all_goals try (simp [vec_new_val]; done)
  all_goals rw [opt_member hw _ r_post]
  all_goals simp_all [nodeOpt, nodeS, strS, resO, json.number.Number.toS, bs]

@[step]
theorem get_object_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_object d o key ⦃ r => opt (msOf d o) (kb key) objS = (resO r).map (Option.map (msOf d)) ⦄ := by
  unfold read.access.get_object
  step*
  all_goals subst_vars
  all_goals rw [opt_member hw _ r_post]
  all_goals simp [nodeOpt, nodeS, objS, resO, json.number.Number.toS]

@[step]
theorem get_array_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_array d o key ⦃ r => opt (msOf d o) (kb key) arrS = (resO r).map (Option.map (elemsOf d)) ⦄ := by
  unfold read.access.get_array
  step*
  all_goals subst_vars
  all_goals rw [opt_member hw _ r_post]
  all_goals simp only [nodeOpt, nodeS]
  all_goals try simp [arrS, resO, json.number.Number.toS]
  all_goals first
    | (have : a.val = [] := List.length_eq_zero_iff.mp (by scalar_tac)
       simp [this])
    | (cases ha : a.val with
       | nil => scalar_tac
       | cons x xs => simp [ha, elemsOf])

theorem elems_drop (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize) (i : Nat) (h : i < a.val.length) :
    (elemsOf d a).drop i = treeN d.val a.val[i].val :: (elemsOf d a).drop (i + 1) := by
  simp only [elemsOf]
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem treeN_oob {d : alloc.vec.Vec json.JsonNode} {id : Nat} (h : d.val.length ≤ id) : treeN d.val id = .null := by
  unfold treeN; simp [List.getElem?_eq_none h]

theorem elems_drop_end (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize) (i : Nat) (h : a.val.length ≤ i) :
    (elemsOf d a).drop i = [] := by
  simp [elemsOf, h]

-- 配列の要素ごとのループの後始末
set_option hygiene false in
macro "elem_tac" : tactic => `(tactic| (
  all_goals subst_vars
  all_goals try simp only at o_post
  all_goals try exact nodesWf_get ‹_› o_post
  all_goals try scalar_tac
  all_goals first
    | simp (disch := scalar_tac) only [elems_drop_end]
    | (rw [elems_drop _ _ i.val (by scalar_tac)]
       first | rw [treeN_oob o_post] | rw [treeN_node ‹_› o_post])))

@[step]
theorem uints_of_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize) (out : alloc.vec.Vec U64)
    (i : Usize) (hw : nodesWf d.val) (hi : i.val ≤ a.val.length) (ho : out.val.length ≤ i.val) :
    read.access.uints_of_loop d a out i ⦃ r => r.map (fun v => v.val.map (·.val)) =
      (List.mapM uintS ((elemsOf d a).drop i.val)).map (out.val.map (·.val) ++ ·) ⦄ := by
  unfold read.access.uints_of_loop
  step*
  elem_tac
  uint_tac
  all_goals simp_all [uintS, Function.comp_def]
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem opt_bind {α β} (ms : List (Bytes × JsonS)) (k : Bytes) (g : JsonS → Option α) (h : α → Option β) :
    opt ms k (fun v => (g v).bind h) = (opt ms k g).bind (fun o => o.elim (some none) (fun x => (h x).map some)) := by
  unfold opt
  cases lookup ms k with
  | none => rfl
  | some v => rcases hg : g v with _ | x <;> simp [hg]

theorem opt_arrOf {α} (ms : List (Bytes × JsonS)) (k : Bytes) (f : JsonS → Option α) :
    opt ms k (arrOf f) = (opt ms k arrS).bind (fun o => o.elim (some none) (fun xs => (xs.mapM f).map some)) :=
  opt_bind ms k arrS (List.mapM f)

theorem opt_numArr (ms : List (Bytes × JsonS)) (k : Bytes) :
    opt ms k numArr = (opt ms k arrS).bind
      (fun o => o.elim (some none) (fun xs => (if xs.all isNum then some xs.length else none).map some)) :=
  opt_bind ms k arrS _

theorem opt_numArrN (ms : List (Bytes × JsonS)) (k : Bytes) (n : Nat) :
    opt ms k (numArrN n) = (opt ms k numArr).bind
      (fun o => o.elim (some none) (fun l => (if l = n then some () else none).map some)) :=
  opt_bind ms k numArr _

@[step]
theorem get_uint_array_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_uint_array d o key ⦃ r => opt (msOf d o) (kb key) (arrOf uintS) =
      (resO r).map (Option.map (fun v => v.val.map (·.val))) ⦄ := by
  unfold read.access.get_uint_array
  step*
  all_goals try rw [opt_arrOf]
  all_goals subst_vars
  all_goals simp_all [resO]
  exact ⟨_, o1_post.symm, o1_post⟩

@[step]
theorem all_numbers_loop_spec (d : alloc.vec.Vec json.JsonNode) (a : alloc.vec.Vec Usize) (i : Usize)
    (hw : nodesWf d.val) (hi : i.val ≤ a.val.length) :
    read.access.all_numbers_loop d a i ⦃ r => r = ((elemsOf d a).drop i.val).all isNum ⦄ := by
  unfold read.access.all_numbers_loop
  step*
  elem_tac
  all_goals simp_all [nodeS, isNum, json.number.Number.toS]
termination_by a.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem get_number_array_len_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.get_number_array_len d o key ⦃ r => opt (msOf d o) (kb key) numArr = (resO r).map ov ⦄ := by
  unfold read.access.get_number_array_len
  step*
  all_goals try rw [opt_numArr]
  all_goals subst_vars
  all_goals simp_all [resO, ov, elemsOf]

@[step]
theorem check_number_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.check_number d o key ⦃ r => opt (msOf d o) (kb key) numS = (resO r).map (fun b => if b then some () else none) ⦄ := by
  unfold read.access.check_number
  step*
  all_goals subst_vars
  all_goals rw [opt_member hw _ r_post]
  all_goals simp [nodeOpt, nodeS, numS, isNum, resO, json.number.Number.toS]

@[step]
theorem check_number_array_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (len : U64) (hw : nodesWf d.val) :
    read.access.check_number_array d o key len ⦃ r => opt (msOf d o) (kb key) (numArrN len.val) =
      (resO r).map (fun b => if b then some () else none) ⦄ := by
  unfold read.access.check_number_array
  step*
  all_goals try rw [opt_numArrN]
  all_goals subst_vars
  all_goals simp_all [resO, ov]

@[step]
theorem as_object_spec (d : alloc.vec.Vec json.JsonNode) (id : Usize) (hw : nodesWf d.val) :
    read.access.as_object d id ⦃ r => objS (jt d id) = (resO r).map (msOf d) ⦄ := by
  unfold read.access.as_object
  step*
  all_goals subst_vars
  all_goals simp only at o_post
  all_goals first | rw [jt, treeN_oob o_post] | rw [jt, treeN_node hw o_post]
  all_goals simp [nodeS, objS, resO, json.number.Number.toS]

theorem req_opt {α} (ms : List (Bytes × JsonS)) (k : Bytes) (f : JsonS → Option α) :
    req ms k f = (opt ms k f).join := by
  unfold req opt; cases lookup ms k <;> simp
  cases f _ <;> rfl

@[step]
theorem req_uint_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member) (key : Slice U8)
    (hw : nodesWf d.val) :
    read.access.req_uint d o key ⦃ r => req (msOf d o) (kb key) uintS = (resO r).map (·.val) ⦄ := by
  unfold read.access.req_uint
  step*
  all_goals rw [req_opt]
  all_goals subst_vars
  all_goals simp_all [resO, ov]

-- コード中のキーのバイト列リテラルを key "..." に直す

@[simp] theorem kb_CUBICSPLINE (h : List.length [67#u8, 85#u8, 66#u8, 73#u8, 67#u8, 83#u8, 80#u8, 76#u8, 73#u8, 78#u8, 69#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [67#u8, 85#u8, 66#u8, 73#u8, 67#u8, 83#u8, 80#u8, 76#u8, 73#u8, 78#u8, 69#u8] h).to_slice = key "CUBICSPLINE" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_LINEAR (h : List.length [76#u8, 73#u8, 78#u8, 69#u8, 65#u8, 82#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [76#u8, 73#u8, 78#u8, 69#u8, 65#u8, 82#u8] h).to_slice = key "LINEAR" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_MAT2 (h : List.length [77#u8, 65#u8, 84#u8, 50#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [77#u8, 65#u8, 84#u8, 50#u8] h).to_slice = key "MAT2" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_MAT3 (h : List.length [77#u8, 65#u8, 84#u8, 51#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [77#u8, 65#u8, 84#u8, 51#u8] h).to_slice = key "MAT3" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_MAT4 (h : List.length [77#u8, 65#u8, 84#u8, 52#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [77#u8, 65#u8, 84#u8, 52#u8] h).to_slice = key "MAT4" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_SCALAR (h : List.length [83#u8, 67#u8, 65#u8, 76#u8, 65#u8, 82#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [83#u8, 67#u8, 65#u8, 76#u8, 65#u8, 82#u8] h).to_slice = key "SCALAR" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_STEP (h : List.length [83#u8, 84#u8, 69#u8, 80#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [83#u8, 84#u8, 69#u8, 80#u8] h).to_slice = key "STEP" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_VEC2 (h : List.length [86#u8, 69#u8, 67#u8, 50#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [86#u8, 69#u8, 67#u8, 50#u8] h).to_slice = key "VEC2" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_VEC3 (h : List.length [86#u8, 69#u8, 67#u8, 51#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [86#u8, 69#u8, 67#u8, 51#u8] h).to_slice = key "VEC3" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_VEC4 (h : List.length [86#u8, 69#u8, 67#u8, 52#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [86#u8, 69#u8, 67#u8, 52#u8] h).to_slice = key "VEC4" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_accessors (h : List.length [97#u8, 99#u8, 99#u8, 101#u8, 115#u8, 115#u8, 111#u8, 114#u8, 115#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [97#u8, 99#u8, 99#u8, 101#u8, 115#u8, 115#u8, 111#u8, 114#u8, 115#u8] h).to_slice = key "accessors" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_alphaCutoff (h : List.length [97#u8, 108#u8, 112#u8, 104#u8, 97#u8, 67#u8, 117#u8, 116#u8, 111#u8, 102#u8, 102#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [97#u8, 108#u8, 112#u8, 104#u8, 97#u8, 67#u8, 117#u8, 116#u8, 111#u8, 102#u8, 102#u8] h).to_slice = key "alphaCutoff" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_alphaMode (h : List.length [97#u8, 108#u8, 112#u8, 104#u8, 97#u8, 77#u8, 111#u8, 100#u8, 101#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [97#u8, 108#u8, 112#u8, 104#u8, 97#u8, 77#u8, 111#u8, 100#u8, 101#u8] h).to_slice = key "alphaMode" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_animations (h : List.length [97#u8, 110#u8, 105#u8, 109#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8, 115#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [97#u8, 110#u8, 105#u8, 109#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8, 115#u8] h).to_slice = key "animations" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_aspectRatio (h : List.length [97#u8, 115#u8, 112#u8, 101#u8, 99#u8, 116#u8, 82#u8, 97#u8, 116#u8, 105#u8, 111#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [97#u8, 115#u8, 112#u8, 101#u8, 99#u8, 116#u8, 82#u8, 97#u8, 116#u8, 105#u8, 111#u8] h).to_slice = key "aspectRatio" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_asset (h : List.length [97#u8, 115#u8, 115#u8, 101#u8, 116#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [97#u8, 115#u8, 115#u8, 101#u8, 116#u8] h).to_slice = key "asset" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_attributes (h : List.length [97#u8, 116#u8, 116#u8, 114#u8, 105#u8, 98#u8, 117#u8, 116#u8, 101#u8, 115#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [97#u8, 116#u8, 116#u8, 114#u8, 105#u8, 98#u8, 117#u8, 116#u8, 101#u8, 115#u8] h).to_slice = key "attributes" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_baseColorFactor (h : List.length [98#u8, 97#u8, 115#u8, 101#u8, 67#u8, 111#u8, 108#u8, 111#u8, 114#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] = (15#usize : Usize).val) :
    kb (Array.make 15#usize [98#u8, 97#u8, 115#u8, 101#u8, 67#u8, 111#u8, 108#u8, 111#u8, 114#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] h).to_slice = key "baseColorFactor" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_baseColorTexture (h : List.length [98#u8, 97#u8, 115#u8, 101#u8, 67#u8, 111#u8, 108#u8, 111#u8, 114#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] = (16#usize : Usize).val) :
    kb (Array.make 16#usize [98#u8, 97#u8, 115#u8, 101#u8, 67#u8, 111#u8, 108#u8, 111#u8, 114#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] h).to_slice = key "baseColorTexture" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_buffer (h : List.length [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8] h).to_slice = key "buffer" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_bufferView (h : List.length [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8, 86#u8, 105#u8, 101#u8, 119#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8, 86#u8, 105#u8, 101#u8, 119#u8] h).to_slice = key "bufferView" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_bufferViews (h : List.length [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8, 86#u8, 105#u8, 101#u8, 119#u8, 115#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8, 86#u8, 105#u8, 101#u8, 119#u8, 115#u8] h).to_slice = key "bufferViews" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_buffers (h : List.length [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8, 115#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [98#u8, 117#u8, 102#u8, 102#u8, 101#u8, 114#u8, 115#u8] h).to_slice = key "buffers" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_byteLength (h : List.length [98#u8, 121#u8, 116#u8, 101#u8, 76#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [98#u8, 121#u8, 116#u8, 101#u8, 76#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8] h).to_slice = key "byteLength" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_byteOffset (h : List.length [98#u8, 121#u8, 116#u8, 101#u8, 79#u8, 102#u8, 102#u8, 115#u8, 101#u8, 116#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [98#u8, 121#u8, 116#u8, 101#u8, 79#u8, 102#u8, 102#u8, 115#u8, 101#u8, 116#u8] h).to_slice = key "byteOffset" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_byteStride (h : List.length [98#u8, 121#u8, 116#u8, 101#u8, 83#u8, 116#u8, 114#u8, 105#u8, 100#u8, 101#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [98#u8, 121#u8, 116#u8, 101#u8, 83#u8, 116#u8, 114#u8, 105#u8, 100#u8, 101#u8] h).to_slice = key "byteStride" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_camera (h : List.length [99#u8, 97#u8, 109#u8, 101#u8, 114#u8, 97#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [99#u8, 97#u8, 109#u8, 101#u8, 114#u8, 97#u8] h).to_slice = key "camera" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_cameras (h : List.length [99#u8, 97#u8, 109#u8, 101#u8, 114#u8, 97#u8, 115#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [99#u8, 97#u8, 109#u8, 101#u8, 114#u8, 97#u8, 115#u8] h).to_slice = key "cameras" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_channels (h : List.length [99#u8, 104#u8, 97#u8, 110#u8, 110#u8, 101#u8, 108#u8, 115#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [99#u8, 104#u8, 97#u8, 110#u8, 110#u8, 101#u8, 108#u8, 115#u8] h).to_slice = key "channels" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_children (h : List.length [99#u8, 104#u8, 105#u8, 108#u8, 100#u8, 114#u8, 101#u8, 110#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [99#u8, 104#u8, 105#u8, 108#u8, 100#u8, 114#u8, 101#u8, 110#u8] h).to_slice = key "children" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_componentType (h : List.length [99#u8, 111#u8, 109#u8, 112#u8, 111#u8, 110#u8, 101#u8, 110#u8, 116#u8, 84#u8, 121#u8, 112#u8, 101#u8] = (13#usize : Usize).val) :
    kb (Array.make 13#usize [99#u8, 111#u8, 109#u8, 112#u8, 111#u8, 110#u8, 101#u8, 110#u8, 116#u8, 84#u8, 121#u8, 112#u8, 101#u8] h).to_slice = key "componentType" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_copyright (h : List.length [99#u8, 111#u8, 112#u8, 121#u8, 114#u8, 105#u8, 103#u8, 104#u8, 116#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [99#u8, 111#u8, 112#u8, 121#u8, 114#u8, 105#u8, 103#u8, 104#u8, 116#u8] h).to_slice = key "copyright" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_count (h : List.length [99#u8, 111#u8, 117#u8, 110#u8, 116#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [99#u8, 111#u8, 117#u8, 110#u8, 116#u8] h).to_slice = key "count" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_doubleSided (h : List.length [100#u8, 111#u8, 117#u8, 98#u8, 108#u8, 101#u8, 83#u8, 105#u8, 100#u8, 101#u8, 100#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [100#u8, 111#u8, 117#u8, 98#u8, 108#u8, 101#u8, 83#u8, 105#u8, 100#u8, 101#u8, 100#u8] h).to_slice = key "doubleSided" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_emissiveFactor (h : List.length [101#u8, 109#u8, 105#u8, 115#u8, 115#u8, 105#u8, 118#u8, 101#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] = (14#usize : Usize).val) :
    kb (Array.make 14#usize [101#u8, 109#u8, 105#u8, 115#u8, 115#u8, 105#u8, 118#u8, 101#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] h).to_slice = key "emissiveFactor" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_emissiveTexture (h : List.length [101#u8, 109#u8, 105#u8, 115#u8, 115#u8, 105#u8, 118#u8, 101#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] = (15#usize : Usize).val) :
    kb (Array.make 15#usize [101#u8, 109#u8, 105#u8, 115#u8, 115#u8, 105#u8, 118#u8, 101#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] h).to_slice = key "emissiveTexture" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_extensions (h : List.length [101#u8, 120#u8, 116#u8, 101#u8, 110#u8, 115#u8, 105#u8, 111#u8, 110#u8, 115#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [101#u8, 120#u8, 116#u8, 101#u8, 110#u8, 115#u8, 105#u8, 111#u8, 110#u8, 115#u8] h).to_slice = key "extensions" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_extensionsRequired (h : List.length [101#u8, 120#u8, 116#u8, 101#u8, 110#u8, 115#u8, 105#u8, 111#u8, 110#u8, 115#u8, 82#u8, 101#u8, 113#u8, 117#u8, 105#u8, 114#u8, 101#u8, 100#u8] = (18#usize : Usize).val) :
    kb (Array.make 18#usize [101#u8, 120#u8, 116#u8, 101#u8, 110#u8, 115#u8, 105#u8, 111#u8, 110#u8, 115#u8, 82#u8, 101#u8, 113#u8, 117#u8, 105#u8, 114#u8, 101#u8, 100#u8] h).to_slice = key "extensionsRequired" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_extensionsUsed (h : List.length [101#u8, 120#u8, 116#u8, 101#u8, 110#u8, 115#u8, 105#u8, 111#u8, 110#u8, 115#u8, 85#u8, 115#u8, 101#u8, 100#u8] = (14#usize : Usize).val) :
    kb (Array.make 14#usize [101#u8, 120#u8, 116#u8, 101#u8, 110#u8, 115#u8, 105#u8, 111#u8, 110#u8, 115#u8, 85#u8, 115#u8, 101#u8, 100#u8] h).to_slice = key "extensionsUsed" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_generator (h : List.length [103#u8, 101#u8, 110#u8, 101#u8, 114#u8, 97#u8, 116#u8, 111#u8, 114#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [103#u8, 101#u8, 110#u8, 101#u8, 114#u8, 97#u8, 116#u8, 111#u8, 114#u8] h).to_slice = key "generator" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_images (h : List.length [105#u8, 109#u8, 97#u8, 103#u8, 101#u8, 115#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [105#u8, 109#u8, 97#u8, 103#u8, 101#u8, 115#u8] h).to_slice = key "images" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_index (h : List.length [105#u8, 110#u8, 100#u8, 101#u8, 120#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [105#u8, 110#u8, 100#u8, 101#u8, 120#u8] h).to_slice = key "index" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_indices (h : List.length [105#u8, 110#u8, 100#u8, 105#u8, 99#u8, 101#u8, 115#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [105#u8, 110#u8, 100#u8, 105#u8, 99#u8, 101#u8, 115#u8] h).to_slice = key "indices" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_input (h : List.length [105#u8, 110#u8, 112#u8, 117#u8, 116#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [105#u8, 110#u8, 112#u8, 117#u8, 116#u8] h).to_slice = key "input" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_interpolation (h : List.length [105#u8, 110#u8, 116#u8, 101#u8, 114#u8, 112#u8, 111#u8, 108#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8] = (13#usize : Usize).val) :
    kb (Array.make 13#usize [105#u8, 110#u8, 116#u8, 101#u8, 114#u8, 112#u8, 111#u8, 108#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8] h).to_slice = key "interpolation" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_inverseBindMatrices (h : List.length [105#u8, 110#u8, 118#u8, 101#u8, 114#u8, 115#u8, 101#u8, 66#u8, 105#u8, 110#u8, 100#u8, 77#u8, 97#u8, 116#u8, 114#u8, 105#u8, 99#u8, 101#u8, 115#u8] = (19#usize : Usize).val) :
    kb (Array.make 19#usize [105#u8, 110#u8, 118#u8, 101#u8, 114#u8, 115#u8, 101#u8, 66#u8, 105#u8, 110#u8, 100#u8, 77#u8, 97#u8, 116#u8, 114#u8, 105#u8, 99#u8, 101#u8, 115#u8] h).to_slice = key "inverseBindMatrices" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_joints (h : List.length [106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 115#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [106#u8, 111#u8, 105#u8, 110#u8, 116#u8, 115#u8] h).to_slice = key "joints" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_magFilter (h : List.length [109#u8, 97#u8, 103#u8, 70#u8, 105#u8, 108#u8, 116#u8, 101#u8, 114#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [109#u8, 97#u8, 103#u8, 70#u8, 105#u8, 108#u8, 116#u8, 101#u8, 114#u8] h).to_slice = key "magFilter" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_material (h : List.length [109#u8, 97#u8, 116#u8, 101#u8, 114#u8, 105#u8, 97#u8, 108#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [109#u8, 97#u8, 116#u8, 101#u8, 114#u8, 105#u8, 97#u8, 108#u8] h).to_slice = key "material" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_materials (h : List.length [109#u8, 97#u8, 116#u8, 101#u8, 114#u8, 105#u8, 97#u8, 108#u8, 115#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [109#u8, 97#u8, 116#u8, 101#u8, 114#u8, 105#u8, 97#u8, 108#u8, 115#u8] h).to_slice = key "materials" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_matrix (h : List.length [109#u8, 97#u8, 116#u8, 114#u8, 105#u8, 120#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [109#u8, 97#u8, 116#u8, 114#u8, 105#u8, 120#u8] h).to_slice = key "matrix" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_max (h : List.length [109#u8, 97#u8, 120#u8] = (3#usize : Usize).val) :
    kb (Array.make 3#usize [109#u8, 97#u8, 120#u8] h).to_slice = key "max" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_mesh (h : List.length [109#u8, 101#u8, 115#u8, 104#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [109#u8, 101#u8, 115#u8, 104#u8] h).to_slice = key "mesh" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_meshes (h : List.length [109#u8, 101#u8, 115#u8, 104#u8, 101#u8, 115#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [109#u8, 101#u8, 115#u8, 104#u8, 101#u8, 115#u8] h).to_slice = key "meshes" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_metallicFactor (h : List.length [109#u8, 101#u8, 116#u8, 97#u8, 108#u8, 108#u8, 105#u8, 99#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] = (14#usize : Usize).val) :
    kb (Array.make 14#usize [109#u8, 101#u8, 116#u8, 97#u8, 108#u8, 108#u8, 105#u8, 99#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] h).to_slice = key "metallicFactor" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_metallicRoughnessTexture (h : List.length [109#u8, 101#u8, 116#u8, 97#u8, 108#u8, 108#u8, 105#u8, 99#u8, 82#u8, 111#u8, 117#u8, 103#u8, 104#u8, 110#u8, 101#u8, 115#u8, 115#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] = (24#usize : Usize).val) :
    kb (Array.make 24#usize [109#u8, 101#u8, 116#u8, 97#u8, 108#u8, 108#u8, 105#u8, 99#u8, 82#u8, 111#u8, 117#u8, 103#u8, 104#u8, 110#u8, 101#u8, 115#u8, 115#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] h).to_slice = key "metallicRoughnessTexture" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_mimeType (h : List.length [109#u8, 105#u8, 109#u8, 101#u8, 84#u8, 121#u8, 112#u8, 101#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [109#u8, 105#u8, 109#u8, 101#u8, 84#u8, 121#u8, 112#u8, 101#u8] h).to_slice = key "mimeType" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_min (h : List.length [109#u8, 105#u8, 110#u8] = (3#usize : Usize).val) :
    kb (Array.make 3#usize [109#u8, 105#u8, 110#u8] h).to_slice = key "min" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_minFilter (h : List.length [109#u8, 105#u8, 110#u8, 70#u8, 105#u8, 108#u8, 116#u8, 101#u8, 114#u8] = (9#usize : Usize).val) :
    kb (Array.make 9#usize [109#u8, 105#u8, 110#u8, 70#u8, 105#u8, 108#u8, 116#u8, 101#u8, 114#u8] h).to_slice = key "minFilter" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_minVersion (h : List.length [109#u8, 105#u8, 110#u8, 86#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [109#u8, 105#u8, 110#u8, 86#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8] h).to_slice = key "minVersion" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_mode (h : List.length [109#u8, 111#u8, 100#u8, 101#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [109#u8, 111#u8, 100#u8, 101#u8] h).to_slice = key "mode" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_name (h : List.length [110#u8, 97#u8, 109#u8, 101#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [110#u8, 97#u8, 109#u8, 101#u8] h).to_slice = key "name" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_node (h : List.length [110#u8, 111#u8, 100#u8, 101#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [110#u8, 111#u8, 100#u8, 101#u8] h).to_slice = key "node" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_nodes (h : List.length [110#u8, 111#u8, 100#u8, 101#u8, 115#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [110#u8, 111#u8, 100#u8, 101#u8, 115#u8] h).to_slice = key "nodes" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_normalTexture (h : List.length [110#u8, 111#u8, 114#u8, 109#u8, 97#u8, 108#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] = (13#usize : Usize).val) :
    kb (Array.make 13#usize [110#u8, 111#u8, 114#u8, 109#u8, 97#u8, 108#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] h).to_slice = key "normalTexture" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_normalized (h : List.length [110#u8, 111#u8, 114#u8, 109#u8, 97#u8, 108#u8, 105#u8, 122#u8, 101#u8, 100#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [110#u8, 111#u8, 114#u8, 109#u8, 97#u8, 108#u8, 105#u8, 122#u8, 101#u8, 100#u8] h).to_slice = key "normalized" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_occlusionTexture (h : List.length [111#u8, 99#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 111#u8, 110#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] = (16#usize : Usize).val) :
    kb (Array.make 16#usize [111#u8, 99#u8, 99#u8, 108#u8, 117#u8, 115#u8, 105#u8, 111#u8, 110#u8, 84#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8] h).to_slice = key "occlusionTexture" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_orthographic (h : List.length [111#u8, 114#u8, 116#u8, 104#u8, 111#u8, 103#u8, 114#u8, 97#u8, 112#u8, 104#u8, 105#u8, 99#u8] = (12#usize : Usize).val) :
    kb (Array.make 12#usize [111#u8, 114#u8, 116#u8, 104#u8, 111#u8, 103#u8, 114#u8, 97#u8, 112#u8, 104#u8, 105#u8, 99#u8] h).to_slice = key "orthographic" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_output (h : List.length [111#u8, 117#u8, 116#u8, 112#u8, 117#u8, 116#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [111#u8, 117#u8, 116#u8, 112#u8, 117#u8, 116#u8] h).to_slice = key "output" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_path (h : List.length [112#u8, 97#u8, 116#u8, 104#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [112#u8, 97#u8, 116#u8, 104#u8] h).to_slice = key "path" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_pbrMetallicRoughness (h : List.length [112#u8, 98#u8, 114#u8, 77#u8, 101#u8, 116#u8, 97#u8, 108#u8, 108#u8, 105#u8, 99#u8, 82#u8, 111#u8, 117#u8, 103#u8, 104#u8, 110#u8, 101#u8, 115#u8, 115#u8] = (20#usize : Usize).val) :
    kb (Array.make 20#usize [112#u8, 98#u8, 114#u8, 77#u8, 101#u8, 116#u8, 97#u8, 108#u8, 108#u8, 105#u8, 99#u8, 82#u8, 111#u8, 117#u8, 103#u8, 104#u8, 110#u8, 101#u8, 115#u8, 115#u8] h).to_slice = key "pbrMetallicRoughness" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_perspective (h : List.length [112#u8, 101#u8, 114#u8, 115#u8, 112#u8, 101#u8, 99#u8, 116#u8, 105#u8, 118#u8, 101#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [112#u8, 101#u8, 114#u8, 115#u8, 112#u8, 101#u8, 99#u8, 116#u8, 105#u8, 118#u8, 101#u8] h).to_slice = key "perspective" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_primitives (h : List.length [112#u8, 114#u8, 105#u8, 109#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 115#u8] = (10#usize : Usize).val) :
    kb (Array.make 10#usize [112#u8, 114#u8, 105#u8, 109#u8, 105#u8, 116#u8, 105#u8, 118#u8, 101#u8, 115#u8] h).to_slice = key "primitives" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_rotation (h : List.length [114#u8, 111#u8, 116#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [114#u8, 111#u8, 116#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8] h).to_slice = key "rotation" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_roughnessFactor (h : List.length [114#u8, 111#u8, 117#u8, 103#u8, 104#u8, 110#u8, 101#u8, 115#u8, 115#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] = (15#usize : Usize).val) :
    kb (Array.make 15#usize [114#u8, 111#u8, 117#u8, 103#u8, 104#u8, 110#u8, 101#u8, 115#u8, 115#u8, 70#u8, 97#u8, 99#u8, 116#u8, 111#u8, 114#u8] h).to_slice = key "roughnessFactor" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_sampler (h : List.length [115#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 114#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [115#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 114#u8] h).to_slice = key "sampler" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_samplers (h : List.length [115#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 114#u8, 115#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [115#u8, 97#u8, 109#u8, 112#u8, 108#u8, 101#u8, 114#u8, 115#u8] h).to_slice = key "samplers" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_scale (h : List.length [115#u8, 99#u8, 97#u8, 108#u8, 101#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [115#u8, 99#u8, 97#u8, 108#u8, 101#u8] h).to_slice = key "scale" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_scene (h : List.length [115#u8, 99#u8, 101#u8, 110#u8, 101#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [115#u8, 99#u8, 101#u8, 110#u8, 101#u8] h).to_slice = key "scene" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_scenes (h : List.length [115#u8, 99#u8, 101#u8, 110#u8, 101#u8, 115#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [115#u8, 99#u8, 101#u8, 110#u8, 101#u8, 115#u8] h).to_slice = key "scenes" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_skeleton (h : List.length [115#u8, 107#u8, 101#u8, 108#u8, 101#u8, 116#u8, 111#u8, 110#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [115#u8, 107#u8, 101#u8, 108#u8, 101#u8, 116#u8, 111#u8, 110#u8] h).to_slice = key "skeleton" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_skin (h : List.length [115#u8, 107#u8, 105#u8, 110#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [115#u8, 107#u8, 105#u8, 110#u8] h).to_slice = key "skin" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_skins (h : List.length [115#u8, 107#u8, 105#u8, 110#u8, 115#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [115#u8, 107#u8, 105#u8, 110#u8, 115#u8] h).to_slice = key "skins" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_source (h : List.length [115#u8, 111#u8, 117#u8, 114#u8, 99#u8, 101#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [115#u8, 111#u8, 117#u8, 114#u8, 99#u8, 101#u8] h).to_slice = key "source" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_sparse (h : List.length [115#u8, 112#u8, 97#u8, 114#u8, 115#u8, 101#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [115#u8, 112#u8, 97#u8, 114#u8, 115#u8, 101#u8] h).to_slice = key "sparse" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_strength (h : List.length [115#u8, 116#u8, 114#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [115#u8, 116#u8, 114#u8, 101#u8, 110#u8, 103#u8, 116#u8, 104#u8] h).to_slice = key "strength" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_target (h : List.length [116#u8, 97#u8, 114#u8, 103#u8, 101#u8, 116#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [116#u8, 97#u8, 114#u8, 103#u8, 101#u8, 116#u8] h).to_slice = key "target" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_targets (h : List.length [116#u8, 97#u8, 114#u8, 103#u8, 101#u8, 116#u8, 115#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [116#u8, 97#u8, 114#u8, 103#u8, 101#u8, 116#u8, 115#u8] h).to_slice = key "targets" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_texCoord (h : List.length [116#u8, 101#u8, 120#u8, 67#u8, 111#u8, 111#u8, 114#u8, 100#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [116#u8, 101#u8, 120#u8, 67#u8, 111#u8, 111#u8, 114#u8, 100#u8] h).to_slice = key "texCoord" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_textures (h : List.length [116#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8, 115#u8] = (8#usize : Usize).val) :
    kb (Array.make 8#usize [116#u8, 101#u8, 120#u8, 116#u8, 117#u8, 114#u8, 101#u8, 115#u8] h).to_slice = key "textures" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_translation (h : List.length [116#u8, 114#u8, 97#u8, 110#u8, 115#u8, 108#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8] = (11#usize : Usize).val) :
    kb (Array.make 11#usize [116#u8, 114#u8, 97#u8, 110#u8, 115#u8, 108#u8, 97#u8, 116#u8, 105#u8, 111#u8, 110#u8] h).to_slice = key "translation" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_type (h : List.length [116#u8, 121#u8, 112#u8, 101#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [116#u8, 121#u8, 112#u8, 101#u8] h).to_slice = key "type" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_uri (h : List.length [117#u8, 114#u8, 105#u8] = (3#usize : Usize).val) :
    kb (Array.make 3#usize [117#u8, 114#u8, 105#u8] h).to_slice = key "uri" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_values (h : List.length [118#u8, 97#u8, 108#u8, 117#u8, 101#u8, 115#u8] = (6#usize : Usize).val) :
    kb (Array.make 6#usize [118#u8, 97#u8, 108#u8, 117#u8, 101#u8, 115#u8] h).to_slice = key "values" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_version (h : List.length [118#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [118#u8, 101#u8, 114#u8, 115#u8, 105#u8, 111#u8, 110#u8] h).to_slice = key "version" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_weights (h : List.length [119#u8, 101#u8, 105#u8, 103#u8, 104#u8, 116#u8, 115#u8] = (7#usize : Usize).val) :
    kb (Array.make 7#usize [119#u8, 101#u8, 105#u8, 103#u8, 104#u8, 116#u8, 115#u8] h).to_slice = key "weights" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_wrapS (h : List.length [119#u8, 114#u8, 97#u8, 112#u8, 83#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [119#u8, 114#u8, 97#u8, 112#u8, 83#u8] h).to_slice = key "wrapS" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_wrapT (h : List.length [119#u8, 114#u8, 97#u8, 112#u8, 84#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [119#u8, 114#u8, 97#u8, 112#u8, 84#u8] h).to_slice = key "wrapT" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_xmag (h : List.length [120#u8, 109#u8, 97#u8, 103#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [120#u8, 109#u8, 97#u8, 103#u8] h).to_slice = key "xmag" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_yfov (h : List.length [121#u8, 102#u8, 111#u8, 118#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [121#u8, 102#u8, 111#u8, 118#u8] h).to_slice = key "yfov" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_ymag (h : List.length [121#u8, 109#u8, 97#u8, 103#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [121#u8, 109#u8, 97#u8, 103#u8] h).to_slice = key "ymag" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_zfar (h : List.length [122#u8, 102#u8, 97#u8, 114#u8] = (4#usize : Usize).val) :
    kb (Array.make 4#usize [122#u8, 102#u8, 97#u8, 114#u8] h).to_slice = key "zfar" := by
  simp only [kb, array_make_to_slice_val]; decide

@[simp] theorem kb_znear (h : List.length [122#u8, 110#u8, 101#u8, 97#u8, 114#u8] = (5#usize : Usize).val) :
    kb (Array.make 5#usize [122#u8, 110#u8, 101#u8, 97#u8, 114#u8] h).to_slice = key "znear" := by
  simp only [kb, array_make_to_slice_val]; decide

-- キーのリテラルを key "..." に書き換える
set_option hygiene false in
macro "keys_norm" : tactic => `(tactic| simp_each [kb_CUBICSPLINE, kb_LINEAR, kb_MAT2, kb_MAT3, kb_MAT4, kb_SCALAR, kb_STEP, kb_VEC2, kb_VEC3, kb_VEC4, kb_accessors, kb_alphaCutoff, kb_alphaMode, kb_animations, kb_aspectRatio, kb_asset, kb_attributes, kb_baseColorFactor, kb_baseColorTexture, kb_buffer, kb_bufferView, kb_bufferViews, kb_buffers, kb_byteLength, kb_byteOffset, kb_byteStride, kb_camera, kb_cameras, kb_channels, kb_children, kb_componentType, kb_copyright, kb_count, kb_doubleSided, kb_emissiveFactor, kb_emissiveTexture, kb_extensions, kb_extensionsRequired, kb_extensionsUsed, kb_generator, kb_images, kb_index, kb_indices, kb_input, kb_interpolation, kb_inverseBindMatrices, kb_joints, kb_magFilter, kb_material, kb_materials, kb_matrix, kb_max, kb_mesh, kb_meshes, kb_metallicFactor, kb_metallicRoughnessTexture, kb_mimeType, kb_min, kb_minFilter, kb_minVersion, kb_mode, kb_name, kb_node, kb_nodes, kb_normalTexture, kb_normalized, kb_occlusionTexture, kb_orthographic, kb_output, kb_path, kb_pbrMetallicRoughness, kb_perspective, kb_primitives, kb_rotation, kb_roughnessFactor, kb_sampler, kb_samplers, kb_scale, kb_scene, kb_scenes, kb_skeleton, kb_skin, kb_skins, kb_source, kb_sparse, kb_strength, kb_target, kb_targets, kb_texCoord, kb_textures, kb_translation, kb_type, kb_uri, kb_values, kb_version, kb_weights, kb_wrapS, kb_wrapT, kb_xmag, kb_yfov, kb_ymag, kb_zfar, kb_znear])

/-! 証明の道具 -/

theorem opt_match_ok {α} (o : Option α) (a : α) :
    (match o with | none => ok a | some v => ok v : Result α) = ok (o.getD a) := by
  cases o <;> rfl

theorem bss_len {a b : alloc.vec.Vec (alloc.vec.Vec U8)} {e : Exts} (h : bss a = bss b ++ e) :
    a.val.length = b.val.length + e.length := by
  have := congrArg List.length h; simpa [bss] using this

/-! 拡張名の収集 -/

theorem msOf_drop (d : alloc.vec.Vec json.JsonNode) (e : alloc.vec.Vec json.Member) (i : Nat) (h : i < e.val.length) :
    (msOf d e).drop i = mS d e.val[i] :: (msOf d e).drop (i + 1) := by
  simp only [msOf]
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

theorem lastOnes_drop (d : alloc.vec.Vec json.JsonNode) (e : alloc.vec.Vec json.Member) (i : Nat) (h : i < e.val.length) :
    lastOnes ((msOf d e).drop i) =
      if (∀ q (hq : q < e.val.length), i < q → bs e.val[q].key ≠ bs e.val[i].key)
      then mS d e.val[i] :: lastOnes ((msOf d e).drop (i + 1)) else lastOnes ((msOf d e).drop (i + 1)) := by
  rw [msOf_drop _ _ _ h, lastOnes]
  have : ((msOf d e).drop (i + 1)).any (fun m' => m'.1 == (mS d e.val[i]).1) = true ↔
      ¬ ∀ q (hq : q < e.val.length), i < q → bs e.val[q].key ≠ bs e.val[i].key := by
    simp only [List.any_eq_true, beq_iff_eq, not_forall, not_not, exists_prop]
    constructor
    · rintro ⟨m, hm, hk⟩
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
      simp only [List.length_drop, msOf, List.length_map] at hq
      refine ⟨i + 1 + q, by omega, by omega, ?_⟩
      simpa [msOf, mS] using hk
    · rintro ⟨q, hq, hiq, hk⟩
      refine ⟨mS d e.val[q], ?_, by simpa [mS] using hk⟩
      rw [List.mem_iff_getElem]
      exact ⟨q - (i + 1), by simp [msOf]; omega, by simp [msOf]; congr 2; omega⟩
  by_cases hc : ∀ q (hq : q < e.val.length), i < q → bs e.val[q].key ≠ bs e.val[i].key
  · rw [if_pos hc, if_neg (by rw [this]; exact not_not_intro hc)]
  · rw [if_neg hc, if_pos (this.mpr hc)]

@[step]
theorem collect_extension_names_loop_spec (d : alloc.vec.Vec json.JsonNode) (e : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (i : Usize) (hw : nodesWf d.val) (hi : i.val ≤ e.val.length)
    (hb : ext.val.length + (lastOnes ((msOf d e).drop i.val)).length ≤ Usize.max) :
    read.access.collect_extension_names_loop d e ext i ⦃ p => match p.1 with
      | .Ok _ => (lastOnes ((msOf d e).drop i.val)).all (fun m => isObj m.2) = true ∧
          bss p.2 = bss ext ++ (lastOnes ((msOf d e).drop i.val)).map (·.1)
      | .Err _ => (lastOnes ((msOf d e).drop i.val)).all (fun m => isObj m.2) = false ⦄ := by
  unfold read.access.collect_extension_names_loop
  step*
  all_goals subst_vars
  all_goals try simp only at o_post
  all_goals first
    | (simp [vec_new_val]; done)
    | (have hd : (msOf d e).drop i.val = [] := by simp only [msOf, List.drop_eq_nil_iff, List.length_map]; scalar_tac
       simp [hd, lastOnes])
    | (have hlt : i.val < e.val.length := by scalar_tac
       rw [lastOnes_drop _ _ _ hlt] at *
       have hc := b_post.mp rfl
       rw [if_pos hc] at *
       first
         | (rw [List.all_cons, mS, treeN_oob o_post]; rfl)
         | (rw [List.all_cons, mS, treeN_node hw o_post]; simp [nodeS, isObj, json.number.Number.toS]; done)
         | (simp only [List.length_cons] at hb; scalar_tac)
         | (simp_all [bss, bs, mS, treeN_node hw o_post, nodeS, isObj]))
    | (have hlt : i.val < e.val.length := by scalar_tac
       rw [lastOnes_drop _ _ _ hlt] at *
       have hc : ¬ _ := fun h => absurd (b_post.mpr h) (by simp_all)
       rw [if_neg hc] at *
       simp_all)
termination_by e.val.length - i.val
decreasing_by all_goals scalar_decr_tac

def szO : Option JsonS → Nat
  | none => 0
  | some v => jsonSize v

theorem lastOnes_length (ms : Members) : (lastOnes ms).length ≤ ms.length := by
  induction ms with
  | nil => simp [lastOnes]
  | cons m ms ih => rw [lastOnes]; split <;> simp <;> omega

theorem jsonSize_pos (v : JsonS) : 1 ≤ jsonSize v := by
  cases v <;> simp [jsonSize] <;> omega

theorem length_le_memSize (ms : Members) : ms.length ≤ memSize ms := by
  induction ms with
  | nil => simp [memSize]
  | cons m ms ih => simp [memSize]; have := jsonSize_pos m.2; omega

theorem opt_obj_some {ms : Members} {k : Bytes} {m : Members} (h : opt ms k objS = some (some m)) :
    lookup ms k = some (.obj m) := by
  unfold opt at h
  split at h
  · cases h
  · rename_i v hv
    cases v <;> simp_all [objS]

@[step]
theorem check_extensions_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "extensions")) ≤ Usize.max) :
    read.access.check_extensions d o ext ⦃ p => match p.1 with
      | .Ok _ => ∃ e, extsS (msOf d o) = some e ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "extensions"))
      | .Err _ => extsS (msOf d o) = none ⦄ := by
  unfold read.access.check_extensions
  step*
  all_goals subst_vars
  all_goals keys_norm
  all_goals simp only [resO, Option.map_some, Option.map_none] at r_post
  · exact ⟨[], by simp [extsS, r_post], by simp, by simp⟩
  · have hl := opt_obj_some r_post
    rw [hl] at hb
    have := lastOnes_length (msOf d e)
    have := length_le_memSize (msOf d e)
    simp only [szO, jsonSize, show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at hb this ⊢
    omega
  · have hl := opt_obj_some r_post
    simp only [List.drop_zero] at p_post
    obtain ⟨r1, ext1⟩ := p
    cases r1 <;> simp only at p_post ⊢
    · refine ⟨_, ?_, p_post.2, ?_⟩
      · simp [extsS, r_post, p_post.1]
      · rw [hl, bss_len p_post.2]
        have := lastOnes_length (msOf d e)
        have := length_le_memSize (msOf d e)
        simp only [szO, jsonSize, List.length_map]; omega
    · simp [extsS, r_post, p_post]
  · simp [extsS, r_post]

@[step]
theorem check_child_of_root_spec (d : alloc.vec.Vec json.JsonNode) (o : alloc.vec.Vec json.Member)
    (ext : alloc.vec.Vec (alloc.vec.Vec U8)) (hw : nodesWf d.val)
    (hb : ext.val.length + szO (lookup (msOf d o) (key "extensions")) ≤ Usize.max) :
    read.access.check_child_of_root d o ext ⦃ p => match p.1 with
      | .Ok _ => ∃ e, childS (msOf d o) = some e ∧ bss p.2 = bss ext ++ e ∧
          p.2.val.length ≤ ext.val.length + szO (lookup (msOf d o) (key "extensions"))
      | .Err _ => childS (msOf d o) = none ⦄ := by
  unfold read.access.check_child_of_root
  step*
  all_goals subst_vars
  all_goals keys_norm
  · obtain ⟨r1, ext1⟩ := p
    cases r1 <;> simp only at p_post ⊢ <;> simp_all [childS, resO]
  · simp_all [childS, resO]

end LoadGltf
