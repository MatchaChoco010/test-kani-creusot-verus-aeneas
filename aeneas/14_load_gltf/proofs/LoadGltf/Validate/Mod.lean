import LoadGltf.Validate.Support
import LoadGltf.Validate.Hierarchy
import LoadGltf.Validate.Animation
import LoadGltf.Validate.Data
import LoadGltf.Validate.Resource

open Aeneas Aeneas.Std Result

namespace LoadGltf

-- A1: min_version ≤ (version_major, version_minor)
-- MUST-012: minVersion ≤ version
def assetOk (g : model.Gltf) : Prop :=
  ∀ a b, g.min_version = some (a, b) →
    a.val < g.version_major.val ∨ (a.val = g.version_major.val ∧ b.val ≤ g.version_minor.val)

-- A2
-- MUST-153, MUST-154, MUST-156, MUST-157: 拡張の列挙・重複なし・包含
def extensionsOk (g : model.Gltf) : Prop :=
  (g.extensions_used.val.map (·.val)).Nodup ∧ (g.extensions_required.val.map (·.val)).Nodup ∧
  bytesSubset g.extensions_required.val g.extensions_used.val ∧
  bytesSubset g.extensions_present.val g.extensions_used.val

-- C1
-- MUST-133, MUST-134: type に対応する perspective / orthographic がある
def camerasOk (g : model.Gltf) : Prop :=
  ∀ c ∈ g.cameras.val, (c.kind.val = 1 → c.has_perspective = true) ∧ (c.kind.val = 2 → c.has_orthographic = true)

-- MUST-012: minVersion ≤ version
@[step]
theorem asset_ok_spec (g : model.Gltf) : validate.asset_ok g ⦃ r => r = true ↔ assetOk g ⦄ := by
  unfold validate.asset_ok assetOk
  rcases hm : g.min_version with _ | ⟨a, b⟩ <;> step_auto

-- MUST-153, MUST-154, MUST-156, MUST-157: 拡張の列挙・重複なし・包含
@[step]
theorem extensions_ok_spec (g : model.Gltf) : validate.extensions_ok g ⦃ r => r = true ↔ extensionsOk g ⦄ := by
  unfold validate.extensions_ok extensionsOk
  step*

@[step]
theorem cameras_ok_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.cameras.val.length) :
    validate.cameras_ok_loop g i ⦃ r => r = true ↔
      forallFrom g.cameras.val i.val (fun x => ((x).kind.val = 1 → (x).has_perspective = true) ∧ ((x).kind.val = 2 → (x).has_orthographic = true)) ⦄ := by
  unfold validate.cameras_ok_loop
  loop_auto [camera_consts, UScalar.eq_equiv]
termination_by g.cameras.val.length - i.val
decreasing_by all_goals scalar_decr_tac

-- MUST-133, MUST-134: type に対応する perspective / orthographic がある
@[step]
theorem cameras_ok_spec (g : model.Gltf) :
    validate.cameras_ok g ⦃ r => r = true ↔ camerasOk g ⦄ := by
  unfold validate.cameras_ok camerasOk
  step*
  simp_all [forallFrom_zero]

/-! ## V.2 rules_ok と V2 (T2) validate -/

-- rules_ok(g): A1, A2, H1–H4, S1, S2, M1–M5, AN1, AN2, B1–B4, AC1–AC3, BU1, IM1, C1
def rulesSpec (g : model.Gltf) : Prop :=
  assetOk g ∧ extensionsOk g ∧ graphSpec g ∧ meshesOk g ∧ animationsOk g ∧ bufferViewsOk g ∧
  accessorsOk g ∧ buffersOk g ∧ imagesOk g ∧ camerasOk g

-- valid(g) = refs_ok ∧ supported ∧ rules_ok
def valid (g : model.Gltf) : Prop := refsOk g ∧ supportedSpec g ∧ rulesSpec g

/-- rules_ok (refs_ok の下で) -/
@[step]
theorem rules_ok_spec (g : model.Gltf) (hr : refsOk g) : validate.rules_ok g ⦃ r => r = true ↔ rulesSpec g ⦄ := by
  unfold validate.rules_ok rulesSpec
  have hr' := hr
  obtain ⟨-, -, hn, hm, -, -, -, -, -, hs, ha⟩ := hr'
  rw [← graphOk_iff g hs]
  step*

/-- T2: validate(g) = Ok ⇔ valid(g)。Err Unsupported は refs_ok ∧ ¬supported のときだけ、
Err Invalid は ¬refs_ok ∨ (supported ∧ ¬rules_ok) のときだけ。Glb/Json は返さない -/
@[step]
theorem validate_spec (g : model.Gltf) :
    validate.validate g ⦃ r => (r = .Ok () ↔ valid g) ∧
      (r = .Err .Unsupported → refsOk g ∧ ¬ supportedSpec g) ∧
      (r = .Err .Invalid → ¬ refsOk g ∨ (supportedSpec g ∧ ¬ rulesSpec g)) ∧
      r ≠ .Err .Glb ∧ r ≠ .Err .Json ⦄ := by
  unfold validate.validate valid
  step*
  all_goals simp_all

end LoadGltf
