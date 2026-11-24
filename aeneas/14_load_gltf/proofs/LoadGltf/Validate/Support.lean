import LoadGltf.Common

open Aeneas Aeneas.Std Result

namespace LoadGltf

/-! ## V.1 supported、A1、A2、C1 -/

def knownComponentType (ct : U64) : Prop :=
  ct.val = 5120 ∨ ct.val = 5121 ∨ ct.val = 5122 ∨ ct.val = 5123 ∨ ct.val = 5125 ∨ ct.val = 5126

def minVersionSupported (v : Option (U64 × U64)) : Prop :=
  ∀ a b, v = some (a, b) → a.val < 2 ∨ (a.val = 2 ∧ b.val = 0)

def componentTypesKnown (g : model.Gltf) : Prop := ∀ a ∈ g.accessors.val, knownComponentType a.component_type

def modesKnown (g : model.Gltf) : Prop := ∀ m ∈ g.meshes.val, ∀ p ∈ m.primitives.val, p.mode.val ≤ 6

-- supported(g)
-- MUST-011: 対応しない minVersion は読み込まない
def supportedSpec (g : model.Gltf) : Prop :=
  g.version_major.val = 2 ∧ minVersionSupported g.min_version ∧ g.extensions_required.val = [] ∧
  componentTypesKnown g ∧ modesKnown g

@[step]
theorem known_component_type_spec (ct : U64) :
    validate.support.known_component_type ct ⦃ r => r = true ↔ knownComponentType ct ⦄ := by
  unfold validate.support.known_component_type knownComponentType
  step_auto

@[step]
theorem component_types_known_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.accessors.val.length) :
    validate.support.component_types_known_loop g i ⦃ r => r = true ↔
      forallFrom g.accessors.val i.val (fun x => knownComponentType (x).component_type) ⦄ := by
  unfold validate.support.component_types_known_loop
  loop_auto
termination_by g.accessors.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem component_types_known_spec (g : model.Gltf) :
    validate.support.component_types_known g ⦃ r => r = true ↔ componentTypesKnown g ⦄ := by
  unfold validate.support.component_types_known componentTypesKnown
  step*
  simp_all [forallFrom_zero]

@[step]
theorem primitive_modes_known_loop_spec (m : model.Mesh) (j : Usize) (hi : j.val ≤ m.primitives.val.length) :
    validate.support.primitive_modes_known_loop m j ⦃ r => r = true ↔
      forallFrom m.primitives.val j.val (fun x => (x).mode.val ≤ 6) ⦄ := by
  unfold validate.support.primitive_modes_known_loop
  loop_auto
termination_by m.primitives.val.length - j.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem primitive_modes_known_spec (m : model.Mesh) :
    validate.support.primitive_modes_known m ⦃ r => r = true ↔ ∀ x ∈ m.primitives.val, (x).mode.val ≤ 6 ⦄ := by
  unfold validate.support.primitive_modes_known
  step*
  simp_all [forallFrom_zero]

@[step]
theorem modes_known_loop_spec (g : model.Gltf) (i : Usize) (hi : i.val ≤ g.meshes.val.length) :
    validate.support.modes_known_loop g i ⦃ r => r = true ↔
      forallFrom g.meshes.val i.val (fun x => ∀ p ∈ (x).primitives.val, p.mode.val ≤ 6) ⦄ := by
  unfold validate.support.modes_known_loop
  loop_auto
termination_by g.meshes.val.length - i.val
decreasing_by all_goals scalar_decr_tac

@[step]
theorem modes_known_spec (g : model.Gltf) :
    validate.support.modes_known g ⦃ r => r = true ↔ modesKnown g ⦄ := by
  unfold validate.support.modes_known modesKnown
  step*
  simp_all [forallFrom_zero]

@[step]
theorem min_version_supported_spec (v : Option (U64 × U64)) :
    validate.support.min_version_supported v ⦃ r => r = true ↔ minVersionSupported v ⦄ := by
  unfold validate.support.min_version_supported minVersionSupported
  rcases v with _ | ⟨a, b⟩ <;> step_auto

-- MUST-011: 対応しない minVersion は読み込まない
/-- supported(g) -/
@[step]
theorem supported_spec (g : model.Gltf) : validate.support.supported g ⦃ r => r = true ↔ supportedSpec g ⦄ := by
  unfold validate.support.supported supportedSpec
  step*
  simp_all [UScalar.eq_equiv]

end LoadGltf
