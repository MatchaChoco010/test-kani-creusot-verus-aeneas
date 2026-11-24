import Aeneas
import Contains.Code.Funs

open Aeneas Aeneas.Std Result
open Contains

@[step]
theorem contains_loop_spec {T : Type} (inst : core.cmp.PartialEq T T) (v : Slice T) (x : T)
    (h0 : ∀ y ∈ v.val, ∃ c, inst.eq y x = ok c)
    (i : Usize) (h1 : i.val ≤ v.length) (h2 : ∀ y ∈ v.val.take i.val, inst.eq y x = ok false) :
    contains_loop inst v x i ⦃ r => r = true ↔ ∃ y ∈ v.val, inst.eq y x = ok true ⦄ := by
  unfold contains_loop
  step*
  · have hmem : t ∈ v.val := by rw [t_post]; exact List.getElem_mem _
    obtain ⟨c, hc⟩ := h0 t hmem
    rw [hc]
    cases c
    · simp only [bind_ok, Bool.false_eq_true, ite_false]
      step*
      rw [i2_post, List.take_succ_eq_append_getElem (by agrind)]
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact h2 y hy
      · rw [List.mem_singleton.mp hy, ← t_post, hc]
    · simp only [bind_ok, ite_true, WP.spec_ok, true_iff]
      exact ⟨t, hmem, hc⟩
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro y hy h
    have := h2 y (by rw [List.take_of_length_le (by agrind)]; exact hy)
    rw [h] at this
    simp at this
termination_by v.length - i.val
decreasing_by scalar_decr_tac

theorem contains_spec {T : Type} (inst : core.cmp.PartialEq T T) (v : Slice T) (x : T)
    (h0 : ∀ y ∈ v.val, ∃ c, inst.eq y x = ok c) :
    contains inst v x ⦃ r => r = true ↔ ∃ y ∈ v.val, inst.eq y x = ok true ⦄ := by
  unfold contains
  step*
  simp

theorem vertex_eq_eq (a b : Vertex) :
    ∃ c, Vertex.Insts.CoreCmpPartialEqVertex.eq a b = ok c ∧ (c = true ↔ a = b) := by
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, by_⟩ := b
  unfold Vertex.Insts.CoreCmpPartialEqVertex.eq
  split <;> simp_all

theorem contains_vertex_spec (v : Slice Vertex) (x : Vertex) :
    contains_vertex v x ⦃ r => r = true ↔ x ∈ v.val ⦄ := by
  unfold contains_vertex
  apply WP.spec_mono (contains_spec _ v x (fun y _ => (vertex_eq_eq y x).imp fun _ h => h.1))
  intro r hr
  rw [hr]
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨c, hc, hce⟩ := vertex_eq_eq y x
    have hct : (ok true : Result Bool) = ok c := he.symm.trans hc
    simp at hct
    exact hce.mp hct ▸ hy
  · intro hx
    obtain ⟨c, hc, hce⟩ := vertex_eq_eq x x
    exact ⟨x, hx, hc.trans (by rw [hce.mpr rfl])⟩
