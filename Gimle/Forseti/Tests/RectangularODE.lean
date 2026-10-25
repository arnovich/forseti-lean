import Gimle.Forseti.RectangularODE

/-! Degenerate coordinates and outward faces are explicit rectangle regressions. -/
namespace Gimle.Forseti.Tests.RectangularODE
open Gimle.Forseti.RectangularODE

def singleton : Rectangle 1 where
  lower := 0
  upper := 0
  ordered := fun _ => le_rfl

theorem zero_solution_exists :
    ∃ state : ℝ → Fin 1 → ℝ, state 0 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, state t = 0 := by
  have hl : LipschitzOnWith 0 (fun _ : Fin 1 → ℝ => (0 : Fin 1 → ℝ)) singleton.box :=
    (LipschitzWith.const _).lipschitzOnWith
  have hin : singleton.Inward (fun _ => 0) := by
    intro x hx i
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  obtain ⟨state, hs, hp, hd⟩ := singleton.exists_solution hl hin 0 0
    (by constructor <;> intro i <;> exact le_rfl) 1
  refine ⟨state, hs, ?_⟩
  intro t ht
  have h := hp t (by simpa using ht)
  funext i
  exact le_antisymm (h.2 i) (h.1 i)

theorem outward_rejected : ¬ singleton.Inward (fun _ => 1) := by
  intro h
  have hh := (h 0 (by constructor <;> intro i <;> exact le_rfl) 0).2 rfl
  norm_num at hh

#print axioms zero_solution_exists
#print axioms outward_rejected
end Gimle.Forseti.Tests.RectangularODE
