module

public import Gimle.Forseti.Examples.LoadedSAIFExistence

/-! Existence includes the zero-capacity phase, exact denominator guards, and
uniqueness across the load jump without imposing a two-sided derivative there. -/

@[expose] public section

namespace Gimle.Forseti.Tests.LoadedSAIFExistence
open Gimle.Forseti.Examples.LoadedSAIFModel
open Gimle.Forseti.Examples.LoadedSAIFExistence

theorem physical_switched_solution : ∃ state : ℝ → State,
    Switched state ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 30, state t 4 = 0) ∧
    (∀ t ∈ Set.Icc (30 : ℝ) 100, 0 ≤ state t 4 ∧ state t 4 ≤ 2) := by
  obtain ⟨state, hs, hb, ha⟩ := switched_exists
  exact ⟨state, hs, fun t ht => capacity_zero (hb t ht), fun t ht => ha t ht 4⟩

example (L : ℝ) (x : State) (hx : Physical L x) :
    kappa ≤ kappa + x 3 ∧ control x ≤ 4 :=
  ⟨denominator_lower (hx 3).1, control_cap (hx 3).1⟩

example {state other : ℝ → State} (hs : Switched state) (ho : Switched other)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ state t 3)
    (hq : ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ other t 3) :
    Set.EqOn state other (Set.Icc (0 : ℝ) 100) :=
  switched_unique hs ho (fun t ht => denominator_pos (hp t ht))
    (fun t ht => denominator_pos (hq t ht))

example (x : State) (hx : x 3 = -kappa) : ¬ Physical 0 x := by
  intro hp
  have h := (hp 3).1
  rw [hx] at h
  linarith [kappa_pos]

#print axioms physical_switched_solution
end Gimle.Forseti.Tests.LoadedSAIFExistence
