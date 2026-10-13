import Gimle.Forseti.Examples.AIFGlobalSolution

/-! Regressions for the full forward domain and agreement at piece boundaries. -/
namespace Gimle.Forseti.Tests.AIFGlobalSolution
open Gimle.Forseti.Examples AIFGlobalSolution AIFPhysicalCoordinates

theorem zero_parameter_start : solution 0 le_rfl 0 = 0 := solution_start 0 le_rfl

/-- A derivative at the initial time is within the entire forward domain. -/
theorem initial_derivative (eta : ℝ) (heta : 0 ≤ eta) (i : Fin 4) :
    HasDerivWithinAt (fun t => solution eta heta t i)
      (physicalField eta 0 i) (Set.Ici 0) 0 := by
  simpa only [solution_start] using solution_derivative eta heta 0 le_rfl i

/-- The ceiling-selected piece agrees with a horizon ending at this integer time. -/
theorem integer_join (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ) :
    solution eta heta (m : ℝ) = piece eta heta m (m : ℝ) :=
  solution_eq_piece eta heta ⟨Nat.cast_nonneg m, le_rfl⟩

theorem all_species_at_100 (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) 12) :
    ∀ i, 0 ≤ solution eta (by linarith [heta.1]) 100 i := by
  exact solution_nonnegative eta (by linarith [heta.1]) 100 (by norm_num)

/-- Any competing realization of the same physical ODE agrees at the safety horizon. -/
theorem competing_solution_at_100 (eta : ℝ) (heta : 0 ≤ eta)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Ici 0, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Ici 0) t) : state 100 = solution eta heta 100 :=
  solution_unique eta heta state initial derivative (by norm_num)

#print axioms competing_solution_at_100
#print axioms zero_parameter_start
#print axioms initial_derivative
#print axioms integer_join
#print axioms all_species_at_100
end Gimle.Forseti.Tests.AIFGlobalSolution
