import Gimle.Forseti.Examples.Oscillator
import Gimle.Asgard.Examples.LinearDiagram

/-! Energy bounds for every trajectory of the compiled initial-value problem.
The existing all-real energy theorem is applied only to its explicit solution;
forward-domain uniqueness transports its conclusion to the circuit trajectory. -/
namespace Gimle.Forseti.LinearOscillator
open Gimle.Asgard

/-- Any initial energy sublevel is invariant from the declared start onward. -/
theorem energyBound (start x0 y0 bound : ℝ) (state : Dynamics.Signal 2)
    (realized : (Examples.LinearOscillator.problem start x0 y0).Realizes state)
    (initial : Oscillator.energy x0 y0 ≤ bound) (t : ℝ) (forward : start ≤ t) :
    0 ≤ Oscillator.energy (state t 0) (state t 1) ∧
      Oscillator.energy (state t 0) (state t 1) ≤ bound := by
  rw [Examples.LinearOscillator.realization_eq_explicit start x0 y0 state realized t forward]
  apply Oscillator.energyBound (Oscillator.explicitSolution x0 y0) bound _
    (t - start) (sub_nonneg.mpr forward)
  simpa [Oscillator.position, Oscillator.velocity] using initial

/-- The generated demo starts at (1,0) and has energy between zero and two. -/
theorem demoBound (state : Dynamics.Signal 2) (realized : Examples.LinearOscillator.demo.problem.Realizes state)
    (t : ℝ) (forward : 0 ≤ t) :
    0 ≤ Oscillator.energy (state t 0) (state t 1) ∧
      Oscillator.energy (state t 0) (state t 1) ≤ 2 := by
  rw [Examples.LinearOscillator.demo_problem] at realized
  apply energyBound 0 1 0 2 state realized _ t forward
  norm_num [Oscillator.energyFormula]

#print axioms energyBound
#print axioms demoBound
end Gimle.Forseti.LinearOscillator
