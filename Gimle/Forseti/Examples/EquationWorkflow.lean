import Gimle.Forseti
import Gimle.Forseti.Examples.LinearOscillator
import Gimle.Asgard.Examples.EquationModels

/-! Properties of the exact circuits compiled from the shared Lean equations.
Open PolynomialCompiler.lean for the editable source and EquationModels.lean
for projection, coefficient extraction and continuous feedback compilation. -/
namespace Gimle.Forseti.EquationWorkflow
open Gimle.Asgard
open Examples.EquationModels

def inputBox : Predicate 2 := ⟨fun x => -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1⟩
def energyRange : Predicate 1 := ⟨fun y => 0 ≤ y 0 ∧ y 0 ≤ 4⟩

/-- Every point of the input square maps into [0,4] under the equation-compiled circuit. -/
theorem energyBound : ExactHoare inputBox energy energyRange := by
  intro x h
  rcases h with ⟨hx0, hx1, hy0, hy1⟩
  have hx : x 0 ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x 0 + 1) (by linarith : 0 ≤ 1 - x 0)]
  have hy : x 1 ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x 1 + 1) (by linarith : 0 ≤ 1 - x 1)]
  change 0 ≤ energy.run x 0 ∧ energy.run x 0 ≤ 4
  rw [energy_formula]
  constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- The bound four is attained by the compiled circuit, so a smaller bound fails. -/
theorem energySharp (bound : ℝ)
    (h : ∀ x, inputBox.holds x → energy.run x 0 ≤ bound) : 4 ≤ bound := by
  have h1 := h ![1, 1] (by norm_num [inputBox])
  norm_num [energy_formula] at h1 ⊢
  exact h1

/-- Starting from the model's (1,0), every exact continuous realization keeps
the same compiled energy circuit's value in [0,2] for all t≥0. This is not an
assertion about the values returned by a numerical Euler run. -/
theorem oscillatorEnergyBound (state : Dynamics.Signal 2)
    (realized : Realizes state) (t : ℝ) (forward : 0 ≤ t) :
    0 ≤ energy.run (state t) 0 ∧ energy.run (state t) 0 ≤ 2 := by
  have linear := (realizes_iff state).mp realized
  rw [problem_eq] at linear
  have h := LinearOscillator.energyBound 0 1 0 2 state linear
    (by norm_num [Oscillator.energyFormula]) t forward
  simpa only [energy_formula, Oscillator.energyFormula, mul_add] using h

theorem oscillatorExists : ∃ state, Realizes state := exists_realization

#print axioms energyBound
#print axioms energySharp
#print axioms oscillatorEnergyBound
#print axioms oscillatorExists
end Gimle.Forseti.EquationWorkflow
