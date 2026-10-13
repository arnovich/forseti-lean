import Gimle.Forseti.Examples.EnergyOptimization
import Gimle.Forseti.Examples.OscillatorData
import Gimle.Asgard.Examples.Oscillator
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Energy safety for x′ = y, y′ = -x - 2y.
The circuit vector field, trajectory relation and explicit solutions come from
Asgard. Here we prove E′ = -8y² ≤ 0 and the resulting forward energy bound. -/
namespace Gimle.Forseti.Oscillator

export Gimle.Asgard.Oscillator (vectorField vectorFieldEquations Solves solvesEquations
  position velocity explicitSolution initialState)

theorem matchesAsgard : vectorField = OscillatorData.vectorField := rfl

-- This reuses the previously verified energy circuit, including its exact formula.
noncomputable def energy (x y : ℝ) : ℝ :=
  EnergyOptimization.optimized.run ![x, y] 0

theorem energyFormula (x y : ℝ) : energy x y = 2*(x^2+y^2) := by
  simp [energy, EnergyOptimization.optimizedIdentity]

-- Chain rule plus the two circuit equations cancel the cross terms.
theorem energyDerivative {x y : ℝ → ℝ} (solution : Solves x y) (t : ℝ) :
    HasDerivAt (fun s => energy (x s) (y s)) (-8*(y t)^2) t := by
  obtain ⟨hx, hy⟩ := (solvesEquations x y).mp solution t
  have derivative := ((hx.mul hx).add (hy.mul hy)).const_mul 2
  simp only [energyFormula, pow_two]
  convert! derivative using 1
  ring

-- The mean value theorem turns the local derivative bound into a global order bound.
theorem energyNonincreasing {x y : ℝ → ℝ} (solution : Solves x y) :
    Antitone (fun t => energy (x t) (y t)) := by
  apply antitone_of_hasDerivAt_nonpos (energyDerivative solution)
  intro t
  change -8*(y t)^2 ≤ (0 : ℝ)
  nlinarith [sq_nonneg (y t)]

-- A trajectory starting inside any energy sublevel stays inside it for all t ≥ 0.
theorem energyBound {x y : ℝ → ℝ} (solution : Solves x y)
    (bound : ℝ) (initial : energy (x 0) (y 0) ≤ bound) (t : ℝ) (forward : 0 ≤ t) :
    0 ≤ energy (x t) (y t) ∧ energy (x t) (y t) ≤ bound := by
  constructor
  · rw [energyFormula]
    positivity
  · exact le_trans (energyNonincreasing solution forward) initial

-- The nontrivial demo starts at (1,0), so E(0)=2 and E(t) remains in [0,2].
theorem demoBound (t : ℝ) (forward : 0 ≤ t) :
    0 ≤ energy (position 1 0 t) (velocity 1 0 t) ∧
      energy (position 1 0 t) (velocity 1 0 t) ≤ 2 := by
  apply energyBound (explicitSolution 1 0) 2 _ t forward
  norm_num [position, velocity, energyFormula]

#print axioms matchesAsgard
#print axioms energyDerivative
#print axioms energyNonincreasing
#print axioms energyBound
#print axioms explicitSolution
#print axioms initialState
#print axioms demoBound

end Gimle.Forseti.Oscillator
