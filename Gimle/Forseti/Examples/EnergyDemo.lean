import Gimle.Forseti.Examples.EnergyDemoData
import Gimle.Asgard.Examples.EnergyDemo

/-! Property bounds for the Asgard energy circuit E(x,y) = (x+y)² + (x-y)². -/
namespace Gimle.Forseti.EnergyDemo

open EnergyDemoData

export Gimle.Asgard.EnergyDemo (duplicate interleave difference sumAndDifference
  square squareBoth energy energyIdentity)

theorem matchesAsgardExport : energy = circuit := rfl

theorem unitSquareBound (x : ℝ) (lower : -1 ≤ x) (upper : x ≤ 1) :
    x^2 ≤ 1 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ x + 1) (by linarith : 0 ≤ 1 - x)]

-- The main Hoare theorem: both inputs in [-1,1] imply output in [0,4].
theorem energyBound : ExactHoare precondition energy postcondition := by
  intro input hypothesis
  have bounds : -1 ≤ input 0 ∧ input 0 ≤ 1 ∧ -1 ≤ input 1 ∧ input 1 ≤ 1 := by
    simpa [precondition, and_assoc, and_left_comm, and_comm] using hypothesis
  have xBound := unitSquareBound (input 0) bounds.1 bounds.2.1
  have yBound := unitSquareBound (input 1) bounds.2.2.1 bounds.2.2.2
  simp [postcondition, energyIdentity]
  constructor <;> nlinarith [sq_nonneg (input 0), sq_nonneg (input 1)]

-- Both endpoints are attained by inputs satisfying the original precondition.
theorem minimumAttained :
    precondition.holds ![0, 0] ∧ energy.run ![0, 0] 0 = 0 := by
  norm_num [precondition, energyIdentity]

theorem maximumAttained :
    precondition.holds ![1, 1] ∧ energy.run ![1, 1] 0 = 4 := by
  norm_num [precondition, energyIdentity]

-- No smaller uniform upper bound works on this input domain.
theorem upperBoundIsSharp (bound : ℝ)
    (valid : ∀ input, precondition.holds input → energy.run input 0 ≤ bound) :
    4 ≤ bound := by
  have atCorner := valid ![1, 1] maximumAttained.1
  simpa [maximumAttained.2] using atCorner

theorem lowerBoundIsSharp (bound : ℝ)
    (valid : ∀ input, precondition.holds input → bound ≤ energy.run input 0) :
    bound ≤ 0 := by
  have atOrigin := valid ![0, 0] minimumAttained.1
  simpa [minimumAttained.2] using atOrigin

#print axioms energyIdentity
#print axioms energyBound
#print axioms upperBoundIsSharp
#print axioms lowerBoundIsSharp

end Gimle.Forseti.EnergyDemo
