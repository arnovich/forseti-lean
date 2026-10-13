import Gimle.Forseti.Examples.AIFDriftPilot

namespace Gimle.Forseti.Tests.AIFDrift
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.Examples

-- Keep the certificate but change one entry of its claimed target.
def changedCoefficient : QMatrix 5 := fun i j =>
  if i = 0 ∧ j = 0 then AIFDriftNegative.coefficients 0 0 i j + 1
  else AIFDriftNegative.coefficients 0 0 i j

set_option maxRecDepth 100000 in
example : ¬ AIFDriftNegative.cert_0_0.Represents changedCoefficient := by
  unfold WeightedSquares.Represents
  decide +kernel

-- Signed square weights cannot acquire authority from a valid source family.
def negativeWeight : WeightedSquares 5 :=
  { AIFDriftNegative.cert_0_0 with weight := fun _ => -1 }

set_option maxRecDepth 100000 in
example : ¬ negativeWeight.Represents (AIFDriftNegative.coefficients 0 0) := by
  unfold WeightedSquares.Represents
  decide +kernel

-- The closed physical endpoint is covered, without a strict-interior shortcut.
example (e : Fin 4 → ℝ) (he : e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200)) :
    AIFDriftPilot.energyRate 0 0 e ≤
      (1/100) * (1/40000 - matrixForm (AIFDriftModel.metric 0) e) - 1/16000000 := by
  simpa using AIFDriftPilot.drift_bound_physical (33/5) 8 e
    (by norm_num) (by norm_num) he

end Gimle.Forseti.Tests.AIFDrift
