import Gimle.Forseti.Examples.LoadedSAIFModel

/-! Exact regression checks for the loaded rational feedback model. -/
namespace Gimle.Forseti.Tests.LoadedSAIFModel
open Gimle.Forseti.Examples.LoadedSAIFModel

example : field 0 0 = ![alpha, 0, 2, 0, 0] := by
  ext i
  fin_cases i <;> norm_num [field, binding, Gimle.Forseti.Examples.LoadedSAIFModel.control, alpha, kappa, dilution]

example (x : State) (h : 0 ≤ x 3) : kappa ≤ kappa + x 3 := by
  exact denominator_lower h

example : ¬ 0 < kappa + (-kappa) := by simp

example (x : State) (h : 0 ≤ x 3) : control x = alpha / (1 + x 3 / kappa) :=
  control_eq_saturating h

example (L : ℝ) (x : State) :
    field L x 1 + field L x 4 = x 0 - x 1 - x 4 / 5 := by
  exact output_balance L x

end Gimle.Forseti.Tests.LoadedSAIFModel
