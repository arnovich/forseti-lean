module

public import Gimle.Forseti.Examples.LoadedSAIFResources

/-! Integral-budget regressions, including the necessity of response-band coverage. -/

@[expose] public section

namespace Gimle.Forseti.Tests.LoadedSAIFResources
open Set Gimle.Forseti.Examples.LoadedSAIFResources

/-- A constant in-band output satisfies the four-segment integral estimate. -/
theorem constant_output : (∫ _t in (0 : ℝ)..100, (2 : ℝ)) ≤ 1112 / 5 := by
  apply output_integral_bound continuousOn_const
  · intro t ht; norm_num
  · intro t ht; norm_num
  · intro t ht; norm_num

/-- The peak cap alone cannot replace the two response-band premises. -/
theorem peak_alone_insufficient :
    ¬ ((∫ _t in (0 : ℝ)..100, (13 / 5 : ℝ)) ≤ 1112 / 5) := by
  norm_num

/-- The exact balance-derived bounds fit strictly inside both declared budgets. -/
theorem budget_margins :
    (25776129 / 100000 : ℝ) < 270 ∧ (2112 / 5 : ℝ) < 500 := by
  norm_num

#check resource_budgets
#print axioms constant_output
#print axioms peak_alone_insufficient
end Gimle.Forseti.Tests.LoadedSAIFResources
