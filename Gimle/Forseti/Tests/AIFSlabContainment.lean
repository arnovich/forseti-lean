import Gimle.Forseti.Examples.AIFSlabContainment
import Gimle.Forseti.Tests.AIFSlab

/-! Sharp closed-boundary and invalid-margin regressions for error containment. -/
namespace Gimle.Forseti.Tests.AIFSlabContainment
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.Examples.AIFSlabModel Gimle.Forseti.Examples.AIFSlabContainment

def sharp : Slab := { AIFSlab.sample (1/200) 8 with
  startMetric := fun i j => if i = 2 ∧ j = 2 then 1/9 else 0
  endMetric := fun i j => if i = 2 ∧ j = 2 then 1/9 else 0
  startMetricSlope := 0
  endMetricSlope := 0 }

theorem sharp_margin_zero (s : ℝ) : errorMargin sharp s = 0 := by
  ext i j
  simp [errorMargin, metric, hermite, sharp]
  split_ifs <;> norm_num

example (s : ℝ) (e : Fin 4 → ℝ)
    (he : matrixForm (metric sharp s) e ≤ 1/40000) :
    e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200) := by
  apply error_contained sharp s e _ he
  simp [sharp_margin_zero, matrixForm]

example (s : ℝ) :
    matrixForm (metric sharp s) ![0, 0, 3/200, 0] = 1/40000 ∧
    matrixForm (metric sharp s) ![0, 0, -3/200, 0] = 1/40000 := by
  norm_num [matrixForm, metric, hermite, sharp, Fin.sum_univ_succ]

example (s : ℝ) :
    ¬ matrixForm (metric sharp s) ![0, 0, 1/50, 0] ≤ 1/40000 := by
  norm_num [matrixForm, metric, hermite, sharp, Fin.sum_univ_succ]

-- A zero metric cannot supply the missing containment hypothesis.
example : ¬ (Gimle.Forseti.RationalLDL.propose (0 : QMatrix 4)).Represents
    (fun i j => if i = 2 ∧ j = 2 then -1/9 else 0) := by
  unfold WeightedSquares.Represents
  decide +kernel

end Gimle.Forseti.Tests.AIFSlabContainment
