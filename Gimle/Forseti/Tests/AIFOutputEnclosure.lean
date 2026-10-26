module

public import Gimle.Forseti.Examples.AIFOutputEnclosure
public import Gimle.Forseti.Tests.AIFSlab

/-! Sharp output-margin, hostile zero-metric, and Hermite overshoot regressions. -/

@[expose] public section

namespace Gimle.Forseti.Tests.AIFOutputEnclosure
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.Examples.AIFSlabModel Gimle.Forseti.Examples.AIFOutputEnclosure

def sharp : Slab := { AIFSlab.sample (1/200) 8 with
  startMetric := fun i j => if i = 1 ∧ j = 1 then 1/40000 else 0
  endMetric := fun i j => if i = 1 ∧ j = 1 then 1/40000 else 0
  startMetricSlope := 0
  endMetricSlope := 0 }

theorem sharp_margin_zero (s : ℝ) : outputMargin sharp 1 s = 0 := by
  ext i j
  simp [outputMargin, metric, hermite, sharp]
  split_ifs <;> norm_num

example (s : ℝ) (e : Fin 4 → ℝ)
    (he : matrixForm (metric sharp s) e ≤ 1/40000) :
    e 1 ∈ Set.Icc (-1 : ℝ) 1 := by
  simpa only [Rat.cast_one] using output_error_contained sharp 1 (by norm_num) s e
    (by simp [sharp_margin_zero, matrixForm]) he

example (s : ℝ) :
    matrixForm (metric sharp s) ![0, 1, 0, 0] = 1/40000 ∧
    matrixForm (metric sharp s) ![0, -1, 0, 0] = 1/40000 := by
  norm_num [matrixForm, metric, hermite, sharp, Fin.sum_univ_succ]

theorem outside_rejected (s : ℝ) :
    ¬ matrixForm (metric sharp s) ![0, 2, 0, 0] ≤ 1/40000 := by
  norm_num [matrixForm, metric, hermite, sharp, Fin.sum_univ_succ]

theorem zero_metric_rejected :
    ¬ (Gimle.Forseti.RationalLDL.propose (0 : QMatrix 4)).Represents
      (fun i j => if i = 1 ∧ j = 1 then -1/40000 else 0) := by
  unfold WeightedSquares.Represents
  decide +kernel

-- Endpoint centers alone do not bound a cubic with nonzero slopes.
theorem endpoint_only_bound_rejected : 0 < hermite 1 0 0 4 (-4) (1/2) := by
  norm_num [hermite]

example (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : hermite 1 0 0 3 (-3) s ≤ 1 := by
  have controls : ∀ i, hermiteControls 1 0 0 3 (-3) i ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [hermiteControls]
  simpa only [Rat.cast_one] using hermite_upper 1 0 0 3 (-3) 1 s hs controls

/-- info: 'Gimle.Forseti.Tests.AIFOutputEnclosure.sharp_margin_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sharp_margin_zero
/-- info: 'Gimle.Forseti.Tests.AIFOutputEnclosure.outside_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms outside_rejected
/-- info: 'Gimle.Forseti.Tests.AIFOutputEnclosure.zero_metric_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_metric_rejected
/-- info: 'Gimle.Forseti.Tests.AIFOutputEnclosure.endpoint_only_bound_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endpoint_only_bound_rejected
end Gimle.Forseti.Tests.AIFOutputEnclosure
