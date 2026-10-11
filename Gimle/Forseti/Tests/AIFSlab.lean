import Gimle.Forseti.Examples.AIFSlabModel
import Gimle.Forseti.RationalLDL

/-! Physical scaling and closed-boundary regressions for all candidate mesh widths. -/
namespace Gimle.Forseti.Tests.AIFSlab
open Gimle.Forseti.Examples.AIFSlabModel

def steps : Fin 3 → ℚ := ![1/200, 1/50, 1/10]

def sample (h lo : ℚ) : Slab where
  tStart := 1/5
  step := h
  etaLo := lo
  etaHi := lo + 1/2
  loStart := fun _ => 2
  loEnd := fun _ => 3
  loStartSlope := fun _ => 5
  loEndSlope := fun _ => 7
  hiStart := fun _ => 4
  hiEnd := fun _ => 6
  hiStartSlope := fun _ => 8
  hiEndSlope := fun _ => 9
  startMetric := fun i j => if i = j then 2 else 0
  endMetric := fun i j => if i = j then 3 else 0
  startMetricSlope := fun i j => if i = j then 5 else 0
  endMetricSlope := fun i j => if i = j then 7 else 0

-- The saved slopes are physical derivatives, at both closed endpoints.
example (k : Fin 3) :
    hermiteRate (steps k) 2 3 5 7 0 = 5 ∧
    hermiteRate (steps k) 2 3 5 7 1 = 7 := by
  fin_cases k <;> norm_num [steps, hermiteRate]

example (k : Fin 3) :
    timeCoordinate (sample (steps k) 8) (1/5) = 0 ∧
    timeCoordinate (sample (steps k) 8) (1/5 + (steps k : ℝ)) = 1 := by
  fin_cases k <;> norm_num [sample, steps, timeCoordinate]

-- Reusing the pilot's factor 10 on a width-1/200 slab gives the wrong rate.
example : hermiteRate (1/200) 2 3 5 7 0 ≠
    10 * (hermiteRate (1/200) 2 3 5 7 0 * (1/200)) := by
  norm_num [hermiteRate]

example : eta (sample (1/50) (23/2)) (etaCoordinate (sample (1/50) (23/2)) 12) = 12 :=
  eta_coordinate_inverse _ (by norm_num [sample]) _

example (k : Fin 3) (t u : ℝ) (i : Fin 4) :
    HasDerivAt (fun z => center (sample (steps k) 8)
      (timeCoordinate (sample (steps k) 8) z) u i)
      (centerRate (sample (steps k) 8) (timeCoordinate (sample (steps k) 8) t) u i) t :=
  center_derivative_physical _ (by fin_cases k <;> norm_num [sample, steps]) t u i

example (k : Fin 3) (t : ℝ) (i j : Fin 4) :
    HasDerivAt (fun z => metric (sample (steps k) 8)
      (timeCoordinate (sample (steps k) 8) z) i j)
      (metricRate (sample (steps k) 8) (timeCoordinate (sample (steps k) 8) t) i j) t :=
  metric_derivative_physical _ (by fin_cases k <;> norm_num [sample, steps]) t i j

/-- info: 'Gimle.Forseti.Examples.AIFSlabModel.drift_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms drift_bound

end Gimle.Forseti.Tests.AIFSlab
