import Gimle.Forseti.Examples.AIFSlabData

namespace Gimle.Forseti.Tests.AIFSlabData
open Gimle.Forseti.Examples

private def slab : AIFSlabModel.Slab where
  tStart := 0
  step := 1
  etaLo := 8
  etaHi := 9
  loStart := 0
  loEnd := 0
  loStartSlope := 0
  loEndSlope := 0
  hiStart := 0
  hiEnd := 0
  hiStartSlope := 0
  hiEndSlope := 0
  startMetric := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
  endMetric := ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
  startMetricSlope := 0
  endMetricSlope := 0


private def asymmetric : Fin 4 → Fin 4 → ℚ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

theorem symmetric_data_accepted : AIFSlabData.SymmetricData slab := by
  unfold AIFSlabData.SymmetricData
  decide +kernel

theorem start_metric_asymmetry_rejected :
    ¬ AIFSlabData.SymmetricData { slab with startMetric := asymmetric } := by
  unfold AIFSlabData.SymmetricData
  decide +kernel

theorem end_metric_asymmetry_rejected :
    ¬ AIFSlabData.SymmetricData { slab with endMetric := asymmetric } := by
  unfold AIFSlabData.SymmetricData
  decide +kernel

theorem start_slope_asymmetry_rejected :
    ¬ AIFSlabData.SymmetricData { slab with startMetricSlope := asymmetric } := by
  unfold AIFSlabData.SymmetricData
  decide +kernel

theorem end_slope_asymmetry_rejected :
    ¬ AIFSlabData.SymmetricData { slab with endMetricSlope := asymmetric } := by
  unfold AIFSlabData.SymmetricData
  decide +kernel

theorem zero_step_rejected :
    ¬ (0 < ({ slab with step := 0 } : AIFSlabModel.Slab).step) := by
  decide +kernel

theorem negative_step_rejected :
    ¬ (0 < ({ slab with step := -1 } : AIFSlabModel.Slab).step) := by
  decide +kernel

theorem reversed_eta_rejected :
    ¬ (({ slab with etaLo := 9, etaHi := 8 } : AIFSlabModel.Slab).etaLo <
      ({ slab with etaLo := 9, etaHi := 8 } : AIFSlabModel.Slab).etaHi) := by
  decide +kernel

#print axioms symmetric_data_accepted
#print axioms start_metric_asymmetry_rejected
#print axioms end_metric_asymmetry_rejected
#print axioms start_slope_asymmetry_rejected
#print axioms end_slope_asymmetry_rejected
#print axioms zero_step_rejected
#print axioms negative_step_rejected
#print axioms reversed_eta_rejected
end Gimle.Forseti.Tests.AIFSlabData
