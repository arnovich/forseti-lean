module

public import Gimle.Forseti.Examples.AIFSlabData

/-! Symmetry checks for stored slab data, and the premises degenerate slabs violate. -/

@[expose] public section

namespace Gimle.Forseti.Tests.AIFSlabData
open Gimle.Forseti.Examples

def slab : AIFSlabModel.Slab where
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

def asymmetric : Fin 4 → Fin 4 → ℚ :=
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

/-- A zero step violates the `0 < step` premise of slab theorems. -/
theorem zero_step_rejected :
    ¬ (0 < ({ slab with step := 0 } : AIFSlabModel.Slab).step) := by
  decide +kernel

/-- A negative step violates the `0 < step` premise of slab theorems. -/
theorem negative_step_rejected :
    ¬ (0 < ({ slab with step := -1 } : AIFSlabModel.Slab).step) := by
  decide +kernel

/-- A reversed parameter range violates the `etaLo < etaHi` premise. -/
theorem reversed_eta_rejected :
    ¬ (({ slab with etaLo := 9, etaHi := 8 } : AIFSlabModel.Slab).etaLo <
      ({ slab with etaLo := 9, etaHi := 8 } : AIFSlabModel.Slab).etaHi) := by
  decide +kernel

/-- info: 'Gimle.Forseti.Tests.AIFSlabData.symmetric_data_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symmetric_data_accepted
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.start_metric_asymmetry_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms start_metric_asymmetry_rejected
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.end_metric_asymmetry_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms end_metric_asymmetry_rejected
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.start_slope_asymmetry_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms start_slope_asymmetry_rejected
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.end_slope_asymmetry_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms end_slope_asymmetry_rejected
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.zero_step_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_step_rejected
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.negative_step_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negative_step_rejected
/-- info: 'Gimle.Forseti.Tests.AIFSlabData.reversed_eta_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reversed_eta_rejected
end Gimle.Forseti.Tests.AIFSlabData
