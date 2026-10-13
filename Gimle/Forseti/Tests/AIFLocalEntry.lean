import Gimle.Forseti.Examples.AIFLocalEntry

/-! Exact regressions for the endpoint coercivity margin and local-entry bridge. -/
namespace Gimle.Forseti.Tests.AIFLocalEntry
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.Examples AIFLocalEntry AIFSlabModel

def sample : Slab where
  tStart := 30
  step := 1
  etaLo := 8
  etaHi := 12
  loStart := 0
  loEnd := 0
  loStartSlope := 0
  loEndSlope := 0
  hiStart := 0
  hiEnd := 0
  hiStartSlope := 0
  hiEndSlope := 0
  startMetric := fun i j => if i=j then 1 else 0
  endMetric := fun i j => if i=j then 1 else 0
  startMetricSlope := 0
  endMetricSlope := 0

def certificate : WeightedSquares 4 where
  count := 4
  weight := fun _ => 49/50
  vector := fun i j => if i=j then 1 else 0

theorem valid : certificate.Represents (coercivityMargin sample.endMetric) := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- The normalized endpoint theorem accepts every parameter interpolation value. -/
theorem all_parameter_values (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 4 → ℝ) (h : matrixForm (metric sample 1) (x-center sample 1 u) ≤ 1/40000) :
    value x < 1/100 := by
  exact (terminal_entry sample certificate valid
    (by norm_num [value,AIFLocalStability.energy,sample])
    (by norm_num [value,AIFLocalStability.energy,sample]) u hu x h).2

/-- The physical endpoint is start+step, with the original eta range retained. -/
theorem endpoint_31 (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) 12)
    (x : Fin 4 → ℝ) (h : AIFMesh.tubeEnergy sample 31 eta x ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  exact terminal_entry_physical sample (by norm_num [sample]) (by norm_num [sample])
    certificate valid (by norm_num [value,AIFLocalStability.energy,sample])
    (by norm_num [value,AIFLocalStability.energy,sample]) eta heta x (by
      simpa only [sample, Rat.cast_ofNat, Rat.cast_one, show (30:ℝ)+1=31 by norm_num] using h)

/-- The checked tube has a concrete member, so the entry example is nonempty. -/
theorem origin_member : AIFMesh.tubeEnergy sample 31 8 0 ≤ 1/40000 := by
  norm_num [AIFMesh.tubeEnergy,timeCoordinate,etaCoordinate,center,metric,hermite,
    sample,matrixForm,Fin.sum_univ_succ]

#print axioms valid
#print axioms all_parameter_values
#print axioms endpoint_31
#print axioms origin_member
end Gimle.Forseti.Tests.AIFLocalEntry
