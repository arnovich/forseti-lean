import Gimle.Forseti.Examples.AIFCertifiedCellData
import Gimle.Forseti.Examples.AIFGlobalSolution
import Gimle.Forseti.Examples.AIFPhysicalCoordinates
import Gimle.Forseti.Examples.AIFSlabDrift

/-! One AIF tube cell with its drift inequality discharged by checked certificates:
physical time `t ∈ [0, 1/200]` and every fixed `η ∈ [8, 17/2]`. The tube is the
energy sublevel set `eᵀ M(t) e ≤ 1/40000` of the error `e` from the moving center;
the zero-start solution of `AIFGlobalSolution`, in shifted coordinates, stays in it
on the whole cell. The only coordinate bound this gives is on the error coordinate
`e₂`, within `±3/200` of the center; nothing here shows the metric is positive
definite inside the cell, so the other coordinates are not enclosed. This is one
cell only; no later time and no output bound are claimed. -/
namespace Gimle.Forseti.Examples.AIFCertifiedCell
open Gimle.Forseti.BernsteinMatrix AIFSlabModel
open AIFCertifiedCellData (slab certificates)

/-- The cell's drift inequality throughout its tube, with no drift premise. -/
theorem drift_in_tube :
    ∀ t q e,
      t ∈ Set.Icc (slab.tStart : ℝ) ((slab.tStart : ℝ) + slab.step) →
      q ∈ Set.Icc (slab.etaLo : ℝ) (slab.etaHi : ℝ) →
      matrixForm (metric slab (timeCoordinate slab t)) e ≤ 1/40000 →
      energyRate slab (timeCoordinate slab t) (etaCoordinate slab q) e ≤
        (1/100) * (1/40000 - matrixForm (metric slab (timeCoordinate slab t)) e) -
          1/16000000 :=
  AIFSlabDrift.drift_in_tube slab certificates (by norm_num [slab]) (by norm_num [slab])

/-- The zero-start solution, in shifted coordinates, keeps its tube energy at most
`1/40000` on `[0, 1/200]` for every fixed `η ∈ [8, 17/2]`. -/
theorem solution_in_tube (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    AIFMesh.tubeEnergy slab t eta
      (AIFPhysicalCoordinates.shift eta (AIFGlobalSolution.solution eta (by linarith [heta.1]) t))
      ≤ 1/40000 := by
  have h0 : (0 : ℝ) ≤ eta := by linarith [heta.1]
  have hs : (slab.tStart : ℝ) = 0 := by norm_num [slab]
  have hstep : (slab.step : ℝ) = 1/200 := by norm_num [slab]
  have hlo : (slab.etaLo : ℝ) = 8 := by norm_num [slab]
  have hhi : (slab.etaHi : ℝ) = 17/2 := by norm_num [slab]
  have hcenter : ∀ i, (slab.loStart i : ℝ) = ![-2, -2, -2, -1] i ∧
      (slab.hiStart i : ℝ) = ![-2, -2, -2, -1] i := by
    intro i; fin_cases i <;> norm_num [slab]
  have start : AIFMesh.tubeEnergy slab 0 eta ![-2, -2, -2, -1] = 0 := by
    simp only [AIFMesh.tubeEnergy, timeCoordinate, hs, sub_self, zero_div]
    have hc : center slab 0 (etaCoordinate slab eta) = ![-2, -2, -2, -1] := by
      funext i
      simp only [center, hermite, (hcenter i).1, (hcenter i).2]
      ring
    simp [hc, matrixForm]
  have h := AIFInvariance.tube_invariant slab (by norm_num [slab]) (by norm_num [slab]) eta
    (by rw [hlo, hhi]; exact heta)
    (fun z => AIFPhysicalCoordinates.shift eta (AIFGlobalSolution.solution eta h0 z))
    (by
      intro z hz i
      simp only [hs, hstep, zero_add] at hz ⊢
      exact AIFPhysicalCoordinates.shift_derivative eta (AIFGlobalSolution.solution eta h0)
        _ z (fun j => (AIFGlobalSolution.solution_derivative eta h0 z hz.1 j).mono
          (fun _ hw => hw.1)) i)
    drift_in_tube
    (by
      simp only [hs]
      rw [AIFGlobalSolution.solution_start, AIFPhysicalCoordinates.shift_zero, start]
      norm_num)
    t (by simp only [hs, hstep, zero_add]; exact ht)
  exact h

/-- The coordinate bound the tube gives: the shifted `z₁` stays within `3/200` of
the moving center's coordinate on the whole cell. -/
theorem solution_error_bound (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    (AIFPhysicalCoordinates.shift eta (AIFGlobalSolution.solution eta (by linarith [heta.1]) t) -
      center slab (timeCoordinate slab t) (etaCoordinate slab eta)) 2 ∈
      Set.Icc (-3/200 : ℝ) (3/200) := by
  have hs : (slab.tStart : ℝ) = 0 := by norm_num [slab]
  have hstep : (slab.step : ℝ) = 1/200 := by norm_num [slab]
  exact AIFSlabContainment.error_contained_of_certificates slab certificates.error
    certificates.errorValid _
    (timeCoordinate_mem slab (by norm_num [slab]) t (by simp only [hs, hstep, zero_add]; exact ht))
    _ (solution_in_tube eta heta t ht)

#print axioms drift_in_tube
#print axioms solution_in_tube
#print axioms solution_error_bound
end Gimle.Forseti.Examples.AIFCertifiedCell
