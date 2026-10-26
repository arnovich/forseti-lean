module

public import Gimle.Forseti.Examples.AIFTrajectory
public import Gimle.Forseti.Tests.AIFSlab

/-! Moving-energy regressions: physical widths, fixed eta, and retained product terms. -/

@[expose] public section

namespace Gimle.Forseti.Tests.AIFTrajectory
open Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.Examples AIFSlabModel AIFMesh AIFTrajectory AIFSlab

-- Neither symmetry nor a stationary metric is needed for the product rule.
example (m : ℝ → Fin 2 → Fin 2 → ℝ) (dm : Fin 2 → Fin 2 → ℝ)
    (x : ℝ → Fin 2 → ℝ) (v : Fin 2 → ℝ) (s : Set ℝ) (t : ℝ)
    (hm : ∀ i j, HasDerivWithinAt (fun z => m z i j) (dm i j) s t)
    (hx : ∀ i, HasDerivWithinAt (fun z => x z i) (v i) s t) :
    HasDerivWithinAt (fun z => matrixForm (m z) (x z))
      (matrixForm dm (x t) + ∑ i, ∑ j,
        (v i * m t i j * x t j + x t i * m t i j * v j)) s t :=
  matrixForm_hasDerivWithinAt m dm x v s t hm hx

-- The physical-time chain rule applies to these widths and closed domains.
example (k : Fin 3) (p t : ℝ) (state : ℝ → Fin 4 → ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun z => state z i)
      (AIFDriftModel.field p (state t) i) (Set.Icc (1/5) (1/5 + (steps k : ℝ))) t) :
    HasDerivWithinAt (fun z => tubeEnergy (sample (steps k) 8) z p (state z))
      (energyRate (sample (steps k) 8) (timeCoordinate (sample (steps k) 8) t)
        (etaCoordinate (sample (steps k) 8) p)
        (state t - center (sample (steps k) 8)
          (timeCoordinate (sample (steps k) 8) t) (etaCoordinate (sample (steps k) 8) p)))
      (Set.Icc (1/5) (1/5 + (steps k : ℝ))) t :=
  tubeEnergy_derivative _ (by fin_cases k <;> norm_num [sample, steps])
    (by norm_num [sample]) p state _ t hx

-- A concrete asymmetric moving metric detects dropping either state product term
-- or the matrix derivative: V(t) = 5*t^3, hence V'(2) = 60.
noncomputable def movingMetric (t : ℝ) : Fin 2 → Fin 2 → ℝ := ![![t, 2*t], ![0, 0]]
noncomputable def movingState (t : ℝ) : Fin 2 → ℝ := ![t, 2*t]

theorem moving_energy_derivative :
    HasDerivAt (fun t => matrixForm (movingMetric t) (movingState t)) 60 2 := by
  have h := matrixForm_hasDerivWithinAt movingMetric (![![1, 2], ![0, 0]])
    movingState (![1, 2]) Set.univ 2
    (by
      intro i j
      fin_cases i <;> fin_cases j
      · exact (hasDerivAt_id (2 : ℝ)).hasDerivWithinAt
      · simpa [movingMetric] using ((hasDerivAt_id (2 : ℝ)).const_mul 2)
      · exact (hasDerivAt_const (2 : ℝ) (0 : ℝ)).hasDerivWithinAt
      · exact (hasDerivAt_const (2 : ℝ) (0 : ℝ)).hasDerivWithinAt)
    (by
      intro i
      fin_cases i
      · exact (hasDerivAt_id (2 : ℝ)).hasDerivWithinAt
      · simpa [movingState] using ((hasDerivAt_id (2 : ℝ)).const_mul 2))
  norm_num [matrixForm, movingMetric, movingState, Fin.sum_univ_succ] at h ⊢
  exact h

-- Omitting the metric-rate contribution would incorrectly give 40.
example : ¬ HasDerivAt (fun t => matrixForm (movingMetric t) (movingState t)) 40 2 := by
  intro h
  have impossible := moving_energy_derivative.unique h
  norm_num at impossible

example : (matrixForm (![![1, 2], ![0, 0]]) (movingState 2) : ℝ) = 20 := by
  norm_num [matrixForm, movingState, Fin.sum_univ_succ]

-- Constant matrix entries make this rate regression independent of diagonal
-- simplification: P(0) has all entries 2 and its physical slope has all entries 5.
-- The center moves at velocity 5, while the field at state (3,3,3,3) is
-- (0,0,-18,-120); hence the error velocity sums to -158 and V' = 80 + 16*(-158).
def movingSlab (h : ℚ) : Slab :=
  { sample h 8 with
    startMetric := fun _ _ => 2
    startMetricSlope := fun _ _ => 5 }

example (k : Fin 3) :
    energyRate (movingSlab (steps k)) 0 0 (fun _ => 1) = -2448 := by
  fin_cases k <;>
    norm_num [energyRate, errorVelocity, errorMatrix, AIFSlabModel.residual,
      AIFDriftModel.field, center, centerRate, metric, metricRate, hermite,
      hermiteRate, eta, movingSlab, sample, steps, matrixForm, Fin.sum_univ_succ]

/-- info: 'Gimle.Forseti.Examples.AIFTrajectory.tubeEnergy_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tubeEnergy_derivative
/-- info: 'Gimle.Forseti.Examples.AIFTrajectory.matrixForm_hasDerivWithinAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms matrixForm_hasDerivWithinAt
end Gimle.Forseti.Tests.AIFTrajectory
