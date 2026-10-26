module

public import Gimle.Forseti.Examples.AIFMesh

/-! Physical-time moving-energy derivatives along supplied AIF trajectories.
These rules require the component ODE derivatives; they do not supply existence
or tube invariance, and no circuit binding is claimed. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFTrajectory
open Gimle.Forseti.BernsteinMatrix AIFSlabModel AIFMesh

/-- Product rule for a moving real matrix, retaining both state factors.
No symmetry or positivity is required. Derivatives within a domain cover endpoints. -/
theorem matrixForm_hasDerivWithinAt {n : Nat}
    (m : ℝ → Fin n → Fin n → ℝ) (dm : Fin n → Fin n → ℝ)
    (x : ℝ → Fin n → ℝ) (v : Fin n → ℝ) (domain : Set ℝ) (t : ℝ)
    (hm : ∀ i j, HasDerivWithinAt (fun z => m z i j) (dm i j) domain t)
    (hx : ∀ i, HasDerivWithinAt (fun z => x z i) (v i) domain t) :
    HasDerivWithinAt (fun z => matrixForm (m z) (x z))
      (matrixForm dm (x t) + ∑ i, ∑ j,
        (v i * m t i j * x t j + x t i * m t i j * v j)) domain t := by
  have h := HasDerivWithinAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivWithinAt.sum (u := Finset.univ) (fun j _ =>
      ((hx i).mul (hm i j)).mul (hx j)))
  refine (h.congr (fun z _ => ?_) ?_).congr_deriv ?_
  · simp [matrixForm, Finset.sum_apply]
  · simp [matrixForm, Finset.sum_apply]
  · simp only [matrixForm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.mul_apply]
    ring

/-- The moving error has exactly the algebraic error velocity for fixed eta. -/
theorem error_derivative (d : Slab) (hh : d.step ≠ 0) (hp : d.etaLo < d.etaHi)
    (p : ℝ) (state : ℝ → Fin 4 → ℝ) (domain : Set ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun z => state z i)
      (AIFDriftModel.field p (state t) i) domain t) (i : Fin 4) :
    HasDerivWithinAt (fun z => (state z -
      center d (timeCoordinate d z) (etaCoordinate d p)) i)
      (errorVelocity d (timeCoordinate d t) (etaCoordinate d p)
        (state t - center d (timeCoordinate d t) (etaCoordinate d p)) i) domain t := by
  have h := (hx i).sub
    (center_derivative_physical d hh t (etaCoordinate d p) i).hasDerivWithinAt
  convert! h using 1
  simp [errorVelocity_eq, eta_coordinate_inverse d hp]

/-- The algebraic drift rate is the physical-time energy derivative along any
supplied solution of the fixed-parameter field, including closed-domain endpoints. -/
theorem tubeEnergy_derivative (d : Slab) (hh : d.step ≠ 0) (hp : d.etaLo < d.etaHi)
    (p : ℝ) (state : ℝ → Fin 4 → ℝ) (domain : Set ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun z => state z i)
      (AIFDriftModel.field p (state t) i) domain t) :
    HasDerivWithinAt (fun z => tubeEnergy d z p (state z))
      (energyRate d (timeCoordinate d t) (etaCoordinate d p)
        (state t - center d (timeCoordinate d t) (etaCoordinate d p))) domain t := by
  exact matrixForm_hasDerivWithinAt
    (fun z => metric d (timeCoordinate d z)) (metricRate d (timeCoordinate d t))
    (fun z => state z - center d (timeCoordinate d z) (etaCoordinate d p))
    (errorVelocity d (timeCoordinate d t) (etaCoordinate d p)
      (state t - center d (timeCoordinate d t) (etaCoordinate d p))) domain t
    (fun i j => (metric_derivative_physical d hh t i j).hasDerivWithinAt)
    (error_derivative d hh hp p state domain t hx)

#print axioms matrixForm_hasDerivWithinAt
#print axioms error_derivative
#print axioms tubeEnergy_derivative
end Gimle.Forseti.Examples.AIFTrajectory
