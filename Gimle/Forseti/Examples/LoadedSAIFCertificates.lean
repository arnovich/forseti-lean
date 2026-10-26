module

public import Gimle.Forseti.BernsteinConversion
public import Gimle.Forseti.Examples.AIFMeshComposition
public import Gimle.Forseti.Examples.LoadedSAIFModel
public import Gimle.Forseti.RationalLDL

/-! Exact quadratic certificates for the five-species rational feedback field.
The positive denominator is cleared only in inequalities. All derivatives remain
physical-time derivatives; no trajectory membership or existence is implicit. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFCertificates
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open LoadedSAIFModel

abbrev Matrix5 := Fin 5 → Fin 5 → ℝ

/-- Product of the center and actual feedback denominators. -/
noncomputable def denominator (p : State) (eb : ℝ) : ℝ :=
  (kappa + p 3) * (kappa + p 3 + eb)

/-- The exact secant matrix multiplied by the denominator product. -/
noncomputable def clearedMatrix (L : ℝ) (p : State) (ec eb : ℝ) : Matrix5 :=
  let D := denominator p eb
  ![![-D, 0, 0, -alpha*kappa, 0],
    ![D, D*(-1-L+p 4+ec), 0, 0, D*(p 1+1)],
    ![0, 0, D*(-8*(p 3+eb)-dilution), D*(-8*p 2), 0],
    ![0, D, D*(-8*(p 3+eb)), D*(-8*p 2-dilution), 0],
    ![0, D*(L-p 4-ec), 0, 0, D*(-p 1-6/5)]]

/-- Polynomial residual after clearing the same denominator product. -/
noncomputable def clearedResidual (L : ℝ) (p v : State) (eb : ℝ) : State :=
  let D := denominator p eb
  ![alpha*kappa*(kappa+p 3+eb)-D*(p 0+v 0),
    D*(p 0-p 1-binding L p-v 1),
    D*(2-8*p 2*p 3-dilution*p 2-v 2),
    D*(p 1-8*p 2*p 3-dilution*p 3-v 3),
    D*(binding L p-p 4/5-v 4)]

/-- Exact cleared error velocity; the actual field denominator is not discarded. -/
theorem cleared_velocity (L : ℝ) (p v e : State)
    (h : kappa + p 3 + e 3 ≠ 0) (i : Fin 5) :
    denominator p (e 3) * (field L (p + e) i - v i) =
      (∑ j, clearedMatrix L p (e 4) (e 3) i j * e j) +
        clearedResidual L p v (e 3) i := by
  fin_cases i <;>
    simp [field, LoadedSAIFModel.control, binding, clearedMatrix, clearedResidual, denominator,
      Pi.add_apply, Fin.sum_univ_succ]
  · field_simp [show kappa + (p 3 + e 3) ≠ 0 by simpa [add_assoc] using h]
    ring
  all_goals ring

/-- Physical-time error energy. -/
noncomputable def energy (P : Matrix5) (p x : State) : ℝ := matrixForm P (x-p)

/-- Chain-rule rate for arbitrary differentiable center and metric. -/
noncomputable def energyRate (L : ℝ) (P Pdot : Matrix5) (p v x : State) : ℝ :=
  matrixForm Pdot (x-p) + ∑ i, ∑ j,
    ((field L x i-v i)*P i j*(x j-p j) +
      (x i-p i)*P i j*(field L x j-v j))

noncomputable def residualProduct (L : ℝ) (p v : State) (P : Matrix5)
    (eb : ℝ) (i : Fin 5) : ℝ := ∑ j, P i j * clearedResidual L p v eb j

noncomputable def driftMatrix (L : ℝ) (p : State) (P Pdot : Matrix5)
    (decay ec eb : ℝ) (i j : Fin 5) : ℝ :=
  -denominator p eb*Pdot i j - (∑ k, P i k*clearedMatrix L p ec eb k j) -
    (∑ k, clearedMatrix L p ec eb k i*P k j) - decay*denominator p eb*P i j

/-- Augmented supply matrix, retaining the center residual in its cross terms. -/
noncomputable def driftBlock (L : ℝ) (p v : State) (P Pdot : Matrix5)
    (C decay margin ec eb : ℝ) : Fin 6 → Fin 6 → ℝ :=
  Matrix.vecCons (Matrix.vecCons (denominator p eb*(decay*C-margin))
    (fun j => -residualProduct L p v P eb j))
    (fun i => Matrix.vecCons (-residualProduct L p v P eb i)
      (driftMatrix L p P Pdot decay ec eb i))

noncomputable def clearedRate (L : ℝ) (p v e : State) (P Pdot : Matrix5) : ℝ :=
  denominator p (e 3)*matrixForm Pdot e + ∑ i, ∑ j,
    (((∑ k, clearedMatrix L p (e 4) (e 3) i k*e k) +
       clearedResidual L p v (e 3) i)*P i j*e j +
     e i*P i j*((∑ k, clearedMatrix L p (e 4) (e 3) j k*e k) +
       clearedResidual L p v (e 3) j))

theorem clearedRate_eq (L : ℝ) (p v e : State) (P Pdot : Matrix5)
    (h : kappa+p 3+e 3 ≠ 0) :
    clearedRate L p v e P Pdot =
      denominator p (e 3)*energyRate L P Pdot p v (p+e) := by
  unfold clearedRate
  simp_rw [← cleared_velocity L p v e h]
  simp only [energyRate, Pi.add_apply, add_sub_cancel_left, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem block_energy_identity (L : ℝ) (p v e : State) (P Pdot : Matrix5)
    (C decay margin : ℝ) (hsym : ∀ i j, P i j = P j i) :
    matrixForm (driftBlock L p v P Pdot C decay margin (e 4) (e 3)) (Matrix.vecCons 1 e) =
      denominator p (e 3)*(decay*(C-matrixForm P e)-margin) -
        clearedRate L p v e P Pdot := by
  simp [driftBlock, driftMatrix, residualProduct, clearedRate, matrixForm,
    Fin.sum_univ_succ]
  simp only [hsym 1 0, hsym 2 0, hsym 3 0, hsym 4 0, hsym 2 1,
    hsym 3 1, hsym 4 1, hsym 3 2, hsym 4 2, hsym 4 3]
  ring

/-- A positive denominator and a checked nonnegative block bound the original
physical-time energy derivative. -/
theorem drift_bound (L : ℝ) (p v e : State) (P Pdot : Matrix5)
    (C decay margin : ℝ) (hsym : ∀ i j, P i j = P j i)
    (hp : 0 < kappa+p 3) (hx : 0 < kappa+p 3+e 3)
    (block : 0 ≤ matrixForm
      (driftBlock L p v P Pdot C decay margin (e 4) (e 3)) (Matrix.vecCons 1 e)) :
    energyRate L P Pdot p v (p+e) ≤ decay*(C-matrixForm P e)-margin := by
  rw [block_energy_identity L p v e P Pdot C decay margin hsym,
    clearedRate_eq L p v e P Pdot (ne_of_gt hx)] at block
  have hD : 0 < denominator p (e 3) := mul_pos hp hx
  exact le_of_mul_le_mul_left (sub_nonneg.mp block) hD

/-- Rank-one margin for a coordinate or any fixed linear observable. -/
noncomputable def observableMargin (P : Matrix5) (C radius : ℝ) (w : State) : Matrix5 :=
  fun i j => P i j - C/radius^2*w i*w j

theorem observable_identity (P : Matrix5) (C radius : ℝ) (w e : State) :
    matrixForm (observableMargin P C radius w) e =
      matrixForm P e - C/radius^2*(∑ i, w i*e i)^2 := by
  simp [matrixForm, observableMargin, Fin.sum_univ_succ]
  ring

/-- A nonnegative rank-one margin converts tube energy to an observable radius. -/
theorem observable_contained (P : Matrix5) (C radius : ℝ) (w e : State)
    (hC : 0 < C) (hr : 0 < radius)
    (hm : 0 ≤ matrixForm (observableMargin P C radius w) e)
    (he : matrixForm P e ≤ C) : |∑ i, w i*e i| ≤ radius := by
  rw [observable_identity] at hm
  have hq : 0 < C/radius^2 := div_pos hC (sq_pos_of_pos hr)
  have hc : C/radius^2*radius^2 = C := div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hr))
  have hs : (∑ i, w i*e i)^2 ≤ radius^2 :=
    le_of_mul_le_mul_left (by linarith) hq
  exact abs_le.mpr (abs_le_of_sq_le_sq' hs hr.le)

/-- Closed-interval chain rule, including each phase's one-sided endpoint derivatives. -/
theorem energy_derivative (L : ℝ) (P Pdot : ℝ → Matrix5) (p v x : ℝ → State)
    (domain : Set ℝ) (t : ℝ)
    (hP : ∀ i j, HasDerivWithinAt (fun s => P s i j) (Pdot t i j) domain t)
    (hp : ∀ i, HasDerivWithinAt (fun s => p s i) (v t i) domain t)
    (hx : ∀ i, HasDerivWithinAt (fun s => x s i) (field L (x t) i) domain t) :
    HasDerivWithinAt (fun s => energy (P s) (p s) (x s))
      (energyRate L (P t) (Pdot t) (p t) (v t) (x t)) domain t :=
  AIFTrajectory.matrixForm_hasDerivWithinAt P (Pdot t)
    (fun s => x s-p s) (fun i => field L (x t) i-v t i) domain t hP
    (fun i => (hx i).sub (hp i))

/-- Strict boundary drift proves tube membership; membership is not assumed
along the trajectory. All hypotheses concern only the closed interval. -/
theorem tube_invariant (L a b C decay margin : ℝ)
    (P Pdot : ℝ → Matrix5) (p v x : ℝ → State)
    (hP : ∀ t ∈ Set.Icc a b, ∀ i j,
      HasDerivWithinAt (fun s => P s i j) (Pdot t i j) (Set.Icc a b) t)
    (hp : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivWithinAt (fun s => p s i) (v t i) (Set.Icc a b) t)
    (hx : Solves L a b x) (hm : 0 < margin)
    (initial : energy (P a) (p a) (x a) ≤ C)
    (drift : ∀ t ∈ Set.Ico a b, energy (P t) (p t) (x t) = C →
      energyRate L (P t) (Pdot t) (p t) (v t) (x t) ≤
        decay*(C-energy (P t) (p t) (x t))-margin) :
    ∀ t ∈ Set.Icc a b, energy (P t) (p t) (x t) ≤ C := by
  apply AIFInvariance.sublevel_of_boundary_derivative
    (fun t => energy (P t) (p t) (x t))
    (fun t => energyRate L (P t) (Pdot t) (p t) (v t) (x t)) a b C
    (fun t ht => energy_derivative L P Pdot p v x _ t (hP t ht) (hp t ht) (hx t ht))
    initial
  intro t ht hb
  have h := drift t ht hb
  rw [hb] at h
  linarith

#print axioms cleared_velocity
#print axioms drift_bound
#print axioms observable_contained
#print axioms tube_invariant
end Gimle.Forseti.Examples.LoadedSAIFCertificates
