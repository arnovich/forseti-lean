module

public import Gimle.Forseti.Examples.LoadedSAIFCertificates

/-! Exact rational local regions for the loaded feedback field. Concrete matrices
and their weighted-square representations are data, not authority; every
representation and its binding to the original rational field must be proved. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFCertificates
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open LoadedSAIFModel

/-- Rational local-region proposal. Validity and invariance are separate. -/
structure StationaryData where
  load : ℚ
  center : Fin 5 → ℚ
  metric : QMatrix 5
  radiusSq : ℚ
  decay : ℚ
  margin : ℚ
  cBound : ℚ
  feedbackBound : ℚ

noncomputable def StationaryData.realCenter (d : StationaryData) : State :=
  fun i => d.center i

noncomputable def StationaryData.energy (d : StationaryData) (x : State) : ℝ :=
  LoadedSAIFCertificates.energy (realMatrix d.metric) d.realCenter x

/-- Feedback error normalized to the closed unit interval. -/
noncomputable def feedbackError (d : StationaryData) (u : ℝ) : ℝ :=
  -(d.feedbackBound : ℝ) + 2*(d.feedbackBound : ℝ)*u

noncomputable def stationaryBlock (d : StationaryData) (ec : ℚ) (u : ℝ) :
    Fin 6 → Fin 6 → ℝ :=
  driftBlock d.load d.realCenter 0 (realMatrix d.metric) 0
    d.radiusSq d.decay d.margin ec (feedbackError d u)

/-- Degree-two feedback Bernstein representation for one capacity-error endpoint. -/
structure StationaryBlockCertificate (d : StationaryData) (ec : ℚ) where
  coefficients : Fin 1 → Fin 3 → QMatrix 6
  squares : Fin 1 → Fin 3 → WeightedSquares 6
  valid : ∀ i j, (squares i j).Represents (coefficients i j)
  binding : ∀ u, stationaryBlock d ec u = tensorMatrix coefficients 0 u

theorem StationaryBlockCertificate.nonnegative {d : StationaryData} {ec : ℚ}
    (certificate : StationaryBlockCertificate d ec) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 6 → ℝ) :
    0 ≤ matrixForm (stationaryBlock d ec u) x :=
  target_nonnegative certificate.squares certificate.valid (certificate.binding u)
    (by norm_num) hu x

/-- Rational rank-one margin for any rational observable. -/
def stationaryMargin (d : StationaryData) (w : Fin 5 → ℚ) (radius : ℚ) : QMatrix 5 :=
  fun i j => d.metric i j - d.radiusSq/radius^2*w i*w j

theorem stationaryMargin_binding (d : StationaryData) (w : Fin 5 → ℚ) (radius : ℚ) :
    realMatrix (stationaryMargin d w radius) =
      observableMargin (realMatrix d.metric) d.radiusSq radius (fun i => (w i : ℝ)) := by
  ext i j
  simp [realMatrix, stationaryMargin, observableMargin]

/-- Checked square representations of the rank-one margin give observable bounds. -/
theorem stationary_observable (d : StationaryData) (w : Fin 5 → ℚ) (radius : ℚ)
    (certificate : WeightedSquares 5)
    (valid : certificate.Represents (stationaryMargin d w radius))
    (hC : 0 < d.radiusSq) (hr : 0 < radius) (x : State)
    (hx : d.energy x ≤ d.radiusSq) :
    |∑ i, (w i : ℝ)*(x i-d.realCenter i)| ≤ radius := by
  apply observable_contained (realMatrix d.metric) d.radiusSq radius
    (fun i => (w i : ℝ)) (x-d.realCenter)
  · exact_mod_cast hC
  · exact_mod_cast hr
  · rw [← stationaryMargin_binding, matrixForm_rat]
    exact certificate.nonnegative _ valid _
  · exact hx

theorem clearedMatrix_interpolation (L : ℝ) (p : State) (lo hi eb s : ℝ) :
    clearedMatrix L p ((1-s)*lo+s*hi) eb =
      fun i j => (1-s)*clearedMatrix L p lo eb i j + s*clearedMatrix L p hi eb i j := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [clearedMatrix] <;> ring

set_option maxHeartbeats 4000000 in
theorem driftBlock_interpolation (L : ℝ) (p v : State) (P Pdot : Matrix5)
    (C decay margin lo hi eb s : ℝ) :
    driftBlock L p v P Pdot C decay margin ((1-s)*lo+s*hi) eb =
      fun i j => (1-s)*driftBlock L p v P Pdot C decay margin lo eb i j +
        s*driftBlock L p v P Pdot C decay margin hi eb i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [driftBlock, driftMatrix, clearedMatrix_interpolation, Fin.sum_univ_succ] <;> ring

theorem matrixForm_interpolation {n : Nat} (A B : Fin n → Fin n → ℝ)
    (s : ℝ) (x : Fin n → ℝ) :
    matrixForm (fun i j => (1-s)*A i j+s*B i j) x =
      (1-s)*matrixForm A x+s*matrixForm B x := by
  simp only [matrixForm, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Endpoint positivity covers every capacity-error value between the endpoints. -/
theorem driftBlock_nonnegative (L : ℝ) (p v : State) (P Pdot : Matrix5)
    (C decay margin lo hi eb ec : ℝ) (hlo : lo < hi)
    (hec : ec ∈ Set.Icc lo hi)
    (negative : ∀ x, 0 ≤ matrixForm (driftBlock L p v P Pdot C decay margin lo eb) x)
    (positive : ∀ x, 0 ≤ matrixForm (driftBlock L p v P Pdot C decay margin hi eb) x)
    (x : Fin 6 → ℝ) :
    0 ≤ matrixForm (driftBlock L p v P Pdot C decay margin ec eb) x := by
  let s := (ec-lo)/(hi-lo)
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hec.1) (sub_pos.mpr hlo).le
  have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr hlo)).mpr (by linarith [hec.2])
  have heq : (1-s)*lo+s*hi = ec := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr hlo)]
    ring
  rw [← heq, driftBlock_interpolation, matrixForm_interpolation]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs1) (negative x))
    (mul_nonneg hs0 (positive x))

/-- Unit vectors for coordinate containment certificates. -/
def coordinate (i : Fin 5) : Fin 5 → ℚ := fun j => if j = i then 1 else 0

@[simp] theorem coordinate_cast (i j : Fin 5) :
    (coordinate i j : ℝ) = if j = i then 1 else 0 := by
  by_cases h : j = i <;> simp [coordinate, h]

theorem stationary_coordinate (d : StationaryData) (i : Fin 5) (radius : ℚ)
    (certificate : WeightedSquares 5)
    (valid : certificate.Represents (stationaryMargin d (coordinate i) radius))
    (hC : 0 < d.radiusSq) (hr : 0 < radius) (x : State)
    (hx : d.energy x ≤ d.radiusSq) : |x i-d.realCenter i| ≤ radius := by
  have h := stationary_observable d (coordinate i) radius certificate valid hC hr x hx
  simpa only [coordinate_cast, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- Only these two nonlinear error coordinates enter the exact secant matrix. -/
structure StationaryCertificate (d : StationaryData) where
  radius_positive : 0 < d.radiusSq
  c_positive : 0 < d.cBound
  feedback_positive : 0 < d.feedbackBound
  margin_positive : 0 < d.margin
  feedback_guard : 0 < kappa+(d.center 3 : ℝ)-d.feedbackBound
  symmetric : ∀ i j, d.metric i j = d.metric j i
  capacity : WeightedSquares 5
  capacity_valid : capacity.Represents (stationaryMargin d (coordinate 4) d.cBound)
  feedback : WeightedSquares 5
  feedback_valid : feedback.Represents (stationaryMargin d (coordinate 3) d.feedbackBound)
  negative : StationaryBlockCertificate d (-d.cBound)
  positive : StationaryBlockCertificate d d.cBound

theorem stationary_drift (d : StationaryData) (certificate : StationaryCertificate d)
    (x : State) (hx : d.energy x ≤ d.radiusSq) :
    energyRate d.load (realMatrix d.metric) 0 d.realCenter 0 x ≤
      (d.decay : ℝ)*(d.radiusSq-d.energy x)-d.margin := by
  let e := x-d.realCenter
  have hc := stationary_coordinate d 4 d.cBound certificate.capacity
    certificate.capacity_valid certificate.radius_positive certificate.c_positive x hx
  have hb := stationary_coordinate d 3 d.feedbackBound certificate.feedback
    certificate.feedback_valid certificate.radius_positive certificate.feedback_positive x hx
  have hc' : e 4 ∈ Set.Icc (-(d.cBound : ℝ)) (d.cBound : ℝ) := abs_le.mp hc
  have hb' : e 3 ∈ Set.Icc (-(d.feedbackBound : ℝ)) (d.feedbackBound : ℝ) := abs_le.mp hb
  have hdb : (0 : ℝ) < d.feedbackBound := by exact_mod_cast certificate.feedback_positive
  have hdc : (0 : ℝ) < d.cBound := by exact_mod_cast certificate.c_positive
  let u := (e 3+(d.feedbackBound : ℝ))/(2*(d.feedbackBound : ℝ))
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · apply div_nonneg <;> linarith [hb'.1]
    · apply (div_le_one (by positivity : (0 : ℝ) < 2*(d.feedbackBound : ℝ))).mpr
      linarith [hb'.2]
  have heb : feedbackError d u = e 3 := by
    dsimp [feedbackError, u]
    field_simp [ne_of_gt hdb]
    ring
  have hn (z : Fin 6 → ℝ) := certificate.negative.nonnegative hu z
  have hp (z : Fin 6 → ℝ) := certificate.positive.nonnegative hu z
  simp only [stationaryBlock, Rat.cast_neg, heb] at hn hp
  have hblock := driftBlock_nonnegative (d.load : ℝ) d.realCenter 0
    (realMatrix d.metric) 0 d.radiusSq d.decay d.margin
    (-(d.cBound : ℝ)) d.cBound (e 3) (e 4) (by linarith) hc' hn hp (Matrix.vecCons 1 e)
  have hcenter : 0 < kappa+d.realCenter 3 := by
    have := certificate.feedback_guard
    dsimp [StationaryData.realCenter]
    linarith
  have hactual : 0 < kappa+d.realCenter 3+e 3 := by
    have := certificate.feedback_guard
    dsimp [StationaryData.realCenter] at *
    linarith [hb'.1]
  have h := drift_bound d.load d.realCenter 0 e (realMatrix d.metric) 0
    d.radiusSq d.decay d.margin (by
      intro i j
      change (d.metric i j : ℝ) = (d.metric j i : ℝ)
      exact_mod_cast certificate.symmetric i j) hcenter hactual hblock
  have he : d.realCenter+e = x := by simp [e]
  simpa only [he, StationaryData.energy, energy] using h

/-- A supplied physical-time trajectory stays in a checked local region. -/
theorem stationary_invariant (d : StationaryData) (certificate : StationaryCertificate d)
    (a b : ℝ) (x : ℝ → State) (hx : Solves d.load a b x)
    (initial : d.energy (x a) ≤ d.radiusSq) :
    ∀ t ∈ Set.Icc a b, d.energy (x t) ≤ d.radiusSq := by
  apply tube_invariant d.load a b d.radiusSq d.decay d.margin
    (fun _ => realMatrix d.metric) 0 (fun _ => d.realCenter) 0 x
  · intro t _ i j
    exact hasDerivWithinAt_const t _ _
  · intro t _ i
    exact hasDerivWithinAt_const t _ _
  · exact hx
  · exact_mod_cast certificate.margin_positive
  · exact initial
  · intro t _ ht
    exact stationary_drift d certificate (x t) (le_of_eq ht)

#print axioms StationaryBlockCertificate.nonnegative
#print axioms stationary_observable
#print axioms stationary_drift
#print axioms stationary_invariant
end Gimle.Forseti.Examples.LoadedSAIFCertificates
