module

public import Gimle.Forseti.Examples.LoadedSAIFStationary

/-! Rational cubic-Hermite moving regions for the fixed feedback field. Endpoint
slopes are physical-time slopes. The normalized time and feedback-error axes are
used only to bind polynomial positivity certificates. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFCertificates
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open LoadedSAIFModel

structure MovingData where
  load : ℚ
  tStart : ℚ
  step : ℚ
  centerStart : Fin 5 → ℚ
  centerEnd : Fin 5 → ℚ
  centerStartSlope : Fin 5 → ℚ
  centerEndSlope : Fin 5 → ℚ
  metricStart : QMatrix 5
  metricEnd : QMatrix 5
  metricStartSlope : QMatrix 5
  metricEndSlope : QMatrix 5
  radiusSq : ℚ
  decay : ℚ
  margin : ℚ
  cBound : ℚ
  feedbackBound : ℚ

noncomputable def movingCenter (d : MovingData) (s : ℝ) (i : Fin 5) : ℝ :=
  AIFSlabModel.hermite d.step (d.centerStart i) (d.centerEnd i)
    (d.centerStartSlope i) (d.centerEndSlope i) s

noncomputable def movingCenterRate (d : MovingData) (s : ℝ) (i : Fin 5) : ℝ :=
  AIFSlabModel.hermiteRate d.step (d.centerStart i) (d.centerEnd i)
    (d.centerStartSlope i) (d.centerEndSlope i) s

noncomputable def movingMetric (d : MovingData) (s : ℝ) (i j : Fin 5) : ℝ :=
  AIFSlabModel.hermite d.step (d.metricStart i j) (d.metricEnd i j)
    (d.metricStartSlope i j) (d.metricEndSlope i j) s

noncomputable def movingMetricRate (d : MovingData) (s : ℝ) (i j : Fin 5) : ℝ :=
  AIFSlabModel.hermiteRate d.step (d.metricStart i j) (d.metricEnd i j)
    (d.metricStartSlope i j) (d.metricEndSlope i j) s

noncomputable def movingTime (d : MovingData) (t : ℝ) : ℝ := (t-d.tStart)/d.step

noncomputable def movingFeedback (d : MovingData) (u : ℝ) : ℝ :=
  -(d.feedbackBound : ℝ)+2*(d.feedbackBound : ℝ)*u

noncomputable def movingBlock (d : MovingData) (ec : ℚ) (s u : ℝ) :
    Fin 6 → Fin 6 → ℝ :=
  driftBlock d.load (movingCenter d s) (movingCenterRate d s)
    (movingMetric d s) (movingMetricRate d s) d.radiusSq d.decay d.margin ec
    (movingFeedback d u)

noncomputable def movingEnergy (d : MovingData) (s : ℝ) (x : State) : ℝ :=
  energy (movingMetric d s) (movingCenter d s) x

/-- Cubic Bernstein control points of a physical-slope Hermite curve. -/
def hermiteControls (h a b c d : ℚ) : Fin 4 → ℚ := ![a, a+h*c/3, b-h*d/3, b]

theorem hermite_controls_identity (h a b c d : ℚ) (s : ℝ) :
    AIFSlabModel.hermite h a b c d s =
      ∑ i : Fin 4, basis 3 i s*(hermiteControls h a b c d i : ℝ) := by
  simp [AIFSlabModel.hermite, hermiteControls, basis, Fin.sum_univ_succ, Nat.choose]
  ring

theorem cubic_partition (s : ℝ) : (∑ i : Fin 4, basis 3 i s) = 1 := by
  simp [basis, Fin.sum_univ_succ, Nat.choose]
  ring

theorem cubic_lower (a : Fin 4 → ℚ) (bound : ℚ) (ha : ∀ i, bound ≤ a i)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (bound : ℝ) ≤ ∑ i : Fin 4, basis 3 i s*(a i : ℝ) := by
  calc (bound : ℝ) = ∑ i : Fin 4, basis 3 i s*(bound : ℝ) := by
        rw [← Finset.sum_mul, cubic_partition, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast ha i) (basis_nonnegative _ _ hs)

theorem cubic_upper (a : Fin 4 → ℚ) (bound : ℚ) (ha : ∀ i, a i ≤ bound)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i : Fin 4, basis 3 i s*(a i : ℝ)) ≤ bound := by
  calc (∑ i : Fin 4, basis 3 i s*(a i : ℝ)) ≤
        ∑ i : Fin 4, basis 3 i s*(bound : ℝ) :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast ha i) (basis_nonnegative _ _ hs)
    _ = _ := by rw [← Finset.sum_mul, cubic_partition, one_mul]

def centerControls (d : MovingData) (w : Fin 5 → ℚ) (j : Fin 4) : ℚ :=
  ∑ i, w i*hermiteControls d.step (d.centerStart i) (d.centerEnd i)
    (d.centerStartSlope i) (d.centerEndSlope i) j

theorem center_controls_identity (d : MovingData) (w : Fin 5 → ℚ) (s : ℝ) :
    (∑ i, (w i : ℝ)*movingCenter d s i) =
      ∑ j : Fin 4, basis 3 j s*(centerControls d w j : ℝ) := by
  simp only [movingCenter, hermite_controls_identity, centerControls, Rat.cast_sum,
    Rat.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem moving_center_lower (d : MovingData) (w : Fin 5 → ℚ) (bound : ℚ)
    (checked : ∀ j, bound ≤ centerControls d w j) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (bound : ℝ) ≤ ∑ i, (w i : ℝ)*movingCenter d s i := by
  rw [center_controls_identity]
  exact cubic_lower _ bound checked s hs

theorem moving_center_upper (d : MovingData) (w : Fin 5 → ℚ) (bound : ℚ)
    (checked : ∀ j, centerControls d w j ≤ bound) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, (w i : ℝ)*movingCenter d s i) ≤ bound := by
  rw [center_controls_identity]
  exact cubic_upper _ bound checked s hs

theorem moving_guard_of_control_points (d : MovingData) (bound : ℚ)
    (guard : 0 < kappa+(bound : ℝ)-d.feedbackBound)
    (checked : ∀ j, bound ≤ centerControls d (coordinate 3) j) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < kappa+movingCenter d s 3-d.feedbackBound := by
  intro s hs
  have h := moving_center_lower d (coordinate 3) bound checked s hs
  simp only [coordinate_cast, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  linarith

@[simp] theorem movingCenter_zero (d : MovingData) (i : Fin 5) :
    movingCenter d 0 i = (d.centerStart i : ℝ) := by simp [movingCenter]

@[simp] theorem movingCenter_one (d : MovingData) (i : Fin 5) :
    movingCenter d 1 i = (d.centerEnd i : ℝ) := by simp [movingCenter]

@[simp] theorem movingMetric_zero (d : MovingData) (i j : Fin 5) :
    movingMetric d 0 i j = (d.metricStart i j : ℝ) := by simp [movingMetric]

@[simp] theorem movingMetric_one (d : MovingData) (i j : Fin 5) :
    movingMetric d 1 i j = (d.metricEnd i j : ℝ) := by simp [movingMetric]

theorem movingEnergy_zero (d : MovingData) (x : State) :
    movingEnergy d 0 x = energy (realMatrix d.metricStart) (fun i => (d.centerStart i : ℝ)) x := by
  simp [movingEnergy, energy, matrixForm, realMatrix, Pi.sub_apply]

theorem movingEnergy_one (d : MovingData) (x : State) :
    movingEnergy d 1 x = energy (realMatrix d.metricEnd) (fun i => (d.centerEnd i : ℝ)) x := by
  simp [movingEnergy, energy, matrixForm, realMatrix, Pi.sub_apply]

/-- Adjacent exact endpoint centers and metrics transfer every enclosed state. -/
theorem movingEnergy_join (d e : MovingData)
    (center : d.centerEnd = e.centerStart) (metric : d.metricEnd = e.metricStart) (x : State) :
    movingEnergy d 1 x = movingEnergy e 0 x := by
  rw [movingEnergy_one, movingEnergy_zero, center, metric]

theorem movingTime_mem (d : MovingData) (hh : 0 < d.step) (t : ℝ)
    (ht : t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ)+d.step)) :
    movingTime d t ∈ Set.Icc (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < d.step := by exact_mod_cast hh
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hr.le,
    (div_le_one hr).mpr (by linarith [ht.2])⟩

theorem movingCenter_derivative (d : MovingData) (hh : d.step ≠ 0) (t : ℝ) (i : Fin 5) :
    HasDerivAt (fun z => movingCenter d (movingTime d z) i)
      (movingCenterRate d (movingTime d t) i) t := by
  have hr : (d.step : ℝ) ≠ 0 := by exact_mod_cast hh
  have h := (AIFSlabModel.hermite_derivative d.step (d.centerStart i) (d.centerEnd i)
    (d.centerStartSlope i) (d.centerEndSlope i) hh (movingTime d t)).comp t
      (((hasDerivAt_id t).sub_const (d.tStart : ℝ)).div_const (d.step : ℝ))
  convert! h using 1
  simp [movingCenterRate, movingTime, hr, div_eq_mul_inv]

theorem movingMetric_derivative (d : MovingData) (hh : d.step ≠ 0) (t : ℝ) (i j : Fin 5) :
    HasDerivAt (fun z => movingMetric d (movingTime d z) i j)
      (movingMetricRate d (movingTime d t) i j) t := by
  have hr : (d.step : ℝ) ≠ 0 := by exact_mod_cast hh
  have h := (AIFSlabModel.hermite_derivative d.step (d.metricStart i j) (d.metricEnd i j)
    (d.metricStartSlope i j) (d.metricEndSlope i j) hh (movingTime d t)).comp t
      (((hasDerivAt_id t).sub_const (d.tStart : ℝ)).div_const (d.step : ℝ))
  convert! h using 1
  simp [movingMetricRate, movingTime, hr, div_eq_mul_inv]

/-- Bernstein interpolation preserves any kernel-proved coefficient positivity. -/
theorem tensor_nonnegative_of_coefficients {n td pd : Nat}
    (c : Fin (td+1) → Fin (pd+1) → QMatrix n)
    (nonnegative : ∀ i j x, 0 ≤ quadratic (c i j) x)
    {s u : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) : 0 ≤ matrixForm (tensorMatrix c s u) x := by
  rw [tensor_matrixForm]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg
    (mul_nonneg (basis_nonnegative _ _ hs) (basis_nonnegative _ _ hu))
    (nonnegative i j x)

structure MovingBlockCertificate (d : MovingData) (ec : ℚ) where
  timeDegree : Nat
  parameterDegree : Nat
  coefficients : Fin (timeDegree+1) → Fin (parameterDegree+1) → QMatrix 6
  coefficient_nonnegative : ∀ i j x, 0 ≤ quadratic (coefficients i j) x
  binding : ∀ s u, movingBlock d ec s u = tensorMatrix coefficients s u

theorem MovingBlockCertificate.nonnegative {d : MovingData} {ec : ℚ}
    (certificate : MovingBlockCertificate d ec) {s u : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 6 → ℝ) :
    0 ≤ matrixForm (movingBlock d ec s u) x := by
  rw [certificate.binding]
  exact tensor_nonnegative_of_coefficients certificate.coefficients
    certificate.coefficient_nonnegative hs hu x

structure MovingObservableCertificate (d : MovingData) (w : Fin 5 → ℚ) (radius : ℚ) where
  timeDegree : Nat
  coefficients : Fin (timeDegree+1) → Fin 1 → QMatrix 5
  coefficient_nonnegative : ∀ i j x, 0 ≤ quadratic (coefficients i j) x
  binding : ∀ s, observableMargin (movingMetric d s) d.radiusSq radius
    (fun i => (w i : ℝ)) = tensorMatrix coefficients s 0

theorem moving_observable (d : MovingData) (w : Fin 5 → ℚ) (radius : ℚ)
    (certificate : MovingObservableCertificate d w radius)
    (hC : 0 < d.radiusSq) (hr : 0 < radius) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (x : State) (hx : movingEnergy d s x ≤ d.radiusSq) :
    |∑ i, (w i : ℝ)*(x i-movingCenter d s i)| ≤ radius := by
  apply observable_contained (movingMetric d s) d.radiusSq radius
    (fun i => (w i : ℝ)) (x-movingCenter d s)
  · exact_mod_cast hC
  · exact_mod_cast hr
  · rw [certificate.binding]
    exact tensor_nonnegative_of_coefficients certificate.coefficients
      certificate.coefficient_nonnegative hs (by norm_num) _
  · exact hx

/-- A coordinate bound extracted from a checked moving observable margin. -/
theorem moving_coordinate (d : MovingData) (i : Fin 5) (radius : ℚ)
    (certificate : MovingObservableCertificate d (coordinate i) radius)
    (hC : 0 < d.radiusSq) (hr : 0 < radius) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (x : State) (hx : movingEnergy d s x ≤ d.radiusSq) :
    |x i-movingCenter d s i| ≤ radius := by
  have h := moving_observable d (coordinate i) radius certificate hC hr s hs x hx
  simpa only [coordinate_cast, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

structure MovingCertificate (d : MovingData) where
  width : 0 < d.step
  radius_positive : 0 < d.radiusSq
  c_positive : 0 < d.cBound
  feedback_positive : 0 < d.feedbackBound
  margin_positive : 0 < d.margin
  center_guard : ∀ s ∈ Set.Icc (0 : ℝ) 1,
    0 < kappa+movingCenter d s 3-d.feedbackBound
  symmetric : ∀ s i j, movingMetric d s i j = movingMetric d s j i
  capacity : MovingObservableCertificate d (coordinate 4) d.cBound
  feedback : MovingObservableCertificate d (coordinate 3) d.feedbackBound
  negative : MovingBlockCertificate d (-d.cBound)
  positive : MovingBlockCertificate d d.cBound

theorem moving_drift (d : MovingData) (certificate : MovingCertificate d)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x : State)
    (hx : movingEnergy d s x ≤ d.radiusSq) :
    energyRate d.load (movingMetric d s) (movingMetricRate d s)
      (movingCenter d s) (movingCenterRate d s) x ≤
      (d.decay : ℝ)*(d.radiusSq-movingEnergy d s x)-d.margin := by
  let p := movingCenter d s
  let e := x-p
  have hc := moving_observable d (coordinate 4) d.cBound certificate.capacity
    certificate.radius_positive certificate.c_positive s hs x hx
  have hb := moving_observable d (coordinate 3) d.feedbackBound certificate.feedback
    certificate.radius_positive certificate.feedback_positive s hs x hx
  have hc0 : |e 4| ≤ (d.cBound : ℝ) := by simpa [coordinate_cast, e, p] using hc
  have hb0 : |e 3| ≤ (d.feedbackBound : ℝ) := by simpa [coordinate_cast, e, p] using hb
  have hc' : e 4 ∈ Set.Icc (-(d.cBound : ℝ)) (d.cBound : ℝ) := abs_le.mp hc0
  have hb' : e 3 ∈ Set.Icc (-(d.feedbackBound : ℝ)) (d.feedbackBound : ℝ) := abs_le.mp hb0
  have hdb : (0 : ℝ) < d.feedbackBound := by exact_mod_cast certificate.feedback_positive
  have hdc : (0 : ℝ) < d.cBound := by exact_mod_cast certificate.c_positive
  let u := (e 3+(d.feedbackBound : ℝ))/(2*(d.feedbackBound : ℝ))
  have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · apply div_nonneg <;> linarith [hb'.1]
    · apply (div_le_one (by positivity : (0 : ℝ) < 2*(d.feedbackBound : ℝ))).mpr
      linarith [hb'.2]
  have heb : movingFeedback d u = e 3 := by
    dsimp [movingFeedback, u]
    field_simp [ne_of_gt hdb]
    ring
  have hn (z : Fin 6 → ℝ) := certificate.negative.nonnegative hs hu z
  have hp (z : Fin 6 → ℝ) := certificate.positive.nonnegative hs hu z
  simp only [movingBlock, Rat.cast_neg, heb] at hn hp
  have hblock := driftBlock_nonnegative (d.load : ℝ) p (movingCenterRate d s)
    (movingMetric d s) (movingMetricRate d s) d.radiusSq d.decay d.margin
    (-(d.cBound : ℝ)) d.cBound (e 3) (e 4) (by linarith) hc' hn hp (Matrix.vecCons 1 e)
  have hcenter : 0 < kappa+p 3 := by linarith [certificate.center_guard s hs]
  have hactual : 0 < kappa+p 3+e 3 := by linarith [certificate.center_guard s hs, hb'.1]
  have h := drift_bound d.load p (movingCenterRate d s) e (movingMetric d s)
    (movingMetricRate d s) d.radiusSq d.decay d.margin (certificate.symmetric s)
    hcenter hactual hblock
  have he : p+e = x := by simp [e]
  simpa only [he, movingEnergy, energy] using h

theorem moving_invariant (d : MovingData) (certificate : MovingCertificate d)
    (x : ℝ → State) (hx : Solves d.load d.tStart ((d.tStart : ℝ)+d.step) x)
    (initial : movingEnergy d 0 (x d.tStart) ≤ d.radiusSq) :
    ∀ t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ)+d.step),
      movingEnergy d (movingTime d t) (x t) ≤ d.radiusSq := by
  apply tube_invariant d.load d.tStart ((d.tStart : ℝ)+d.step) d.radiusSq d.decay d.margin
    (fun t => movingMetric d (movingTime d t))
    (fun t => movingMetricRate d (movingTime d t))
    (fun t => movingCenter d (movingTime d t))
    (fun t => movingCenterRate d (movingTime d t)) x
  · intro t _ i j
    exact (movingMetric_derivative d (ne_of_gt certificate.width) t i j).hasDerivWithinAt
  · intro t _ i
    exact (movingCenter_derivative d (ne_of_gt certificate.width) t i).hasDerivWithinAt
  · exact hx
  · exact_mod_cast certificate.margin_positive
  · simpa only [movingTime, sub_self, zero_div, movingEnergy] using initial
  · intro t ht hbound
    exact moving_drift d certificate (movingTime d t)
      (movingTime_mem d certificate.width t (Set.Ico_subset_Icc_self ht)) (x t)
      (le_of_eq hbound)

#print axioms moving_invariant
end Gimle.Forseti.Examples.LoadedSAIFCertificates
