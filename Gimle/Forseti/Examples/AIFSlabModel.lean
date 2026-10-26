module

public import Gimle.Forseti.Examples.AIFDriftModel

/-! One slab of the AIF moving tube: exact rational time and parameter bounds, and
cubic Hermite interpolation of the tube center and metric between endpoint values
and physical-time slopes. The drift identities and the pointwise dissipative margin
are stated over this data; no certificate or trajectory is assumed by it. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFSlabModel
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFDriftModel (field cubic_derivative)

/-- Rational inputs for one physical-time and parameter slab. -/
structure Slab where
  tStart : ℚ
  step : ℚ
  etaLo : ℚ
  etaHi : ℚ
  loStart : Fin 4 → ℚ
  loEnd : Fin 4 → ℚ
  loStartSlope : Fin 4 → ℚ
  loEndSlope : Fin 4 → ℚ
  hiStart : Fin 4 → ℚ
  hiEnd : Fin 4 → ℚ
  hiStartSlope : Fin 4 → ℚ
  hiEndSlope : Fin 4 → ℚ
  startMetric : QMatrix 4
  endMetric : QMatrix 4
  startMetricSlope : QMatrix 4
  endMetricSlope : QMatrix 4

noncomputable def hermite (h a b c d : ℚ) (s : ℝ) : ℝ :=
  (a : ℝ) + s * (h*c : ℚ) + s^2 * (3*(b-a)-h*(2*c+d) : ℚ) +
    s^3 * (2*(a-b)+h*(c+d) : ℚ)

noncomputable def hermiteRate (h a b c d : ℚ) (s : ℝ) : ℝ :=
  ((h*c : ℚ) + 2*s * (3*(b-a)-h*(2*c+d) : ℚ) +
    3*s^2 * (2*(a-b)+h*(c+d) : ℚ)) / (h : ℝ)

noncomputable def timeCoordinate (d : Slab) (t : ℝ) : ℝ :=
  (t - d.tStart) / d.step

noncomputable def etaCoordinate (d : Slab) (p : ℝ) : ℝ :=
  (p - d.etaLo) / ((d.etaHi : ℝ) - d.etaLo)

noncomputable def center (d : Slab) (s u : ℝ) (i : Fin 4) : ℝ :=
  hermite d.step (d.loStart i) (d.loEnd i) (d.loStartSlope i) (d.loEndSlope i) s +
  u * (hermite d.step (d.hiStart i) (d.hiEnd i) (d.hiStartSlope i) (d.hiEndSlope i) s -
    hermite d.step (d.loStart i) (d.loEnd i) (d.loStartSlope i) (d.loEndSlope i) s)

noncomputable def centerRate (d : Slab) (s u : ℝ) (i : Fin 4) : ℝ :=
  hermiteRate d.step (d.loStart i) (d.loEnd i) (d.loStartSlope i) (d.loEndSlope i) s +
  u * (hermiteRate d.step (d.hiStart i) (d.hiEnd i) (d.hiStartSlope i) (d.hiEndSlope i) s -
    hermiteRate d.step (d.loStart i) (d.loEnd i) (d.loStartSlope i) (d.loEndSlope i) s)

noncomputable def metric (d : Slab) (s : ℝ) (i j : Fin 4) : ℝ :=
  hermite d.step (d.startMetric i j) (d.endMetric i j)
    (d.startMetricSlope i j) (d.endMetricSlope i j) s

noncomputable def metricRate (d : Slab) (s : ℝ) (i j : Fin 4) : ℝ :=
  hermiteRate d.step (d.startMetric i j) (d.endMetric i j)
    (d.startMetricSlope i j) (d.endMetricSlope i j) s

noncomputable def eta (d : Slab) (u : ℝ) : ℝ :=
  d.etaLo + u * ((d.etaHi : ℝ) - d.etaLo)

noncomputable def residual (d : Slab) (s u : ℝ) (i : Fin 4) : ℝ :=
  field (eta d u) (center d s u) i - centerRate d s u i

/-- Exact difference matrix; the nonlinear error coordinate is retained. -/
noncomputable def errorMatrix (d : Slab) (s u ec : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-1, 0, 1, 0], ![1, -1, 0, 0],
    ![0, 0, -(1+center d s u 3), -(2+center d s u 2+ec)],
    ![0, eta d u, -eta d u*(1+center d s u 3), -eta d u*(2+center d s u 2+ec)]]

noncomputable def pr (d : Slab) (s u : ℝ) (i : Fin 4) : ℝ :=
  ∑ k, metric d s i k * residual d s u k

/-- Negative error-energy matrix, minus alpha P, alpha=1/100. -/
noncomputable def q (d : Slab) (s u ec : ℝ) (i j : Fin 4) : ℝ :=
  -metricRate d s i j - (∑ k, metric d s i k * errorMatrix d s u ec k j) -
    (∑ k, errorMatrix d s u ec k i * metric d s k j) - metric d s i j / 100

/-- Augmented supply matrix; alpha R - delta = 3/16000000. -/
noncomputable def block (d : Slab) (s u ec : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![3/16000000, -pr d s u 0, -pr d s u 1, -pr d s u 2, -pr d s u 3],
    ![-pr d s u 0, q d s u ec 0 0, q d s u ec 0 1, q d s u ec 0 2, q d s u ec 0 3],
    ![-pr d s u 1, q d s u ec 1 0, q d s u ec 1 1, q d s u ec 1 2, q d s u ec 1 3],
    ![-pr d s u 2, q d s u ec 2 0, q d s u ec 2 1, q d s u ec 2 2, q d s u ec 2 3],
    ![-pr d s u 3, q d s u ec 3 0, q d s u ec 3 1, q d s u ec 3 2, q d s u ec 3 3]]

theorem hermite_derivative (h a b c d : ℚ) (hh : h ≠ 0) (s : ℝ) :
    HasDerivAt (hermite h a b c d) (hermiteRate h a b c d s * (h : ℝ)) s := by
  have hr : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  convert! cubic_derivative (a : ℝ) (h*c : ℚ) (3*(b-a)-h*(2*c+d) : ℚ)
    (2*(a-b)+h*(c+d) : ℚ) s using 1
  simp [hermiteRate, hr]

theorem center_derivative (d : Slab) (hh : d.step ≠ 0) (s u : ℝ) (i : Fin 4) :
    HasDerivAt (fun z => center d z u i) (centerRate d s u i * (d.step : ℝ)) s := by
  have lo := hermite_derivative d.step (d.loStart i) (d.loEnd i)
    (d.loStartSlope i) (d.loEndSlope i) hh s
  have hi := hermite_derivative d.step (d.hiStart i) (d.hiEnd i)
    (d.hiStartSlope i) (d.hiEndSlope i) hh s
  convert! lo.add ((hi.sub lo).const_mul u) using 1
  dsimp [centerRate]
  ring

theorem center_derivative_physical (d : Slab) (hh : d.step ≠ 0)
    (t u : ℝ) (i : Fin 4) :
    HasDerivAt (fun z => center d (timeCoordinate d z) u i)
      (centerRate d (timeCoordinate d t) u i) t := by
  have hr : (d.step : ℝ) ≠ 0 := by exact_mod_cast hh
  have hc := (center_derivative d hh (timeCoordinate d t) u i).comp t
    (((hasDerivAt_id t).sub_const (d.tStart : ℝ)).div_const (d.step : ℝ))
  convert! hc using 1
  simp [timeCoordinate, hr, div_eq_mul_inv]

theorem metric_derivative_physical (d : Slab) (hh : d.step ≠ 0)
    (t : ℝ) (i j : Fin 4) :
    HasDerivAt (fun z => metric d (timeCoordinate d z) i j)
      (metricRate d (timeCoordinate d t) i j) t := by
  have hr : (d.step : ℝ) ≠ 0 := by exact_mod_cast hh
  have hc := (hermite_derivative d.step (d.startMetric i j) (d.endMetric i j)
    (d.startMetricSlope i j) (d.endMetricSlope i j) hh (timeCoordinate d t)).comp t
      (((hasDerivAt_id t).sub_const (d.tStart : ℝ)).div_const (d.step : ℝ))
  convert! hc using 1
  simp [metricRate, timeCoordinate, hr, div_eq_mul_inv]

theorem timeCoordinate_mem (d : Slab) (hh : 0 < d.step) (t : ℝ)
    (ht : t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step)) :
    timeCoordinate d t ∈ Set.Icc (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < d.step := by exact_mod_cast hh
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hr.le,
    (div_le_one hr).2 (by linarith [ht.2])⟩

theorem etaCoordinate_mem (d : Slab) (hp : d.etaLo < d.etaHi) (p : ℝ)
    (he : p ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ)) :
    etaCoordinate d p ∈ Set.Icc (0 : ℝ) 1 := by
  have hr : (d.etaLo : ℝ) < d.etaHi := by exact_mod_cast hp
  exact ⟨div_nonneg (sub_nonneg.mpr he.1) (sub_pos.mpr hr).le,
    (div_le_one (sub_pos.mpr hr)).2 (by linarith [he.2])⟩

theorem eta_coordinate_inverse (d : Slab) (hp : d.etaLo < d.etaHi) (p : ℝ) :
    eta d (etaCoordinate d p) = p := by
  have hr : (d.etaLo : ℝ) < d.etaHi := by exact_mod_cast hp
  simp [eta, etaCoordinate, ne_of_gt (sub_pos.mpr hr)]

theorem field_difference (d : Slab) (s u : ℝ) (e : Fin 4 → ℝ) :
    field (eta d u) (center d s u + e) - field (eta d u) (center d s u) =
      fun i => ∑ j, errorMatrix d s u (e 2) i j * e j := by
  ext i
  fin_cases i <;>
    simp [field, errorMatrix, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 4000000 in
/-- The matrix is affine in the retained nonlinear error coordinate. -/
theorem block_interpolation (d : Slab) (s u ec : ℝ) (x : Fin 5 → ℝ) :
    matrixForm (block d s u ec) x =
      (1/2 - (100/3)*ec) * matrixForm (block d s u (-1*(3/200))) x +
      (1/2 + (100/3)*ec) * matrixForm (block d s u (1*(3/200))) x := by
  simp [matrixForm, block, q, errorMatrix, Fin.sum_univ_succ]
  ring

theorem block_nonnegative (d : Slab) (s u ec : ℝ)
    (hn : ∀ x, 0 ≤ matrixForm (block d s u (-1*(3/200))) x)
    (hp : ∀ x, 0 ≤ matrixForm (block d s u (1*(3/200))) x)
    (he : ec ∈ Set.Icc (-3/200 : ℝ) (3/200)) (x : Fin 5 → ℝ) :
    0 ≤ matrixForm (block d s u ec) x := by
  rw [block_interpolation]
  exact add_nonneg
    (mul_nonneg (by linarith [he.2]) (hn x))
    (mul_nonneg (by linarith [he.1]) (hp x))

/-- Error velocity, retaining the residual from the moving center. -/
noncomputable def errorVelocity (d : Slab) (s u : ℝ) (e : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (∑ j, errorMatrix d s u (e 2) i j * e j) + residual d s u i

theorem errorVelocity_eq (d : Slab) (s u : ℝ) (e : Fin 4 → ℝ) (i : Fin 4) :
    errorVelocity d s u e i = field (eta d u) (center d s u + e) i - centerRate d s u i := by
  have h := congrFun (field_difference d s u e) i
  simp only [Pi.sub_apply] at h
  dsimp [errorVelocity, AIFSlabModel.residual]
  linarith

/-- Algebraic chain-rule expression for the moving error energy. -/
noncomputable def energyRate (d : Slab) (s u : ℝ) (e : Fin 4 → ℝ) : ℝ :=
  matrixForm (metricRate d s) e +
    ∑ i, ∑ j, (errorVelocity d s u e i * metric d s i j * e j +
      e i * metric d s i j * errorVelocity d s u e j)

set_option maxHeartbeats 8000000 in
theorem block_energy_identity (d : Slab) (s u : ℝ) (e : Fin 4 → ℝ)
    (hsym : ∀ i j, metric d s i j = metric d s j i) :
    matrixForm (block d s u (e 2)) (Fin.cons 1 e) =
      (1/100) * (1/40000 - matrixForm (metric d s) e) - 1/16000000 -
        energyRate d s u e := by
  simp [energyRate, errorVelocity, matrixForm, block, q, pr, Fin.sum_univ_succ]
  simp only [hsym 1 0, hsym 2 0,
    hsym 3 0, hsym 2 1,
    hsym 3 1, hsym 3 2]
  ring

/-- Strict dissipative margin at one point `(s, u, e)` of a slab, given nonnegative
drift blocks at the two error extremes `±3/200` and `e₂` between them. Covering the
whole time/parameter box needs these hypotheses at every point. -/
theorem drift_bound (d : Slab) (s u : ℝ) (e : Fin 4 → ℝ)
    (hsym : ∀ i j, metric d s i j = metric d s j i)
    (hn : ∀ x, 0 ≤ matrixForm (block d s u (-1*(3/200))) x)
    (hp : ∀ x, 0 ≤ matrixForm (block d s u (1*(3/200))) x)
    (he : e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200)) :
    energyRate d s u e ≤ (1/100) * (1/40000 - matrixForm (metric d s) e) - 1/16000000 := by
  have h := block_nonnegative d s u (e 2) hn hp he (Fin.cons 1 e)
  rw [block_energy_identity d s u e hsym] at h
  linarith

#print axioms center_derivative_physical
#print axioms metric_derivative_physical
#print axioms field_difference
#print axioms drift_bound
end Gimle.Forseti.Examples.AIFSlabModel
