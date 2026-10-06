import Gimle.Forseti.Examples.AIFDriftData

/-! Independent drift target for the saved AIF slab. Derivatives below are
physical-time polynomial formulas (ds/dt = 10). No trajectory or circuit
contract is assumed or concluded in this module. -/
namespace Gimle.Forseti.Examples.AIFDriftModel
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFDriftData

noncomputable def hermite (a b c d : ℚ) (s : ℝ) : ℝ :=
  (a : ℝ) + s * (c / 10 : ℚ) + s^2 * (3*(b-a)-(2*c+d)/10 : ℚ) +
    s^3 * (2*(a-b)+(c+d)/10 : ℚ)

noncomputable def hermiteRate (a b c d : ℚ) (s : ℝ) : ℝ :=
  (c : ℝ) + 20*s * (3*(b-a)-(2*c+d)/10 : ℚ) +
    30*s^2 * (2*(a-b)+(c+d)/10 : ℚ)

noncomputable def center (s u : ℝ) (i : Fin 4) : ℝ :=
  hermite (loStart i) (loEnd i) (loStartSlope i) (loEndSlope i) s +
  u * (hermite (hiStart i) (hiEnd i) (hiStartSlope i) (hiEndSlope i) s -
    hermite (loStart i) (loEnd i) (loStartSlope i) (loEndSlope i) s)

noncomputable def centerRate (s u : ℝ) (i : Fin 4) : ℝ :=
  hermiteRate (loStart i) (loEnd i) (loStartSlope i) (loEndSlope i) s +
  u * (hermiteRate (hiStart i) (hiEnd i) (hiStartSlope i) (hiEndSlope i) s -
    hermiteRate (loStart i) (loEnd i) (loStartSlope i) (loEndSlope i) s)

noncomputable def metric (s : ℝ) (i j : Fin 4) : ℝ :=
  (AIFMetricPilot.startMetric i j : ℝ) + s * (AIFMetricPilot.linear i j : ℝ) +
    s^2 * (AIFMetricPilot.quadraticTerm i j : ℝ) +
    s^3 * (AIFMetricPilot.cubicTerm i j : ℝ)

noncomputable def metricRate (s : ℝ) (i j : Fin 4) : ℝ :=
  10 * ((AIFMetricPilot.linear i j : ℝ) + 2*s * (AIFMetricPilot.quadraticTerm i j : ℝ) +
    3*s^2 * (AIFMetricPilot.cubicTerm i j : ℝ))

noncomputable def eta (u : ℝ) : ℝ := 8 + u/2

/-- Shifted AIF field in coordinates (x1-2,x2-2,z1-2,eta*z2-1). -/
noncomputable def field (eta : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-y 0 + y 2, y 0 - y 1, -y 2 - (2+y 2)*y 3,
    eta*(y 1-y 2-(2+y 2)*y 3)]

noncomputable def residual (s u : ℝ) (i : Fin 4) : ℝ :=
  field (eta u) (center s u) i - centerRate s u i

/-- Exact difference matrix; the nonlinear error coordinate is retained. -/
noncomputable def errorMatrix (s u ec : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-1, 0, 1, 0], ![1, -1, 0, 0],
    ![0, 0, -(1+center s u 3), -(2+center s u 2+ec)],
    ![0, eta u, -eta u*(1+center s u 3), -eta u*(2+center s u 2+ec)]]

noncomputable def pr (s u : ℝ) (i : Fin 4) : ℝ :=
  ∑ k, metric s i k * residual s u k

/-- Negative error-energy matrix, minus alpha P, alpha=1/100. -/
noncomputable def q (s u ec : ℝ) (i j : Fin 4) : ℝ :=
  -metricRate s i j - (∑ k, metric s i k * errorMatrix s u ec k j) -
    (∑ k, errorMatrix s u ec k i * metric s k j) - metric s i j / 100

/-- Augmented supply matrix; alpha R - delta = 3/16000000. -/
noncomputable def block (s u ec : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![3/16000000, -pr s u 0, -pr s u 1, -pr s u 2, -pr s u 3],
    ![-pr s u 0, q s u ec 0 0, q s u ec 0 1, q s u ec 0 2, q s u ec 0 3],
    ![-pr s u 1, q s u ec 1 0, q s u ec 1 1, q s u ec 1 2, q s u ec 1 3],
    ![-pr s u 2, q s u ec 2 0, q s u ec 2 1, q s u ec 2 2, q s u ec 2 3],
    ![-pr s u 3, q s u ec 3 0, q s u ec 3 1, q s u ec 3 2, q s u ec 3 3]]

/-- Derivative of a cubic with coefficients in the indicated power order. -/
theorem cubic_derivative (a b c d s : ℝ) :
    HasDerivAt (fun x => a + x*b + x^2*c + x^3*d)
      (b + 2*s*c + 3*s^2*d) s := by
  convert! (((hasDerivAt_const s a).add ((hasDerivAt_id s).mul_const b)).add
    (((hasDerivAt_id s).pow 2).mul_const c)).add
      (((hasDerivAt_id s).pow 3).mul_const d) using 1
  simp [id_eq]

theorem hermite_derivative (a b c d : ℚ) (s : ℝ) :
    HasDerivAt (hermite a b c d) (hermiteRate a b c d s / 10) s := by
  convert! cubic_derivative (a : ℝ) (c/10 : ℚ)
    (3*(b-a)-(2*c+d)/10 : ℚ) (2*(a-b)+(c+d)/10 : ℚ) s using 1
  simp [hermiteRate]
  ring

theorem center_derivative (s u : ℝ) (i : Fin 4) :
    HasDerivAt (fun z => center z u i) (centerRate s u i / 10) s := by
  have lo := hermite_derivative (loStart i) (loEnd i)
    (loStartSlope i) (loEndSlope i) s
  have hi := hermite_derivative (hiStart i) (hiEnd i)
    (hiStartSlope i) (hiEndSlope i) s
  convert! lo.add ((hi.sub lo).const_mul u) using 1
  dsimp [centerRate]
  ring

theorem metric_derivative (s : ℝ) (i j : Fin 4) :
    HasDerivAt (fun z => metric z i j) (metricRate s i j / 10) s := by
  convert! cubic_derivative (AIFMetricPilot.startMetric i j : ℝ)
    (AIFMetricPilot.linear i j : ℝ) (AIFMetricPilot.quadraticTerm i j : ℝ)
    (AIFMetricPilot.cubicTerm i j : ℝ) s using 1
  simp [metricRate]

theorem center_derivative_physical (t u : ℝ) (i : Fin 4) :
    HasDerivAt (fun z => center (10*(z-33/5)) u i)
      (centerRate (10*(t-33/5)) u i) t := by
  have h := (center_derivative (10*(t-33/5)) u i).comp t
    (((hasDerivAt_id t).sub_const (33/5)).const_mul 10)
  convert! h using 1
  simp

theorem metric_derivative_physical (t : ℝ) (i j : Fin 4) :
    HasDerivAt (fun z => metric (10*(z-33/5)) i j)
      (metricRate (10*(t-33/5)) i j) t := by
  have h := (metric_derivative (10*(t-33/5)) i j).comp t
    (((hasDerivAt_id t).sub_const (33/5)).const_mul 10)
  convert! h using 1
  simp

/-- The retained nonlinear coordinate gives the exact field difference. -/
theorem field_difference (s u : ℝ) (e : Fin 4 → ℝ) :
    field (eta u) (center s u + e) - field (eta u) (center s u) =
      fun i => ∑ j, errorMatrix s u (e 2) i j * e j := by
  ext i
  fin_cases i <;>
    simp [field, errorMatrix, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_succ] <;> ring

/-- The time-varying metric is symmetric, checked from its rational data. -/
theorem metric_symmetric (s : ℝ) (i j : Fin 4) : metric s i j = metric s j i := by
  fin_cases i <;> fin_cases j <;>
    norm_num [metric, AIFMetricPilot.startMetric, AIFMetricPilot.linear,
      AIFMetricPilot.quadraticTerm, AIFMetricPilot.cubicTerm,
      AIFMetricPilot.endMetric, AIFMetricPilot.startSlope,
      AIFMetricPilot.endSlope, scale]

#print axioms field_difference
end Gimle.Forseti.Examples.AIFDriftModel
