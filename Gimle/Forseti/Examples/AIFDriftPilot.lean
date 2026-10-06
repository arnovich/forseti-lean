import Gimle.Forseti.Examples.AIFDriftNegative
import Gimle.Forseti.Examples.AIFDriftPositive

/-! One complete AIF drift box, not a full startup trajectory theorem. -/
namespace Gimle.Forseti.Examples.AIFDriftPilot
open Gimle.Forseti.BernsteinMatrix AIFDriftModel

set_option maxHeartbeats 4000000 in
/-- The matrix is affine in the retained nonlinear error coordinate. -/
theorem block_interpolation (s u ec : ℝ) (x : Fin 5 → ℝ) :
    matrixForm (block s u ec) x =
      (1/2 - (100/3)*ec) * matrixForm (block s u (-1*(3/200))) x +
      (1/2 + (100/3)*ec) * matrixForm (block s u (1*(3/200))) x := by
  simp [matrixForm, block, q, errorMatrix, Fin.sum_univ_succ]
  ring

theorem block_nonnegative (s u ec : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (he : ec ∈ Set.Icc (-3/200 : ℝ) (3/200)) (x : Fin 5 → ℝ) :
    0 ≤ matrixForm (block s u ec) x := by
  rw [block_interpolation]
  exact add_nonneg
    (mul_nonneg (by linarith [he.2]) (AIFDriftNegative.nonnegative s u hs hu x))
    (mul_nonneg (by linarith [he.1]) (AIFDriftPositive.nonnegative s u hs hu x))

/-- Error velocity, retaining the residual from the moving center. -/
noncomputable def errorVelocity (s u : ℝ) (e : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  (∑ j, errorMatrix s u (e 2) i j * e j) + residual s u i

theorem errorVelocity_eq (s u : ℝ) (e : Fin 4 → ℝ) (i : Fin 4) :
    errorVelocity s u e i = field (eta u) (center s u + e) i - centerRate s u i := by
  have h := congrFun (field_difference s u e) i
  simp only [Pi.sub_apply] at h
  dsimp [errorVelocity, AIFDriftModel.residual]
  linarith

/-- Algebraic chain-rule expression for the moving error energy. -/
noncomputable def energyRate (s u : ℝ) (e : Fin 4 → ℝ) : ℝ :=
  matrixForm (metricRate s) e +
    ∑ i, ∑ j, (errorVelocity s u e i * metric s i j * e j +
      e i * metric s i j * errorVelocity s u e j)

set_option maxHeartbeats 8000000 in
theorem block_energy_identity (s u : ℝ) (e : Fin 4 → ℝ) :
    matrixForm (block s u (e 2)) (Fin.cons 1 e) =
      (1/100) * (1/40000 - matrixForm (metric s) e) - 1/16000000 -
        energyRate s u e := by
  simp [energyRate, errorVelocity, matrixForm, block, q, pr, Fin.sum_univ_succ]
  simp only [metric_symmetric s 1 0, metric_symmetric s 2 0,
    metric_symmetric s 3 0, metric_symmetric s 2 1,
    metric_symmetric s 3 1, metric_symmetric s 3 2]
  ring

/-- Strict dissipative margin on the entire time/parameter/error box. -/
theorem drift_bound (s u : ℝ) (e : Fin 4 → ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (he : e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200)) :
    energyRate s u e ≤ (1/100) * (1/40000 - matrixForm (metric s) e) - 1/16000000 := by
  have h := block_nonnegative s u (e 2) hs hu he (Fin.cons 1 e)
  rw [block_energy_identity] at h
  linarith

/-- Physical time and fixed eta, with both interval endpoints included. -/
theorem drift_bound_physical (t eta₀ : ℝ) (e : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc (33/5 : ℝ) (67/10))
    (hp : eta₀ ∈ Set.Icc (8 : ℝ) (17/2))
    (he : e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200)) :
    energyRate (10*(t-33/5)) (2*(eta₀-8)) e ≤
      (1/100) * (1/40000 - matrixForm (metric (10*(t-33/5))) e) - 1/16000000 := by
  apply drift_bound _ _ _ _ _ he
  · constructor <;> linarith [ht.1, ht.2]
  · constructor <;> linarith [hp.1, hp.2]

#print axioms drift_bound_physical
end Gimle.Forseti.Examples.AIFDriftPilot
