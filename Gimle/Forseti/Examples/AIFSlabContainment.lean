module

public import Gimle.Forseti.Examples.AIFSlabModel

/-! The error-coordinate bound `|e₂| ≤ 3/200` used by the drift margin, derived from
an AIF slab's metric tube. The four rational Bernstein matrices it rests on need
checked certificates, which are hypotheses here. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFSlabContainment
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix AIFSlabModel

/-- Subtract exactly radius² / error-bound² = 1/9 in coordinate two. -/
def constantMargin (d : Slab) : QMatrix 4 :=
  fun i j => d.startMetric i j - if i = 2 ∧ j = 2 then 1/9 else 0

def linearMetric (d : Slab) : QMatrix 4 := scale d.step d.startMetricSlope

def quadraticMetric (d : Slab) : QMatrix 4 := fun i j =>
  3 * (d.endMetric i j - d.startMetric i j) -
    d.step * (2 * d.startMetricSlope i j + d.endMetricSlope i j)

def cubicMetric (d : Slab) : QMatrix 4 := fun i j =>
  2 * (d.startMetric i j - d.endMetric i j) +
    d.step * (d.startMetricSlope i j + d.endMetricSlope i j)

/-- The metric margin has degree three in normalized time and no eta dependence. -/
def errorCoefficients (d : Slab) : Fin 4 → Fin 1 → QMatrix 4 :=
  cubicCoefficients (constantMargin d) (linearMetric d) (quadraticMetric d) (cubicMetric d)

noncomputable def errorMargin (d : Slab) (s : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => metric d s i j - if i = 2 ∧ j = 2 then 1/9 else 0

/-- Bind the certificate target to the same Hermite metric used by the drift proof. -/
theorem error_binding (d : Slab) (s u : ℝ) :
    errorMargin d s = tensorMatrix (errorCoefficients d) s u := by
  ext i j
  simp [errorMargin, metric, hermite, tensorMatrix, errorCoefficients,
    cubicCoefficients, constantMargin, linearMetric, quadraticMetric, cubicMetric,
    scale, basis, Fin.sum_univ_succ, Nat.choose]
  split_ifs <;> ring

theorem error_energy_identity (d : Slab) (s : ℝ) (e : Fin 4 → ℝ) :
    matrixForm (errorMargin d s) e = matrixForm (metric d s) e - (e 2)^2/9 := by
  simp [matrixForm, errorMargin, Fin.sum_univ_succ]
  ring

/-- Closed tube membership implies the exact closed error interval. -/
theorem error_contained (d : Slab) (s : ℝ) (e : Fin 4 → ℝ)
    (hm : 0 ≤ matrixForm (errorMargin d s) e)
    (he : matrixForm (metric d s) e ≤ 1/40000) :
    e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200) := by
  rw [error_energy_identity] at hm
  constructor <;> nlinarith [sq_nonneg (e 2 + 3/200), sq_nonneg (e 2 - 3/200)]

/-- Only checked representations, not the proposal algorithm, carry authority. -/
theorem error_contained_of_certificates (d : Slab)
    (certificates : Fin 4 → Fin 1 → WeightedSquares 4)
    (valid : ∀ i j, (certificates i j).Represents (errorCoefficients d i j))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (e : Fin 4 → ℝ)
    (he : matrixForm (metric d s) e ≤ 1/40000) :
    e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200) :=
  error_contained d s e
    (target_nonnegative certificates valid (error_binding d s 0) hs (by norm_num) e) he

#print axioms error_binding
#print axioms error_contained_of_certificates
end Gimle.Forseti.Examples.AIFSlabContainment
