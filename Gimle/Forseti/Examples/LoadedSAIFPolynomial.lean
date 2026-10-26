module

public import Gimle.Forseti.Examples.AIFPolynomialBinding
public import Gimle.Forseti.Examples.LoadedSAIFMoving

/-! A checked rational-polynomial encoding of the moving five-species drift block.
Its evaluation theorem binds generated Bernstein tables to the original
physical-time field. Polynomial and table producers are not trusted. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFPolynomial
open Gimle.Forseti.RationalPolynomial
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open LoadedSAIFCertificates

local infixl:65 " ⊞ " => RationalPolynomial.add
local infixl:70 " ⊠ " => RationalPolynomial.mul
local prefix:75 "⊟" => RationalPolynomial.neg

def center (d : MovingData) (i : Fin 5) : Poly :=
  AIFPolynomialBinding.hermite d.step (d.centerStart i) (d.centerEnd i)
    (d.centerStartSlope i) (d.centerEndSlope i)

def centerRate (d : MovingData) (i : Fin 5) : Poly :=
  AIFPolynomialBinding.hermiteRate d.step (d.centerStart i) (d.centerEnd i)
    (d.centerStartSlope i) (d.centerEndSlope i)

def metric (d : MovingData) (i j : Fin 5) : Poly :=
  AIFPolynomialBinding.hermite d.step (d.metricStart i j) (d.metricEnd i j)
    (d.metricStartSlope i j) (d.metricEndSlope i j)

def metricRate (d : MovingData) (i j : Fin 5) : Poly :=
  AIFPolynomialBinding.hermiteRate d.step (d.metricStart i j) (d.metricEnd i j)
    (d.metricStartSlope i j) (d.metricEndSlope i j)

def feedback (d : MovingData) : Poly :=
  constant (-d.feedbackBound) ⊞ constant (2*d.feedbackBound) ⊠ parameter

def denominator (d : MovingData) : Poly :=
  (constant (147261/1000000) ⊞ center d 3) ⊠
    (constant (147261/1000000) ⊞ center d 3 ⊞ feedback d)

def capacityBinding (d : MovingData) : Poly :=
  center d 1 ⊠ (constant d.load ⊞ ⊟(center d 4)) ⊞ ⊟(center d 4)

def clearedMatrix (d : MovingData) (ec : ℚ) : Fin 5 → Fin 5 → Poly :=
  let D := denominator d
  ![![⊟D, constant 0, constant 0, constant (-(316129/100000)*(147261/1000000)), constant 0],
    ![D, D ⊠ (constant (-1-d.load+ec) ⊞ center d 4), constant 0, constant 0,
      D ⊠ (center d 1 ⊞ constant 1)],
    ![constant 0, constant 0,
      D ⊠ (constant (-8) ⊠ (center d 3 ⊞ feedback d) ⊞ constant (-3/100)),
      D ⊠ (constant (-8) ⊠ center d 2), constant 0],
    ![constant 0, D, D ⊠ (constant (-8) ⊠ (center d 3 ⊞ feedback d)),
      D ⊠ (constant (-8) ⊠ center d 2 ⊞ constant (-3/100)), constant 0],
    ![constant 0, D ⊠ (constant (d.load-ec) ⊞ ⊟(center d 4)), constant 0, constant 0,
      D ⊠ (⊟(center d 1) ⊞ constant (-6/5))]]

def clearedResidual (d : MovingData) : Fin 5 → Poly :=
  let D := denominator d
  let p := center d
  let v := centerRate d
  ![constant ((316129/100000)*(147261/1000000)) ⊠
      (constant (147261/1000000) ⊞ p 3 ⊞ feedback d) ⊞ ⊟(D ⊠ (p 0 ⊞ v 0)),
    D ⊠ (p 0 ⊞ ⊟(p 1) ⊞ ⊟(capacityBinding d) ⊞ ⊟(v 1)),
    D ⊠ (constant 2 ⊞ constant (-8) ⊠ p 2 ⊠ p 3 ⊞
      constant (-3/100) ⊠ p 2 ⊞ ⊟(v 2)),
    D ⊠ (p 1 ⊞ constant (-8) ⊠ p 2 ⊠ p 3 ⊞
      constant (-3/100) ⊠ p 3 ⊞ ⊟(v 3)),
    D ⊠ (capacityBinding d ⊞ constant (-1/5) ⊠ p 4 ⊞ ⊟(v 4))]

def residualProduct (d : MovingData) (i : Fin 5) : Poly :=
  finSum fun k => metric d i k ⊠ clearedResidual d k

def driftMatrix (d : MovingData) (ec : ℚ) (i j : Fin 5) : Poly :=
  ⊟(denominator d ⊠ metricRate d i j) ⊞
    ⊟(finSum fun k => metric d i k ⊠ clearedMatrix d ec k j) ⊞
    ⊟(finSum fun k => clearedMatrix d ec k i ⊠ metric d k j) ⊞
    ⊟(constant d.decay ⊠ denominator d ⊠ metric d i j)

def block (d : MovingData) (ec : ℚ) : Fin 6 → Fin 6 → Poly :=
  Matrix.vecCons (Matrix.vecCons (denominator d ⊠ constant (d.decay*d.radiusSq-d.margin))
    (fun j => ⊟(residualProduct d j)))
    (fun i => Matrix.vecCons (⊟(residualProduct d i)) (driftMatrix d ec i))

@[simp] theorem eval_center (d : MovingData) (s u : ℝ) (i : Fin 5) :
    eval (center d i) s u = movingCenter d s i := by simp [center, movingCenter]

@[simp] theorem eval_centerRate (d : MovingData) (s u : ℝ) (i : Fin 5) :
    eval (centerRate d i) s u = movingCenterRate d s i := by
  simp [centerRate, movingCenterRate]

@[simp] theorem eval_metric (d : MovingData) (s u : ℝ) (i j : Fin 5) :
    eval (metric d i j) s u = movingMetric d s i j := by simp [metric, movingMetric]

@[simp] theorem eval_metricRate (d : MovingData) (s u : ℝ) (i j : Fin 5) :
    eval (metricRate d i j) s u = movingMetricRate d s i j := by
  simp [metricRate, movingMetricRate]

@[simp] theorem eval_feedback (d : MovingData) (s u : ℝ) :
    eval (feedback d) s u = movingFeedback d u := by simp [feedback, movingFeedback]

@[simp] theorem eval_denominator (d : MovingData) (s u : ℝ) :
    eval (denominator d) s u =
      LoadedSAIFCertificates.denominator (movingCenter d s) (movingFeedback d u) := by
  simp [denominator, LoadedSAIFCertificates.denominator, LoadedSAIFModel.kappa]

@[simp] theorem eval_capacityBinding (d : MovingData) (s u : ℝ) :
    eval (capacityBinding d) s u = LoadedSAIFModel.binding d.load (movingCenter d s) := by
  simp [capacityBinding, LoadedSAIFModel.binding, sub_eq_add_neg]

@[simp] theorem eval_clearedMatrix (d : MovingData) (ec : ℚ) (s u : ℝ) (i j : Fin 5) :
    eval (clearedMatrix d ec i j) s u =
      LoadedSAIFCertificates.clearedMatrix d.load (movingCenter d s) ec
        (movingFeedback d u) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [clearedMatrix, LoadedSAIFCertificates.clearedMatrix, LoadedSAIFModel.alpha,
      LoadedSAIFModel.kappa, LoadedSAIFModel.dilution] <;> ring_nf <;> simp

@[simp] theorem eval_clearedResidual (d : MovingData) (s u : ℝ) (i : Fin 5) :
    eval (clearedResidual d i) s u =
      LoadedSAIFCertificates.clearedResidual d.load (movingCenter d s)
        (movingCenterRate d s) (movingFeedback d u) i := by
  fin_cases i <;>
    simp [clearedResidual, LoadedSAIFCertificates.clearedResidual, LoadedSAIFModel.alpha,
      LoadedSAIFModel.kappa, LoadedSAIFModel.dilution] <;> ring_nf <;> simp

@[simp] theorem eval_residualProduct (d : MovingData) (s u : ℝ) (i : Fin 5) :
    eval (residualProduct d i) s u =
      LoadedSAIFCertificates.residualProduct d.load (movingCenter d s)
        (movingCenterRate d s) (movingMetric d s) (movingFeedback d u) i := by
  simp [residualProduct, LoadedSAIFCertificates.residualProduct]

@[simp] theorem eval_driftMatrix (d : MovingData) (ec : ℚ) (s u : ℝ) (i j : Fin 5) :
    eval (driftMatrix d ec i j) s u =
      LoadedSAIFCertificates.driftMatrix d.load (movingCenter d s)
        (movingMetric d s) (movingMetricRate d s) d.decay ec (movingFeedback d u) i j := by
  simp [driftMatrix, LoadedSAIFCertificates.driftMatrix, sub_eq_add_neg]

theorem eval_block (d : MovingData) (ec : ℚ) (s u : ℝ) (i j : Fin 6) :
    eval (block d ec i j) s u = movingBlock d ec s u i j := by
  fin_cases i <;> fin_cases j <;>
    simp [block, movingBlock, driftBlock, sub_eq_add_neg]

/-- Exact rational table checks supply the missing real matrix binding. -/
theorem binding {td pd : Nat} (d : MovingData) (ec : ℚ)
    (c : Fin (td+1) → Fin (pd+1) → QMatrix 6)
    (checked : ∀ i j, BernsteinConversion.tableMatches (block d ec) c i j = true)
    (s u : ℝ) : movingBlock d ec s u = tensorMatrix c s u := by
  rw [← BernsteinConversion.binding (block d ec) c checked s u]
  ext i j
  exact (eval_block d ec s u i j).symm

/-- An independently checked normal form avoids recomputing the field polynomial
for every Bernstein coefficient. Both equivalence and table binding stay exact. -/
theorem binding_of_normalized {td pd : Nat} (d : MovingData) (ec : ℚ)
    (normalized : Fin 6 → Fin 6 → Poly)
    (c : Fin (td+1) → Fin (pd+1) → QMatrix 6)
    (equivalent_checked : ∀ i j, equivalent (block d ec i j) (normalized i j) = true)
    (table_checked : ∀ i j, BernsteinConversion.tableMatches normalized c i j = true)
    (s u : ℝ) : movingBlock d ec s u = tensorMatrix c s u := by
  rw [← BernsteinConversion.binding normalized c table_checked s u]
  ext i j
  exact (eval_block d ec s u i j).symm.trans
    (eval_eq_of_equivalent (equivalent_checked i j) s u)

def certificateOfCheck {td pd : Nat} (d : MovingData) (ec : ℚ)
    (c : Fin (td+1) → Fin (pd+1) → QMatrix 6)
    (squares : Fin (td+1) → Fin (pd+1) → WeightedSquares 6)
    (valid : ∀ i j, (squares i j).Represents (c i j))
    (checked : ∀ i j, BernsteinConversion.tableMatches (block d ec) c i j = true) :
    MovingBlockCertificate d ec where
  timeDegree := td
  parameterDegree := pd
  coefficients := c
  coefficient_nonnegative := fun i j x => (squares i j).nonnegative _ (valid i j) x
  binding := binding d ec c checked

def observable (d : MovingData) (w : Fin 5 → ℚ) (radius : ℚ) (i j : Fin 5) : Poly :=
  metric d i j ⊞ constant (-(d.radiusSq/radius^2*w i*w j))

@[simp] theorem eval_observable (d : MovingData) (w : Fin 5 → ℚ) (radius : ℚ)
    (s u : ℝ) (i j : Fin 5) :
    eval (observable d w radius i j) s u =
      observableMargin (movingMetric d s) d.radiusSq radius (fun k => (w k : ℝ)) i j := by
  simp [observable, observableMargin, sub_eq_add_neg]

def observableCertificateOfCheck {td : Nat} (d : MovingData) (w : Fin 5 → ℚ) (radius : ℚ)
    (c : Fin (td+1) → Fin 1 → QMatrix 5)
    (squares : Fin (td+1) → Fin 1 → WeightedSquares 5)
    (valid : ∀ i j, (squares i j).Represents (c i j))
    (checked : ∀ i j, BernsteinConversion.tableMatches (observable d w radius) c i j = true) :
    MovingObservableCertificate d w radius where
  timeDegree := td
  coefficients := c
  coefficient_nonnegative := fun i j x => (squares i j).nonnegative _ (valid i j) x
  binding := by
    intro s
    rw [← BernsteinConversion.binding (observable d w radius) c checked s 0]
    ext i j
    exact (eval_observable d w radius s 0 i j).symm

#print axioms eval_block
#print axioms binding
#print axioms binding_of_normalized
end Gimle.Forseti.Examples.LoadedSAIFPolynomial
