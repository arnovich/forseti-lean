import Gimle.Forseti.Examples.AIFSlabModel
import Gimle.Forseti.RationalPolynomial

/-! Rational polynomial encoding of the independently stated AIF slab model.
The shared evaluation proofs separate algebra from per-slab coefficient checking. -/
namespace Gimle.Forseti.Examples.AIFPolynomialBinding
open Gimle.Forseti.RationalPolynomial
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFSlabModel (Slab)

local infixl:65 " ⊞ " => RationalPolynomial.add
local infixl:70 " ⊠ " => RationalPolynomial.mul
local prefix:75 "⊟" => RationalPolynomial.neg

def hermite (h a b c d : ℚ) : Poly :=
  constant a ⊞ time ⊠ constant (h*c) ⊞
    power time 2 ⊠ constant (3*(b-a)-h*(2*c+d)) ⊞
    power time 3 ⊠ constant (2*(a-b)+h*(c+d))

def hermiteRate (h a b c d : ℚ) : Poly :=
  (constant (h*c) ⊞ constant 2 ⊠ time ⊠ constant (3*(b-a)-h*(2*c+d)) ⊞
    constant 3 ⊠ power time 2 ⊠ constant (2*(a-b)+h*(c+d))) ⊠ constant h⁻¹

def center (d : Slab) (i : Fin 4) : Poly :=
  let lo := hermite d.step (d.loStart i) (d.loEnd i) (d.loStartSlope i) (d.loEndSlope i)
  let hi := hermite d.step (d.hiStart i) (d.hiEnd i) (d.hiStartSlope i) (d.hiEndSlope i)
  lo ⊞ parameter ⊠ (hi ⊞ ⊟lo)

def centerRate (d : Slab) (i : Fin 4) : Poly :=
  let lo := hermiteRate d.step (d.loStart i) (d.loEnd i) (d.loStartSlope i) (d.loEndSlope i)
  let hi := hermiteRate d.step (d.hiStart i) (d.hiEnd i) (d.hiStartSlope i) (d.hiEndSlope i)
  lo ⊞ parameter ⊠ (hi ⊞ ⊟lo)

def metric (d : Slab) (i j : Fin 4) : Poly :=
  hermite d.step (d.startMetric i j) (d.endMetric i j)
    (d.startMetricSlope i j) (d.endMetricSlope i j)

def metricRate (d : Slab) (i j : Fin 4) : Poly :=
  hermiteRate d.step (d.startMetric i j) (d.endMetric i j)
    (d.startMetricSlope i j) (d.endMetricSlope i j)

def eta (d : Slab) : Poly := constant d.etaLo ⊞ parameter ⊠ constant (d.etaHi-d.etaLo)

def field (d : Slab) : Fin 4 → Poly :=
  let m := center d
  ![⊟(m 0) ⊞ m 2, m 0 ⊞ ⊟(m 1), ⊟(m 2) ⊞ ⊟((constant 2 ⊞ m 2) ⊠ m 3),
    eta d ⊠ (m 1 ⊞ ⊟(m 2) ⊞ ⊟((constant 2 ⊞ m 2) ⊠ m 3))]

def residual (d : Slab) (i : Fin 4) : Poly := field d i ⊞ ⊟(centerRate d i)

def errorMatrix (d : Slab) (ec : ℚ) : Fin 4 → Fin 4 → Poly :=
  ![![constant (-1), constant 0, constant 1, constant 0],
    ![constant 1, constant (-1), constant 0, constant 0],
    ![constant 0, constant 0, ⊟(constant 1 ⊞ center d 3),
      ⊟(constant 2 ⊞ center d 2 ⊞ constant ec)],
    ![constant 0, eta d, ⊟(eta d) ⊠ (constant 1 ⊞ center d 3),
      ⊟(eta d) ⊠ (constant 2 ⊞ center d 2 ⊞ constant ec)]]

def pr (d : Slab) (i : Fin 4) : Poly := finSum fun k => metric d i k ⊠ residual d k

def q (d : Slab) (ec : ℚ) (i j : Fin 4) : Poly :=
  ⊟(metricRate d i j) ⊞ ⊟(finSum fun k => metric d i k ⊠ errorMatrix d ec k j) ⊞
    ⊟(finSum fun k => errorMatrix d ec k i ⊠ metric d k j) ⊞
    ⊟(metric d i j ⊠ constant (1/100))

def block (d : Slab) (ec : ℚ) : Fin 5 → Fin 5 → Poly :=
  ![![constant (3/16000000), ⊟(pr d 0), ⊟(pr d 1), ⊟(pr d 2), ⊟(pr d 3)],
    ![⊟(pr d 0), q d ec 0 0, q d ec 0 1, q d ec 0 2, q d ec 0 3],
    ![⊟(pr d 1), q d ec 1 0, q d ec 1 1, q d ec 1 2, q d ec 1 3],
    ![⊟(pr d 2), q d ec 2 0, q d ec 2 1, q d ec 2 2, q d ec 2 3],
    ![⊟(pr d 3), q d ec 3 0, q d ec 3 1, q d ec 3 2, q d ec 3 3]]

@[simp] theorem eval_hermite (h a b c d : ℚ) (s u : ℝ) :
    eval (hermite h a b c d) s u = AIFSlabModel.hermite h a b c d s := by
  simp [hermite, AIFSlabModel.hermite]

@[simp] theorem eval_hermiteRate (h a b c d : ℚ) (s u : ℝ) :
    eval (hermiteRate h a b c d) s u = AIFSlabModel.hermiteRate h a b c d s := by
  simp [hermiteRate, AIFSlabModel.hermiteRate, div_eq_mul_inv]

@[simp] theorem eval_center (d : Slab) (s u : ℝ) (i : Fin 4) :
    eval (center d i) s u = AIFSlabModel.center d s u i := by
  simp [center, AIFSlabModel.center, sub_eq_add_neg]

@[simp] theorem eval_centerRate (d : Slab) (s u : ℝ) (i : Fin 4) :
    eval (centerRate d i) s u = AIFSlabModel.centerRate d s u i := by
  simp [centerRate, AIFSlabModel.centerRate, sub_eq_add_neg]

@[simp] theorem eval_metric (d : Slab) (s u : ℝ) (i j : Fin 4) :
    eval (metric d i j) s u = AIFSlabModel.metric d s i j := by
  simp [metric, AIFSlabModel.metric]

@[simp] theorem eval_metricRate (d : Slab) (s u : ℝ) (i j : Fin 4) :
    eval (metricRate d i j) s u = AIFSlabModel.metricRate d s i j := by
  simp [metricRate, AIFSlabModel.metricRate]

@[simp] theorem eval_eta (d : Slab) (s u : ℝ) :
    eval (eta d) s u = AIFSlabModel.eta d u := by
  simp [eta, AIFSlabModel.eta]

@[simp] theorem eval_field (d : Slab) (s u : ℝ) (i : Fin 4) :
    eval (field d i) s u = AIFDriftModel.field (AIFSlabModel.eta d u)
      (AIFSlabModel.center d s u) i := by
  fin_cases i <;> simp [field, AIFDriftModel.field, sub_eq_add_neg]

@[simp] theorem eval_residual (d : Slab) (s u : ℝ) (i : Fin 4) :
    eval (residual d i) s u = AIFSlabModel.residual d s u i := by
  simp [residual, AIFSlabModel.residual, sub_eq_add_neg]

@[simp] theorem eval_errorMatrix (d : Slab) (ec : ℚ) (s u : ℝ) (i j : Fin 4) :
    eval (errorMatrix d ec i j) s u = AIFSlabModel.errorMatrix d s u ec i j := by
  fin_cases i <;> fin_cases j <;> simp [errorMatrix, AIFSlabModel.errorMatrix]

@[simp] theorem eval_pr (d : Slab) (s u : ℝ) (i : Fin 4) :
    eval (pr d i) s u = AIFSlabModel.pr d s u i := by
  simp [pr, AIFSlabModel.pr]

@[simp] theorem eval_q (d : Slab) (ec : ℚ) (s u : ℝ) (i j : Fin 4) :
    eval (q d ec i j) s u = AIFSlabModel.q d s u ec i j := by
  simp [q, AIFSlabModel.q, sub_eq_add_neg, div_eq_mul_inv]

/-- The polynomial target equals the original model for arbitrary rational slab data. -/
theorem eval_block (d : Slab) (ec : ℚ) (s u : ℝ) (i j : Fin 5) :
    eval (block d ec i j) s u = AIFSlabModel.block d s u ec i j := by
  fin_cases i <;> fin_cases j <;>
    simp [block, AIFSlabModel.block, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]

def bernsteinBasis (degree index : Nat) (v : Poly) : Poly :=
  constant (degree.choose index) ⊠ power v index ⊠
    power (constant 1 ⊞ ⊟v) (degree-index)

/-- Collect each parameter row before multiplying by its time basis. -/
def tensor {n td pd : Nat} (c : Fin (td+1) → Fin (pd+1) → QMatrix n)
    (i j : Fin n) : Poly :=
  finSum fun a => bernsteinBasis td a time ⊠
    (finSum fun b => bernsteinBasis pd b parameter ⊠ constant (c a b i j))

@[simp] theorem eval_bernsteinBasis (degree index : Nat) (v : Poly) (s u : ℝ) :
    eval (bernsteinBasis degree index v) s u = basis degree index (eval v s u) := by
  simp [bernsteinBasis, basis, sub_eq_add_neg]

theorem eval_tensor {n td pd : Nat} (c : Fin (td+1) → Fin (pd+1) → QMatrix n)
    (s u : ℝ) (i j : Fin n) : eval (tensor c i j) s u = tensorMatrix c s u i j := by
  simp [tensor, tensorMatrix, Finset.sum_apply, Finset.mul_sum, mul_assoc]

/-- Only the small rational equality test depends on the concrete slab and table. -/
theorem binding {td pd : Nat} (d : Slab) (ec : ℚ)
    (c : Fin (td+1) → Fin (pd+1) → QMatrix 5)
    (checked : ∀ i j, equivalent (block d ec i j) (tensor c i j) = true)
    (s u : ℝ) : AIFSlabModel.block d s u ec = tensorMatrix c s u := by
  ext i j
  rw [← eval_block, ← eval_tensor]
  exact eval_eq_of_equivalent (checked i j) s u

#print axioms eval_block
#print axioms binding
end Gimle.Forseti.Examples.AIFPolynomialBinding
