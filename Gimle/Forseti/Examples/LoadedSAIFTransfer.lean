import Gimle.Forseti.Examples.LoadedSAIFCertificates

/-! Exact transfer of a whole five-dimensional quadratic region to another.
The certificate includes the center displacement, not merely the nominal point. -/
namespace Gimle.Forseti.Examples.LoadedSAIFCertificates
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open LoadedSAIFModel

noncomputable def transferBlock (P Q : Matrix5) (shift : State) (C D scale : ℝ) :
    Fin 6 → Fin 6 → ℝ :=
  Matrix.vecCons (Matrix.vecCons (D-scale*C-matrixForm Q shift)
    (fun j => -(∑ k, Q j k*shift k)))
    (fun i => Matrix.vecCons (-(∑ k, Q i k*shift k)) (fun j => scale*P i j-Q i j))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem transfer_identity (P Q : Matrix5) (shift e : State) (C D scale : ℝ)
    (hsym : ∀ i j, Q i j = Q j i) :
    matrixForm (transferBlock P Q shift C D scale) (Matrix.vecCons 1 e) =
      D-scale*C+scale*matrixForm P e-matrixForm Q (e+shift) := by
  simp [transferBlock, matrixForm, Pi.add_apply, Fin.sum_univ_succ]
  simp only [hsym 1 0, hsym 2 0, hsym 3 0, hsym 4 0, hsym 2 1,
    hsym 3 1, hsym 4 1, hsym 3 2, hsym 4 2, hsym 4 3]
  ring

/-- A nonnegative augmented block certifies inclusion for every source-region state. -/
theorem transfer_bound (P Q : Matrix5) (p q x : State) (C D scale : ℝ)
    (hsym : ∀ i j, Q i j = Q j i) (hscale : 0 ≤ scale)
    (hblock : 0 ≤ matrixForm (transferBlock P Q (p-q) C D scale) (Matrix.vecCons 1 (x-p)))
    (hx : energy P p x ≤ C) : energy Q q x ≤ D := by
  rw [transfer_identity P Q (p-q) (x-p) C D scale hsym] at hblock
  have he : (x-p)+(p-q) = x-q := by abel
  rw [he] at hblock
  have hmul := mul_le_mul_of_nonneg_left hx hscale
  change scale*matrixForm P (x-p) ≤ scale*C at hmul
  change matrixForm Q (x-q) ≤ D
  linarith

def rationalTransfer (P Q : QMatrix 5) (p q : Fin 5 → ℚ) (C D scale : ℚ) : QMatrix 6 :=
  let shift := p-q
  Matrix.vecCons (Matrix.vecCons (D-scale*C-(∑ i, ∑ j, shift i*Q i j*shift j))
    (fun j => -(∑ k, Q j k*shift k)))
    (fun i => Matrix.vecCons (-(∑ k, Q i k*shift k)) (fun j => scale*P i j-Q i j))

set_option maxHeartbeats 2000000 in
theorem rationalTransfer_binding (P Q : QMatrix 5) (p q : Fin 5 → ℚ) (C D scale : ℚ) :
    realMatrix (rationalTransfer P Q p q C D scale) =
      transferBlock (realMatrix P) (realMatrix Q)
        ((fun i => (p i : ℝ))-(fun i => (q i : ℝ))) C D scale := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalTransfer, realMatrix, transferBlock, matrixForm, Pi.sub_apply,
      Fin.sum_univ_succ]

theorem transfer_of_certificate (P Q : QMatrix 5) (p q : Fin 5 → ℚ) (C D scale : ℚ)
    (certificate : WeightedSquares 6)
    (valid : certificate.Represents (rationalTransfer P Q p q C D scale))
    (hsym : ∀ i j, Q i j = Q j i) (hscale : 0 ≤ scale) (x : State)
    (hx : energy (realMatrix P) (fun i => (p i : ℝ)) x ≤ C) :
    energy (realMatrix Q) (fun i => (q i : ℝ)) x ≤ D := by
  apply transfer_bound (realMatrix P) (realMatrix Q)
    (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) x C D scale
  · intro i j
    change (Q i j : ℝ) = (Q j i : ℝ)
    exact_mod_cast hsym i j
  · exact_mod_cast hscale
  · rw [← rationalTransfer_binding, matrixForm_rat]
    exact certificate.nonnegative _ valid _
  · exact hx

#print axioms transfer_of_certificate
end Gimle.Forseti.Examples.LoadedSAIFCertificates
