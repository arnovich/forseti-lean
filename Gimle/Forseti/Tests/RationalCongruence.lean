import Gimle.Forseti.RationalCongruence

/-! Regression checks for weak diagonal dominance and guarded congruence. -/
namespace Gimle.Forseti.Tests.RationalCongruence
open Gimle.Forseti LinearEnergy RationalCongruence
open scoped Matrix

private def laplacian : QMatrix 2 := !![1, -1; -1, 1]
private def basis : QMatrix 2 := !![1, 1; 0, 1]

example : transform basis laplacian = (!![1, 0; 0, 0] : QMatrix 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [transform, basis, laplacian, Matrix.mul_apply, Fin.sum_univ_succ]

example (x : Fin 2 → ℝ) : 0 ≤ quadratic laplacian x := by
  apply nonnegative_of_diagonallyDominant
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [laplacian]
  · intro i
    fin_cases i <;> norm_num [DiagonallyDominant, laplacian, Fin.sum_univ_succ]

example (x : Fin 2 → ℝ) : 0 ≤ quadratic laplacian x := by
  apply nonnegative_of_upperTriangular laplacian basis
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [laplacian]
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [basis] at *
  · intro i
    fin_cases i <;> norm_num [basis]
  · intro i
    fin_cases i <;> norm_num [DiagonallyDominant, transform, laplacian, basis,
      Matrix.mul_apply, Fin.sum_univ_succ]

example (x : Fin 2 → ℝ) : 0 ≤ quadratic laplacian x := by
  apply nonnegative_of_inverse laplacian basis (!![1, -1; 0, 1])
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [laplacian]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [basis, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro i
    fin_cases i <;> norm_num [DiagonallyDominant, transform, laplacian, basis,
      Matrix.mul_apply, Fin.sum_univ_succ]

example : ¬ DiagonallyDominant (!![1, 2; 2, 1] : QMatrix 2) := by
  intro h
  have hh := h 0
  norm_num [Fin.sum_univ_succ] at hh

example : ¬ (∀ i : Fin 2, (!![1, 0; 0, 0] : QMatrix 2) i i ≠ 0) := by
  intro h
  exact h 1 rfl

private def integerLaplacian : Matrix (Fin 2) (Fin 2) ℤ := !![2, -2; -2, 2]
private def integerBasis : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

example (x : Fin 2 → ℝ) :
    0 ≤ quadratic (fun i j => (integerLaplacian i j : ℚ) / 2) x := by
  apply integer_scaled_nonnegative integerLaplacian integerBasis 2 (by norm_num)
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [integerLaplacian]
  · intro i j h
    fin_cases i <;> fin_cases j <;> norm_num [integerBasis] at *
  · intro i
    fin_cases i <;> norm_num [integerBasis]
  · intro i
    fin_cases i <;> norm_num [integerBasis, integerLaplacian,
      Matrix.mul_apply, Fin.sum_univ_succ]

example : ¬ 0 < (0 : ℕ) := by decide

end Gimle.Forseti.Tests.RationalCongruence
