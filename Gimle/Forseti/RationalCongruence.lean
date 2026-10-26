module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Gimle.Forseti.LinearEnergy

/-! Exact rational congruence certificates for nonnegative quadratic forms.
A symmetric matrix with nonnegative diagonal slack is positive semidefinite.
An invertible change of coordinates preserves this conclusion. Upper triangular
bases need only checked zero entries and nonzero diagonals; no numerical inverse
or floating-point eigenvalue computation is trusted. -/

@[expose] public section

namespace Gimle.Forseti.RationalCongruence
open LinearEnergy
open scoped Matrix

/-- Matrix operations use matrix multiplication, not pointwise function multiplication. -/
abbrev RationalMatrix (n : Nat) := Matrix (Fin n) (Fin n) ℚ

/-- Symmetry checked entry by entry over the rationals. -/
def Symmetric {n : Nat} (M : RationalMatrix n) : Prop := ∀ i j, M i j = M j i

/-- Weak row dominance, allowing zero eigenvalues. -/
def DiagonallyDominant {n : Nat} (M : RationalMatrix n) : Prop :=
  ∀ i, (∑ j, if i = j then 0 else |M i j|) ≤ M i i

/-- Exact change of coordinates, without modifying the target matrix. -/
def transform {n : Nat} (Q M : RationalMatrix n) : RationalMatrix n := Q.transpose * M * Q

private def offDiagonal {n : Nat} (M : RationalMatrix n) (i j : Fin n) : ℚ :=
  if i = j then 0 else M i j

private theorem pair_nonnegative (c a b : ℝ) :
    0 ≤ 2 * (a * (c * b)) + |c| * a ^ 2 + |c| * b ^ 2 := by
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    nlinarith [mul_nonneg hc (sq_nonneg (a + b))]
  · rw [abs_of_neg (lt_of_not_ge hc)]
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hc)) (sq_nonneg (a - b))]

/-- The elementary row-dominance bound is sound for every dimension. -/
theorem nonnegative_of_diagonallyDominant {n : Nat} {M : RationalMatrix n}
    (hs : Symmetric M) (hd : DiagonallyDominant M) (x : Fin n → ℝ) :
    0 ≤ quadratic M x := by
  let O : Matrix (Fin n) (Fin n) ℝ := fun i j => offDiagonal M i j
  have hsym (i j : Fin n) : O i j = O j i := by
    dsimp [O, offDiagonal]
    by_cases h : i = j
    · subst j; rfl
    · simp [h, Ne.symm h, hs i j]
  have hrow (i : Fin n) : (∑ j, |O i j|) ≤ (M i i : ℝ) := by
    have he (j : Fin n) : |O i j| =
        ((if i = j then 0 else |M i j| : ℚ) : ℝ) := by
      by_cases h : i = j <;> simp [O, offDiagonal, h]
    simp_rw [he]
    exact_mod_cast hd i
  have hdiag (i : Fin n) :
      (∑ j, x i * ((M i j : ℝ) * x j)) =
        (M i i : ℝ) * x i ^ 2 + ∑ j, x i * (O i j * x j) := by
    have he (j : Fin n) : x i * ((M i j : ℝ) * x j) =
        (if j = i then (M i i : ℝ) * x i ^ 2 else 0) + x i * (O i j * x j) := by
      by_cases h : j = i
      · subst j; simp [O, offDiagonal]; ring
      · simp [O, offDiagonal, h, Ne.symm h]
    simp_rw [he, Finset.sum_add_distrib]
    simp
  have hquadratic : quadratic M x = (∑ i, (M i i : ℝ) * x i ^ 2) +
      ∑ i, ∑ j, x i * (O i j * x j) := by
    simp only [quadratic, realMatrix, Matrix.mulVec, dotProduct, Finset.mul_sum,
      hdiag, Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, |O i j| * x j ^ 2) =
      ∑ i, ∑ j, |O i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hp : 0 ≤ ∑ i, ∑ j,
      (2 * (x i * (O i j * x j)) + |O i j| * x i ^ 2 + |O i j| * x j ^ 2) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      pair_nonnegative (O i j) (x i) (x j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  rw [hswap] at hp
  have hfactor : (∑ i, x i * ∑ j, O i j * x j) =
      ∑ i, ∑ j, x i * (O i j * x j) := by simp only [Finset.mul_sum]
  rw [hfactor] at hp
  have hl : (∑ i, ∑ j, |O i j| * x i ^ 2) ≤
      ∑ i, (M i i : ℝ) * x i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _)
  rw [hquadratic]
  linarith

@[simp] theorem realMatrix_mul {n : Nat} (A B : RationalMatrix n) :
    realMatrix (A * B) = realMatrix A * realMatrix B := by
  ext i j
  simp [realMatrix, Matrix.mul_apply]

@[simp] theorem realMatrix_transpose {n : Nat} (A : RationalMatrix n) :
    realMatrix A.transpose = (realMatrix A).transpose := rfl

/-- Congruence has exactly the intended real quadratic semantics. -/
theorem quadratic_transform {n : Nat} (Q M : RationalMatrix n) (x : Fin n → ℝ) :
    quadratic (transform Q M) x = quadratic M ((realMatrix Q).mulVec x) := by
  simp only [quadratic, transform, realMatrix_mul, realMatrix_transpose,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem transform_symmetric {n : Nat} {M : RationalMatrix n} (hs : Symmetric M)
    (Q : RationalMatrix n) : Symmetric (transform Q M) := by
  have hm : M.transpose = M := Matrix.ext fun i j => hs j i
  have ht : (transform Q M).transpose = transform Q M := by
    simp [transform, Matrix.transpose_mul, hm, Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun ht j) i

/-- A supplied right inverse is an alternative explicit invertibility witness. -/
theorem nonnegative_of_inverse {n : Nat} (M Q S : RationalMatrix n)
    (hs : Symmetric M) (hinv : Q * S = 1)
    (hd : DiagonallyDominant (transform Q M)) (x : Fin n → ℝ) :
    0 ≤ quadratic M x := by
  have hinv' : realMatrix Q * realMatrix S = 1 := by
    rw [← realMatrix_mul, hinv]
    ext i j
    by_cases h : i = j <;> simp [realMatrix, Matrix.one_apply, h]
  obtain ⟨y, rfl⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    ⟨realMatrix S, hinv'⟩ x
  rw [← quadratic_transform]
  exact nonnegative_of_diagonallyDominant (transform_symmetric hs Q) hd y

/-- Upper triangular bases with nonzero diagonals require no inverse data. -/
theorem nonnegative_of_upperTriangular {n : Nat} (M Q : RationalMatrix n)
    (hs : Symmetric M) (htri : Q.IsUpperTriangular) (hdiag : ∀ i, Q i i ≠ 0)
    (hd : DiagonallyDominant (transform Q M)) (x : Fin n → ℝ) :
    0 ≤ quadratic M x := by
  have ht : (realMatrix Q).IsUpperTriangular := by
    intro i j h
    simp [realMatrix, htri h]
  have hdet : (realMatrix Q).det ≠ 0 := ht.det_ne_zero_iff.mpr (fun i => by
    simpa [Matrix.diag, realMatrix] using (Rat.cast_ne_zero.mpr (hdiag i) :
      (Q i i : ℝ) ≠ 0))
  have hu : IsUnit (realMatrix Q) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu x
  rw [← quadratic_transform]
  exact nonnegative_of_diagonallyDominant (transform_symmetric hs Q) hd y

/-- Exact entrywise inclusion of an integer matrix into the rational matrices. -/
def integerMatrix {n : Nat} (A : Matrix (Fin n) (Fin n) ℤ) : RationalMatrix n :=
  fun i j => A i j

@[simp] theorem integerMatrix_mul {n : Nat} (A B : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrix (A * B) = integerMatrix A * integerMatrix B := by
  ext i j
  simp [integerMatrix, Matrix.mul_apply]

@[simp] theorem integerMatrix_transpose {n : Nat} (A : Matrix (Fin n) (Fin n) ℤ) :
    integerMatrix A.transpose = (integerMatrix A).transpose := rfl

/-- Integer row inequalities can certify the unchanged rational quadratic form
with a positive common denominator. Scaling the coordinate basis requires no
inverse and introduces no additional approximation. -/
theorem integer_scaled_nonnegative {n : Nat} (A B : Matrix (Fin n) (Fin n) ℤ)
    (D : ℕ) (hD : 0 < D) (hs : ∀ i j, A i j = A j i)
    (ht : B.IsUpperTriangular) (hb : ∀ i, B i i ≠ 0)
    (hd : ∀ i, (∑ j, if i = j then 0 else |(B.transpose * A * B) i j|) ≤
      (B.transpose * A * B) i i) (x : Fin n → ℝ) :
    0 ≤ quadratic (fun i j => (A i j : ℚ) / (D : ℚ)) x := by
  have hsym : Symmetric (integerMatrix A) := by
    intro i j
    simp only [integerMatrix, hs i j]
  have htri : (integerMatrix B).IsUpperTriangular := by
    intro i j h
    simp [integerMatrix, ht h]
  have hdiag : ∀ i, integerMatrix B i i ≠ 0 := by
    intro i
    change (B i i : ℚ) ≠ 0
    exact_mod_cast hb i
  have htransform : transform (integerMatrix B) (integerMatrix A) =
      integerMatrix (B.transpose * A * B) := by
    simp only [transform, integerMatrix_mul, integerMatrix_transpose]
  have hdd : DiagonallyDominant (transform (integerMatrix B) (integerMatrix A)) := by
    rw [htransform]
    intro i
    have he (j : Fin n) :
        (if i = j then 0 else |integerMatrix (B.transpose * A * B) i j|) =
          ((if i = j then 0 else |(B.transpose * A * B) i j| : ℤ) : ℚ) := by
      by_cases h : i = j <;> simp [integerMatrix, h]
    simp_rw [he]
    simp only [integerMatrix]
    exact_mod_cast hd i
  have hnonnegative := nonnegative_of_upperTriangular (integerMatrix A)
    (integerMatrix B) hsym htri hdiag hdd x
  have heq : quadratic (fun i j => (A i j : ℚ) / (D : ℚ)) x =
      quadratic (integerMatrix A) x / (D : ℝ) := by
    simp only [quadratic, realMatrix, integerMatrix, Matrix.mulVec, dotProduct,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact div_nonneg hnonnegative (by exact_mod_cast hD.le)

#print axioms nonnegative_of_diagonallyDominant
#print axioms nonnegative_of_inverse
#print axioms nonnegative_of_upperTriangular
#print axioms integer_scaled_nonnegative
end Gimle.Forseti.RationalCongruence
