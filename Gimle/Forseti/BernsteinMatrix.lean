import Gimle.Forseti.LinearEnergy

/-! Positivity of exact rational matrix polynomials in tensor Bernstein form.
The caller must separately establish that its target polynomial equals this
representation. No coefficient conversion, dynamics, or coverage is assumed. -/
namespace Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.LinearEnergy

/-- The polynomial Bernstein basis, including both closed endpoints. -/
noncomputable def basis (degree index : Nat) (s : ℝ) : ℝ :=
  (degree.choose index : ℝ) * s ^ index * (1 - s) ^ (degree - index)

theorem basis_nonnegative (degree index : Nat) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ basis degree index s := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.1 _))
    (pow_nonneg (sub_nonneg.mpr hs.2) _)

/-- Evaluate the quadratic form of a tensor Bernstein matrix polynomial.
The two `Fin` indices include the degree endpoint; degrees may be zero. -/
noncomputable def tensorQuadratic {n timeDegree parameterDegree : Nat}
    (coefficients : Fin (timeDegree + 1) → Fin (parameterDegree + 1) → QMatrix n)
    (s u : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin (timeDegree + 1), ∑ j : Fin (parameterDegree + 1),
    basis timeDegree i s * basis parameterDegree j u *
    quadratic (coefficients i j) x

/-- Exact coefficient certificates imply positivity everywhere on the closed box.
The kernel checks each `Represents` premise; the producer has no authority. -/
theorem tensor_nonnegative {n timeDegree parameterDegree : Nat}
    {coefficients : Fin (timeDegree + 1) → Fin (parameterDegree + 1) → QMatrix n}
    (certificates : Fin (timeDegree + 1) → Fin (parameterDegree + 1) → WeightedSquares n)
    (valid : ∀ i j, (certificates i j).Represents (coefficients i j))
    {s u : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → ℝ) : 0 ≤ tensorQuadratic coefficients s u x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg
    (mul_nonneg (basis_nonnegative _ _ hs) (basis_nonnegative _ _ hu))
    ((certificates i j).nonnegative _ (valid i j) x)

/-- Rational scaling stays inside the existing exact matrix language. -/
def scale {n : Nat} (r : ℚ) (p : QMatrix n) : QMatrix n := fun i j => r * p i j

theorem quadratic_scale {n : Nat} (r : ℚ) (p : QMatrix n) (x : Fin n → ℝ) :
    quadratic (scale r p) x = (r : ℝ) * quadratic p x := by
  simp only [quadratic, realMatrix, scale, Matrix.mulVec, dotProduct, Rat.cast_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cubic power coefficients converted algebraically, with a degree-zero second axis. -/
def cubicCoefficients {n : Nat} (a b c d : QMatrix n) : Fin 4 → Fin 1 → QMatrix n :=
  fun i _ => ![a, a + scale (1/3) b,
    a + scale (2/3) b + scale (1/3) c, a + b + c + d] i

/-- The quadratic form of a matrix polynomial in the power basis. -/
noncomputable def cubicQuadratic {n : Nat} (a b c d : QMatrix n)
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  quadratic a x + s * quadratic b x + s^2 * quadratic c x + s^3 * quadratic d x

/-- Checked conversion identity, independent of a certificate producer. -/
theorem cubic_identity {n : Nat} (a b c d : QMatrix n) (s u : ℝ) (x : Fin n → ℝ) :
    tensorQuadratic (cubicCoefficients a b c d) s u x = cubicQuadratic a b c d s x := by
  simp [tensorQuadratic, cubicCoefficients, basis, cubicQuadratic,
    Fin.sum_univ_succ, quadratic_add, quadratic_scale]
  ring

#print axioms tensor_nonnegative
#print axioms cubic_identity
end Gimle.Forseti.BernsteinMatrix
