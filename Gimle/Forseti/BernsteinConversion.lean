module

public import Gimle.Forseti.RationalPolynomial

/-! Exact conversion of a rational polynomial in `(s, u)` to its tensor Bernstein
coefficients. A polynomial whose degrees are within `(td, pd)` equals the tensor
Bernstein form of its converted coefficients, so a concrete table can be bound to
a polynomial by comparing rational coefficients, without rebuilding and comparing
polynomials. -/

@[expose] public section

namespace Gimle.Forseti.BernsteinConversion
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix Gimle.Forseti.RationalPolynomial
open Finset

/-- `∑ν C(ν,k) C(n,ν) sᵛ (1-s)ⁿ⁻ᵛ = C(n,k) sᵏ`, the monomial in Bernstein form. -/
theorem choose_bernstein_sum (n k : Nat) (hk : k ≤ n) (s : ℝ) :
    ∑ ν ∈ range (n + 1), (ν.choose k : ℝ) * basis n ν s = (n.choose k : ℝ) * s ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show k + m + 1 = k + (m + 1) by omega, sum_range_add]
  have low : ∑ ν ∈ range k, (ν.choose k : ℝ) * basis (k + m) ν s = 0 := by
    apply sum_eq_zero
    intro ν hν
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hν)]
    simp
  rw [low, zero_add]
  have term : ∀ j ∈ range (m + 1),
      ((k + j).choose k : ℝ) * basis (k + m) (k + j) s =
        ((k + m).choose k : ℝ) * s ^ k * (s ^ j * (1 - s) ^ (m - j) * (m.choose j : ℝ)) := by
    intro j hj
    have hj' : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hc := Nat.choose_mul (n := k + m) (k := k + j) (s := k) (by omega)
    rw [show k + m - k = m by omega, show k + j - k = j by omega] at hc
    have hc' : ((k + m).choose (k + j) : ℝ) * ((k + j).choose k : ℝ) =
        ((k + m).choose k : ℝ) * (m.choose j : ℝ) := by exact_mod_cast hc
    simp only [basis, show k + m - (k + j) = m - j by omega, pow_add]
    linear_combination (s ^ k * s ^ j * (1 - s) ^ (m - j)) * hc'
  rw [sum_congr rfl term, ← mul_sum]
  have binom := (add_pow s (1 - s) m).symm
  rw [show s + (1 - s) = 1 by ring, one_pow] at binom
  rw [binom, mul_one]

/-- `Nat.choose` through falling factorials, which the kernel evaluates with a few
multiplications and one division instead of the binomial recursion. -/
def binomial (n k : Nat) : Nat := n.descFactorial k / k.factorial

theorem binomial_eq (n k : Nat) : binomial n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- Weight of Bernstein index `ν` for the monomial `sᵏ` in degree `n`. -/
def weight (n k ν : Nat) : ℚ := (binomial ν k : ℚ) / (binomial n k : ℚ)

theorem monomial_bernstein (n k : Nat) (hk : k ≤ n) (s : ℝ) :
    ∑ ν : Fin (n + 1), (weight n k ν : ℝ) * basis n ν s = s ^ k := by
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h := choose_bernstein_sum n k hk s
  rw [Fin.sum_univ_eq_sum_range (fun ν => (weight n k ν : ℝ) * basis n ν s)]
  simp only [weight, binomial_eq, Rat.cast_div, Rat.cast_natCast, div_mul_eq_mul_div, ← sum_div, h]
  field_simp

/-- Tensor Bernstein coefficient `(a, b)` of `p` in degrees `(td, pd)`. -/
def coefficient (td pd : Nat) (p : Poly) (a b : Nat) : ℚ :=
  (p.map fun t => t.coefficient * weight td t.timeDegree a * weight pd t.parameterDegree b).sum

/-- Every term is within the time and parameter degrees. -/
def withinDegree (td pd : Nat) (p : Poly) : Bool :=
  p.all fun t => decide (t.timeDegree ≤ td) && decide (t.parameterDegree ≤ pd)

/-- A polynomial within the degrees equals the tensor Bernstein form of its
converted coefficients. -/
theorem eval_eq_bernstein (td pd : Nat) (p : Poly) (h : withinDegree td pd p = true)
    (s u : ℝ) :
    eval p s u = ∑ a : Fin (td + 1), ∑ b : Fin (pd + 1),
      basis td a s * basis pd b u * (coefficient td pd p a b : ℝ) := by
  induction p with
  | nil => simp [coefficient]
  | cons t p ih =>
    simp only [withinDegree, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [eval_cons, ih h.2]
    have ht : termEval t s u = ∑ a : Fin (td + 1), ∑ b : Fin (pd + 1),
        basis td a s * basis pd b u *
          ((t.coefficient * weight td t.timeDegree a * weight pd t.parameterDegree b : ℚ) : ℝ) := by
      have hs := monomial_bernstein td t.timeDegree h.1.1 s
      have hu := monomial_bernstein pd t.parameterDegree h.1.2 u
      have expand : termEval t s u = (t.coefficient : ℝ) *
          (∑ a : Fin (td + 1), (weight td t.timeDegree a : ℝ) * basis td a s) *
          (∑ b : Fin (pd + 1), (weight pd t.parameterDegree b : ℝ) * basis pd b u) := by
        rw [hs, hu]; simp only [termEval]
      rw [expand, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun b _ => ?_
      push_cast
      ring
    rw [ht, ← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun b _ => ?_
    simp only [coefficient, List.map_cons, List.sum_cons, Rat.cast_add]
    ring

/-- The per-entry check: degrees within bounds and every converted coefficient
equal to the table entry. -/
def tableMatches {n td pd : Nat} (target : Fin n → Fin n → Poly)
    (c : Fin (td + 1) → Fin (pd + 1) → QMatrix n) (i j : Fin n) : Bool :=
  withinDegree td pd (target i j) &&
    (List.finRange (td + 1)).all fun a => (List.finRange (pd + 1)).all fun b =>
      coefficient td pd (target i j) a b == c a b i j

/-- Coefficient checks bind a polynomial matrix to its Bernstein table. -/
theorem binding {n td pd : Nat} (target : Fin n → Fin n → Poly)
    (c : Fin (td + 1) → Fin (pd + 1) → QMatrix n)
    (checked : ∀ i j, tableMatches target c i j = true) (s u : ℝ) :
    (fun i j => eval (target i j) s u) = tensorMatrix c s u := by
  ext i j
  have h := checked i j
  simp only [tableMatches, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, beq_iff_eq] at h
  rw [eval_eq_bernstein td pd _ h.1]
  simp only [tensorMatrix, Finset.sum_apply]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [h.2 a b]

/-- The Bernstein table of a polynomial matrix, computed from its coefficients. -/
def table {n : Nat} (td pd : Nat) (target : Fin n → Fin n → Poly) :
    Fin (td + 1) → Fin (pd + 1) → QMatrix n :=
  fun a b i j => coefficient td pd (target i j) a b

/-- A computed table needs only the degree check to be bound to its polynomials. -/
theorem table_binding {n : Nat} (td pd : Nat) (target : Fin n → Fin n → Poly)
    (degree : ∀ i j, withinDegree td pd (target i j) = true) (s u : ℝ) :
    (fun i j => eval (target i j) s u) = tensorMatrix (table td pd target) s u := by
  ext i j
  rw [eval_eq_bernstein td pd _ (degree i j)]
  simp only [tensorMatrix, Finset.sum_apply, table]

#print axioms monomial_bernstein
#print axioms eval_eq_bernstein
#print axioms binding
#print axioms table_binding
end Gimle.Forseti.BernsteinConversion
