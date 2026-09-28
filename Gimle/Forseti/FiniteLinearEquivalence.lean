import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Exact finite-prefix equivalence for autonomous linear observations.
The core proof reduces powers modulo the characteristic polynomial. Matrix
outputs use column states, fixed initial vectors and fixed linear readouts. -/

namespace Gimle.Forseti.FiniteLinearEquivalence

open Polynomial

/-- Vanishing through the dimension bound forces every later observation to vanish. -/
theorem observation_zero_of_prefix
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (z : V) (ell : V →ₗ[K] K)
    (h : ∀ j < Module.finrank K V, ell ((T ^ j) z) = 0) :
    ∀ n : ℕ, ell ((T ^ n) z) = 0 := by
  classical
  by_cases hd : Module.finrank K V = 0
  · letI : Subsingleton V := Module.finrank_zero_iff.mp hd
    intro n
    rw [Subsingleton.elim ((T ^ n) z) 0, map_zero]
  · have hp : T.charpoly ≠ 1 := by
      intro he
      apply hd
      rw [← T.charpoly_natDegree, he, natDegree_one]
    intro n
    have hb : (X ^ n %ₘ T.charpoly).natDegree < Module.finrank K V := by
      rw [← T.charpoly_natDegree]
      exact natDegree_modByMonic_lt _ T.charpoly_monic hp
    rw [T.pow_eq_aeval_mod_charpoly n, aeval_eq_sum_range' hb]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj), smul_zero]

/-- Exact rational output at a natural time, with a column-state convention. -/
def matrix_output {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ)
    (x c : Fin d → ℚ) (n : ℕ) : ℚ :=
  dotProduct c ((A ^ n).mulVec x)

/-- Matrix powers act by the same iterates as their induced linear endomorphism. -/
theorem matrix_power_action {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ)
    (x : Fin d → ℚ) (n : ℕ) :
    (A.mulVecLin ^ n) x = (A ^ n).mulVec x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih]
    exact (Matrix.mulVec_mulVec x A (A ^ n))

/-- The product transition evolves both component systems at the same time. -/
theorem product_power_action {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (T : Module.End K V) (S : Module.End K W) (x : V) (y : W) (n : ℕ) :
    (T.prodMap S ^ n) (x, y) = ((T ^ n) x, (S ^ n) y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, ih, LinearMap.prodMap_apply]

/-- Two fixed linear outputs agree forever exactly when their first `d₁ + d₂`
observations agree. Both dimensions may be zero. -/
theorem matrix_prefix_iff_all {d₁ d₂ : ℕ}
    (A₁ : Matrix (Fin d₁) (Fin d₁) ℚ) (x₁ c₁ : Fin d₁ → ℚ)
    (A₂ : Matrix (Fin d₂) (Fin d₂) ℚ) (x₂ c₂ : Fin d₂ → ℚ) :
    (∀ n < d₁ + d₂, matrix_output A₁ x₁ c₁ n = matrix_output A₂ x₂ c₂ n) ↔
    ∀ n : ℕ, matrix_output A₁ x₁ c₁ n = matrix_output A₂ x₂ c₂ n := by
  constructor
  · intro h
    let T := A₁.mulVecLin.prodMap A₂.mulVecLin
    let ell : ((Fin d₁ → ℚ) × (Fin d₂ → ℚ)) →ₗ[ℚ] ℚ :=
      (dotProductBilin ℚ ℚ c₁).comp (LinearMap.fst ℚ _ _) -
        (dotProductBilin ℚ ℚ c₂).comp (LinearMap.snd ℚ _ _)
    have ho (n : ℕ) : ell ((T ^ n) (x₁, x₂)) =
        matrix_output A₁ x₁ c₁ n - matrix_output A₂ x₂ c₂ n := by
      simp [T, ell, product_power_action, matrix_power_action, matrix_output]
    have hz := observation_zero_of_prefix T (x₁, x₂) ell (by
      intro n hn
      rw [ho, sub_eq_zero]
      apply h n
      simpa using hn)
    intro n
    exact sub_eq_zero.mp ((ho n).symm.trans (hz n))
  · intro h n _
    exact h n

/-- Any unequal output has a distinguishing index strictly below total dimension. -/
theorem matrix_distinguishing_index {d₁ d₂ : ℕ}
    (A₁ : Matrix (Fin d₁) (Fin d₁) ℚ) (x₁ c₁ : Fin d₁ → ℚ)
    (A₂ : Matrix (Fin d₂) (Fin d₂) ℚ) (x₂ c₂ : Fin d₂ → ℚ)
    (h : ∃ n : ℕ, matrix_output A₁ x₁ c₁ n ≠ matrix_output A₂ x₂ c₂ n) :
    ∃ n < d₁ + d₂, matrix_output A₁ x₁ c₁ n ≠ matrix_output A₂ x₂ c₂ n := by
  classical
  by_contra hc
  push Not at hc
  obtain ⟨n, hn⟩ := h
  exact hn ((matrix_prefix_iff_all A₁ x₁ c₁ A₂ x₂ c₂).mp hc n)

#print axioms observation_zero_of_prefix
#print axioms matrix_power_action
#print axioms matrix_prefix_iff_all
#print axioms matrix_distinguishing_index

end Gimle.Forseti.FiniteLinearEquivalence
