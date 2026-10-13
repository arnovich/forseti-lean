import Gimle.Forseti.FiniteLinearEquivalence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! Boundary regressions for fixed-initial-state rational output equivalence.
The positive examples use the finite criterion to obtain an infinite theorem;
the negative examples expose initialization, horizon and readout mistakes. -/

namespace Gimle.Forseti.Tests.FiniteLinearEquivalence

open Gimle.Forseti.FiniteLinearEquivalence
open scoped Matrix

def fibonacci : Matrix (Fin 2) (Fin 2) ℚ := ![![1, 1], ![1, 0]]

-- Swap the visible coordinates and add an unobserved growing coordinate.
def extendedFibonacci : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 1, 0], ![1, 1, 0], ![0, 0, 2]]

theorem fibonacci_equivalent :
    ∀ n, matrix_output fibonacci ![0, 1] ![1, 0] n =
      matrix_output extendedFibonacci ![1, 0, 1] ![0, 1, 0] n := by
  apply (matrix_prefix_iff_all fibonacci ![0, 1] ![1, 0]
    extendedFibonacci ![1, 0, 1] ![0, 1, 0]).mp
  intro n hn
  interval_cases n <;> decide +kernel

theorem empty_equivalent
    (A B : Matrix (Fin 0) (Fin 0) ℚ) (x c u v : Fin 0 → ℚ) :
    ∀ n, matrix_output A x c n = matrix_output B u v n := by
  apply (matrix_prefix_iff_all A x c B u v).mp
  intro n hn
  omega

def emptyMatrix : Matrix (Fin 0) (Fin 0) ℚ := fun i => Fin.elim0 i
def emptyVector : Fin 0 → ℚ := Fin.elim0

theorem one_empty_equivalent :
    ∀ n, matrix_output (![![2]] : Matrix (Fin 1) (Fin 1) ℚ) ![0] ![1] n =
      matrix_output emptyMatrix emptyVector emptyVector n := by
  apply (matrix_prefix_iff_all (![![2]]) ![0] ![1]
    emptyMatrix emptyVector emptyVector).mp
  intro n hn
  interval_cases n
  decide +kernel

def hiddenGrowth : Matrix (Fin 2) (Fin 2) ℚ := ![![1 / 2, 0], ![0, 2]]

theorem hidden_output_equivalent :
    ∀ n, matrix_output (![![1 / 2]] : Matrix (Fin 1) (Fin 1) ℚ) ![1] ![1] n =
      matrix_output hiddenGrowth ![1, 1] ![1, 0] n := by
  apply (matrix_prefix_iff_all (![![1 / 2]]) ![1] ![1]
    hiddenGrowth ![1, 1] ![1, 0]).mp
  intro n hn
  interval_cases n <;> decide +kernel

/-- The unobserved coordinate is exactly `2 ^ n`, despite output equivalence. -/
theorem hidden_state (n : ℕ) :
    (hiddenGrowth ^ n) *ᵥ ![1, 1] = ![(1 / 2 : ℚ) ^ n, (2 : ℚ) ^ n] := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
    ext i
    fin_cases i <;> simp [hiddenGrowth, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      pow_succ']

-- A changed observed initial value must fail already at time zero.
example : matrix_output fibonacci ![1, 1] ![1, 0] 0 ≠
    matrix_output extendedFibonacci ![1, 0, 1] ![0, 1, 0] 0 := by
  decide +kernel

-- Total dimension two: one matching observation is insufficient.
example : matrix_output (![![0]] : Matrix (Fin 1) (Fin 1) ℚ) ![1] ![1] 0 =
    matrix_output (![![1]] : Matrix (Fin 1) (Fin 1) ℚ) ![1] ![1] 0 := by
  decide +kernel

example : matrix_output (![![0]] : Matrix (Fin 1) (Fin 1) ℚ) ![1] ![1] 1 ≠
    matrix_output (![![1]] : Matrix (Fin 1) (Fin 1) ℚ) ![1] ![1] 1 := by
  decide +kernel

-- An asymmetric nilpotent transition tests the column-state convention.
def shiftThree : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0]]

theorem shift_prefix :
    ∀ n < 2, matrix_output shiftThree ![1, 0, 0] ![0, 0, 1] n = 0 := by
  intro n hn
  interval_cases n <;> decide +kernel

theorem shift_distinguishes :
    matrix_output shiftThree ![1, 0, 0] ![0, 0, 1] 2 = 1 := by
  decide +kernel

theorem shift_witness :
    ∃ n < 3, matrix_output shiftThree ![1, 0, 0] ![0, 0, 1] n ≠
      matrix_output emptyMatrix emptyVector emptyVector n := by
  exact matrix_distinguishing_index shiftThree ![1, 0, 0] ![0, 0, 1]
    emptyMatrix emptyVector emptyVector ⟨2, by decide +kernel⟩

/-- Outside the theorem's linear-readout hypotheses. -/
def nonlinearReadout (z : ℚ) : ℚ := (z - 1) * (z - 2)

theorem nonlinear_readout_control :
    (∀ n < 2, nonlinearReadout ((2 : ℚ) ^ n) = nonlinearReadout ((1 : ℚ) ^ n)) ∧
    nonlinearReadout ((2 : ℚ) ^ 2) ≠ nonlinearReadout ((1 : ℚ) ^ 2) := by
  constructor
  · intro n hn
    interval_cases n <;> decide +kernel
  · decide +kernel

/-- Affine updates must account for an additional homogeneous coordinate. -/
theorem affine_control :
    (∀ n < 2, ((fun z : ℚ => z + 1)^[n]) 1 = ((fun z : ℚ => 2 * z)^[n]) 1) ∧
    ((fun z : ℚ => z + 1)^[2]) 1 ≠ ((fun z : ℚ => 2 * z)^[2]) 1 := by
  constructor
  · intro n hn
    interval_cases n <;> decide +kernel
  · decide +kernel

#print axioms fibonacci_equivalent
#print axioms empty_equivalent
#print axioms one_empty_equivalent
#print axioms hidden_output_equivalent
#print axioms hidden_state
#print axioms shift_prefix
#print axioms shift_distinguishes
#print axioms shift_witness
#print axioms nonlinear_readout_control
#print axioms affine_control

end Gimle.Forseti.Tests.FiniteLinearEquivalence
