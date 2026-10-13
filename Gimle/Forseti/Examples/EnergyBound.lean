import Gimle.Forseti

/-! Generated untrusted Lean proof candidate. -/

namespace Gimle.Forseti.EnergyBound

open Gimle.Forseti

-- Input assumptions: -1 ≤ x ≤ 1 and -1 ≤ y ≤ 1.
-- The input vector stores x at coordinate 0 and y at coordinate 1.
def precondition : Predicate 2 where
  holds := fun point => ((((-1 : ℝ)) + ((-1 : ℝ) * (point 1)) ≤ 0) ∧ (((-1 : ℝ)) + ((1 : ℝ) * (point 1)) ≤ 0) ∧ (((-1 : ℝ)) + ((-1 : ℝ) * (point 0)) ≤ 0) ∧ (((-1 : ℝ)) + ((1 : ℝ) * (point 0)) ≤ 0))

/-
For real inputs x and y:
  s = x + y
  d = x - y
  E(x,y) = s² + d²
-/
def circuit : Circuit 2 1 :=
  Circuit.compose
    (Circuit.compose
      (Circuit.compose
        (Circuit.compose
          (Circuit.parallel (leftInput := 1) (leftOutput := 2)
            (Circuit.split)
            (Circuit.split))
          (Circuit.parallel (leftInput := 1) (leftOutput := 1)
            (Circuit.id)
            (Circuit.parallel (leftInput := 2) (leftOutput := 2)
              (Circuit.swap)
              (Circuit.id))))
        (Circuit.parallel (leftInput := 2) (leftOutput := 1)
          (Circuit.add)
          (Circuit.compose
            (Circuit.parallel (leftInput := 1) (leftOutput := 1)
              (Circuit.id)
              (Circuit.scalar (-1 : ℚ)))
            (Circuit.add))))
      (Circuit.parallel (leftInput := 1) (leftOutput := 1)
        (Circuit.compose (Circuit.split) (Circuit.multiplication))
        (Circuit.compose (Circuit.split) (Circuit.multiplication))))
    (Circuit.add)

-- Output guarantee: 0 ≤ E ≤ 4.
-- In normalized form below, these are E - 4 ≤ 0 and -E ≤ 0.
def postcondition : Predicate 1 where
  holds := fun point => ((((-4 : ℝ)) + ((1 : ℝ) * (point 0)) ≤ 0) ∧ (((-1 : ℝ) * (point 0)) ≤ 0))

/-
  For every real x,y, if both inputs lie in [-1,1], then
    0 ≤ (x+y)² + (x-y)² ≤ 4.

Proof idea: E = 2x² + 2y², each square is nonnegative, and the input
assumptions imply x² ≤ 1 and y² ≤ 1. Hence 0 ≤ E ≤ 2 + 2 = 4.
EnergyDemo.lean additionally proves that both endpoints are attained
and that no stronger uniform lower or upper bound is possible.
-/
set_option maxHeartbeats 500000 in
theorem forsetiCandidate :
    ExactHoare precondition circuit postcondition := by
  -- Fix arbitrary inputs satisfying the precondition.
  intro input hypothesis
  -- Expand the circuit interpreter and the input/output predicates.
  simp [precondition, circuit, postcondition] at hypothesis ⊢
  -- (x + 1)(1 - x) ≥ 0 supplies the quadratic upper bound x² ≤ 1.
  have intervalProduct0 :
      0 ≤ (input 0 - (-1 : ℝ)) * ((1 : ℝ) - input 0) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  -- The same interval argument supplies y² ≤ 1.
  have intervalProduct1 :
      0 ≤ (input 1 - (-1 : ℝ)) * ((1 : ℝ) - input 1) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  -- Prove the upper and lower output bounds as separate goals.
  constructor
  -- Close each bound using the interval products and nonnegativity of squares.
  all_goals nlinarith [intervalProduct0, intervalProduct1, sq_nonneg (input 0), sq_nonneg (input 1)]

#print axioms forsetiCandidate

end Gimle.Forseti.EnergyBound
