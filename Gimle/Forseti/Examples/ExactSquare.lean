import Gimle.Forseti

/-! Generated untrusted Lean proof candidate. -/

namespace Gimle.Forseti.ExactSquare

open Gimle.Forseti

def precondition : Predicate 1 where
  holds := fun point => (((((-1 : ℝ) / 10)) + ((-1 : ℝ) * (point 0)) ≤ 0) ∧ ((((-1 : ℝ) / 10)) + ((1 : ℝ) * (point 0)) ≤ 0))

def circuit : Circuit 1 1 :=
  Circuit.compose (Circuit.split) (Circuit.multiplication)

def postcondition : Predicate 1 where
  holds := fun point => (((((-1 : ℝ) / 100)) + ((1 : ℝ) * (point 0)) ≤ 0) ∧ (((-1 : ℝ) * (point 0)) ≤ 0))

set_option maxHeartbeats 500000 in
theorem forsetiCandidate :
    ExactHoare precondition circuit postcondition := by
  intro input hypothesis
  simp [precondition, circuit, postcondition] at hypothesis ⊢
  have intervalProduct0 :
      0 ≤ (input 0 - ((-1 : ℝ) / 10)) * (((1 : ℝ) / 10) - input 0) :=
    mul_nonneg (by nlinarith) (by nlinarith)
  constructor
  all_goals nlinarith [intervalProduct0, sq_nonneg (input 0)]

#print axioms forsetiCandidate

end Gimle.Forseti.ExactSquare
