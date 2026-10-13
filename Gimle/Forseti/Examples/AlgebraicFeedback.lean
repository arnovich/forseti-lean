import Gimle.Forseti.Algebraic
import Gimle.Asgard.Examples.AlgebraicFeedback

namespace Gimle.Forseti.AlgebraicFeedback
open Gimle.Asgard.Algebraic Gimle.Asgard.Algebraic.Examples

/-- Input assumption: -1 ≤ u ≤ 1. -/
def precondition : Predicate 1 := ⟨inputDomain⟩

/-- Output claim: -2 ≤ y ≤ 2. -/
def postcondition : Predicate 1 := ⟨loopDomain⟩

/-- The original circuit implements z=z/2+u, y=z.
The Lean compiler constructs the eliminated circuit y=2u automatically. -/
theorem feedforward_bound : ExactHoare precondition
    (halfLoop.eliminatedCircuit halfInverse.value) postcondition := by
  intro u hu
  have hm := half_membership u hu
  rw [Problem.output_correct]
  simpa [postcondition, loopDomain, halfLoop, Affine.eval,
    realMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pointAppend] using hm

/-- What we prove: for every u∈[-1,1], the original circuit has exactly one loop
solution z∈[-2,2], and every original output y satisfies -2≤y≤2.
No numerical simulation, convergence, delay or time horizon is assumed. -/
theorem feedback_bound : Algebraic.TotalHoare halfLoop.loopAffine.circuit
    halfLoop.output.circuit loopDomain precondition postcondition :=
  Algebraic.transport halfLoop halfInverse loopDomain precondition postcondition
    half_membership feedforward_bound

#print axioms feedback_bound
end Gimle.Forseti.AlgebraicFeedback
