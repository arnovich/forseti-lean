import Gimle.Forseti
import Gimle.Asgard.AlgebraicCompiler

/-! Total algebraic Hoare semantics are separate from stateless feedforward
Hoare triples: existence and a unique admissible loop solution are included. -/
namespace Gimle.Forseti.Algebraic
open Gimle.Asgard.Algebraic

/-- A precondition admits external vectors; the loop domain is an independent
semantic restriction. Safety alone would permit vacuous no-solution models. -/
def TotalHoare {n d o : Nat} (loop : Circuit (n + d) n) (output : Circuit (n + d) o)
    (domain : Point n → Prop) (precondition : Predicate d) (postcondition : Predicate o) : Prop :=
  ∀ u, precondition.holds u →
    (∃! z, domain z ∧ loop.run (pointAppend z u) = z) ∧
    ∀ y, Rel loop output domain u y → postcondition.holds y

/-- Transport an ordinary feedforward Hoare theorem through verified elimination.
The original loop, its domain and its observed output remain the theorem subject. -/
theorem transport {n d o : Nat} (p : Problem n d o) (inverse : Inverse p.matrix)
    (domain : Point n → Prop) (precondition : Predicate d) (postcondition : Predicate o)
    (membership : ∀ u, precondition.holds u → domain ((p.solutionCircuit inverse.value).run u))
    (feedforward : ExactHoare precondition (p.eliminatedCircuit inverse.value) postcondition) :
    TotalHoare p.loopAffine.circuit p.output.circuit domain precondition postcondition := by
  intro u hu
  obtain ⟨unique, equal⟩ := p.eliminate_correct inverse domain precondition.holds membership u hu
  refine ⟨unique, ?_⟩
  intro y hy
  rw [(equal y).mp hy]
  exact feedforward u hu

#print axioms transport
end Gimle.Forseti.Algebraic
