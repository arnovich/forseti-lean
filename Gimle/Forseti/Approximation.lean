import Gimle.Forseti
import Gimle.Asgard.Approximation

/-! Optional property adapter for the same Asgard approximation relation.
The original binding is supplied independently. Opaque identifiers are retained
metadata, not authenticated hashes or native/foreign validation receipts. -/
namespace Gimle.Forseti.Approximation

structure OriginalBinding (n m : Nat) where
  artifactId : String
  sourceId : String
  targetId : String
  claim : Gimle.Asgard.Approximation.Claim n m

/-- A Lean proof about the complete original claim; no measurement constructor. -/
structure BoundFact {n m : Nat} (original : OriginalBinding n m) : Prop where
  valid : original.claim.Holds

/-- The adapter always retains the supplied original, including all labels,
actual typed circuits, region, budget and interpretation/metric context. -/
def BoundFact.binding {n m : Nat} {original : OriginalBinding n m}
    (_fact : BoundFact original) : OriginalBinding n m := original

theorem BoundFact.binding_preserved {n m : Nat} {original : OriginalBinding n m}
    (fact : BoundFact original) : fact.binding = original := rfl

theorem BoundFact.toCircuitFact {n m : Nat} {original : OriginalBinding n m}
    (fact : BoundFact original) : QuantitativeCircuitEquivalence
      original.claim.source original.claim.target ⟨original.claim.region⟩ original.claim.error.value :=
  fact.valid

theorem BoundFact.transportExact {n m : Nat} {original : OriginalBinding n m}
    (fact : BoundFact original) {pre : Predicate n} {post : Predicate m}
    (sourceProof : ExactHoare pre original.claim.source post)
    (coverage : PredicateEntailment pre ⟨original.claim.region⟩) :
    QuantitativeHoare pre original.claim.target post original.claim.error.value :=
  approximateCircuitTransportExact sourceProof fact.toCircuitFact coverage

theorem BoundFact.transportQuantitative {n m : Nat} {original : OriginalBinding n m}
    (fact : BoundFact original) {pre : Predicate n} {post : Predicate m} {sourceError : ℝ}
    (sourceProof : QuantitativeHoare pre original.claim.source post sourceError)
    (coverage : PredicateEntailment pre ⟨original.claim.region⟩) :
    QuantitativeHoare pre original.claim.target post (sourceError+original.claim.error.value) :=
  approximateCircuitTransportQuantitative sourceProof fact.toCircuitFact coverage


/-! ### Bridge to Asgard's sensitivity notion

`Gimle.Asgard.Approximation.LipschitzOn` is the affine-in-delta special case of
`CircuitModulus`: a single non-negative rational gain applied at every radius.
Asgard's `Approximation.sequential` is the corresponding composition theorem at
the circuit-equivalence layer.

The bridge lives here rather than in `Gimle/Forseti.lean` because importing
Asgard's approximation layer into the core would pull `Budget`, `Claim`,
`Sample` and `Observation` into the module a foreign candidate may import.
`CircuitModulus` is the more general notion -- it admits non-linear moduli,
where `LipschitzOn` is affine -- so it is kept, and this lemma lets any Asgard
sensitivity fact feed the Forseti sequential rules. -/

/-- An Asgard Lipschitz bound yields a Forseti modulus at any non-negative
radius. -/
theorem lipschitzToModulus {inputDegree outputDegree : Nat}
    {circuit : Circuit inputDegree outputDegree}
    {region : Predicate inputDegree} {gain : Gimle.Asgard.Approximation.Budget}
    {radius : ℝ} (nonnegative : 0 ≤ radius)
    (sensitivity : Gimle.Asgard.Approximation.LipschitzOn circuit region.holds gain) :
    CircuitModulus circuit region radius ((gain.value : ℝ) * radius) :=
  fun left right leftHeld rightHeld close =>
    sensitivity left right leftHeld rightHeld radius nonnegative close

#print axioms lipschitzToModulus

#print axioms BoundFact.toCircuitFact
#print axioms BoundFact.transportExact
#print axioms BoundFact.transportQuantitative
end Gimle.Forseti.Approximation
