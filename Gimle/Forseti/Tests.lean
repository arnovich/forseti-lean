import Gimle.Forseti
import Gimle.Forseti.Tests.LinearEnergy
import Gimle.Forseti.Tests.Discrete
import Gimle.Forseti.Tests.Approximation
import Gimle.Forseti.Tests.EquationWorkflow
import Gimle.Forseti.Tests.Syntax
import Gimle.Forseti.Tests.Context
import Gimle.Forseti.Tests.SequentialHoare

namespace Gimle.Forseti.Tests

-- The facade introduces no second circuit type or evaluator.
example : Circuit = Gimle.Asgard.Circuit := rfl
example (c : Circuit 7 3) (x : Point 7) : c.run x = Gimle.Asgard.Circuit.run c x := rfl

example (a b : Circuit 2 1) (p : Predicate 2) (e : ℝ) :
    QuantitativeCircuitEquivalence a b p e ↔
      Gimle.Asgard.QuantitativeCircuitEquivalence a b p.holds e := Iff.rfl

example : ¬ ExactHoare ⟨fun _ => True⟩ Circuit.id ⟨fun x => x 0 = 0⟩ := by
  intro h
  have bad := h ![1] trivial
  norm_num at bad

#print axioms exactCircuitSubstitution
#print axioms approximateCircuitTransportQuantitative
#print axioms quantitativeHoareMonoidal
#print axioms exactHoareSequential
#print axioms exactThenQuantitativeHoareSequential
#print axioms quantitativeHoareSequential
#print axioms modulusCompose
#print axioms modulusNarrow
#print axioms canonicalSequential
#print axioms coverageSequential
#print axioms SequentialHoare.coverageCarriesOnlyTheSecondError
#print axioms quantitativeThenExactSequential
#print axioms SequentialHoare.naiveRuleIsFalse
#print axioms SequentialHoare.squareHasNoModulus
#print axioms SequentialHoare.generalRuleOnBoundedRegion
#print axioms SequentialHoare.threeStages

end Gimle.Forseti.Tests

-- Generated code outside the namespace uses these fully-qualified legacy names.
example (c : Gimle.Forseti.Circuit 2 1) (x : Gimle.Forseti.Point 2) :
    Gimle.Forseti.Circuit.run c x = Gimle.Asgard.Circuit.run c x := rfl

example : Gimle.Forseti.Circuit 2 2 :=
  Gimle.Forseti.Circuit.parallel (leftInput := 1) (leftOutput := 1)
    (rightInput := 1) (rightOutput := 1)
    Gimle.Forseti.Circuit.id Gimle.Forseti.Circuit.id
