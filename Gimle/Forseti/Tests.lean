module

public import Gimle.Forseti.Tests.ClassicalElliptic
public import Gimle.Forseti.Tests.ClassicalUniqueness
public import Gimle.Forseti.Tests.ClassicalVorticity
public import Gimle.Forseti.Tests.MildVorticity
public import Gimle.Forseti.Tests.MildStream
public import Gimle.Forseti
public import Gimle.Forseti.Tests.LinearEnergy
public import Gimle.Forseti.Tests.Discrete
public import Gimle.Forseti.Tests.Approximation
public import Gimle.Forseti.Tests.EquationWorkflow
public import Gimle.Forseti.Tests.Syntax
public import Gimle.Forseti.Tests.Context
public import Gimle.Forseti.Tests.Certificate
public import Gimle.Forseti.Tests.Trajectory
public import Gimle.Forseti.Tests.ThreeState
public import Gimle.Forseti.Tests.DampedOscillator
public import Gimle.Forseti.Tests.ForcedDecay
public import Gimle.Forseti.Tests.HedgedSpread
public import Gimle.Forseti.Tests.Stepped
public import Gimle.Forseti.Tests.HedgedSpreadStepped
public import Gimle.Forseti.Tests.LinearEnergyContract
public import Gimle.Forseti.Tests.Stream
public import Gimle.Forseti.Tests.SequentialHoare
public import Gimle.Forseti.Tests.StreamObservation
public import Gimle.Forseti.Tests.FieldBound
public import Gimle.Forseti.Tests.FieldObservation
public import Gimle.Forseti.Tests.AlgebraicWitness
public import Gimle.Forseti.Tests.Positivstellensatz
public import Gimle.Forseti.Tests.Lorenz
public import Gimle.Forseti.Tests.Nonlinear
public import Gimle.Forseti.Tests.GalerkinNS
public import Gimle.Forseti.Tests.GalerkinNSFamily
public import Gimle.Forseti.Tests.LocalTrapping
public import Gimle.Forseti.Tests.PolynomialTrapping
public import Gimle.Forseti.Tests.Hedging

@[expose] public section

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
