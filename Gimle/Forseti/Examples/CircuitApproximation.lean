import Gimle.Forseti.Approximation
import Gimle.Asgard.Examples.Approximation

/-! Consume Asgard's certified secant approximation without re-proving its
circuit error or relabeling its supplied binding. This is standalone Lean
property transport, not a native/foreign artifact-admission command. -/
namespace Gimle.Forseti.Examples.CircuitApproximation
open Gimle.Forseti.Approximation
open Gimle.Asgard.Examples.Approximation

def original : OriginalBinding 1 1 where
  artifactId := "secant-on-unit-interval"
  sourceId := "original-typed-square"
  targetId := "original-typed-identity"
  claim := secantClaim

theorem fact : BoundFact original := ⟨secant_bound⟩

def unit : Predicate 1 := ⟨unitRegion⟩

theorem square_property : ExactHoare unit original.claim.source unit := by
  intro x hx
  exact (intermediate_coverage x hx).1

/-- The target inherits the source property with the original 1/4 allowance. -/
theorem transported : QuantitativeHoare unit original.claim.target unit (1/4) := by
  simpa [original, secantClaim] using fact.transportExact square_property (fun _ h => h)

theorem original_preserved : fact.binding = original := fact.binding_preserved

#print axioms fact
#print axioms transported
end Gimle.Forseti.Examples.CircuitApproximation
