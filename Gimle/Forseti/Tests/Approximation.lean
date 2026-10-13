import Gimle.Forseti.Examples.CircuitApproximation

namespace Gimle.Forseti.Tests.Approximation
open Gimle.Forseti.Approximation
open Gimle.Forseti.Examples.CircuitApproximation

example : fact.binding.artifactId = "secant-on-unit-interval" := rfl
example : fact.binding.sourceId = original.sourceId := rfl
example : fact.binding.targetId = original.targetId := rfl
example : fact.binding.claim.source = original.claim.source := rfl
example : fact.binding.claim.target = original.claim.target := rfl
example : fact.binding.claim.error.value = 1/4 := rfl
example : fact.binding.claim.region = original.claim.region := rfl
example : fact.binding.claim.context = original.claim.context := rfl

/-- Identical mathematical claims do not erase distinct supplied bindings. -/
def another : OriginalBinding 1 1 := {original with artifactId := "another-artifact"}
theorem anotherFact : BoundFact another := ⟨Gimle.Asgard.Examples.Approximation.secant_bound⟩
example : fact.binding.artifactId ≠ anotherFact.binding.artifactId := by decide

/-- Changing the budget requires a new proof, and zero is false in the interior. -/
def wrongBudget : OriginalBinding 1 1 :=
  {original with claim := {original.claim with error := ⟨0, by norm_num⟩}}
example : ¬ BoundFact wrongBudget := by
  intro h
  have hd := h.valid ![1/2] (by norm_num [wrongBudget, original,
    Gimle.Asgard.Examples.Approximation.secantClaim, Gimle.Asgard.Examples.Approximation.unitRegion]) 0
  change |Gimle.Asgard.Examples.Approximation.square.run ![1/2] 0 - Circuit.id.run ![1/2] 0| ≤ ((0 : ℚ) : ℝ) at hd
  rw [Gimle.Asgard.Examples.Approximation.interior_error] at hd
  norm_num at hd

/-- The actual target circuit is bound, not just the target's retained label. -/
def wrongTarget : OriginalBinding 1 1 :=
  {original with claim := {original.claim with target := .compose .terminal (.const 5)}}
example : ¬ BoundFact wrongTarget := by
  intro h
  have hd := h.valid ![0] (by norm_num [wrongTarget, original,
    Gimle.Asgard.Examples.Approximation.secantClaim, Gimle.Asgard.Examples.Approximation.unitRegion]) 0
  norm_num [wrongTarget, original, Gimle.Asgard.Examples.Approximation.secantClaim,
    Gimle.Asgard.Examples.Approximation.square] at hd

#print axioms BoundFact.transportExact
#print axioms transported
end Gimle.Forseti.Tests.Approximation
