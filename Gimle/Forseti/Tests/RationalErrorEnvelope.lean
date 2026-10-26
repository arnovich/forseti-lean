module

public import Gimle.Forseti.RationalErrorEnvelope

/-! Exact regression with nonzero incoming error, growth and residual. -/
@[expose] public section
namespace Gimle.Forseti.Tests.RationalErrorEnvelope
open Gimle.Forseti.ErrorEnvelope

noncomputable def sample : Segment := ⟨0, 1/20, 1/100, 2, 1/1000, 67/6000⟩

theorem sample_valid : sample.Valid := by
  apply Segment.valid_of_rational_cap
  all_goals norm_num [sample]

theorem impossible_budget : ¬ ((1/100 : ℝ) + (1/20)*(1/1000)) /
    (1 - 2*(1/20)) ≤ 1/100 := by norm_num

/-- The regression exposes its analytic controls rather than asserting them. -/
theorem controlled_sample {e d : ℝ → ℝ} (h : sample.Controls e d)
    (initial : e 0 ≤ 1/100) : ∀ t ∈ Set.Icc (0 : ℝ) (1/20), e t ≤ 67/6000 := by
  have result := Segment.sound sample_valid h initial
  norm_num [sample] at result
  intro t ht
  exact result t ht.1 ht.2

#print axioms sample_valid
#print axioms controlled_sample
end Gimle.Forseti.Tests.RationalErrorEnvelope
