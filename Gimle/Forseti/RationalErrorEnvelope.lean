module

public import Gimle.Forseti.ErrorEnvelope
public import Mathlib.Analysis.Complex.Exponential

/-!
# Rational caps for affine error segments

A positive-growth affine Grönwall envelope has a rational upper bound when
`growth * duration < 1`. This supplies the finite endpoint obligation of an
error-envelope segment. Application-specific differential inequalities, initial
error and trajectory existence remain separate hypotheses.
-/

@[expose] public section
namespace Gimle.Forseti.ErrorEnvelope
open Real

/-- Rational endpoint cap for nonnegative incoming error and residual. -/
theorem affine_rational_cap {δ g R h : ℝ}
    (hδ : 0 ≤ δ) (hg : 0 < g) (hR : 0 ≤ R) (hh : 0 ≤ h)
    (hq : g * h < 1) :
    gronwallBound δ g R h ≤ (δ + h * R) / (1 - g * h) := by
  have he := exp_bound_div_one_sub_of_interval (mul_nonneg hg.le hh) hq
  rw [gronwallBound_of_K_ne_0 (ne_of_gt hg)]
  calc
    δ * exp (g * h) + R / g * (exp (g * h) - 1) ≤
        δ * (1 / (1 - g * h)) + R / g * (1 / (1 - g * h) - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left he hδ)
        (mul_le_mul_of_nonneg_left (sub_le_sub_right he 1) (div_nonneg hR hg.le))
    _ = (δ + h * R) / (1 - g * h) := by
      field_simp [ne_of_gt hg, ne_of_gt (sub_pos.mpr hq)]
      ring

/-- Rational arithmetic can establish segment validity, but not its controls. -/
theorem Segment.valid_of_rational_cap (s : Segment)
    (ordered : s.start ≤ s.stop) (incoming : 0 ≤ s.incoming)
    (residual : 0 ≤ s.residual) (growth : 0 < s.growth)
    (cap : s.growth * (s.stop - s.start) < 1)
    (budget : (s.incoming + (s.stop - s.start) * s.residual) /
      (1 - s.growth * (s.stop - s.start)) ≤ s.outgoing) : s.Valid := by
  exact ⟨ordered, incoming, residual,
    (affine_rational_cap incoming growth residual (sub_nonneg.mpr ordered) cap).trans budget⟩

#print axioms affine_rational_cap
#print axioms Segment.valid_of_rational_cap
end Gimle.Forseti.ErrorEnvelope
