module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Residual error envelopes on closed time intervals

A scalar growth/residual inequality and an initial bound imply an affine
Grönwall envelope. Growth may be negative. Derivatives are required only in
the interior of each interval, so adjacent intervals can have different
derivatives at their common endpoint. The scalar analytic assumptions remain
separate from the finite endpoint certificate. No PDE, circuit translation,
existence result, or method for finding those assumptions is asserted here.
-/

@[expose] public section

namespace Gimle.Forseti.ErrorEnvelope

open Set Real

/-- Integrating-factor comparison on an arbitrary closed interval. -/
theorem homogeneous_comparison {e e' : ℝ → ℝ} {a b g : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn e (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt e (e' t) t)
    (hbound : ∀ t ∈ Ioo a b, e' t ≤ g * e t) :
    ∀ t ∈ Icc a b, e t ≤ exp (g * (t - a)) * e a := by
  let E := fun t => exp (-g * (t - a)) * e t
  have hE (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt E (exp (-g * (t - a)) * (e' t - g * e t)) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul (-g)).exp.mul (hd t ht)) using 1
    simp only [id_eq, mul_one]
    ring
  have ha : AntitoneOn E (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      ((Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn.mul hc)
    · intro t ht
      exact (hE t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      change deriv E t ≤ 0
      rw [(hE t (by simpa using ht)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (exp_pos _))
        (sub_nonpos.mpr (hbound t (by simpa using ht)))
  intro t ht
  have hh := ha ⟨le_rfl, hab⟩ ht ht.1
  dsimp [E] at hh
  simp only [sub_self, mul_zero, exp_zero, one_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (le_of_lt (exp_pos (g * (t - a))))
  simpa only [← mul_assoc, ← exp_add, neg_mul, add_neg_cancel, exp_zero,
    one_mul] using hh'

/-- Initial error, signed growth and residual imply the exact affine envelope.
Only interior derivatives are needed, including when the interval is a singleton. -/
theorem affine_comparison {e e' : ℝ → ℝ} {a b δ g R : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn e (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt e (e' t) t)
    (hinit : e a ≤ δ)
    (hbound : ∀ t ∈ Ioo a b, e' t ≤ g * e t + R) :
    ∀ t ∈ Icc a b, e t ≤ gronwallBound δ g R (t - a) := by
  let q := fun t => gronwallBound δ g R (t - a)
  have hq (t : ℝ) : HasDerivAt q (g * q t + R) t :=
    hasDerivAt_gronwallBound_shift δ g R t a
  have hqc : Continuous q := continuous_iff_continuousAt.mpr
    (fun t => (hq t).continuousAt)
  have h := homogeneous_comparison (g := g) (e := fun t => e t - q t)
    (e' := fun t => e' t - (g * q t + R)) hab
    (hc.sub hqc.continuousOn) (fun t ht => (hd t ht).sub (hq t))
    (fun t ht => by have := hbound t ht; linarith)
  intro t ht
  have hstart : e a - q a ≤ 0 := by simpa [q, gronwallBound_x0] using sub_nonpos.mpr hinit
  have hh := (h t ht).trans
    (mul_nonpos_of_nonneg_of_nonpos (le_of_lt (exp_pos _)) hstart)
  exact sub_nonpos.mp hh

/-- One-sided liminf slopes support scalar errors that are not differentiable
at zero. The slope premise must be supplied by the application, not inferred
from a numerical trajectory. -/
theorem affine_comparison_liminf {e e' : ℝ → ℝ} {a b δ g R : ℝ}
    (hc : ContinuousOn e (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ r, e' x < r →
      ∃ᶠ z in nhdsWithin x (Ioi x), (z - x)⁻¹ * (e z - e x) < r)
    (hinit : e a ≤ δ)
    (hbound : ∀ t ∈ Ico a b, e' t ≤ g * e t + R) :
    ∀ t ∈ Icc a b, e t ≤ gronwallBound δ g R (t - a) :=
  le_gronwallBound_of_liminf_deriv_right_le hc hd hinit hbound

/-- The affine solution's derivative has the fixed sign of its initial slope. -/
theorem envelope_derivative (δ g R t : ℝ) :
    HasDerivAt (gronwallBound δ g R) (exp (g * t) * (g * δ + R)) t := by
  convert hasDerivAt_gronwallBound δ g R t using 1
  by_cases hg : g = 0
  · simp [hg, gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hg]
    field_simp
    ring

/-- For either sign of growth, the full affine envelope lies below its two
endpoint maximum. This also covers increasing approach to a stable equilibrium. -/
theorem envelope_le_max_endpoints (δ g R : ℝ) {h s : ℝ}
    (hs : s ∈ Icc 0 h) :
    gronwallBound δ g R s ≤ max δ (gronwallBound δ g R h) := by
  by_cases hd : 0 ≤ g * δ + R
  · have hm : Monotone (gronwallBound δ g R) :=
      monotone_of_deriv_nonneg (fun t => (envelope_derivative δ g R t).differentiableAt)
        (fun t => by rw [(envelope_derivative δ g R t).deriv]; positivity)
    exact (hm hs.2).trans (le_max_right _ _)
  · have hm : Antitone (gronwallBound δ g R) :=
      antitone_of_deriv_nonpos (fun t => (envelope_derivative δ g R t).differentiableAt)
        (fun t => by
          rw [(envelope_derivative δ g R t).deriv]
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (exp_pos _)) (le_of_not_ge hd))
    have hh := hm hs.1
    rw [gronwallBound_x0] at hh
    exact hh.trans (le_max_left _ _)

/-- Scalar enclosure data. Proposing these numbers does not establish validity. -/
structure Segment where
  start : ℝ
  stop : ℝ
  incoming : ℝ
  growth : ℝ
  residual : ℝ
  outgoing : ℝ

/-- Finite endpoint obligations, distinct from the application's differential
inequality. Nonnegative errors/residuals retain their intended interpretation. -/
structure Segment.Valid (s : Segment) : Prop where
  ordered : s.start ≤ s.stop
  incoming_nonneg : 0 ≤ s.incoming
  residual_nonneg : 0 ≤ s.residual
  endpoint : gronwallBound s.incoming s.growth s.residual (s.stop - s.start) ≤ s.outgoing

/-- Application-supplied analytic premises on one segment. These do not assert
existence of a trajectory or bind an error to any particular physical model. -/
structure Segment.Controls (s : Segment) (e e' : ℝ → ℝ) : Prop where
  continuous : ContinuousOn e (Icc s.start s.stop)
  derivative : ∀ t ∈ Ioo s.start s.stop, HasDerivAt e (e' t) t
  growth_bound : ∀ t ∈ Ioo s.start s.stop, e' t ≤ s.growth * e t + s.residual

/-- A valid scalar certificate bounds the terminal error of every controlled
error function that starts within the declared incoming bound. -/
theorem Segment.endpoint_sound {s : Segment} (hv : s.Valid)
    {e e' : ℝ → ℝ} (hc : s.Controls e e') (hi : e s.start ≤ s.incoming) :
    e s.stop ≤ s.outgoing :=
  (affine_comparison hv.ordered hc.continuous hc.derivative hi hc.growth_bound
    s.stop ⟨hv.ordered, le_rfl⟩).trans hv.endpoint

/-- Endpoint propagation plus a max-endpoint argument covers every time in
the segment, not only the saved knots. -/
theorem Segment.sound {s : Segment} (hv : s.Valid)
    {e e' : ℝ → ℝ} (hc : s.Controls e e') (hi : e s.start ≤ s.incoming) :
    ∀ t ∈ Icc s.start s.stop, e t ≤ max s.incoming s.outgoing := by
  intro t ht
  apply (affine_comparison hv.ordered hc.continuous hc.derivative hi hc.growth_bound t ht).trans
  exact (envelope_le_max_endpoints s.incoming s.growth s.residual
    ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 _⟩).trans
    (max_le_max le_rfl hv.endpoint)

/-- Two adjoining segments may use different derivative witnesses. Endpoint
coverage and the incoming/outgoing handoff are explicit hypotheses. -/
theorem stitch {first second : Segment} (hfirst : first.Valid) (hsecond : second.Valid)
    {e dfirst dsecond : ℝ → ℝ}
    (cfirst : first.Controls e dfirst) (csecond : second.Controls e dsecond)
    (join : first.stop = second.start) (handoff : first.outgoing ≤ second.incoming)
    (initial : e first.start ≤ first.incoming) :
    (∀ t ∈ Icc first.start second.stop,
      e t ≤ max (max first.incoming first.outgoing) (max second.incoming second.outgoing)) ∧
    e second.stop ≤ second.outgoing := by
  have hnext : e second.start ≤ second.incoming := by
    rw [← join]
    exact (Segment.endpoint_sound hfirst cfirst initial).trans handoff
  refine ⟨?_, Segment.endpoint_sound hsecond csecond hnext⟩
  intro t ht
  by_cases hleft : t ≤ first.stop
  · exact (Segment.sound hfirst cfirst initial t ⟨ht.1, hleft⟩).trans (le_max_left _ _)
  · have hright : second.start ≤ t := by rw [← join]; exact le_of_lt (lt_of_not_ge hleft)
    exact (Segment.sound hsecond csecond hnext t ⟨hright, ht.2⟩).trans (le_max_right _ _)

/-- A finite, nonempty chain of locally controlled segments. The indices record
the first start/incoming bound, final stop/outgoing bound and global envelope.
Appending requires an exact time join and a valid error-bound handoff. -/
inductive Chain (e : ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ → Prop
  | single {s : Segment} {e' : ℝ → ℝ} (valid : s.Valid) (controls : s.Controls e e') :
      Chain e s.start s.incoming s.stop s.outgoing (max s.incoming s.outgoing)
  | append {a incoming b outgoing bound : ℝ} {s : Segment} {e' : ℝ → ℝ}
      (previous : Chain e a incoming b outgoing bound)
      (valid : s.Valid) (controls : s.Controls e e')
      (join : b = s.start) (handoff : outgoing ≤ s.incoming) :
      Chain e a incoming s.stop s.outgoing (max bound (max s.incoming s.outgoing))

/-- Finite-chain induction propagates both the terminal error and the entire
continuous-time bound. No common derivative at a join is required. -/
theorem Chain.sound {e : ℝ → ℝ} {a incoming b outgoing bound : ℝ}
    (chain : Chain e a incoming b outgoing bound) :
    e a ≤ incoming →
      (∀ t ∈ Icc a b, e t ≤ bound) ∧ e b ≤ outgoing := by
  induction chain with
  | single valid controls =>
      intro initial
      exact ⟨Segment.sound valid controls initial, Segment.endpoint_sound valid controls initial⟩
  | @append a incoming b outgoing bound s e' previous valid controls join handoff ih =>
      intro initial
      obtain ⟨hprevious, hterminal⟩ := ih initial
      have hnext : e s.start ≤ s.incoming := by
        rw [← join]
        exact hterminal.trans handoff
      refine ⟨?_, Segment.endpoint_sound valid controls hnext⟩
      intro t ht
      by_cases hleft : t ≤ b
      · exact (hprevious t ⟨ht.1, hleft⟩).trans (le_max_left _ _)
      · have hright : s.start ≤ t := by rw [← join]; exact le_of_lt (lt_of_not_ge hleft)
        exact (Segment.sound valid controls hnext t ⟨hright, ht.2⟩).trans (le_max_right _ _)

#print axioms affine_comparison
#print axioms affine_comparison_liminf
#print axioms envelope_le_max_endpoints
#print axioms Segment.sound
#print axioms stitch
#print axioms Chain.sound

end Gimle.Forseti.ErrorEnvelope
