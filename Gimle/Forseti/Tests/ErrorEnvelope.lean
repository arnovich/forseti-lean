module

public import Gimle.Forseti.ErrorEnvelope

/-! Regression proofs for signed affine error envelopes and their boundaries. -/

@[expose] public section

namespace Gimle.Forseti.Tests.ErrorEnvelope

open Set Real Gimle.Forseti.ErrorEnvelope

/-- A collapsed interval needs no derivative, only its initial bound. -/
theorem zero_duration (e e' : ℝ → ℝ) (a δ g R : ℝ) (hi : e a ≤ δ) :
    ∀ t ∈ Icc a a, e t ≤ gronwallBound δ g R (t - a) := by
  apply affine_comparison (e' := e') le_rfl
  · simpa only [Icc_self] using continuousOn_singleton e a
  · simp
  · exact hi
  · simp

/-- A nonzero start time and zero growth produce linear residual accumulation. -/
theorem zero_growth {e e' : ℝ → ℝ} (hc : ContinuousOn e (Icc 3 5))
    (hd : ∀ t ∈ Ioo 3 5, HasDerivAt e (e' t) t)
    (hi : e 3 ≤ 1) (hb : ∀ t ∈ Ioo 3 5, e' t ≤ 2) : e 5 ≤ 5 := by
  have h := affine_comparison (g := 0) (R := 2) (δ := 1) (by norm_num : (3 : ℝ) ≤ 5)
    hc hd hi (by simpa using hb) 5 (by norm_num)
  norm_num [gronwallBound_K0] at h
  exact h

/-- Negative growth can accompany rising error toward a positive equilibrium. -/
theorem negative_growth_rising (t : ℝ) :
    gronwallBound 0 (-1) 1 t = 1 - exp (-t) := by
  simp [gronwallBound, neg_sub]

/-- Negative growth and zero residual retain exponential decay. -/
theorem negative_growth_decay (t : ℝ) :
    gronwallBound 1 (-1) 0 t = exp (-t) := by
  simp [gronwallBound_ε0]

/-- Rising negative-growth comparison is bounded by its final endpoint. -/
theorem rising_whole_segment {t : ℝ} (ht : t ∈ Icc 0 1) :
    gronwallBound 0 (-1) 1 t ≤ 1 - exp (-1) := by
  have h := envelope_le_max_endpoints 0 (-1) 1 ht
  have he : exp (-1 : ℝ) ≤ 1 := by exact exp_le_one_iff.mpr (by norm_num)
  simpa only [negative_growth_rising, max_eq_right (sub_nonneg.mpr he)] using h

/-- A decreasing comparison must retain its incoming bound for whole coverage. -/
theorem decaying_whole_segment {t : ℝ} (ht : t ∈ Icc 0 1) :
    gronwallBound 1 (-1) 0 t ≤ 1 := by
  have h := envelope_le_max_endpoints 1 (-1) 0 ht
  have he : exp (-1 : ℝ) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  simpa only [negative_growth_decay, max_eq_left he] using h

/-- For decay, using the terminal value as a uniform bound would be false. -/
theorem terminal_value_is_not_whole_bound :
    ¬ (∀ t ∈ Icc (0 : ℝ) 1,
      gronwallBound 1 (-1) 0 t ≤ gronwallBound 1 (-1) 0 1) := by
  intro h
  have hzero := h 0 (by norm_num)
  rw [gronwallBound_x0, negative_growth_decay] at hzero
  exact (not_le_of_gt (exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))) hzero

/-- First half of the corner example: a constant comparison upper bound. -/
def first : Segment := ⟨0, 1, 1, 0, 0, 1⟩
/-- Second half: one unit of residual accumulated over one unit of time. -/
def second : Segment := ⟨1, 2, 1, 0, 1, 2⟩

private theorem first_valid : first.Valid := by
  constructor <;> norm_num [first, gronwallBound_K0]

private theorem second_valid : second.Valid := by
  constructor <;> norm_num [second, gronwallBound_K0]

/-- Distinct derivative witnesses on the two sides of a join are permitted;
the common function remains continuous separately through the shared endpoint. -/
theorem derivative_jump {e : ℝ → ℝ}
    (left : first.Controls e (fun _ => -1))
    (right : second.Controls e (fun _ => 1)) (hi : e 0 ≤ 1) :
    (∀ t ∈ Icc 0 2, e t ≤ 2) ∧ e 2 ≤ 2 := by
  simpa [first, second] using stitch first_valid second_valid left right rfl
    (by norm_num [first, second]) hi

private theorem absolute_left : first.Controls (fun t => |t - 1|) (fun _ => -1) where
  continuous := (continuous_id.sub continuous_const).abs.continuousOn
  derivative := by
    intro t ht
    have hlt : t < 1 := ht.2
    have heq : (fun s : ℝ => |s - 1|) =ᶠ[nhds t] (fun s => -(s - 1)) := by
      filter_upwards [eventually_lt_nhds hlt] with s hs
      exact abs_of_neg (sub_neg.mpr hs)
    exact ((hasDerivAt_id t).sub_const 1).neg.congr_of_eventuallyEq heq
  growth_bound := by intro t _; norm_num [first]

private theorem absolute_right : second.Controls (fun t => |t - 1|) (fun _ => 1) where
  continuous := (continuous_id.sub continuous_const).abs.continuousOn
  derivative := by
    intro t ht
    have hlt : 1 < t := ht.1
    have heq : (fun s : ℝ => |s - 1|) =ᶠ[nhds t] (fun s => s - 1) := by
      filter_upwards [eventually_gt_nhds hlt] with s hs
      exact abs_of_pos (sub_pos.mpr hs)
    exact ((hasDerivAt_id t).sub_const 1).congr_of_eventuallyEq heq
  growth_bound := by intro t _; norm_num [second]

/-- The join theorem applies to an actual continuous function with a corner. -/
theorem absolute_value_corner : ∀ t ∈ Icc (0 : ℝ) 2, |t - 1| ≤ 2 :=
  (derivative_jump absolute_left absolute_right (by norm_num)).1

/-- The inductive chain API consumes the same local certificates and handoff. -/
theorem finite_chain_corner : ∀ t ∈ Icc (0 : ℝ) 2, |t - 1| ≤ 2 := by
  have h := Chain.append (Chain.single first_valid absolute_left)
    second_valid absolute_right rfl (by norm_num [first, second])
  have hs := h.sound (by norm_num [first])
  simpa [first, second] using hs.1

/-- A proposed endpoint below the affine solution is not a valid certificate. -/
theorem understated_endpoint : ¬ (⟨0, 1, 0, 0, 1, 0⟩ : Segment).Valid := by
  intro h
  have := h.endpoint
  norm_num [gronwallBound_K0] at this

/-- A zero bound cannot cover a nonzero initial error. -/
theorem initial_bound_is_necessary : ¬ (∀ t ∈ Icc (0 : ℝ) 1, (1 : ℝ) ≤ 0) := by
  intro h
  have := h 0 (by norm_num)
  norm_num at this

/- Missing premises must remain visible in the theorem type. These commands
deliberately omit a required argument and must fail without producing a theorem. -/

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
#check fun (s : Segment) (hv : s.Valid) (e e' : ℝ → ℝ) (hc : s.Controls e e') =>
  (show e s.stop ≤ s.outgoing from Segment.endpoint_sound hv hc)

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
#check fun (s : Segment) (e e' : ℝ → ℝ) (hc : s.Controls e e')
    (hi : e s.start ≤ s.incoming) =>
  (show e s.stop ≤ s.outgoing from Segment.endpoint_sound (hc := hc) (hi := hi))

#print axioms zero_duration
#print axioms zero_growth
#print axioms negative_growth_rising
#print axioms terminal_value_is_not_whole_bound
#print axioms rising_whole_segment
#print axioms decaying_whole_segment
#print axioms derivative_jump
#print axioms absolute_value_corner
#print axioms finite_chain_corner
#print axioms understated_endpoint

end Gimle.Forseti.Tests.ErrorEnvelope
