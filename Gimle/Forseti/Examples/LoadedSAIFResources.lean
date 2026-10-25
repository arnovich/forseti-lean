import Gimle.Forseti.Examples.LoadedSAIFModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite resource budgets from continuous response bounds and exact balances.
The output and capacity bounds are explicit premises. This module integrates
the original physical-time equations across both load phases; it does not
infer intermediate bounds or integrals from sampled trajectories. -/
namespace Gimle.Forseti.Examples.LoadedSAIFResources
open Set MeasureTheory LoadedSAIFModel

/-- A continuous scalar upper bound gives the corresponding interval budget. -/
theorem integral_bound_const {f : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hb : ∀ t ∈ Icc a b, f t ≤ C) :
    (∫ t in a..b, f t) ≤ (b - a) * C := by
  simpa using intervalIntegral.integral_mono_on (μ := volume) hab
    (hc.intervalIntegrable_of_Icc hab) intervalIntegrable_const hb

private theorem sub_integrable {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 100))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 100) (hab : a ≤ b) :
    IntervalIntegrable f volume a b :=
  (hc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab

/-- Account for both startup/recovery windows at the peak cap and all other
times at the response-band cap. Both boundaries are included. -/
theorem output_integral_bound {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 100))
    (hp : ∀ t ∈ Icc 0 100, f t ≤ 13 / 5)
    (hbefore : ∀ t ∈ Icc 3 30, f t ≤ 11 / 5)
    (hafter : ∀ t ∈ Icc 33 100, f t ≤ 11 / 5) :
    (∫ t in (0 : ℝ)..100, f t) ≤ 1112 / 5 := by
  have h03 := integral_bound_const (by norm_num : (0 : ℝ) ≤ 3)
    (hc.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    (fun t ht => hp t ⟨ht.1, by linarith [ht.2]⟩)
  have h330 := integral_bound_const (by norm_num : (3 : ℝ) ≤ 30)
    (hc.mono (Icc_subset_Icc (by norm_num) (by norm_num))) hbefore
  have h3033 := integral_bound_const (by norm_num : (30 : ℝ) ≤ 33)
    (hc.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    (fun t ht => hp t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have h33100 := integral_bound_const (by norm_num : (33 : ℝ) ≤ 100)
    (hc.mono (Icc_subset_Icc (by norm_num) (by norm_num))) hafter
  have join1 := intervalIntegral.integral_add_adjacent_intervals
    (sub_integrable hc (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (3 : ℝ) ≤ 100)
      (by norm_num))
    (sub_integrable hc (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (30 : ℝ) ≤ 100)
      (by norm_num))
  have join2 := intervalIntegral.integral_add_adjacent_intervals
    (sub_integrable hc (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (30 : ℝ) ≤ 100)
      (by norm_num))
    (sub_integrable hc (by norm_num : (0 : ℝ) ≤ 30) (by norm_num : (33 : ℝ) ≤ 100)
      (by norm_num))
  have join3 := intervalIntegral.integral_add_adjacent_intervals
    (sub_integrable hc (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (33 : ℝ) ≤ 100)
      (by norm_num))
    (sub_integrable hc (by norm_num : (0 : ℝ) ≤ 33) (by norm_num : (100 : ℝ) ≤ 100)
      (by norm_num))
  linarith

/-- Closed one-sided endpoint derivatives suffice for the balance identity. -/
theorem integral_balance {f r : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hr : ContinuousOn r (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt f (r t) (Icc a b) t) :
    (∫ t in a..b, r t) = f b - f a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc
  · intro t ht
    exact (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact hr.intervalIntegrable_of_Icc hab

/-- The shared state and both closed phase solutions imply global continuity. -/
theorem switched_continuous {state : ℝ → State} (hs : Switched state) (i : Fin 5) :
    ContinuousOn (fun t => state t i) (Icc 0 100) := by
  have hb : ContinuousOn (fun t => state t i) (Icc 0 30) :=
    fun t ht => (hs.before t ht i).continuousWithinAt
  have ha : ContinuousOn (fun t => state t i) (Icc 30 100) :=
    fun t ht => (hs.after t ht i).continuousWithinAt
  exact (hb.union_of_isClosed ha isClosed_Icc isClosed_Icc).mono
    Icc_subset_Icc_union_Icc

private theorem phase_balances {state : ℝ → State} {L a b : ℝ} (hab : a ≤ b)
    (hs : Solves L a b state)
    (hc : ∀ i, ContinuousOn (fun t => state t i) (Icc a b))
    (hu : ContinuousOn (fun t => control (state t)) (Icc a b)) :
    ((∫ t in a..b, control (state t)) - (∫ t in a..b, state t 0) =
      state b 0 - state a 0) ∧
    ((∫ t in a..b, state t 0) - (∫ t in a..b, state t 1) -
      (∫ t in a..b, state t 4) / 5 =
      (state b 1 + state b 4) - (state a 1 + state a 4)) := by
  have first := integral_balance hab (hc 0) (hu.sub (hc 0))
    (fun t ht => (hs t ht 0).congr_deriv (precursor_balance L (state t)))
  have second := integral_balance hab ((hc 1).add (hc 4))
    (((hc 0).sub (hc 1)).sub ((hc 4).div_const 5))
    (fun t ht => ((hs t ht 1).add (hs t ht 4)).congr_deriv
      (output_balance L (state t)))
  simp only [Pi.sub_apply, Pi.add_apply] at first second
  rw [intervalIntegral.integral_sub (hu.intervalIntegrable_of_Icc hab)
    ((hc 0).intervalIntegrable_of_Icc hab)] at first
  rw [intervalIntegral.integral_sub (μ := volume)
    (f := fun t => state t 0 - state t 1) (g := fun t => state t 4 / 5)
    (((hc 0).sub (hc 1)).intervalIntegrable_of_Icc hab)
    (((hc 4).div_const 5).intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_sub (μ := volume)
      (f := fun t => state t 0) (g := fun t => state t 1)
      ((hc 0).intervalIntegrable_of_Icc hab)
      ((hc 1).intervalIntegrable_of_Icc hab), intervalIntegral.integral_div] at second
  exact ⟨first, second⟩

/-- The two physical balances telescope through the load switch without a reset. -/
theorem actuation_balance {state : ℝ → State} (hs : Switched state)
    (hz : ∀ t ∈ Icc 0 100, 0 ≤ state t 3) :
    (∫ t in (0 : ℝ)..100, control (state t)) =
      state 100 0 + state 100 1 + state 100 4 +
      (∫ t in (0 : ℝ)..100, state t 1) + (∫ t in (0 : ℝ)..100, state t 4) / 5 := by
  have hc := switched_continuous hs
  have hu : ContinuousOn (fun t => control (state t)) (Icc 0 100) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_const.add (hc 3))
    exact fun t ht => ne_of_gt (denominator_pos (hz t ht))
  have before := phase_balances (by norm_num : (0 : ℝ) ≤ 30) hs.before
    (fun i => (hc i).mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    (hu.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  have after := phase_balances (by norm_num : (30 : ℝ) ≤ 100) hs.after
    (fun i => (hc i).mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    (hu.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
  have joins (f : ℝ → ℝ) (h : ContinuousOn f (Icc 0 100)) :
      (∫ t in (0 : ℝ)..30, f t) + (∫ t in (30 : ℝ)..100, f t) =
        (∫ t in (0 : ℝ)..100, f t) :=
    intervalIntegral.integral_add_adjacent_intervals
      (sub_integrable h (by norm_num) (by norm_num) (by norm_num))
      (sub_integrable h (by norm_num) (by norm_num) (by norm_num))
  have ju := joins _ hu
  have j0 := joins _ (hc 0)
  have j1 := joins _ (hc 1)
  have j4 := joins _ (hc 4)
  have z0 : state 0 0 = 0 := congrFun hs.initial 0
  have z1 : state 0 1 = 0 := congrFun hs.initial 1
  have z4 : state 0 4 = 0 := congrFun hs.initial 4
  linarith [before.1, before.2, after.1, after.2]

/-- Continuous capacity and response bounds imply the exact finite resource
budgets. Existence and the response bounds themselves are not premises hidden
in numerical data: a caller must supply their proofs for this original model. -/
theorem resource_budgets {state : ℝ → State} (hs : Switched state)
    (hz : ∀ t ∈ Icc 0 100, 0 ≤ state t 3)
    (hx1 : state 100 0 ≤ alpha)
    (hc0 : ∀ t ∈ Icc 0 30, state t 4 = 0)
    (hc2 : ∀ t ∈ Icc 30 100, state t 4 ≤ 2)
    (hp : ∀ t ∈ Icc 0 100, state t 1 ≤ 13 / 5)
    (hbefore : ∀ t ∈ Icc 3 30, state t 1 ≤ 11 / 5)
    (hafter : ∀ t ∈ Icc 33 100, state t 1 ≤ 11 / 5) :
    (∫ t in (0 : ℝ)..100, control (state t)) ≤ 25776129 / 100000 ∧
    (∫ t in (0 : ℝ)..100, (2 + state t 1)) ≤ 2112 / 5 := by
  have hc := switched_continuous hs
  have output := output_integral_bound (hc 1) hp hbefore hafter
  have zero : (∫ t in (0 : ℝ)..30, state t 4) = 0 := by
    calc
      _ = ∫ _t in (0 : ℝ)..30, (0 : ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        exact hc0 t (by simpa using ht))
      _ = 0 := by simp
  have cap := integral_bound_const (by norm_num : (30 : ℝ) ≤ 100)
    ((hc 4).mono (Icc_subset_Icc (by norm_num) (by norm_num))) hc2
  have join := intervalIntegral.integral_add_adjacent_intervals
    (sub_integrable (hc 4) (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (30 : ℝ) ≤ 100) (by norm_num))
    (sub_integrable (hc 4) (by norm_num : (0 : ℝ) ≤ 30)
      (by norm_num : (100 : ℝ) ≤ 100) (by norm_num))
  have capacity : (∫ t in (0 : ℝ)..100, state t 4) ≤ 140 := by linarith
  constructor
  · have balance := actuation_balance hs hz
    have final_output := hafter 100 (by norm_num)
    have final_capacity := hc2 100 (by norm_num)
    norm_num [alpha] at hx1
    linarith
  · rw [intervalIntegral.integral_add intervalIntegrable_const
      ((hc 1).intervalIntegrable_of_Icc (by norm_num)), intervalIntegral.integral_const]
    norm_num
    linarith

#print axioms output_integral_bound
#print axioms actuation_balance
#print axioms resource_budgets
end Gimle.Forseti.Examples.LoadedSAIFResources
