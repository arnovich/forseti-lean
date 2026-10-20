import Gimle.Forseti.Stepped

/-! Coverage for the stepped path semantics.

Pinned here: the iteration's defining equations and its agreement with `Discrete.run`;
that the path measure of a probability law is a probability measure; the four claim
forms, unfolded, with the probability-law and threshold conjuncts that make them fail,
rather than hold for nothing, at a negative threshold or under the zero measure; the
trivial bound at a threshold of at least `1` and monotonicity in the threshold; the
horizon breach bound on a scalar chain `x ↦ x − Δx + Δd` with centred shocks of finite
second moment, the squared state as the drift function and the barrier at level one;
the drift recursion with equality on a small deterministic chain; both law classes for
the centred Gaussian, and the three-point law's moments; the weighted-sum bound on the
scalar chain from zero and the fixed-date bound on a Gaussian random walk; two numeric
lower bounds on `Real.exp`; Bernoulli's inequality at `x = 1/10`; the refutation device
at Bernoulli's and at the exact threshold, on the scalar chain under
`threePoint (1/8) 8`; and the axiom policy, asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.Stepped

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Gimle.Forseti.Stepped

/-! ### The stable interface -/

example (f : ℝ → ℝ → ℝ) (x₀ : ℝ) (ω : ℕ → ℝ) : run f x₀ ω 0 = x₀ := rfl
example (f : ℝ → ℝ → ℝ) (x₀ : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    run f x₀ ω (n + 1) = f (run f x₀ ω n) (ω n) := rfl
example {s u m : ℕ} (update : Gimle.Asgard.Circuit (s + (u + m)) s)
    (p : Gimle.Asgard.Point m) (x₀ : Gimle.Asgard.Point s)
    (input : ℕ → Gimle.Asgard.Point u) (n : ℕ) :
    Gimle.Forseti.Discrete.run update p x₀ input n
      = run (Gimle.Forseti.Discrete.step update p) x₀ input n :=
  run_discrete update p x₀ input n
example (law : Measure ℝ) [IsProbabilityMeasure law] : IsProbabilityMeasure (pathMeasure law) :=
  inferInstance

/-! The four claim forms, unfolded. -/

section ClaimForms

variable (f : ℝ → ℝ → ℝ) (x₀ : ℝ) (law : Measure ℝ) (N n : ℕ) (safe : ℝ → Prop)
  (q : ℝ) (V : ℝ → ℝ)

example : BreachWithin f x₀ law N safe q ↔ IsProbabilityMeasure law ∧ 0 ≤ q ∧
    pathMeasure law {ω | ∃ k ≤ N, ¬ safe (run f x₀ ω k)} ≤ ENNReal.ofReal q := Iff.rfl
example : ExceedsAt f x₀ law n safe q ↔ IsProbabilityMeasure law ∧ 0 ≤ q ∧
    pathMeasure law {ω | ¬ safe (run f x₀ ω n)} ≤ ENNReal.ofReal q := Iff.rfl
example : AtEveryMark f x₀ law N safe q ↔ ∀ k ≤ N, ExceedsAt f x₀ law k safe q := Iff.rfl
example : ExpectedLe f x₀ law V n q ↔ IsProbabilityMeasure law ∧ 0 ≤ q ∧
    ∫⁻ ω, ENNReal.ofReal (V (run f x₀ ω n)) ∂pathMeasure law ≤ ENNReal.ofReal q := Iff.rfl

end ClaimForms

/-! ### The scalar chain and the horizon breach bound -/

/-- The scalar test chain `x ↦ x - Δ x + Δ d`. -/
def scalarStep (Δ : ℝ) (x d : ℝ) : ℝ := x - Δ * x + Δ * d

theorem measurable_scalarStep (Δ : ℝ) :
    Measurable (fun p : ℝ × ℝ => scalarStep Δ p.1 p.2) := by
  unfold scalarStep
  fun_prop

theorem measurable_ofReal_sq : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) :=
  ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)

/-- One step of the scalar chain with centred shocks of second moment `v` raises the
expectation of `x ^ 2` by at most `Δ ^ 2 * v`. -/
theorem scalarStep_drift {law : Measure ℝ} {Δ v : ℝ} (h : TwoMomentLaw law v)
    (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (x : ℝ) :
    ∫⁻ d, ENNReal.ofReal ((scalarStep Δ x d) ^ 2) ∂law
      ≤ ENNReal.ofReal (x ^ 2) + ENNReal.ofReal (Δ ^ 2 * v) := by
  haveI := h.prob
  have hexp : (fun d => (scalarStep Δ x d) ^ 2)
      = fun d => (((1 - Δ) * x) ^ 2 + (2 * (1 - Δ) * x * Δ) * d) + Δ ^ 2 * d ^ 2 := by
    funext d
    unfold scalarStep
    ring
  have h0 : Integrable (fun _ : ℝ => ((1 - Δ) * x) ^ 2) law := integrable_const _
  have h1 : Integrable (fun d : ℝ => (2 * (1 - Δ) * x * Δ) * d) law :=
    h.integrable_id.const_mul _
  have h2 : Integrable (fun d : ℝ => Δ ^ 2 * d ^ 2) law := h.integrable_sq.const_mul _
  have h01 : Integrable (fun d : ℝ => ((1 - Δ) * x) ^ 2 + (2 * (1 - Δ) * x * Δ) * d) law :=
    h0.add h1
  have hint : Integrable (fun d => (scalarStep Δ x d) ^ 2) law := by
    rw [hexp]
    exact h01.add h2
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun d => sq_nonneg _)]
  have hval : ∫ d, (scalarStep Δ x d) ^ 2 ∂law = ((1 - Δ) * x) ^ 2 + Δ ^ 2 * v := by
    rw [hexp, integral_add h01 h2, integral_add h0 h1, integral_const, integral_const_mul,
      integral_const_mul, h.mean, h.second]
    simp
  rw [hval]
  refine ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  rw [mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg x) (pow_le_one₀ (by linarith) (by linarith))

example (law : Measure ℝ) {Δ v : ℝ} (h : TwoMomentLaw law v) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (N : ℕ) : BreachWithin (scalarStep Δ) 0 law N (fun x => |x| ≤ 1) (N * (Δ ^ 2 * v)) := by
  haveI := h.prob
  have hv := h.nonneg
  refine breachWithin_of_drift (V := fun x : ℝ => ENNReal.ofReal (x ^ 2)) (c := 1)
    (β := ENNReal.ofReal (Δ ^ 2 * v)) law (measurable_scalarStep Δ) measurable_ofReal_sq
    one_ne_zero ENNReal.one_ne_top (fun x _ => scalarStep_drift h hΔ0 hΔ1 x)
    (fun x hx => ?_) (by positivity) ?_
  · exact ENNReal.one_le_ofReal.2 ((one_lt_sq_iff_one_lt_abs x).2 (not_le.1 hx)).le
  · simp [ENNReal.ofReal_mul (Nat.cast_nonneg N)]

/-! ### Trivial thresholds, the conjuncts and monotonicity -/

example : BreachWithin (scalarStep (1/4)) 0 (Measure.dirac 0) 10 (fun x => |x| ≤ 1) 1 :=
  breachWithin_of_le_one le_rfl

example : AtEveryMark (scalarStep (1/4)) 0 (Measure.dirac 0) 10 (fun x => |x| ≤ 1) 1 :=
  fun _ _ => exceedsAt_of_le_one le_rfl

/-- A negative threshold fails, even for a probability law. -/
example (law : Measure ℝ) [IsProbabilityMeasure law] :
    ¬ BreachWithin (scalarStep (1/4)) 0 law 10 (fun x => |x| ≤ 1) (-1) :=
  fun h => absurd h.2.1 (by norm_num)

/-- The zero measure is not a law: the claim forms fail for it, even at the threshold
`1`. -/
example : ¬ BreachWithin (scalarStep (1/4)) 0 (0 : Measure ℝ) 10 (fun x => |x| ≤ 1) 1 := by
  intro h
  have := h.1.measure_univ
  simp at this

example (f : ℝ → ℝ → ℝ) (law : Measure ℝ) (h : BreachWithin f 0 law 5 (· ≤ 1) (1/4)) :
    BreachWithin f 0 law 5 (· ≤ 1) (1/2) := h.mono (by norm_num)
example (f : ℝ → ℝ → ℝ) (law : Measure ℝ) (h : ExceedsAt f 0 law 5 (· ≤ 1) (1/4)) :
    ExceedsAt f 0 law 5 (· ≤ 1) (1/2) := h.mono (by norm_num)
example (f : ℝ → ℝ → ℝ) (law : Measure ℝ) (h : AtEveryMark f 0 law 5 (· ≤ 1) (1/4)) :
    AtEveryMark f 0 law 5 (· ≤ 1) (1/2) := h.mono (by norm_num)
example (f : ℝ → ℝ → ℝ) (law : Measure ℝ) (h : ExpectedLe f 0 law (· ^ 2) 5 (1/4)) :
    ExpectedLe f 0 law (· ^ 2) 5 (1/2) := h.mono (by norm_num)

/-! ### The drift recursion -/

example (x₀ : ℝ≥0∞) (n : ℕ) :
    ∫⁻ ω, run (fun (x : ℝ≥0∞) (_ : ℝ) => 2 * x + 3) x₀ ω n ∂pathMeasure (Measure.dirac (0 : ℝ))
      = 2 ^ n * x₀ + 3 * ∑ k ∈ Finset.range n, 2 ^ k :=
  lintegral_run_eq_geom (V := fun x => x) (Measure.dirac 0) (by fun_prop) measurable_id
    (fun x => by simp) x₀ n

/-! ### The law classes and the fixed-date bound -/

example : SubGaussianLaw (gaussianReal 0 64) 64 := gaussian_subGaussian 64
example : TwoMomentLaw (gaussianReal 0 64) 64 := gaussian_twoMoment 64

-- the three-point law with jumps `±257` has the second moment `64` of `gaussianReal 0 64`
example : TwoMomentLaw (threePoint (64 / (2 * 257 ^ 2)) 257) 64 := by
  have := threePoint_twoMoment (ε := 64 / (2 * 257 ^ 2)) (L := 257) (by norm_num) (by norm_num)
  convert this using 1; norm_num

-- its fourth moment, from the three weights
example : ∫ d, d ^ 4 ∂threePoint (1/8) 2 = 4 := by
  rw [integral_threePoint (by norm_num) (by norm_num)]
  norm_num

-- the scalar chain from 0 is a weighted sum, hence sub-Gaussian
example (law : Measure ℝ) (h : SubGaussianLaw law 64) (n : ℕ) :
    HasSubgaussianMGF
      (fun ω : ℕ → ℝ => ∑ k ∈ Finset.range n, ((1 - 1/4 : ℝ) ^ (n - 1 - k) * (1/4)) * ω k)
      (∑ k ∈ Finset.range n, sqNN ((1 - 1/4 : ℝ) ^ (n - 1 - k) * (1/4)) * 64)
      (pathMeasure law) :=
  weighted_sum_hasSubgaussianMGF h _ n

/-- The random walk with unit steps is the unweighted sum of its inputs. -/
theorem run_walk (n : ℕ) (ω : ℕ → ℝ) :
    run (fun x d : ℝ => x + d) 0 ω n = ∑ k ∈ Finset.range n, 1 * ω k := by
  induction n with
  | zero => simp
  | succ n ih => rw [run_succ, ih, Finset.sum_range_succ]; simp

-- a Gaussian random walk leaves `|x| ≤ 10` at mark `10` with probability at most
-- `2 exp(−5) ≈ 0.0135`, since the sum of ten unit-variance shocks has proxy `10`
example : ExceedsAt (fun x d : ℝ => x + d) 0 (gaussianReal 0 1) 10 (fun x => |x| ≤ 10)
    (2 * Real.exp (-5)) :=
  exceedsAt_of_weighted (obs := id) (w := fun _ => 1) (B := 10) (gaussian_subGaussian 1)
    (by norm_num) (fun ω => run_walk 10 ω) (fun x hx => not_le.1 hx)
    (le_of_eq (by norm_num))

/-! ### Numeric lower bounds on the exponential -/

-- `e^{5.47} ≥ 200`: at a proxy `c ≤ 0.0913`, `2 exp(−1/(2c)) ≤ 2 e^{−5.47} ≤ 1/100`
example : (200 : ℝ) ≤ Real.exp (547 / 100) := by
  have := exp_ge_floor_cubic 5 (r := 547 / 100) (by norm_num)
  norm_num at this ⊢; linarith

-- `e^{255/64} ≥ 50`: at the proxy `32/255`, `2 exp(−1/(2 · 32/255)) = 2 e^{−255/64} ≤ 1/25`
example : (50 : ℝ) ≤ Real.exp (255 / 64) := by
  have := exp_ge_floor_cubic 3 (r := 255 / 64) (by norm_num)
  norm_num at this ⊢; linarith

/-! ### The refutation device -/

example (N : ℕ) : N * (1/10 : ℝ) / (1 + N * (1/10)) ≤ 1 - (1 - 1/10) ^ N :=
  one_sub_pow_ge_bernoulli (by norm_num) (by norm_num) N

-- the scalar chain breaches at the first big shock: Bernoulli's threshold `4/5` refutes `1/2`
example : ¬ BreachWithin (scalarStep (1/4)) 0 (threePoint (1/8) 8) 16 (fun x => |x| ≤ 1) (1/2) :=
  not_breachWithin_threePoint (by norm_num) (by norm_num) (by simp [scalarStep])
    (by norm_num [scalarStep]) (by norm_num [scalarStep]) (by norm_num)

-- the exact threshold `1 − (3/4)¹⁶ ≈ 0.99` refutes `9/10`, which Bernoulli's does not reach
example : ¬ BreachWithin (scalarStep (1/4)) 0 (threePoint (1/8) 8) 16 (fun x => |x| ≤ 1) (9/10) :=
  not_breachWithin_threePoint_exact (by norm_num) (by norm_num) (by simp [scalarStep])
    (by norm_num [scalarStep]) (by norm_num [scalarStep]) (by norm_num)

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Stepped.run_zero' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms run_zero
/--
info: 'Gimle.Forseti.Stepped.run_succ' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms run_succ
/--
info: 'Gimle.Forseti.Stepped.run_congr' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in #print axioms run_congr
/--
info: 'Gimle.Forseti.Stepped.run_discrete'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms run_discrete
/--
info: 'Gimle.Forseti.Stepped.measurable_piFinset_of_dependsOn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms measurable_piFinset_of_dependsOn
/--
info: 'Gimle.Forseti.Stepped.isProbabilityMeasure_pathMeasure'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms isProbabilityMeasure_pathMeasure
/--
info: 'Gimle.Forseti.Stepped.BreachWithin.mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms BreachWithin.mono
/--
info: 'Gimle.Forseti.Stepped.ExceedsAt.mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ExceedsAt.mono
/--
info: 'Gimle.Forseti.Stepped.AtEveryMark.mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms AtEveryMark.mono
/--
info: 'Gimle.Forseti.Stepped.ExpectedLe.mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms ExpectedLe.mono
/--
info: 'Gimle.Forseti.Stepped.breachWithin_of_le_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breachWithin_of_le_one
/--
info: 'Gimle.Forseti.Stepped.exceedsAt_of_le_one'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exceedsAt_of_le_one
/--
info: 'Gimle.Forseti.Stepped.measurable_run'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms measurable_run
/--
info: 'Gimle.Forseti.Stepped.lintegral_run_succ'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lintegral_run_succ
/--
info: 'Gimle.Forseti.Stepped.lintegral_run_le_geom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lintegral_run_le_geom
/--
info: 'Gimle.Forseti.Stepped.lintegral_run_eq_geom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lintegral_run_eq_geom
/--
info: 'Gimle.Forseti.Stepped.stopped_of_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stopped_of_le
/--
info: 'Gimle.Forseti.Stepped.stopped_of_not_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms stopped_of_not_le
/--
info: 'Gimle.Forseti.Stepped.le_run_stopped_of_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms le_run_stopped_of_le
/--
info: 'Gimle.Forseti.Stepped.run_stopped_eq_run'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms run_stopped_eq_run
/--
info: 'Gimle.Forseti.Stepped.exists_le_iff_le_run_stopped'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exists_le_iff_le_run_stopped
/--
info: 'Gimle.Forseti.Stepped.breachSet_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breachSet_eq
/--
info: 'Gimle.Forseti.Stepped.lintegral_stopped_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lintegral_stopped_le
/--
info: 'Gimle.Forseti.Stepped.measurable_stopped'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms measurable_stopped
/--
info: 'Gimle.Forseti.Stepped.lintegral_run_stopped_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lintegral_run_stopped_le
/--
info: 'Gimle.Forseti.Stepped.meas_breachSet_le_div'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms meas_breachSet_le_div
/--
info: 'Gimle.Forseti.Stepped.breachWithin_of_drift'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breachWithin_of_drift
/--
info: 'Gimle.Forseti.Stepped.TwoMomentLaw.nonneg'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TwoMomentLaw.nonneg
/--
info: 'Gimle.Forseti.Stepped.gaussian_twoMoment'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms gaussian_twoMoment
/--
info: 'Gimle.Forseti.Stepped.gaussian_subGaussian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms gaussian_subGaussian
/--
info: 'Gimle.Forseti.Stepped.two_sided_tail'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms two_sided_tail
/--
info: 'Gimle.Forseti.Stepped.coe_sqNN'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms coe_sqNN
/--
info: 'Gimle.Forseti.Stepped.coord_hasSubgaussianMGF'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms coord_hasSubgaussianMGF
/--
info: 'Gimle.Forseti.Stepped.weighted_sum_hasSubgaussianMGF'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms weighted_sum_hasSubgaussianMGF
/--
info: 'Gimle.Forseti.Stepped.exceedsAt_of_weighted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exceedsAt_of_weighted
/--
info: 'Gimle.Forseti.Stepped.exp_ge_floor_cubic'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exp_ge_floor_cubic
/--
info: 'Gimle.Forseti.Stepped.isProbabilityMeasure_threePoint'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms isProbabilityMeasure_threePoint
/--
info: 'Gimle.Forseti.Stepped.integral_threePoint'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms integral_threePoint
/--
info: 'Gimle.Forseti.Stepped.threePoint_twoMoment'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms threePoint_twoMoment
/--
info: 'Gimle.Forseti.Stepped.breach_ge_threePoint'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breach_ge_threePoint
/--
info: 'Gimle.Forseti.Stepped.not_breachWithin_threePoint_exact'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms not_breachWithin_threePoint_exact
/--
info: 'Gimle.Forseti.Stepped.one_sub_pow_ge_bernoulli'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms one_sub_pow_ge_bernoulli
/--
info: 'Gimle.Forseti.Stepped.not_breachWithin_threePoint'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms not_breachWithin_threePoint

end Gimle.Forseti.Tests.Stepped
