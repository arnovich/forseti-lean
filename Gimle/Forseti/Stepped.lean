import Gimle.Forseti.Discrete
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian

/-! A discrete-time probability semantics: a law on the inputs of a deterministic
iteration.

A step map `f : S → D → S` advances a state under one input. `run f x₀ ω` iterates it
along an input path `ω : ℕ → D` from `x₀`; its value at mark `n` is the state after the
first `n` inputs, and the marks `0, 1, 2, …` are the only times the semantics knows. It
is the recurrence of `Gimle.Forseti.Discrete.run` for an abstract step map
(`run_discrete`). All randomness lives in the inputs: `pathMeasure law` is the product
measure on input paths whose coordinates are independent and each distributed as `law`
(Mathlib's `Measure.infinitePi`), so the state at each mark is a random variable.

The claim forms. `BreachWithin f x₀ law N safe q`: the probability that some mark
`n ≤ N` is not `safe` is at most `q`. `ExceedsAt f x₀ law n safe q`: the same at the
one mark `n`; `AtEveryMark` asks it at each mark `n ≤ N` separately, which does not
bound the probability of a breach at some mark. `ExpectedLe f x₀ law V n c`: the
expectation of `max V 0` at mark `n` is at most `c`, a lower integral into `ℝ≥0∞` that
needs no integrability hypothesis. The two probability forms compare a probability with
`ENNReal.ofReal q`; `ExpectedLe` compares the lower integral with `ENNReal.ofReal c`.
The claim forms carry `IsProbabilityMeasure law` and a nonnegative threshold (`0 ≤ q`,
`0 ≤ c`) so that a non-probability "law" or a negative threshold cannot make a claim hold
for nothing; for a probability law any `q ≥ 1` makes the two probability forms hold
trivially (`breachWithin_of_le_one`, `exceedsAt_of_le_one`). Each form is monotone in its
threshold (`BreachWithin.mono` and its siblings).

* The one-shock split (`lintegral_run_succ`): the expectation of a measurable `V ≥ 0` at
  mark `n + 1` is the expectation, over the path to mark `n`, of the one-step expectation
  of `V` under `law`, because input `n` is independent of the first `n` inputs.
* The drift recursion (`lintegral_run_le_geom`, `lintegral_run_eq_geom`): if one step
  satisfies `E V(f x d) ≤ ρ V(x) + β`, the expectation at mark `n` is at most
  `ρⁿ V(x₀) + β ∑_{k<n} ρᵏ`, with equality when the one-step drift is an equality.
* The horizon breach bound (`meas_breachSet_le_div`, `breachWithin_of_drift`): if
  `E V(f x d) ≤ V(x) + β` at every state with `V(x) < c` and every unsafe state has
  `V ≥ c`, the probability of leaving the safe set at some mark `n ≤ N` is at most
  `(V(x₀) + N β) / c`. The chain stopped at level `c` (`stopped`) has the same drift, and
  the free chain reaches `c` by mark `N` exactly when the stopped chain is at `c` at mark
  `N`, so Markov's inequality at the single mark `N` bounds the whole horizon.
* The law classes. `TwoMomentLaw law v`: a centred probability law with second moment
  `v`. `SubGaussianLaw law v`: a probability law whose moment generating function is at
  most `exp(v t²/2)` (Mathlib's `HasSubgaussianMGF`). The centred Gaussian is in both
  (`gaussian_twoMoment`, `gaussian_subGaussian`). They are kept apart because a variance
  does not control the tail: a horizon bound from the variance alone holds for the
  three-point law below as well, so it cannot go below the breach probability that law
  reaches.
* The fixed-date bound (`weighted_sum_hasSubgaussianMGF`, `two_sided_tail`,
  `exceedsAt_of_weighted`): under a sub-Gaussian law a weighted sum `X = ∑_{k<n} wₖ ωₖ`
  of the inputs is sub-Gaussian with proxy `c = ∑ wₖ² v`, so `P(|X| > B)` is at most
  `2 exp(−B²/(2c))`. The module uses the sub-Gaussian hypothesis only at a single mark,
  in `exceedsAt_of_weighted`, and proves no horizon bound under it.
* A numeric lower bound on the exponential (`exp_ge_floor_cubic`), so that `norm_num`
  can check a bound such as `2 exp(−B²/(2c)) ≤ q` at rational `B`, `c` and `q`.
* The refutation device. `threePoint ε L` puts mass `1 − 2ε` at `0` and `ε` at each of
  `±L`: a bounded law whose variance `2εL²` sits in rare one-step jumps
  (`threePoint_twoMoment`). If the input `0` fixes the start and both jumps leave the
  safe set, the chain breaches by mark `N` with probability at least `1 − (1 − 2ε)ᴺ`
  (`breach_ge_threePoint`), so no smaller `BreachWithin` bound holds
  (`not_breachWithin_threePoint_exact`); Bernoulli's inequality gives the simpler
  threshold `2εN / (1 + 2εN)` (`not_breachWithin_threePoint`).

What is not claimed. Nothing here is about continuous time, a stochastic differential
equation or a discretisation: a continuous model enters only through a step map given
explicitly. The law is a hypothesis of each claim, never fitted to data. No horizon
bound is proved under the sub-Gaussian hypothesis, and no probability is computed for a
particular law beyond the three-point lower bound.
-/

open MeasureTheory ProbabilityTheory ENNReal Finset Function
open scoped NNReal

namespace Gimle.Forseti.Stepped

variable {S D : Type*}

/-! ### The iteration -/

/-- Iteration of the step map `f` from `x₀` along the input path `ω`; mark `n + 1` is
`f` applied to mark `n` and input `n`. -/
def run (f : S → D → S) (x₀ : S) (ω : ℕ → D) : ℕ → S
  | 0 => x₀
  | n + 1 => f (run f x₀ ω n) (ω n)

@[simp] theorem run_zero (f : S → D → S) (x₀ : S) (ω : ℕ → D) : run f x₀ ω 0 = x₀ := rfl

@[simp] theorem run_succ (f : S → D → S) (x₀ : S) (ω : ℕ → D) (n : ℕ) :
    run f x₀ ω (n + 1) = f (run f x₀ ω n) (ω n) := rfl

/-- The state at mark `n` depends only on the first `n` inputs. -/
theorem run_congr (f : S → D → S) (x₀ : S) {ω ω' : ℕ → D} :
    ∀ n, (∀ i < n, ω i = ω' i) → run f x₀ ω n = run f x₀ ω' n
  | 0, _ => rfl
  | n + 1, h => by
    rw [run_succ, run_succ, run_congr f x₀ n (fun i hi => h i (Nat.lt_succ_of_lt hi)),
      h n (Nat.lt_succ_self n)]

open Gimle.Asgard in
/-- On a circuit step, the iteration is `Discrete.run`: the two recurrences agree. -/
theorem run_discrete {s u m : ℕ} (update : Circuit (s + (u + m)) s) (p : Point m)
    (x₀ : Point s) (input : ℕ → Point u) (n : ℕ) :
    Discrete.run update p x₀ input n = run (Discrete.step update p) x₀ input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ← ih]
    rfl

/-! ### The path measure and the claim forms -/

section Path

variable [MeasurableSpace D]

/-- A measurable function of the path that reads only the coordinates in `s` is
measurable for the σ-algebra generated by those coordinates, `Filtration.piFinset s`.
It is the measurability hypothesis of the finite-coordinate Fubini theorem
`lintegral_infinitePi_of_piFinset`. -/
theorem measurable_piFinset_of_dependsOn [Nonempty D] {E : Type*} [MeasurableSpace E]
    {s : Finset ℕ} {Φ : (ℕ → D) → E} (hΦ : Measurable Φ)
    (hd : ∀ ω ω' : ℕ → D, (∀ i ∈ s, ω i = ω' i) → Φ ω = Φ ω') :
    Measurable[Filtration.piFinset s] Φ := by
  classical
  obtain ⟨x⟩ : Nonempty (ℕ → D) := inferInstance
  have hfac : Φ = (fun y : (↥s → D) => Φ (updateFinset x s y)) ∘ s.restrict := by
    funext ω
    apply hd
    intro i hi
    simp [updateFinset, hi]
  rw [hfac, Filtration.piFinset_eq_comap_restrict]
  exact (hΦ.comp measurable_updateFinset).comp (comap_measurable _)

/-- The law of the input path: independent inputs, each distributed as `law`. -/
noncomputable def pathMeasure (law : Measure D) : Measure (ℕ → D) :=
  Measure.infinitePi (fun _ : ℕ => law)

/-- The path measure of a probability law is a probability measure. -/
instance isProbabilityMeasure_pathMeasure (law : Measure D) [IsProbabilityMeasure law] :
    IsProbabilityMeasure (pathMeasure law) := by
  unfold pathMeasure
  infer_instance

/-- For a probability law and a threshold `0 ≤ q`, the probability that the iteration
leaves `safe` at some mark `n ≤ N` is at most `q`. -/
def BreachWithin (f : S → D → S) (x₀ : S) (law : Measure D) (N : ℕ) (safe : S → Prop)
    (q : ℝ) : Prop :=
  IsProbabilityMeasure law ∧ 0 ≤ q ∧
    pathMeasure law {ω | ∃ n ≤ N, ¬ safe (run f x₀ ω n)} ≤ ENNReal.ofReal q

/-- For a probability law and a threshold `0 ≤ q`, the probability that the iteration is
not `safe` at mark `n` is at most `q`. -/
def ExceedsAt (f : S → D → S) (x₀ : S) (law : Measure D) (n : ℕ) (safe : S → Prop)
    (q : ℝ) : Prop :=
  IsProbabilityMeasure law ∧ 0 ≤ q ∧
    pathMeasure law {ω | ¬ safe (run f x₀ ω n)} ≤ ENNReal.ofReal q

/-- `ExceedsAt` at each mark `n ≤ N` separately. It bounds the probability of being
unsafe at any one mark, not the probability of being unsafe at some mark. -/
def AtEveryMark (f : S → D → S) (x₀ : S) (law : Measure D) (N : ℕ) (safe : S → Prop)
    (q : ℝ) : Prop :=
  ∀ n ≤ N, ExceedsAt f x₀ law n safe q

/-- For a probability law and a threshold `0 ≤ c`, the expectation at mark `n` of
`ENNReal.ofReal ∘ V` is at most `c`. It bounds the expectation of `max V 0`, which is
that of `V` when `V ≥ 0`. -/
def ExpectedLe (f : S → D → S) (x₀ : S) (law : Measure D) (V : S → ℝ) (n : ℕ) (c : ℝ) :
    Prop :=
  IsProbabilityMeasure law ∧ 0 ≤ c ∧
    ∫⁻ ω, ENNReal.ofReal (V (run f x₀ ω n)) ∂pathMeasure law ≤ ENNReal.ofReal c

variable {f : S → D → S} {x₀ : S} {law : Measure D} {safe : S → Prop}

/-- A breach bound holds for every larger threshold. -/
theorem BreachWithin.mono {N : ℕ} {q q' : ℝ} (hq : q ≤ q')
    (h : BreachWithin f x₀ law N safe q) : BreachWithin f x₀ law N safe q' :=
  ⟨h.1, h.2.1.trans hq, h.2.2.trans (ENNReal.ofReal_le_ofReal hq)⟩

/-- A bound at one mark holds for every larger threshold. -/
theorem ExceedsAt.mono {n : ℕ} {q q' : ℝ} (hq : q ≤ q')
    (h : ExceedsAt f x₀ law n safe q) : ExceedsAt f x₀ law n safe q' :=
  ⟨h.1, h.2.1.trans hq, h.2.2.trans (ENNReal.ofReal_le_ofReal hq)⟩

/-- A bound at each mark holds for every larger threshold. -/
theorem AtEveryMark.mono {N : ℕ} {q q' : ℝ} (hq : q ≤ q')
    (h : AtEveryMark f x₀ law N safe q) : AtEveryMark f x₀ law N safe q' :=
  fun n hn => (h n hn).mono hq

/-- An expectation bound holds for every larger threshold. -/
theorem ExpectedLe.mono {V : S → ℝ} {n : ℕ} {c c' : ℝ} (hc : c ≤ c')
    (h : ExpectedLe f x₀ law V n c) : ExpectedLe f x₀ law V n c' :=
  ⟨h.1, h.2.1.trans hc, h.2.2.trans (ENNReal.ofReal_le_ofReal hc)⟩

/-- For a probability law, a bound of at least `1` on the breach probability always
holds. -/
theorem breachWithin_of_le_one [IsProbabilityMeasure law] {N : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    BreachWithin f x₀ law N safe q :=
  ⟨inferInstance, zero_le_one.trans hq, prob_le_one.trans (ENNReal.one_le_ofReal.2 hq)⟩

/-- For a probability law, a bound of at least `1` on the probability of being unsafe
at one mark always holds. -/
theorem exceedsAt_of_le_one [IsProbabilityMeasure law] {n : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    ExceedsAt f x₀ law n safe q :=
  ⟨inferInstance, zero_le_one.trans hq, prob_le_one.trans (ENNReal.one_le_ofReal.2 hq)⟩

end Path

/-! ### The one-shock split and the drift recursion -/

section Drift

variable [MeasurableSpace S] [MeasurableSpace D]

/-- For a jointly measurable step map, the state at each mark is a measurable function
of the input path. -/
theorem measurable_run {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2))
    (x₀ : S) : ∀ n, Measurable (fun ω : ℕ → D => run f x₀ ω n)
  | 0 => measurable_const
  | n + 1 => by
    simp only [run_succ]
    exact hf.comp ((measurable_run hf x₀ n).prodMk (measurable_pi_apply n))

/-- The one-shock split: integrating a function of the state at mark `n + 1` over the
input path equals integrating, over the path to mark `n`, its expectation under a
fresh input. -/
theorem lintegral_run_succ (law : Measure D) [IsProbabilityMeasure law]
    {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2)) (x₀ : S)
    {V : S → ℝ≥0∞} (hV : Measurable V) (n : ℕ) :
    ∫⁻ ω, V (run f x₀ ω (n + 1)) ∂pathMeasure law
      = ∫⁻ ω, (∫⁻ d, V (f (run f x₀ ω n) d) ∂law) ∂pathMeasure law := by
  classical
  haveI : Nonempty D := nonempty_of_isProbabilityMeasure law
  obtain ⟨x⟩ : Nonempty (ℕ → D) := inferInstance
  have hF : Measurable (fun ω : ℕ → D => V (run f x₀ ω (n + 1))) :=
    hV.comp (measurable_run hf x₀ (n + 1))
  have hG : Measurable (fun ω : ℕ → D => ∫⁻ d, V (f (run f x₀ ω n) d) ∂law) := by
    apply Measurable.lintegral_prod_right
    exact hV.comp (hf.comp ((measurable_run hf x₀ n).comp measurable_fst |>.prodMk measurable_snd))
  unfold pathMeasure
  -- left side: integrate out the first `n + 1` coordinates
  rw [lintegral_infinitePi_of_piFinset (fun _ => law) (s := range (n + 1))
    (measurable_piFinset_of_dependsOn hF (fun ω ω' h =>
      congrArg V (run_congr f x₀ (n + 1) (fun i hi => h i (mem_range.2 hi))))) x]
  -- right side: integrate out the first `n` coordinates
  rw [lintegral_infinitePi_of_piFinset (fun _ => law) (s := range n)
    (measurable_piFinset_of_dependsOn hG (fun ω ω' h => by
      rw [run_congr f x₀ n (fun i hi => h i (mem_range.2 hi))])) x]
  rw [range_add_one, lmarginal_insert' _ hF notMem_range_self]
  congr 1
  funext ω
  congr 1
  funext d
  rw [run_succ, update_self,
    run_congr f x₀ n (ω := update ω n d) (ω' := ω) (fun i hi => update_of_ne hi.ne _ _)]

variable (law : Measure D) [IsProbabilityMeasure law]

/-- The drift recursion: if one step satisfies `E V(f x d) ≤ ρ V(x) + β`, then the
expectation of `V` at mark `n` is at most `ρⁿ V(x₀) + β ∑_{k<n} ρᵏ`. -/
theorem lintegral_run_le_geom {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2))
    {V : S → ℝ≥0∞} (hV : Measurable V) {ρ β : ℝ≥0∞}
    (hdrift : ∀ x, ∫⁻ d, V (f x d) ∂law ≤ ρ * V x + β) (x₀ : S) :
    ∀ n : ℕ, ∫⁻ ω, V (run f x₀ ω n) ∂pathMeasure law
      ≤ ρ ^ n * V x₀ + β * ∑ k ∈ range n, ρ ^ k
  | 0 => by
    simp only [run_zero, lintegral_const, measure_univ, mul_one, pow_zero, one_mul,
      range_zero, sum_empty, mul_zero, add_zero, le_refl]
  | n + 1 => by
    have ih := lintegral_run_le_geom hf hV hdrift x₀ n
    have hVn : Measurable (fun ω : ℕ → D => V (run f x₀ ω n)) :=
      hV.comp (measurable_run hf x₀ n)
    rw [lintegral_run_succ law hf x₀ hV n]
    calc ∫⁻ ω, (∫⁻ d, V (f (run f x₀ ω n) d) ∂law) ∂pathMeasure law
        ≤ ∫⁻ ω, (ρ * V (run f x₀ ω n) + β) ∂pathMeasure law :=
          lintegral_mono fun ω => hdrift _
      _ = ρ * ∫⁻ ω, V (run f x₀ ω n) ∂pathMeasure law + β := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVn,
            lintegral_const, measure_univ, mul_one]
      _ ≤ ρ * (ρ ^ n * V x₀ + β * ∑ k ∈ range n, ρ ^ k) + β := by gcongr
      _ = ρ ^ (n + 1) * V x₀ + β * ∑ k ∈ range (n + 1), ρ ^ k := by
          rw [geom_sum_succ]
          ring

/-- The drift recursion with equality: if one step satisfies
`E V(f x d) = ρ V(x) + β`, then the expectation of `V` at mark `n` is exactly
`ρⁿ V(x₀) + β ∑_{k<n} ρᵏ`. -/
theorem lintegral_run_eq_geom {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2))
    {V : S → ℝ≥0∞} (hV : Measurable V) {ρ β : ℝ≥0∞}
    (hdrift : ∀ x, ∫⁻ d, V (f x d) ∂law = ρ * V x + β) (x₀ : S) :
    ∀ n : ℕ, ∫⁻ ω, V (run f x₀ ω n) ∂pathMeasure law
      = ρ ^ n * V x₀ + β * ∑ k ∈ range n, ρ ^ k
  | 0 => by
    simp only [run_zero, lintegral_const, measure_univ, mul_one, pow_zero, one_mul,
      range_zero, sum_empty, mul_zero, add_zero]
  | n + 1 => by
    have ih := lintegral_run_eq_geom hf hV hdrift x₀ n
    have hVn : Measurable (fun ω : ℕ → D => V (run f x₀ ω n)) :=
      hV.comp (measurable_run hf x₀ n)
    rw [lintegral_run_succ law hf x₀ hV n]
    calc ∫⁻ ω, (∫⁻ d, V (f (run f x₀ ω n) d) ∂law) ∂pathMeasure law
        = ∫⁻ ω, (ρ * V (run f x₀ ω n) + β) ∂pathMeasure law :=
          lintegral_congr fun ω => hdrift _
      _ = ρ * ∫⁻ ω, V (run f x₀ ω n) ∂pathMeasure law + β := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVn,
            lintegral_const, measure_univ, mul_one]
      _ = ρ * (ρ ^ n * V x₀ + β * ∑ k ∈ range n, ρ ^ k) + β := by rw [ih]
      _ = ρ ^ (n + 1) * V x₀ + β * ∑ k ∈ range (n + 1), ρ ^ k := by
          rw [geom_sum_succ]
          ring

end Drift

/-! ### The stopped chain and the horizon breach bound -/

section Stopped

/-- The step map `f` stopped at level `c` of `V`: a state with `c ≤ V x` is frozen,
every other state moves by `f`. -/
noncomputable def stopped (f : S → D → S) (V : S → ℝ≥0∞) (c : ℝ≥0∞) (x : S) (d : D) : S :=
  if c ≤ V x then x else f x d

/-- A state at level `c` or above is frozen. -/
theorem stopped_of_le {f : S → D → S} {V : S → ℝ≥0∞} {c : ℝ≥0∞} {x : S} (h : c ≤ V x)
    (d : D) : stopped f V c x d = x :=
  if_pos h

/-- A state below level `c` moves by `f`. -/
theorem stopped_of_not_le {f : S → D → S} {V : S → ℝ≥0∞} {c : ℝ≥0∞} {x : S}
    (h : ¬ c ≤ V x) (d : D) : stopped f V c x d = f x d :=
  if_neg h

/-- Once the stopped chain has reached level `c`, it stays there. -/
theorem le_run_stopped_of_le {f : S → D → S} {V : S → ℝ≥0∞} {c : ℝ≥0∞} {x₀ : S}
    {ω : ℕ → D} {n : ℕ} (h : c ≤ V (run (stopped f V c) x₀ ω n)) :
    ∀ m, n ≤ m → c ≤ V (run (stopped f V c) x₀ ω m) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => rw [run_succ, stopped_of_le ih]; exact ih

/-- Before the free chain first reaches level `c`, the stopped chain agrees with it. -/
theorem run_stopped_eq_run {f : S → D → S} {V : S → ℝ≥0∞} {c : ℝ≥0∞} {x₀ : S}
    {ω : ℕ → D} :
    ∀ n, (∀ k < n, ¬ c ≤ V (run f x₀ ω k)) → run (stopped f V c) x₀ ω n = run f x₀ ω n
  | 0, _ => rfl
  | n + 1, h => by
    rw [run_succ, run_succ, run_stopped_eq_run n (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      stopped_of_not_le (h n (Nat.lt_succ_self n))]

/-- The free chain reaches level `c` at some mark `n ≤ N` exactly when the stopped chain
is at level `c` at mark `N`. -/
theorem exists_le_iff_le_run_stopped {f : S → D → S} {V : S → ℝ≥0∞} {c : ℝ≥0∞}
    {x₀ : S} {ω : ℕ → D} (N : ℕ) :
    (∃ n ≤ N, c ≤ V (run f x₀ ω n)) ↔ c ≤ V (run (stopped f V c) x₀ ω N) := by
  classical
  constructor
  · rintro ⟨n, hn, hhit⟩
    have hex : ∃ k, c ≤ V (run f x₀ ω k) := ⟨n, hhit⟩
    refine le_run_stopped_of_le ?_ N ((Nat.find_min' hex hhit).trans hn)
    rw [run_stopped_eq_run (Nat.find hex) fun k hk => Nat.find_min hex hk]
    exact Nat.find_spec hex
  · intro h
    by_contra hno
    push Not at hno
    rw [run_stopped_eq_run N fun k hk => not_le.2 (hno k hk.le)] at h
    exact absurd h (not_le.2 (hno N le_rfl))

/-- The set of paths along which `V` reaches level `c` at some mark `n ≤ N`. -/
def breachSet (f : S → D → S) (V : S → ℝ≥0∞) (c : ℝ≥0∞) (x₀ : S) (N : ℕ) : Set (ℕ → D) :=
  {ω | ∃ n ≤ N, c ≤ V (run f x₀ ω n)}

/-- The breach event of the free chain is the terminal level-`c` event of the stopped
chain. -/
theorem breachSet_eq (f : S → D → S) (V : S → ℝ≥0∞) (c : ℝ≥0∞) (x₀ : S) (N : ℕ) :
    breachSet f V c x₀ N = {ω | c ≤ V (run (stopped f V c) x₀ ω N)} :=
  Set.ext fun _ => exists_le_iff_le_run_stopped N

end Stopped

section Breach

variable [MeasurableSpace D] (law : Measure D) [IsProbabilityMeasure law]

/-- The stopped step satisfies the additive drift bound of the free step below level
`c`, at every state: in a frozen state the expectation is `V x` itself. -/
theorem lintegral_stopped_le {f : S → D → S} {V : S → ℝ≥0∞} {c β : ℝ≥0∞}
    (hdrift : ∀ x, V x < c → ∫⁻ d, V (f x d) ∂law ≤ V x + β) (x : S) :
    ∫⁻ d, V (stopped f V c x d) ∂law ≤ V x + β := by
  by_cases h : c ≤ V x
  · simp only [stopped_of_le h, lintegral_const, measure_univ, mul_one]
    exact le_self_add
  · simp only [stopped_of_not_le h]
    exact hdrift x (not_le.1 h)

variable [MeasurableSpace S]

/-- The stopped step map is jointly measurable when `f` and `V` are. -/
theorem measurable_stopped {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2))
    {V : S → ℝ≥0∞} (hV : Measurable V) (c : ℝ≥0∞) :
    Measurable (fun p : S × D => stopped f V c p.1 p.2) := by
  unfold stopped
  exact Measurable.ite (measurableSet_le measurable_const (hV.comp measurable_fst))
    measurable_fst hf

/-- The expectation of `V` along the stopped chain grows by at most `β` per mark. -/
theorem lintegral_run_stopped_le {f : S → D → S}
    (hf : Measurable (fun p : S × D => f p.1 p.2)) {V : S → ℝ≥0∞} (hV : Measurable V)
    {c β : ℝ≥0∞} (hdrift : ∀ x, V x < c → ∫⁻ d, V (f x d) ∂law ≤ V x + β) (x₀ : S)
    (n : ℕ) :
    ∫⁻ ω, V (run (stopped f V c) x₀ ω n) ∂pathMeasure law ≤ V x₀ + n * β := by
  refine (lintegral_run_le_geom law (measurable_stopped hf hV c) hV (ρ := 1)
    (fun x => by simpa only [one_mul] using lintegral_stopped_le law hdrift x) x₀ n).trans ?_
  simp [mul_comm]

/-- The horizon breach bound: if `E V(f x d) ≤ V(x) + β` at every state below the level
`c`, the probability that `V` reaches `c` at some mark `n ≤ N` is at most
`(V(x₀) + N β) / c`. -/
theorem meas_breachSet_le_div {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2))
    {V : S → ℝ≥0∞} (hV : Measurable V) {c β : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞)
    (hdrift : ∀ x, V x < c → ∫⁻ d, V (f x d) ∂law ≤ V x + β) (x₀ : S) (N : ℕ) :
    pathMeasure law (breachSet f V c x₀ N) ≤ (V x₀ + N * β) / c := by
  rw [breachSet_eq]
  exact (meas_ge_le_lintegral_div
    (hV.comp (measurable_run (measurable_stopped hf hV c) x₀ N)).aemeasurable hc hc').trans
    (ENNReal.div_le_div_right (lintegral_run_stopped_le law hf hV hdrift x₀ N) c)

/-- The horizon breach bound as a claim: if every unsafe state has `V ≥ c`, `V` has
additive drift `β` below `c`, and `(V(x₀) + N β) / c ≤ ENNReal.ofReal q` with `0 ≤ q`,
then `BreachWithin f x₀ law N safe q` holds. -/
theorem breachWithin_of_drift {f : S → D → S} (hf : Measurable (fun p : S × D => f p.1 p.2))
    {V : S → ℝ≥0∞} (hV : Measurable V) {c β : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ∞)
    (hdrift : ∀ x, V x < c → ∫⁻ d, V (f x d) ∂law ≤ V x + β) {x₀ : S} {N : ℕ}
    {safe : S → Prop} {q : ℝ} (hsafe : ∀ x, ¬ safe x → c ≤ V x) (hq0 : 0 ≤ q)
    (hq : (V x₀ + N * β) / c ≤ ENNReal.ofReal q) : BreachWithin f x₀ law N safe q := by
  refine ⟨inferInstance, hq0, le_trans (measure_mono ?_)
    ((meas_breachSet_le_div law hf hV hc hc' hdrift x₀ N).trans hq)⟩
  rintro ω ⟨n, hn, hn'⟩
  exact ⟨n, hn, hsafe _ hn'⟩

end Breach

/-! ### The law classes -/

section Laws

/-- A centred law with finite second moment: a probability measure on `ℝ` whose
identity coordinate and its square are integrable, with mean zero and second moment
`v`. -/
structure TwoMomentLaw (law : Measure ℝ) (v : ℝ) : Prop where
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law
  /-- The identity coordinate is integrable. -/
  integrable_id : Integrable (fun d : ℝ => d) law
  /-- Its square is integrable. -/
  integrable_sq : Integrable (fun d : ℝ => d ^ 2) law
  /-- The mean is zero. -/
  mean : ∫ d, d ∂law = 0
  /-- The second moment is `v`. -/
  second : ∫ d, d ^ 2 ∂law = v

/-- The second moment of a two-moment law is nonnegative. -/
theorem TwoMomentLaw.nonneg {law : Measure ℝ} {v : ℝ} (h : TwoMomentLaw law v) : 0 ≤ v :=
  h.second ▸ integral_nonneg fun d => sq_nonneg d

/-- A sub-Gaussian law: a probability measure on `ℝ` whose identity coordinate is
sub-Gaussian with variance proxy `v`, that is, whose moment generating function is
at most `exp(v t² / 2)`, that of the centred Gaussian of variance `v`. -/
structure SubGaussianLaw (law : Measure ℝ) (v : ℝ≥0) : Prop where
  /-- The law is a probability measure. -/
  prob : IsProbabilityMeasure law
  /-- The identity coordinate is sub-Gaussian with proxy `v`. -/
  subgaussian : HasSubgaussianMGF (fun d : ℝ => d) v law

/-- The centred Gaussian of variance `v` has mean zero and second moment `v`. -/
theorem gaussian_twoMoment (v : ℝ≥0) : TwoMomentLaw (gaussianReal 0 v) v where
  prob := inferInstance
  integrable_id := (memLp_id_gaussianReal' (μ := 0) (v := v) 1 ENNReal.one_ne_top).integrable
    le_rfl
  integrable_sq := (memLp_two_iff_integrable_sq
    (memLp_id_gaussianReal' (μ := 0) (v := v) 2 ENNReal.ofNat_ne_top).aestronglyMeasurable).1
    (memLp_id_gaussianReal' (μ := 0) (v := v) 2 ENNReal.ofNat_ne_top)
  mean := integral_id_gaussianReal
  second := by
    have h := variance_eq_sub (μ := gaussianReal 0 v) (X := id)
      (memLp_id_gaussianReal' (μ := 0) (v := v) 2 ENNReal.ofNat_ne_top)
    rw [variance_id_gaussianReal] at h
    have hmean : (gaussianReal 0 v)[id] = 0 := integral_id_gaussianReal
    rw [hmean] at h
    simpa using h.symm

/-- The centred Gaussian of variance `v` is sub-Gaussian with proxy `v`: its moment
generating function is `exp(v t² / 2)`. -/
theorem gaussian_subGaussian (v : ℝ≥0) : SubGaussianLaw (gaussianReal 0 v) v where
  prob := inferInstance
  subgaussian :=
    { integrable_exp_mul := fun t => integrable_exp_mul_gaussianReal t
      mgf_le := fun t => by
        rw [mgf_fun_id_gaussianReal]
        simp }

end Laws

/-! ### The fixed-date bound -/

section SubGaussian

/-- A sub-Gaussian variable leaves the band `|X| ≤ ε` with probability at most
`2 exp(-ε² / (2c))`: the two one-sided Chernoff bounds and a union bound. -/
theorem two_sided_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε < |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have h1 : μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * c)) := h.measure_ge_le hε
  have h2 : μ.real {ω | ε ≤ (-X) ω} ≤ Real.exp (-ε ^ 2 / (2 * c)) := h.neg.measure_ge_le hε
  have hsub : {ω | ε < |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply] at hω ⊢
    rcases le_or_gt 0 (X ω) with hx | hx
    · left
      rw [abs_of_nonneg hx] at hω
      exact hω.le
    · right
      rw [abs_of_neg hx] at hω
      exact hω.le
  have hfinite : IsFiniteMeasure μ := by
    have h0 := h.integrable_exp_mul 0
    simp only [zero_mul, Real.exp_zero] at h0
    exact (integrable_const_iff.mp h0).resolve_left one_ne_zero
  have hfin : μ ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) ≠ ⊤ := measure_ne_top _ _
  calc μ.real {ω | ε < |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) := measureReal_mono hsub hfin
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) := add_le_add h1 h2
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

/-- `r ^ 2` as a nonnegative real: the variance proxy that scaling a sub-Gaussian
variable by `r` produces. -/
def sqNN (r : ℝ) : ℝ≥0 := ⟨r ^ 2, sq_nonneg r⟩

@[simp] theorem coe_sqNN (r : ℝ) : ((sqNN r : ℝ≥0) : ℝ) = r ^ 2 := rfl

variable {law : Measure ℝ} {v : ℝ≥0}

/-- Each coordinate of the path measure of a sub-Gaussian law is sub-Gaussian with the
proxy of the law. -/
theorem coord_hasSubgaussianMGF (h : SubGaussianLaw law v) (i : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ω i) v (pathMeasure law) := by
  haveI := h.prob
  have hmeas : Measurable (fun ω : ℕ → ℝ => ω i) := measurable_pi_apply i
  have hlaw := h.subgaussian
  unfold pathMeasure
  rw [← Measure.infinitePi_map_eval (fun _ : ℕ => law) i] at hlaw
  exact (HasSubgaussianMGF.of_map hmeas.aemeasurable hlaw :
    HasSubgaussianMGF ((fun x : ℝ => x) ∘ (fun ω : ℕ → ℝ => ω i)) v _)

/-- A weighted sum of the first `n` inputs is sub-Gaussian under the path measure of a
sub-Gaussian law, with proxy `∑ wₖ² v`: the inputs are independent, so the proxies add
(`HasSubgaussianMGF.sum_of_iIndepFun`), and scaling by `wₖ` multiplies the proxy
by `wₖ²`. -/
theorem weighted_sum_hasSubgaussianMGF (h : SubGaussianLaw law v) (w : ℕ → ℝ) (n : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℝ => ∑ k ∈ Finset.range n, w k * ω k)
      (∑ k ∈ Finset.range n, sqNN (w k) * v) (pathMeasure law) := by
  haveI := h.prob
  have hind : iIndepFun (fun k (ω : ℕ → ℝ) => w k * ω k) (pathMeasure law) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => law) (X := fun k (x : ℝ) => w k * x)
      (fun k => by fun_prop)
  exact HasSubgaussianMGF.sum_of_iIndepFun hind
    (fun k _ => (coord_hasSubgaussianMGF h k).const_mul (w k))

/-- The fixed-date bound. If the observable at mark `n` is the weighted sum
`∑_{k<n} wₖ ωₖ` of the first `n` inputs, every unsafe state has `|obs| > B`, and
`2 exp(-B² / (2 ∑ wₖ² v)) ≤ q`, then the probability of being unsafe at mark `n` is at
most `q`. -/
theorem exceedsAt_of_weighted (h : SubGaussianLaw law v) {f : S → ℝ → S} {x₀ : S}
    {n : ℕ} {safe : S → Prop} {q : ℝ} {w : ℕ → ℝ} {obs : S → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hrun : ∀ ω, obs (run f x₀ ω n) = ∑ k ∈ Finset.range n, w k * ω k)
    (hsafe : ∀ x, ¬ safe x → B < |obs x|)
    (hq : 2 * Real.exp (-B ^ 2 / (2 * ∑ k ∈ Finset.range n, (w k) ^ 2 * (v : ℝ))) ≤ q) :
    ExceedsAt f x₀ law n safe q := by
  haveI := h.prob
  have htail := two_sided_tail (weighted_sum_hasSubgaussianMGF h w n) hB
  have hcoe : ((∑ k ∈ Finset.range n, sqNN (w k) * v : ℝ≥0) : ℝ)
      = ∑ k ∈ Finset.range n, (w k) ^ 2 * (v : ℝ) := by
    simp [NNReal.coe_sum]
  rw [hcoe] at htail
  refine ⟨inferInstance, (by positivity : (0 : ℝ) ≤ 2 * Real.exp _).trans hq, ?_⟩
  calc pathMeasure law {ω | ¬ safe (run f x₀ ω n)}
      ≤ pathMeasure law {ω | B < |∑ k ∈ Finset.range n, w k * ω k|} :=
        measure_mono fun ω hω => by
          simp only [Set.mem_setOf_eq] at hω ⊢
          rw [← hrun ω]
          exact hsafe _ hω
    _ = ENNReal.ofReal ((pathMeasure law).real
          {ω | B < |∑ k ∈ Finset.range n, w k * ω k|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal (htail.trans hq)

end SubGaussian

/-! ### A numeric lower bound on the exponential -/

section ExpBound

/-- A lower bound on `Real.exp` at a real `r ≥ n`: the integer part contributes
`eⁿ ≥ 2.7182818283ⁿ`, and the remainder `s = r - n ≥ 0` the cubic Taylor polynomial
`1 + s + s²/2 + s³/6`. At a rational `r` the left side is a rational number, so
`norm_num` turns a lower bound on `eʳ` into a numeric inequality. -/
theorem exp_ge_floor_cubic (n : ℕ) {r : ℝ} (h : (n : ℝ) ≤ r) :
    (2.7182818283 : ℝ) ^ n * (1 + (r - n) + (r - n) ^ 2 / 2 + (r - n) ^ 3 / 6)
      ≤ Real.exp r := by
  have hs : 0 ≤ r - n := sub_nonneg.2 h
  have hsplit : Real.exp r = Real.exp n * Real.exp (r - n) := by
    rw [← Real.exp_add]
    ring_nf
  have h1 : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
    have hn : Real.exp n = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul]
      simp
    rw [hn]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n
  have h2 : 1 + (r - n) + (r - n) ^ 2 / 2 + (r - n) ^ 3 / 6 ≤ Real.exp (r - n) := by
    have := Real.sum_le_exp_of_nonneg hs 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  rw [hsplit]
  exact mul_le_mul h1 h2 (by positivity) (Real.exp_nonneg _)

end ExpBound

/-! ### The three-point law and the refutation device -/

section ThreePoint

/-- The three-point law: the input is `0` with probability `1 - 2ε` and `L`, `-L` with
probability `ε` each. -/
noncomputable def threePoint (ε L : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - 2 * ε) • Measure.dirac 0 + ENNReal.ofReal ε • Measure.dirac L
    + ENNReal.ofReal ε • Measure.dirac (-L)

/-- The three weights of the three-point law sum to one. -/
private theorem threePoint_weights {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    ENNReal.ofReal (1 - 2 * ε) + ENNReal.ofReal ε + ENNReal.ofReal ε = 1 := by
  rw [← ENNReal.ofReal_add (by linarith) hε, ← ENNReal.ofReal_add (by linarith) hε,
    show 1 - 2 * ε + ε + ε = 1 by ring, ENNReal.ofReal_one]

/-- The three-point law is a probability measure. -/
theorem isProbabilityMeasure_threePoint {ε L : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    IsProbabilityMeasure (threePoint ε L) :=
  ⟨by
    simp only [threePoint, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    exact threePoint_weights hε hε'⟩

/-- Every real function is integrable under the three-point law. -/
private theorem integrable_threePoint (ε L : ℝ) (g : ℝ → ℝ) : Integrable g (threePoint ε L) :=
  (((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)).add_measure
    ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)

/-- The expectation under the three-point law is the weighted sum of the three values. -/
theorem integral_threePoint {ε L : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (g : ℝ → ℝ) :
    ∫ d, g d ∂threePoint ε L = (1 - 2 * ε) * g 0 + ε * g L + ε * g (-L) := by
  have hd : ∀ a : ℝ, Integrable g (Measure.dirac a) := fun _ => integrable_dirac enorm_lt_top
  unfold threePoint
  rw [integral_add_measure (((hd 0).smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hd L).smul_measure ENNReal.ofReal_ne_top)) ((hd (-L)).smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure ((hd 0).smul_measure ENNReal.ofReal_ne_top)
      ((hd L).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hε,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - 2 * ε by linarith), smul_eq_mul]

/-- The three-point law is centred with second moment `2 ε L²`: a two-moment law. -/
theorem threePoint_twoMoment {ε L : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) :
    TwoMomentLaw (threePoint ε L) (2 * ε * L ^ 2) where
  prob := isProbabilityMeasure_threePoint hε hε'
  integrable_id := integrable_threePoint ε L _
  integrable_sq := integrable_threePoint ε L _
  mean := by
    rw [integral_threePoint hε hε']
    ring
  second := by
    rw [integral_threePoint hε hε' (fun d => d ^ 2)]
    ring

variable {f : S → ℝ → S} {x₀ : S} {safe : S → Prop}

/-- If the input `0` fixes `x₀`, the chain stays at `x₀` while the inputs are `0`. -/
private theorem run_eq_of_forall_zero (h0 : f x₀ 0 = x₀) {ω : ℕ → ℝ} (n : ℕ)
    (h : ∀ j < n, ω j = 0) : run f x₀ ω n = x₀ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n), h0]

/-- The breach probability under the three-point law. If the input `0` fixes `x₀` and
both jumps `±L` from `x₀` leave the safe set, the chain breaches at its first nonzero
input, so it breaches by mark `N` with probability at least `1 - (1 - 2ε)ᴺ`: the
probability that some of the first `N` inputs is nonzero. At `N = 0` the bound is
`0`. -/
theorem breach_ge_threePoint {ε L : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (h0 : f x₀ 0 = x₀)
    (hL : ¬ safe (f x₀ L)) (hL' : ¬ safe (f x₀ (-L))) {N : ℕ} :
    ENNReal.ofReal (1 - (1 - 2 * ε) ^ N)
      ≤ pathMeasure (threePoint ε L) {ω | ∃ n ≤ N, ¬ safe (run f x₀ ω n)} := by
  classical
  haveI := isProbabilityMeasure_threePoint (L := L) hε hε'
  have h2ε : 0 ≤ 1 - 2 * ε := by linarith
  by_cases hx₀ : safe x₀
  swap
  · -- an unsafe start breaches at mark `0` on every path
    have hall : {ω : ℕ → ℝ | ∃ n ≤ N, ¬ safe (run f x₀ ω n)} = Set.univ :=
      Set.eq_univ_of_forall fun ω => ⟨0, Nat.zero_le N, hx₀⟩
    rw [hall, measure_univ]
    exact ENNReal.ofReal_le_one.2 (sub_le_self _ (pow_nonneg h2ε N))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact hL (h0.symm ▸ hx₀)
  -- `A`: the first `N` inputs are `0`; `T`: the first `N` inputs lie in the support
  set A : Set (ℕ → ℝ) := Set.pi (range N : Set ℕ) (fun _ => {0}) with hA
  set T : Set (ℕ → ℝ) := Set.pi (range N : Set ℕ) (fun _ => {0, L, -L}) with hT
  have hsupp : MeasurableSet ({0, L, -L} : Set ℝ) := (Set.toFinite _).measurableSet
  have hAm : MeasurableSet A :=
    MeasurableSet.pi (range N).countable_toSet fun _ _ => measurableSet_singleton 0
  have hTm : MeasurableSet T := MeasurableSet.pi (range N).countable_toSet fun _ _ => hsupp
  have hμA : pathMeasure (threePoint ε L) A = ENNReal.ofReal ((1 - 2 * ε) ^ N) := by
    have h1 : threePoint ε L {0} = ENNReal.ofReal (1 - 2 * ε) := by
      simp [threePoint, hL0]
    rw [hA, pathMeasure,
      Measure.infinitePi_pi (fun _ => threePoint ε L) fun _ _ => measurableSet_singleton 0]
    simp only [h1, prod_const, card_range, ENNReal.ofReal_pow h2ε]
  have hμT : pathMeasure (threePoint ε L) Tᶜ = 0 := by
    have h1 : threePoint ε L {0, L, -L} = 1 := by
      simp only [threePoint, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem (show (0 : ℝ) ∈ ({0, L, -L} : Set ℝ) by simp),
        Measure.dirac_apply_of_mem (show L ∈ ({0, L, -L} : Set ℝ) by simp),
        Measure.dirac_apply_of_mem (show -L ∈ ({0, L, -L} : Set ℝ) by simp), mul_one]
      exact threePoint_weights hε hε'
    rw [prob_compl_eq_zero_iff hTm, hT, pathMeasure,
      Measure.infinitePi_pi (fun _ => threePoint ε L) fun _ _ => hsupp]
    simp only [h1, prod_const_one]
  -- off `A` and on `T`, the first nonzero input is a jump `±L` before mark `N`
  have hsub : Aᶜ \ Tᶜ ⊆ {ω | ∃ n ≤ N, ¬ safe (run f x₀ ω n)} := by
    rintro ω ⟨hωA, hωT⟩
    rw [Set.notMem_compl_iff] at hωT
    have hex : ∃ k, k < N ∧ ω k ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hωA fun k hk => hno k (mem_range.1 hk)
    have hk : Nat.find hex < N ∧ ω (Nat.find hex) ≠ 0 := Nat.find_spec hex
    have hbefore : ∀ j < Nat.find hex, ω j = 0 := fun j hj => by
      have hj' := Nat.find_min hex hj
      push Not at hj'
      exact hj' (hj.trans hk.1)
    refine ⟨Nat.find hex + 1, hk.1, ?_⟩
    rw [run_succ, run_eq_of_forall_zero h0 _ hbefore]
    have hmem : ω (Nat.find hex) ∈ ({0, L, -L} : Set ℝ) := hωT _ (mem_range.2 hk.1)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact absurd h hk.2
    · rwa [h]
    · rwa [h]
  calc ENNReal.ofReal (1 - (1 - 2 * ε) ^ N)
      = 1 - pathMeasure (threePoint ε L) A := by
        rw [ENNReal.ofReal_sub _ (pow_nonneg h2ε N), ENNReal.ofReal_one, hμA]
    _ = pathMeasure (threePoint ε L) Aᶜ := (prob_compl_eq_one_sub hAm).symm
    _ = pathMeasure (threePoint ε L) (Aᶜ \ Tᶜ) := (measure_sdiff_null hμT).symm
    _ ≤ _ := measure_mono hsub

/-- The refutation device, at the exact threshold. Under the hypotheses of
`breach_ge_threePoint`, no bound `q < 1 - (1 - 2ε)ᴺ` on the breach probability by mark
`N` holds for the three-point law, although that law has the mean and second moment of
any centred law of variance `2εL²`. -/
theorem not_breachWithin_threePoint_exact {ε L : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2)
    (h0 : f x₀ 0 = x₀) (hL : ¬ safe (f x₀ L)) (hL' : ¬ safe (f x₀ (-L))) {N : ℕ}
    {q : ℝ} (hq : q < 1 - (1 - 2 * ε) ^ N) :
    ¬ BreachWithin f x₀ (threePoint ε L) N safe q := by
  rintro ⟨-, hq0, hB⟩
  have hlow := (breach_ge_threePoint hε hε' h0 hL hL').trans hB
  rw [ENNReal.ofReal_le_ofReal_iff hq0] at hlow
  linarith

/-- Bernoulli's inequality, rearranged: for `0 ≤ x ≤ 1`,
`N x / (1 + N x) ≤ 1 - (1 - x)ᴺ`. It follows from `(1 - x)ᴺ (1 + N x) ≤ 1`, which is
`1 + N x ≤ (1 + x)ᴺ` multiplied by `(1 - x)ᴺ`, with `(1 - x)ᴺ (1 + x)ᴺ = (1 - x²)ᴺ ≤ 1`. -/
theorem one_sub_pow_ge_bernoulli {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) (N : ℕ) :
    N * x / (1 + N * x) ≤ 1 - (1 - x) ^ N := by
  have hpos : 0 < 1 + N * x := by positivity
  have hbern : 1 + N * x ≤ (1 + x) ^ N := one_add_mul_le_pow (by linarith) N
  have hprod : (1 - x) ^ N * (1 + x) ^ N ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hkey : (1 - x) ^ N * (1 + N * x) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hbern (pow_nonneg (by linarith) N)).trans hprod
  rw [div_le_iff₀ hpos]
  linarith

/-- The refutation device, at Bernoulli's threshold: under the hypotheses of
`breach_ge_threePoint`, no bound `q < 2εN / (1 + 2εN)` holds for the three-point law. -/
theorem not_breachWithin_threePoint {ε L : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2)
    (h0 : f x₀ 0 = x₀) (hL : ¬ safe (f x₀ L)) (hL' : ¬ safe (f x₀ (-L))) {N : ℕ}
    {q : ℝ} (hq : q < 2 * ε * N / (1 + 2 * ε * N)) :
    ¬ BreachWithin f x₀ (threePoint ε L) N safe q := by
  have hbern := one_sub_pow_ge_bernoulli (x := 2 * ε) (by linarith) (by linarith) N
  rw [show (N : ℝ) * (2 * ε) = 2 * ε * N by ring] at hbern
  exact not_breachWithin_threePoint_exact hε hε' h0 hL hL' (hq.trans_le hbern)

end ThreePoint

end Gimle.Forseti.Stepped
