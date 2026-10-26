module

public import Gimle.Forseti.Stepped
public import Gimle.Forseti.Examples.HedgedSpreadContract

/-! The hedged exposure of `Examples/HedgedSpread.lean`, stepped by Euler under
independent random shocks.

What this module proves, from the flat start `s = h = 0`, with `256` steps to one unit of
time, called a year below:

* under every centred shock law of variance `64`, the exposure leaves the band `|s| ≤ 1`
  at some step of the year with probability at most `1/4` (`breach_within_year`), and the
  energy `V = s² + h²` has expectation at most `32/255` at every step
  (`expected_energy_le`) and at most `1086/10000` at the year end
  (`expected_energy_year`);
* under every shock law sub-Gaussian with proxy `64`, the exposure lies outside the band
  on any one date of the year, chosen in advance, with probability at most `1/100`
  (`exceeds_at_each_mark_year`);
* one centred law of variance `64`, with rare large jumps, makes the exposure leave the
  band within the year with probability above `1/5` (`breach_within_year_fifth_refuted`),
  so the horizon bound cannot be brought below `1/5` from the variance alone.

The step. The system is the compiled field `ds := (-s + -h) + d`, `dh := s + -h` over
`[d, s, h]`, advanced by one explicit Euler step of size `Δ = 1/256`: `step x d` adds `Δ`
times the compiled rates at `[d, s, h]` to the state `x = [s, h]`, with the shock `d` in
the driver slot. `step_s` and `step_h` read the two rows of the step off the compiled
expressions (`rates_s`, `rates_h`), and `exposureWithin_iff_obs` reads the band off the
compiled `obs-s` output, so nothing restates the equations unverified. The input path `ω`
is random, its coordinates independent and each distributed as a law `law` on `ℝ`
(`Stepped.pathMeasure`), and the state at mark `n`, after `n` steps, is
`run step compiled.initial ω n`.

The energy. `V = s² + h²` (`energy`, from the contract module) shrinks by the factor
`ρ = (1 − Δ)² + Δ² = 1 − 2Δ + 2Δ²` under the deterministic part of a step; as in
continuous time the coupling is skew-symmetric, so the cross terms between `s` and `h`
cancel. The shock adds a term linear in `d` and the term `Δ²d²`. For a centred law of
second moment `v` (`TwoMomentLaw`) the one-step expectation is therefore exactly
`ρ V + Δ²v` (`energy_step_eq`), and from the flat start the expectation at mark `n` is
exactly `Δ²v ∑_{k<n} ρᵏ` (`expected_energy_eq`), at most the stationary value
`Δ²v / (1 − ρ)` (`expected_energy_le`). At `v = 64` the stationary value `32/255` holds
at every mark, and the year-end value is about `0.1085`: `expected_energy_year` proves
it is at most `1086/10000`, the kernel evaluating `geomSum`, the same geometric sum by
recursion over `ℚ` (`geomSum_eq`).

The horizon bound. A breach of the band `|s| ≤ B` forces `V ≥ B²`, and `V` grows in
expectation by at most `Δ²v` per mark, since `ρ ≤ 1`. The horizon breach bound
(`Stepped.breachWithin_of_drift`) then gives
`P(|s| > B at some mark n ≤ N) ≤ N Δ²v / B²` for every centred law of second moment `v`,
whatever its shape (`breach_within`). At `v = 64`, `B = 1` and `N = 256` the bound is
`1/4` (`breach_within_year`). The variance `64` is `σ²/Δ` with `σ = 1/2`: the shocks'
contribution `Δ ∑ dₖ` over one unit of time then has variance `σ² = 1/4`.

The fixed-date bound. From the flat start the state is linear in the shocks. Shock `k`
reaches the exposure at mark `n` with the weight `Δ weight(n − 1 − k)`, where
`weights j = Aʲ (1, 0)` follows the deterministic part `A = [[1 − Δ, −Δ], [Δ, 1 − Δ]]`
of the step and `weight j` is its first component (`run_s_eq`, `run_h_eq`). A law is
sub-Gaussian with proxy `v` (`SubGaussianLaw`) when its moment generating function is at
most `exp(v t²/2)`, that of the centred Gaussian of variance `v`; a variable `X` of such
a law has `P(|X| > t) ≤ 2 exp(−t²/(2v))` (`Stepped.two_sided_tail`). Under such shocks
the exposure at mark `n` is sub-Gaussian with the proxy `Δ²v ∑_{k<n} weight(k)²`
(`proxy v n`), computed from the weights themselves rather than from a bound on them
(for Gaussian shocks of variance `v` it is the variance of the exposure), and evaluated
exactly over `ℚ`. So the exposure leaves `|s| ≤ B` at mark `n` with probability at most
`2 exp(−B² / (2 proxy v n))` (`exceeds_at` with the proxy written over `ℝ`,
`exceeds_at_proxy` with the rational `proxy` cast to `ℝ`). `proxyRec` computes the same
proxy by a recursion over `ℚ` that the kernel evaluates (`proxyRec_eq`). At `v = 64` the
proxy at the year end is about `0.09125`; the kernel proves it is at most `913/10000`
(`proxy_256_le`), and it grows with the mark (`proxy_mono`). So at each mark `n ≤ 256`,
taken separately, `P(|s| > 1) ≤ 2 exp(−1/(2 · 0.0913)) ≈ 0.0084`;
`exceeds_at_each_mark_year` states the rounder `1/100`. This is the shape of a
value-at-risk statement: on any one date of the year, chosen in advance, the exposure
stays within `1` with probability at least `99 %`. It bounds each date separately: a
union bound over the `256` dates gives nothing (`256 · 0.0084 > 1`), and no horizon
bound under the sub-Gaussian hypothesis is proved here. A breach at some date of the
year is what the horizon bound controls.

The refutation. The three-point law with mass `ε = 64 / (2 · 257²)` at each of `±257`
and the rest at `0` is centred with variance `64` (`Stepped.threePoint_twoMoment`): a
bounded law whose variance sits in rare one-step jumps. Being bounded it is sub-Gaussian
with some proxy (Hoeffding's lemma gives `257²`), but not with the proxy `64` of its
variance (`threePoint_not_subGaussian`). The jump `257` is the smallest whole jump that
clears the band in one step. A zero shock leaves the flat start in place
(`step_zero_fixed`), and one jump of size `257` moves the exposure to `257/256 > 1`
(`step_big_breaches`). Under this law the exposure therefore breaches within the year
with probability at least `1 − (1 − 2ε)²⁵⁶` (`Stepped.breach_ge_threePoint`), about
`22 %`. The same three facts refute every bound below Bernoulli's
`2εN / (1 + 2εN) ≈ 0.199` at `N = 256` (`breach_within_year_tenth_refuted`, at `1/10`)
and every bound below the exact threshold `1 − (1 − 2ε)²⁵⁶ ≈ 0.2198`
(`breach_within_year_fifth_refuted`, at `1/5`, the kernel evaluating the rational
power). Over all centred laws of variance `64` the worst breach probability within the
year therefore lies between about `0.22` and `1/4`: the distribution-free bound is nearly
attained, by a law whose variance sits in rare one-step jumps.

While the chain waits at the start, each mark carries the same chance `2ε` of a jump out
of the band, so the breach probability by mark `N` is at least `1 − (1 − 2ε)ᴺ`, close to
`2εN` while that is small. Under the Gaussian of the same variance, an input clears the
band in one step, `|d| > 256`, with probability at most `2 exp(−256²/(2 · 64)) = 2e⁻⁵¹²`
(`Stepped.two_sided_tail`); under the three-point law it does so with probability
`2ε = 64/257²`. This is a familiar point in financial risk: equal volatility does not
mean equal risk of ruin. A horizon bound below the three-point level needs a hypothesis
on the tail, such as `SubGaussianLaw`, and not only on the variance. The centred Gaussian
of variance `v` is in both law classes (`gaussian_in_both_classes`), so the horizon bound
and the bound at every mark both apply to it.

What this module does not claim. It speaks of the marks `0, 1, 2, …` of the Euler chain
only: nothing about the continuous-time system of the contract module, about a
stochastic differential equation, or about how close the chain comes to either. It says
nothing about markets: the shock law is a hypothesis of each bound, not a fit to prices.
Nor does it compute probabilities under Gaussian shocks: the bounds hold for the Gaussian
because it belongs to the law classes, but they are bounds over each whole class, and
the Gaussian's own breach probability, within the year or at a single mark, is not
computed here. -/

@[expose] public section

namespace Gimle.Forseti.Examples.HedgedSpreadStepped

open MeasureTheory
open Gimle.Asgard
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open scoped NNReal

/-! ### The step -/

/-- The step size: `256` steps to one unit of time. -/
def Δ : ℚ := 1 / 256

/-- The factor `(1 − Δ)² + Δ²` by which one step without a shock scales the energy. -/
def ρ : ℚ := 1 - 2 * Δ + 2 * Δ ^ 2

/-- One explicit Euler step of the compiled field: the state `x = [s, h]` moves by `Δ`
times the compiled rates at `[d, s, h]`, with the shock `d` in the driver slot. -/
noncomputable def step (x : Point states) (d : ℝ) : Point states :=
  fun i => x i + (Δ : ℝ) * (compiled.rates.expressions i).eval
    (pointAppend (fun _ : Fin width => d) x)

/-- The exposure row of the step: `s ↦ s + Δ(−s − h + d)`. -/
theorem step_s (x : Point states) (d : ℝ) :
    step x d (0 : Fin 2) = x (0 : Fin 2) + Δ * (-x (0 : Fin 2) - x (1 : Fin 2) + d) := by
  simp only [step, rates_s]
  ring

/-- The hedge row of the step: `h ↦ h + Δ(s − h)`. -/
theorem step_h (x : Point states) (d : ℝ) :
    step x d (1 : Fin 2) = x (1 : Fin 2) + Δ * (x (0 : Fin 2) - x (1 : Fin 2)) := by
  simp only [step, rates_h]
  ring

/-- The step is jointly measurable in the state and the shock. -/
theorem measurable_step : Measurable (fun p : Point states × ℝ => step p.1 p.2) := by
  rw [measurable_pi_iff]
  change ∀ i : Fin 2, Measurable fun p : Point states × ℝ => step p.1 p.2 i
  rw [Fin.forall_fin_two]
  simp only [step_s, step_h]
  constructor <;> fun_prop

/-- The exposure band `|s| ≤ B`. -/
def exposureWithin (B : ℝ) (x : Point states) : Prop := |x (0 : Fin 2)| ≤ B

/-- The band read off the compiled observation: the state `x` is in the band exactly when
the `obs-s` output at `[d, s, h]` is, whatever the driver value `d`. -/
theorem exposureWithin_iff_obs (B : ℝ) (d : Point width) (x : Point states) :
    exposureWithin B x ↔ |compiled.outputs.circuit.run (pointAppend d x) sIndex| ≤ B := by
  rw [s_at, append_s]
  rfl

/-! ### The one-step identity and the expected energy -/

variable {law : Measure ℝ} {v : ℝ}

private theorem ρ_nonneg : (0 : ℝ) ≤ ρ := by norm_num [ρ, Δ]

private theorem ρ_lt_one : (ρ : ℝ) < 1 := by norm_num [ρ, Δ]

private theorem measurable_ofReal_energy :
    Measurable (fun x : Point states => ENNReal.ofReal (energy x)) :=
  ENNReal.measurable_ofReal.comp (by unfold energy; fun_prop)

private theorem energy_initial : energy compiled.initial = 0 := by
  rw [initial_eq]
  simp [energy]

/-- **The one-step identity.** For a centred shock law of second moment `v`, one step
scales the expected energy by `ρ` and adds `Δ²v`, exactly:
`energy (step x d) = ρ · energy x + 2Δ((1 − Δ)s − Δh) d + Δ²d²`, and the linear term
has mean zero. -/
theorem energy_step_eq (h : TwoMomentLaw law v) (x : Point states) :
    ∫⁻ d, ENNReal.ofReal (energy (step x d)) ∂law
      = ENNReal.ofReal ρ * ENNReal.ofReal (energy x) + ENNReal.ofReal (Δ ^ 2 * v) := by
  have := h.prob
  have hv := h.nonneg
  have hfun : (fun d => energy (step x d)) = fun d =>
      ((ρ : ℝ) * energy x + 2 * Δ * ((1 - Δ) * x (0 : Fin 2) - Δ * x (1 : Fin 2)) * d)
        + (Δ : ℝ) ^ 2 * d ^ 2 := by
    funext d
    simp only [energy, step_s, step_h, ρ]
    push_cast
    ring
  have h0 : Integrable (fun _ : ℝ => (ρ : ℝ) * energy x) law := integrable_const _
  have h1 : Integrable
      (fun d : ℝ => 2 * Δ * ((1 - Δ) * x (0 : Fin 2) - Δ * x (1 : Fin 2)) * d) law :=
    h.integrable_id.const_mul _
  have h2 : Integrable (fun d : ℝ => (Δ : ℝ) ^ 2 * d ^ 2) law := h.integrable_sq.const_mul _
  have h01 : Integrable (fun d : ℝ => (ρ : ℝ) * energy x
      + 2 * Δ * ((1 - Δ) * x (0 : Fin 2) - Δ * x (1 : Fin 2)) * d) law := h0.add h1
  have hint : Integrable (fun d => energy (step x d)) law := by
    rw [hfun]
    exact h01.add h2
  have hval : ∫ d, energy (step x d) ∂law = ρ * energy x + Δ ^ 2 * v := by
    rw [hfun, integral_add h01 h2, integral_add h0 h1, integral_const, integral_const_mul,
      integral_const_mul, h.mean, h.second]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun d => energy_nonneg _), hval,
    ENNReal.ofReal_add (mul_nonneg ρ_nonneg (energy_nonneg x)) (by positivity),
    ENNReal.ofReal_mul ρ_nonneg]

/-- **The expected energy from the flat start**, exactly: `Δ²v ∑_{k<n} ρᵏ` at mark
`n`, for every centred shock law of second moment `v`. -/
theorem expected_energy_eq (h : TwoMomentLaw law v) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (energy (run step compiled.initial ω n : Point states))
        ∂pathMeasure law
      = ENNReal.ofReal (Δ ^ 2 * v * ∑ k ∈ Finset.range n, (ρ : ℝ) ^ k) := by
  have := h.prob
  have hv := h.nonneg
  refine (lintegral_run_eq_geom (V := fun x : Point states => ENNReal.ofReal (energy x)) law
    measurable_step measurable_ofReal_energy (energy_step_eq h) compiled.initial n).trans ?_
  simp only [energy_initial, ENNReal.ofReal_zero, mul_zero, zero_add]
  rw [ENNReal.ofReal_mul (p := (Δ : ℝ) ^ 2 * v) (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun k _ => pow_nonneg ρ_nonneg k]
  simp only [ENNReal.ofReal_pow ρ_nonneg]

/-- **The expected energy stays below its stationary value** `Δ²v / (1 − ρ)` at every
mark. -/
theorem expected_energy_le (h : TwoMomentLaw law v) (n : ℕ) :
    ExpectedLe step compiled.initial law energy n (Δ ^ 2 * v / (1 - ρ)) := by
  have hv := h.nonneg
  have hρ : (0 : ℝ) < 1 - ρ := sub_pos.2 ρ_lt_one
  refine ⟨h.prob, div_nonneg (by positivity) hρ.le, ?_⟩
  rw [expected_energy_eq h]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsum : ∑ k ∈ Finset.range n, (ρ : ℝ) ^ k ≤ 1 / (1 - ρ) := by
    rw [geom_sum_eq ρ_lt_one.ne n, ← neg_div_neg_eq, neg_sub, neg_sub]
    exact div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg ρ_nonneg n)) hρ.le
  calc (Δ : ℝ) ^ 2 * v * ∑ k ∈ Finset.range n, (ρ : ℝ) ^ k
      ≤ (Δ : ℝ) ^ 2 * v * (1 / (1 - ρ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Δ : ℝ) ^ 2 * v / (1 - ρ) := mul_one_div _ _

/-! ### The geometric sum, by recursion -/

/-- `∑_{k<n} ρᵏ` by recursion over `ℚ`, `geomSum (n + 1) = ρ · geomSum n + 1`, in a form
the kernel evaluates. -/
def geomSum : ℕ → ℚ
  | 0 => 0
  | n + 1 => ρ * geomSum n + 1

/-- The recursion computes the geometric sum. -/
theorem geomSum_eq (n : ℕ) : (geomSum n : ℝ) = ∑ k ∈ Finset.range n, (ρ : ℝ) ^ k := by
  induction n with
  | zero => simp [geomSum]
  | succ n ih =>
    rw [geomSum, Rat.cast_add, Rat.cast_mul, Rat.cast_one, ih, Finset.sum_range_succ',
      Finset.mul_sum]
    simp [pow_succ']

/-! ### The horizon breach bound -/

/-- A breach of the band forces `B² ≤ V`. -/
private theorem sq_le_energy {B : ℝ} (hB : 0 < B) {x : Point states}
    (hx : ¬ exposureWithin B x) : B ^ 2 ≤ energy x := by
  have hlt : B < |x (0 : Fin 2)| := not_le.1 hx
  have hsq : B ^ 2 < |x (0 : Fin 2)| ^ 2 :=
    sq_lt_sq' (by linarith [abs_nonneg (x (0 : Fin 2))]) hlt
  rw [sq_abs] at hsq
  unfold energy
  nlinarith [sq_nonneg (x (1 : Fin 2))]

/-- **The horizon breach bound for every two-moment law.** From the flat start, the
probability that the exposure leaves `|s| ≤ B` at some mark `n ≤ N` is at most
`N Δ²v / B²`, for every centred shock law of second moment `v`. -/
theorem breach_within (h : TwoMomentLaw law v) {B : ℝ} (hB : 0 < B) (N : ℕ) :
    BreachWithin step compiled.initial law N (exposureWithin B) (N * (Δ ^ 2 * v) / B ^ 2) := by
  have := h.prob
  have hv := h.nonneg
  have hB2 : 0 < B ^ 2 := by positivity
  have hρ : ENNReal.ofReal ρ ≤ 1 := ENNReal.ofReal_le_one.2 ρ_lt_one.le
  refine breachWithin_of_drift (V := fun x : Point states => ENNReal.ofReal (energy x))
    (c := ENNReal.ofReal (B ^ 2)) (β := ENNReal.ofReal (Δ ^ 2 * v)) law measurable_step
    measurable_ofReal_energy (ENNReal.ofReal_pos.2 hB2).ne' ENNReal.ofReal_ne_top
    (fun x _ => (energy_step_eq h x).trans_le
      (add_le_add (mul_le_of_le_one_left zero_le hρ) le_rfl))
    (fun x hx => ENNReal.ofReal_le_ofReal (sq_le_energy hB hx)) (by positivity) ?_
  simp only [energy_initial, ENNReal.ofReal_zero, zero_add]
  rw [ENNReal.ofReal_div_of_pos hB2, ENNReal.ofReal_mul (Nat.cast_nonneg N),
    ENNReal.ofReal_natCast]

/-! ### The bounds at the year end -/

/-- **The year-end horizon bound.** Under every centred shock law of variance `64`, the
exposure leaves `|s| ≤ 1` at some mark of the year, `n ≤ 256`, with probability at
most `1/4`. -/
theorem breach_within_year (h : TwoMomentLaw law 64) :
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1 / 4) :=
  (breach_within h one_pos 256).mono (by norm_num [Δ])

/-- **The year-end expected energy.** Under every centred shock law of variance `64`,
the expected energy at mark `256` is at most `1086/10000`; its value is about `0.1085`,
below the stationary `32/255` of `expected_energy_le`. -/
theorem expected_energy_year (h : TwoMomentLaw law 64) :
    ExpectedLe step compiled.initial law energy 256 (1086 / 10000) := by
  have hq : Δ ^ 2 * 64 * geomSum 256 ≤ 1086 / 10000 := by decide +kernel
  have hr := Rat.cast_le (K := ℝ) |>.mpr hq
  push_cast at hr
  refine ⟨h.prob, by norm_num, ?_⟩
  rw [expected_energy_eq h, ← geomSum_eq]
  exact ENNReal.ofReal_le_ofReal hr

/-! ### The weights of the shocks -/

/-- The state `[s, h]` `j` marks after a unit of exposure with no hedge, under the
deterministic part of the step: `weights j = Aʲ (1, 0)` with
`A = [[1 − Δ, −Δ], [Δ, 1 − Δ]]`. -/
def weights : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | k + 1 => ((1 - Δ) * (weights k).1 - Δ * (weights k).2,
      Δ * (weights k).1 + (1 - Δ) * (weights k).2)

/-- The exposure component of `weights`: the shock `k` enters the exposure at mark `n`
with the weight `Δ weight(n − 1 − k)`. -/
def weight (k : ℕ) : ℚ := (weights k).1

/-- Both components of the state at mark `n`, from the flat start, as weighted sums of
the shocks. -/
private theorem run_eq_sums (ω : ℕ → ℝ) (n : ℕ) :
    run step compiled.initial ω n (0 : Fin 2)
        = ∑ k ∈ Finset.range n, ((Δ : ℝ) * (weight (n - 1 - k) : ℝ)) * ω k ∧
      run step compiled.initial ω n (1 : Fin 2)
        = ∑ k ∈ Finset.range n, ((Δ : ℝ) * ((weights (n - 1 - k)).2 : ℝ)) * ω k := by
  induction n with
  | zero => simp [initial_eq]
  | succ n ih =>
    have hs : ∀ k ∈ Finset.range n,
        ((Δ : ℝ) * (weight (n + 1 - 1 - k) : ℝ)) * ω k
          = (1 - Δ) * (((Δ : ℝ) * (weight (n - 1 - k) : ℝ)) * ω k)
            - Δ * (((Δ : ℝ) * ((weights (n - 1 - k)).2 : ℝ)) * ω k) := by
      intro k hk
      rw [show n + 1 - 1 - k = n - 1 - k + 1 by have := Finset.mem_range.1 hk; omega]
      simp only [weight, weights]
      push_cast
      ring
    have hh : ∀ k ∈ Finset.range n,
        ((Δ : ℝ) * ((weights (n + 1 - 1 - k)).2 : ℝ)) * ω k
          = Δ * (((Δ : ℝ) * (weight (n - 1 - k) : ℝ)) * ω k)
            + (1 - Δ) * (((Δ : ℝ) * ((weights (n - 1 - k)).2 : ℝ)) * ω k) := by
      intro k hk
      rw [show n + 1 - 1 - k = n - 1 - k + 1 by have := Finset.mem_range.1 hk; omega]
      simp only [weight, weights]
      push_cast
      ring
    rw [run_succ, step_s, step_h, ih.1, ih.2, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_congr rfl hs, Finset.sum_congr rfl hh, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, Nat.add_sub_cancel, Nat.sub_self, weight, weights]
    push_cast
    constructor <;> ring

/-- **The exposure as a weighted sum of the shocks.** From the flat start, the exposure
at mark `n` is `∑_{k<n} Δ weight(n − 1 − k) ωₖ`. -/
theorem run_s_eq (ω : ℕ → ℝ) (n : ℕ) :
    run step compiled.initial ω n (0 : Fin 2)
      = ∑ k ∈ Finset.range n, ((Δ : ℝ) * (weight (n - 1 - k) : ℝ)) * ω k :=
  (run_eq_sums ω n).1

/-- The hedge at mark `n`, `∑_{k<n} Δ (weights (n − 1 − k)).2 ωₖ`. -/
theorem run_h_eq (ω : ℕ → ℝ) (n : ℕ) :
    run step compiled.initial ω n (1 : Fin 2)
      = ∑ k ∈ Finset.range n, ((Δ : ℝ) * ((weights (n - 1 - k)).2 : ℝ)) * ω k :=
  (run_eq_sums ω n).2

/-! ### The proxy of the exposure -/

/-- The variance proxy of the exposure at mark `n` under shocks of proxy `v`,
`Δ²v ∑_{k<n} weight(k)²`. It is computed from the weights themselves rather than from a
bound on them; for Gaussian shocks of variance `v` it is the variance of the exposure. -/
def proxy (v : ℚ) (n : ℕ) : ℚ := Δ ^ 2 * v * ∑ k ∈ Finset.range n, (weight k) ^ 2

/-- The iteration behind `proxyRec`. From `(1, 0, 0)`, each mark adds the square of the
first component to the accumulator and then advances the first two components by `A`;
at mark `n` it is `(weight n, (weights n).2, ∑_{k<n} weight(k)²)` (`proxyIter_eq`). -/
def proxyIter : ℕ → ℚ × ℚ × ℚ
  | 0 => (1, 0, 0)
  | n + 1 =>
    let p := proxyIter n
    ((1 - Δ) * p.1 - Δ * p.2.1, Δ * p.1 + (1 - Δ) * p.2.1, p.2.2 + p.1 ^ 2)

/-- `proxy` by a recursion over `ℚ` that the kernel evaluates in one pass. -/
def proxyRec (v : ℚ) (n : ℕ) : ℚ := Δ ^ 2 * v * (proxyIter n).2.2

/-- The iteration tracks the weights and the sum of their squares. -/
theorem proxyIter_eq (n : ℕ) :
    proxyIter n = (weight n, (weights n).2, ∑ k ∈ Finset.range n, (weight k) ^ 2) := by
  induction n with
  | zero => simp [proxyIter, weight, weights]
  | succ n ih =>
    simp only [proxyIter, ih, Finset.sum_range_succ, weight, weights]

/-- The recursion computes the proxy. -/
theorem proxyRec_eq (v : ℚ) (n : ℕ) : proxyRec v n = proxy v n := by
  rw [proxyRec, proxyIter_eq, proxy]

/-- The proxy read over `ℝ`. -/
theorem proxy_cast (v : ℚ) (n : ℕ) :
    (proxy v n : ℝ) = (Δ : ℝ) ^ 2 * v * ∑ k ∈ Finset.range n, (weight k : ℝ) ^ 2 := by
  unfold proxy
  push_cast
  ring

/-- The proxy grows with the mark. -/
theorem proxy_mono (v : ℚ) (hv : 0 ≤ v) {n m : ℕ} (h : n ≤ m) : proxy v n ≤ proxy v m :=
  mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 h)
      fun _ _ _ => sq_nonneg _)
    (mul_nonneg (sq_nonneg _) hv)

/-- The proxy at the year end under shocks of proxy `64` is at most `913/10000`, by the
kernel; its value is about `0.09125`. -/
theorem proxy_256_le : proxy 64 256 ≤ 913 / 10000 := by
  rw [← proxyRec_eq]
  decide +kernel

/-! ### The fixed-date bound -/

/-- **The fixed-date bound for every sub-Gaussian law.** From the flat start, the
probability that the exposure leaves `|s| ≤ B` at mark `n` is at most `q` as soon as
`2 exp(−B² / (2c)) ≤ q`, for every shock law that is sub-Gaussian with proxy `v`. Here
`c = Δ²v ∑_{k<n} weight(k)²` is the proxy of the exposure at that mark, written over
`ℝ`; `exceeds_at_proxy` states it with the rational `proxy`. -/
theorem exceeds_at {v : ℝ≥0} (h : SubGaussianLaw law v) {B : ℝ}
    (hB : 0 ≤ B) (n : ℕ) {q : ℝ}
    (hq : 2 * Real.exp (-B ^ 2 / (2 * ((Δ : ℝ) ^ 2 * v
      * ∑ k ∈ Finset.range n, (weight k : ℝ) ^ 2))) ≤ q) :
    ExceedsAt step compiled.initial law n (exposureWithin B) q := by
  have hsum : ∑ k ∈ Finset.range n, ((Δ : ℝ) * (weight (n - 1 - k) : ℝ)) ^ 2 * (v : ℝ)
      = (Δ : ℝ) ^ 2 * v * ∑ k ∈ Finset.range n, (weight k : ℝ) ^ 2 := by
    rw [Finset.sum_range_reflect (fun j => ((Δ : ℝ) * (weight j : ℝ)) ^ 2 * (v : ℝ)) n,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact exceedsAt_of_weighted h (w := fun k => (Δ : ℝ) * (weight (n - 1 - k) : ℝ))
    (obs := fun x => x (0 : Fin 2)) hB (fun ω => run_s_eq ω n) (fun x hx => not_le.1 hx)
    (hsum ▸ hq)

/-- **The fixed-date bound with the rational proxy.** For a shock law sub-Gaussian with a
whole-number proxy `v`, the bound of `exceeds_at` with `c = proxy v n` cast to `ℝ`. For a
law of proxy `64`, a hypothesis `h : SubGaussianLaw law 64` serves as it stands:
`exceeds_at_proxy h hB n hq` reads `64` as a natural number, so the side condition `hq`
is about `proxy 64 n`, which `proxyRec_eq` and the kernel evaluate. -/
theorem exceeds_at_proxy {v : ℕ} (h : SubGaussianLaw law v) {B : ℝ} (hB : 0 ≤ B) (n : ℕ)
    {q : ℝ} (hq : 2 * Real.exp (-B ^ 2 / (2 * (proxy v n : ℝ))) ≤ q) :
    ExceedsAt step compiled.initial law n (exposureWithin B) q := by
  refine exceeds_at h hB n ?_
  rw [proxy_cast, Rat.cast_natCast] at hq
  rwa [NNReal.coe_natCast]

/-- The numerical core of the bound at every mark: a proxy `0 < c ≤ 0.0913` puts
`2 exp(−1 / (2c))` below `1/100`, through `e^{5.47} ≥ 200`. -/
private theorem fixed_date_numeric {c : ℝ} (h0 : 0 < c) (h1 : c ≤ 913 / 10000) :
    2 * Real.exp (-1 ^ 2 / (2 * c)) ≤ 1 / 100 := by
  have hr : (547 / 100 : ℝ) ≤ 1 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hexp : Real.exp (-1 ^ 2 / (2 * c)) ≤ Real.exp (-(547 / 100)) := by
    rw [Real.exp_le_exp, one_pow, neg_div]
    exact neg_le_neg hr
  have hE : (200 : ℝ) ≤ Real.exp (547 / 100) := by
    have := exp_ge_floor_cubic 5 (r := 547 / 100) (by norm_num)
    norm_num at this
    linarith
  have hinv : Real.exp (-(547 / 100)) ≤ 1 / 200 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) hE
  linarith

/-- **The bound at each mark of the year.** Under every shock law that is sub-Gaussian
with proxy `64`, at each mark `n ≤ 256`, taken separately, the exposure lies outside
`|s| ≤ 1` with probability at most `1/100`. -/
theorem exceeds_at_each_mark_year (h : SubGaussianLaw law 64) :
    AtEveryMark step compiled.initial law 256 (exposureWithin 1) (1 / 100) := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- at mark `0` the chain sits at the start, inside the band, on every path
    have hempty :
        {ω : ℕ → ℝ | ¬ exposureWithin 1 (run step compiled.initial ω 0)} = ∅ := by
      ext ω
      simp [exposureWithin, initial_eq]
    refine ⟨h.prob, by norm_num, ?_⟩
    rw [hempty, measure_empty]
    exact zero_le
  · refine exceeds_at_proxy h zero_le_one n ?_
    have hle : (proxy 64 n : ℝ) ≤ 913 / 10000 := by
      have := Rat.cast_le (K := ℝ) |>.mpr ((proxy_mono 64 (by norm_num) hn).trans proxy_256_le)
      push_cast at this
      exact this
    have hpos : (0 : ℝ) < proxy 64 n := by
      have h1 : (0 : ℚ) < proxy 64 1 := by
        rw [← proxyRec_eq]
        decide +kernel
      exact_mod_cast h1.trans_le (proxy_mono 64 (by norm_num) hn0)
    exact fixed_date_numeric hpos hle

/-! ### The refutation by rare large jumps -/

/-- A zero shock leaves the flat start where it is. -/
theorem step_zero_fixed : step compiled.initial 0 = compiled.initial := by
  have key : ∀ i : Fin 2, step compiled.initial 0 i = compiled.initial i := by
    rw [Fin.forall_fin_two, step_s, step_h, initial_eq]
    simp
  exact funext key

/-- A single shock of size `|L| > 1/Δ` moves the exposure out of `|s| ≤ 1` from the
flat start. -/
theorem step_big_breaches (L : ℝ) (hL : 1 < Δ * |L|) :
    ¬ exposureWithin 1 (step compiled.initial L) := by
  have hΔ : (0 : ℝ) < Δ := by norm_num [Δ]
  unfold exposureWithin
  rw [step_s, initial_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_zero, sub_zero, zero_add,
    abs_mul, abs_of_pos hΔ]
  exact not_le.2 hL

/-- The three-point law with mass `64 / (2 · 257²)` at each of `±257` is centred with
variance `64`. -/
private theorem threePoint_year_twoMoment :
    TwoMomentLaw (threePoint (64 / (2 * 257 ^ 2)) 257) 64 := by
  have hlaw := threePoint_twoMoment (ε := 64 / (2 * 257 ^ 2)) (L := 257) (by norm_num)
    (by norm_num)
  rwa [show 2 * (64 / (2 * 257 ^ 2) : ℝ) * 257 ^ 2 = 64 by norm_num] at hlaw

/-- The three-point law with jumps `±257` is not sub-Gaussian with the proxy `64` of its
variance: at `t = 1/10` its moment generating function exceeds `ε e^{25.7} > 3`, while
`exp(64 t² / 2) = e^{0.32} < 3`. -/
theorem threePoint_not_subGaussian :
    ¬ SubGaussianLaw (threePoint (64 / (2 * 257 ^ 2)) 257) 64 := by
  intro h
  have hm := h.subgaussian.mgf_le (1 / 10)
  rw [ProbabilityTheory.mgf, integral_threePoint (by norm_num) (by norm_num)] at hm
  norm_num at hm
  have hup : Real.exp (8 / 25) < 3 := by
    have : Real.exp (8 / 25) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    linarith [Real.exp_one_lt_d9]
  have hlow : (200000 : ℝ) ≤ Real.exp (257 / 10) := by
    have := exp_ge_floor_cubic 5 (r := 257 / 10) (by norm_num)
    norm_num at this
    linarith
  have hneg : 0 ≤ Real.exp (-(257 / 10)) := (Real.exp_pos _).le
  linarith

/-- **The horizon bound `1/10` is refuted for two-moment laws.** The three-point law with
mass `64 / (2 · 257²)` at each of `±257` is centred with variance `64`, and under it the
exposure breaches within the year with probability at least Bernoulli's
`2εN / (1 + 2εN) ≈ 0.199 > 1/10`. -/
theorem breach_within_year_tenth_refuted : ¬ ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1 / 10) := by
  intro h
  exact not_breachWithin_threePoint (by norm_num) (by norm_num) step_zero_fixed
    (step_big_breaches 257 (by norm_num [Δ])) (step_big_breaches (-257) (by norm_num [Δ]))
    (by norm_num) (h _ threePoint_year_twoMoment)

/-- **The horizon bound `1/5` is refuted for two-moment laws.** Under the same
three-point law the exposure breaches within the year with probability at least
`1 − (1 − 2ε)²⁵⁶ ≈ 0.2198 > 1/5`, the kernel evaluating the rational power. Over all
centred laws of variance `64`, the worst breach probability within the year therefore
lies between `1/5` and the `1/4` of `breach_within_year`. -/
theorem breach_within_year_fifth_refuted : ¬ ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1 / 5) := by
  intro h
  have hq : (1 / 5 : ℚ) < 1 - (1 - 2 * (64 / (2 * 257 ^ 2) : ℚ)) ^ 256 := by decide +kernel
  have hr := Rat.cast_lt (K := ℝ) |>.mpr hq
  push_cast at hr
  exact not_breachWithin_threePoint_exact (by norm_num) (by norm_num) step_zero_fixed
    (step_big_breaches 257 (by norm_num [Δ])) (step_big_breaches (-257) (by norm_num [Δ]))
    hr (h _ threePoint_year_twoMoment)

/-! ### The Gaussian in both classes -/

open ProbabilityTheory in
/-- The centred Gaussian of variance `v` is both a two-moment law and a sub-Gaussian law
with proxy `v`, so every bound of this module at variance `v` applies to it. -/
theorem gaussian_in_both_classes (v : ℝ≥0) :
    TwoMomentLaw (gaussianReal 0 v) v ∧ SubGaussianLaw (gaussianReal 0 v) v :=
  ⟨gaussian_twoMoment v, gaussian_subGaussian v⟩

#print axioms step_s
#print axioms step_h
#print axioms measurable_step
#print axioms exposureWithin_iff_obs
#print axioms energy_step_eq
#print axioms expected_energy_eq
#print axioms expected_energy_le
#print axioms geomSum_eq
#print axioms breach_within
#print axioms breach_within_year
#print axioms expected_energy_year
#print axioms run_s_eq
#print axioms run_h_eq
#print axioms proxyIter_eq
#print axioms proxyRec_eq
#print axioms proxy_cast
#print axioms proxy_mono
#print axioms proxy_256_le
#print axioms exceeds_at
#print axioms exceeds_at_proxy
#print axioms exceeds_at_each_mark_year
#print axioms step_zero_fixed
#print axioms step_big_breaches
#print axioms threePoint_not_subGaussian
#print axioms breach_within_year_tenth_refuted
#print axioms breach_within_year_fifth_refuted
#print axioms gaussian_in_both_classes

end Gimle.Forseti.Examples.HedgedSpreadStepped
