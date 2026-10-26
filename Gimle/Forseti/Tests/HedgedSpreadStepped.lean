module

public import Gimle.Forseti.Examples.HedgedSpreadStepped

/-! Coverage for the hedged exposure stepped by Euler under random shocks.

Pinned here: the step size and the energy factor as exact rationals, the kernel
evaluating both; the two rows of the step read off the compiled field; the exposure band
and its reading off the compiled `obs-s` output; the one-step identity at the variance
`64` and the exact expected energy; the stationary energy `32/255` at every mark, and
the year-end expected energy at most `1086/10000` and at least `1085/10000`; the general
horizon bound as a claim form at another band and horizon, and the year-end horizon
bound `1/4`; the weights and the proxy at small marks, its kernel value at the year end
from both sides, and its rational and real forms; the exposure and the hedge as weighted
sums of the shocks; the fixed-date bound with the real and with the rational proxy, and
the bound at each mark of the year; the refutation by rare large jumps, with its two step
facts, at `1/10` and at `1/5`, and the three-point law not sub-Gaussian with proxy `64`;
the Gaussian in both law classes; and the axiom policy, asserted with `#guard_msgs`.
-/

@[expose] public section

namespace Gimle.Forseti.Tests.HedgedSpreadStepped

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Gimle.Asgard
open Gimle.Forseti.Stepped
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract
open Gimle.Forseti.Examples.HedgedSpreadStepped

/-! ### The stable interface -/

example : Δ = 1 / 256 := rfl
example : ρ = 32513 / 32768 := by decide +kernel
-- `Point states` is indexed by `Fin states`, which has no numeral instance, so the
-- coordinates are written as `Fin 2` literals, as in `HedgedSpread.rates_s`.
example (x : Point states) (d : ℝ) :
    step x d (0 : Fin 2) = x (0 : Fin 2) + (1/256 : ℝ) * (-x (0 : Fin 2) - x (1 : Fin 2) + d) := by
  rw [step_s]; norm_num [Δ]
example (x : Point states) (d : ℝ) :
    step x d (1 : Fin 2) = x (1 : Fin 2) + (1/256 : ℝ) * (x (0 : Fin 2) - x (1 : Fin 2)) := by
  rw [step_h]; norm_num [Δ]
example : Measurable (fun p : Point states × ℝ => step p.1 p.2) := measurable_step
example (B : ℝ) (x : Point states) : exposureWithin B x ↔ |x (0 : Fin 2)| ≤ B := Iff.rfl
example (B : ℝ) (d : Point width) (x : Point states) :
    exposureWithin B x ↔ |compiled.outputs.circuit.run (pointAppend d x) sIndex| ≤ B :=
  exposureWithin_iff_obs B d x

/-! ### The energy -/

/-- The one-step identity at the variance of the year-end bounds. -/
example (law : Measure ℝ) (h : TwoMomentLaw law 64) (x : Point states) :
    ∫⁻ d, ENNReal.ofReal (energy (step x d)) ∂law
      = ENNReal.ofReal ρ * ENNReal.ofReal (energy x) + ENNReal.ofReal (Δ ^ 2 * 64) :=
  energy_step_eq h x

example (law : Measure ℝ) {v : ℝ} (h : TwoMomentLaw law v) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (energy (run step compiled.initial ω n)) ∂pathMeasure law
      = ENNReal.ofReal (Δ ^ 2 * v * ∑ k ∈ Finset.range n, (ρ : ℝ) ^ k) :=
  expected_energy_eq h n

/-- The stationary energy `32/255` bounds the expectation at every mark. -/
example (law : Measure ℝ) (h : TwoMomentLaw law 64) (n : ℕ) :
    ExpectedLe step compiled.initial law energy n (32 / 255) :=
  (expected_energy_le h n).mono (by norm_num [Δ, ρ])
example : (Δ : ℝ) ^ 2 * 64 / (1 - ρ) = 32 / 255 := by norm_num [Δ, ρ]

example (law : Measure ℝ) (h : TwoMomentLaw law 64) :
    ExpectedLe step compiled.initial law energy 256 (1086 / 10000) := expected_energy_year h
-- the year-end value is at least `0.1085`, so `1086/10000` is within `10⁻⁴` of it
example : 1085 / 10000 ≤ Δ ^ 2 * 64 * geomSum 256 := by decide +kernel

example : geomSum 2 = 1 + ρ := by simp [geomSum]; ring
example (n : ℕ) : (geomSum n : ℝ) = ∑ k ∈ Finset.range n, (ρ : ℝ) ^ k := geomSum_eq n

/-! ### The horizon bound -/

example (law : Measure ℝ) (h : TwoMomentLaw law 64) :
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/4) := breach_within_year h

/-- A wider band at a shorter horizon, from the general bound. -/
example (law : Measure ℝ) (h : TwoMomentLaw law 64) :
    BreachWithin step compiled.initial law 64 (exposureWithin 2)
      ((64 : ℕ) * (Δ ^ 2 * 64) / 2 ^ 2) :=
  breach_within h (by norm_num) 64

/-! ### The weights, the proxy and the fixed-date bound -/

example : proxy 64 1 = Δ ^ 2 * 64 := by simp [proxy, weight, weights]
example : proxy 64 2 = Δ ^ 2 * 64 * (1 + (1 - Δ) ^ 2) := by
  simp only [proxy, Finset.sum_range_succ, Finset.sum_range_zero, weight, weights]; ring
example : 912 / 10000 ≤ proxy 64 256 := by rw [← proxyRec_eq]; decide +kernel
example : proxy 64 256 ≤ 913 / 10000 := proxy_256_le
example (v : ℚ) (n : ℕ) : proxyRec v n = proxy v n := proxyRec_eq v n
example (v : ℚ) (n : ℕ) :
    (proxy v n : ℝ) = (Δ : ℝ) ^ 2 * v * ∑ k ∈ Finset.range n, (weight k : ℝ) ^ 2 :=
  proxy_cast v n
example : proxy 64 100 ≤ proxy 64 256 := proxy_mono 64 (by norm_num) (by norm_num)

/-- The exposure at mark `n` is the weighted sum of the shocks, with the weight
`Δ weight(n − 1 − k)` on shock `k`; the hedge is the same sum with the second
component. -/
example (ω : ℕ → ℝ) (n : ℕ) :
    run step compiled.initial ω n (0 : Fin 2)
      = ∑ k ∈ Finset.range n, ((Δ : ℝ) * (weight (n - 1 - k) : ℝ)) * ω k := run_s_eq ω n
example (ω : ℕ → ℝ) (n : ℕ) :
    run step compiled.initial ω n (1 : Fin 2)
      = ∑ k ∈ Finset.range n, ((Δ : ℝ) * ((weights (n - 1 - k)).2 : ℝ)) * ω k := run_h_eq ω n

example (law : Measure ℝ) {v : ℝ≥0} (h : SubGaussianLaw law v) {B q : ℝ} (hB : 0 ≤ B)
    (n : ℕ) (hq : 2 * Real.exp (-B ^ 2 / (2 * ((Δ : ℝ) ^ 2 * v
      * ∑ k ∈ Finset.range n, (weight k : ℝ) ^ 2))) ≤ q) :
    ExceedsAt step compiled.initial law n (exposureWithin B) q := exceeds_at h hB n hq

/-- The rational proxy serves a law of proxy `64` as it stands. -/
example (law : Measure ℝ) (h : SubGaussianLaw law 64) :
    ExceedsAt step compiled.initial law 100 (exposureWithin 1)
      (2 * Real.exp (-1 ^ 2 / (2 * (proxy 64 100 : ℝ)))) :=
  exceeds_at_proxy h zero_le_one 100 le_rfl

example (law : Measure ℝ) (h : SubGaussianLaw law 64) :
    AtEveryMark step compiled.initial law 256 (exposureWithin 1) (1/100) :=
  exceeds_at_each_mark_year h

/-! ### The refutation and the Gaussian in both classes -/

example : step compiled.initial 0 = compiled.initial := step_zero_fixed
example : ¬ exposureWithin 1 (step compiled.initial 512) :=
  step_big_breaches 512 (by norm_num [Δ])
example : ¬ SubGaussianLaw (threePoint (64 / (2 * 257 ^ 2)) 257) 64 :=
  threePoint_not_subGaussian
example : ¬ ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/10) :=
  breach_within_year_tenth_refuted
example : ¬ ∀ law : Measure ℝ, TwoMomentLaw law 64 →
    BreachWithin step compiled.initial law 256 (exposureWithin 1) (1/5) :=
  breach_within_year_fifth_refuted
example : TwoMomentLaw (gaussianReal 0 64) 64 := (gaussian_in_both_classes 64).1
example : SubGaussianLaw (gaussianReal 0 64) 64 := (gaussian_in_both_classes 64).2

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.step_s'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms step_s
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.step_h'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms step_h
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.measurable_step'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms measurable_step
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.exposureWithin_iff_obs'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exposureWithin_iff_obs
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.energy_step_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms energy_step_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.expected_energy_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms expected_energy_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.expected_energy_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms expected_energy_le
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.geomSum_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms geomSum_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.breach_within'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breach_within
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.breach_within_year'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breach_within_year
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.expected_energy_year'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms expected_energy_year
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.run_s_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms run_s_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.run_h_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms run_h_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.proxyIter_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms proxyIter_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.proxyRec_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms proxyRec_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.proxy_cast'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms proxy_cast
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.proxy_mono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms proxy_mono
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.proxy_256_le'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms proxy_256_le
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.exceeds_at'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exceeds_at
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.exceeds_at_proxy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exceeds_at_proxy
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.exceeds_at_each_mark_year'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exceeds_at_each_mark_year
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.step_zero_fixed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms step_zero_fixed
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.step_big_breaches'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms step_big_breaches
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.threePoint_not_subGaussian'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms threePoint_not_subGaussian
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.breach_within_year_tenth_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breach_within_year_tenth_refuted
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.breach_within_year_fifth_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms breach_within_year_fifth_refuted
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadStepped.gaussian_in_both_classes'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms gaussian_in_both_classes

end Gimle.Forseti.Tests.HedgedSpreadStepped
