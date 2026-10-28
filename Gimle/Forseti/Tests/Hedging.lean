module

public import Gimle.Forseti.Hedging

/-! Coverage for model-free super-hedging under a daily move band.

Pinned here: the defining equations of the binomial price and of the wealth recursion, by
`rfl`; the claim forms `Band.InBand`, `Covers` and `Extreme`, unfolded; the band
`[S (1 - 1/4), S (1 + 1/2)]`, whose up-weight is `1/3` and for which the fair-bet identity
holds; the identity `price b id 2 S = S`, the fair bet applied twice; the super-hedge
`covers_hedge` on the call payoff `max (S - 1) 0` at spot `1` over three steps, and its
monotonicity in the initial wealth; the lower bound `not_covers_of_lt` on a one-step
identity payoff started below its price; and the axiom policy, asserted with
`#guard_msgs`.
-/

@[expose] public section

namespace Gimle.Forseti.Tests.Hedging

open Gimle.Forseti.Hedging

/-! ### The stable interface -/

section Definitions

variable (b : Band) (g : ℝ → ℝ) (n : ℕ) (S S' : ℝ)

example : price b g 0 S = g S := rfl
example : price b g (n + 1) S
    = b.q * price b g n (S * (1 + b.u)) + (1 - b.q) * price b g n (S * (1 - b.d)) := rfl
example : delta b g n S
    = (price b g n (S * (1 + b.u)) - price b g n (S * (1 - b.d))) / (S * (b.u + b.d)) := rfl
example (N k : ℕ) : hedge b g N k S = delta b g (N - 1 - k) S := rfl
example : b.InBand S S' ↔ S * (1 - b.d) ≤ S' ∧ S' ≤ S * (1 + b.u) := Iff.rfl

end Definitions

section Wealth

variable (δ : ℕ → ℝ → ℝ) (w : ℝ) (path : ℕ → ℝ) (k : ℕ)

example : wealth δ w path 0 = w := rfl
example : wealth δ w path (k + 1) = wealth δ w path k + δ k (path k) * (path (k + 1) - path k) :=
  rfl

end Wealth

section ClaimForms

variable (b : Band) (g : ℝ → ℝ) (N : ℕ) (δ : ℕ → ℝ → ℝ) (w S₀ : ℝ) (path : ℕ → ℝ)

example : Covers b g N δ w S₀ ↔ ∀ S : ℕ → ℝ, S 0 = S₀ →
    (∀ k < N, b.InBand (S k) (S (k + 1))) → g (S N) ≤ wealth δ w S N := Iff.rfl
example : Extreme b path N ↔ ∀ k < N,
    path (k + 1) = path k * (1 + b.u) ∨ path (k + 1) = path k * (1 - b.d) := Iff.rfl

/-- More initial wealth keeps a covering. -/
example {w' : ℝ} (h : w ≤ w') (hc : Covers b g N δ w S₀) : Covers b g N δ w' S₀ := hc.mono h

/-- An extreme path from a positive spot stays in the band. -/
example (h0 : 0 < path 0) (h : Extreme b path N) :
    ∀ k < N, b.InBand (path k) (path (k + 1)) := h.inBand h0

end ClaimForms

/-! ### A concrete band

Up by at most one half, down by at most one quarter: the up-weight is `(1/4) / (3/4) = 1/3`.
-/

/-- The band `[S (1 - 1/4), S (1 + 1/2)]`. -/
noncomputable def band : Band := ⟨1 / 2, 1 / 4, by norm_num, by norm_num, by norm_num⟩

example : band.q = 1 / 3 := by norm_num [Band.q, band]

example : band.q * (1 + band.u) + (1 - band.q) * (1 - band.d) = 1 := band.fair

example : band.q * (band.u + band.d) = band.d := band.q_mul

example : 0 < band.q ∧ band.q < 1 := ⟨band.q_pos, band.q_lt_one⟩

/-- The fair bet applied twice: the payoff `id` has price equal to the spot. -/
example (b : Band) (S : ℝ) : price b id 2 S = S := by
  have h := b.fair
  simp only [price, id]
  linear_combination (S * (b.q * (1 + b.u) + (1 - b.q) * (1 - b.d)) + S) * h

/-- The same on the concrete band, for the value at spot `1` after one step. -/
example : price band id 1 1 = 1 := by
  norm_num [price, Band.q, band]

/-! ### The super-hedge -/

/-- The call payoff at strike one is convex. -/
theorem convexOn_call_one : ConvexOn ℝ Set.univ (fun S : ℝ => max (S - 1) 0) := by
  have h1 : ConvexOn ℝ Set.univ (fun S : ℝ => S - 1) :=
    ((convexOn_id convex_univ).add_const (-1)).congr (fun x _ => by simp [sub_eq_add_neg])
  exact h1.sup (convexOn_const 0 convex_univ)

/-- Re-hedging a call at the binomial ratio once a step, from the binomial price, covers it on
every three-step path whose moves stay in the band. -/
example : Covers band (fun S : ℝ => max (S - 1) 0) 3
    (hedge band (fun S : ℝ => max (S - 1) 0) 3)
    (price band (fun S : ℝ => max (S - 1) 0) 3 1) 1 :=
  covers_hedge band convexOn_call_one 3 one_pos

/-- A path that stays in the band is covered: the all-up path of the same band. -/
example : max (1 * (1 + band.u) ^ 3 - 1) 0
    ≤ wealth (hedge band (fun S : ℝ => max (S - 1) 0) 3)
        (price band (fun S : ℝ => max (S - 1) 0) 3 1) (fun k => (1 + band.u) ^ k) 3 := by
  have h := covers_hedge band convexOn_call_one 3 one_pos
  have hpath := h (fun k => (1 + band.u) ^ k) (by simp)
    (fun k _ => by
      refine ⟨?_, ?_⟩
      · have h1 : 0 < (1 + band.u) ^ k := pow_pos (by linarith [band.u_pos]) k
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_left (by linarith [band.u_pos, band.d_pos]) h1.le
      · rw [pow_succ])
  simpa using hpath

/-! ### The lower bound -/

/-- Starting from zero below the one-step price of the identity payoff at spot one, no
spot-feedback strategy covers it. -/
example (δ : ℕ → ℝ → ℝ) : ¬ Covers band (fun S : ℝ => S) 1 δ 0 1 := by
  refine not_covers_of_lt band (fun S : ℝ => S) 1 one_pos ?_ δ
  norm_num [price, Band.q, band]

/-- Below the price some extreme path leaves the wealth short of the payoff. -/
example (δ : ℕ → ℝ → ℝ) :
    ∃ S : ℕ → ℝ, S 0 = 1 ∧ Extreme band S 1
      ∧ wealth δ 0 S 1 < (fun S : ℝ => S) (S 1) := by
  refine exists_extreme_shortfall band (fun S : ℝ => S) 1 δ 1 0 ?_
  norm_num [price, Band.q, band]

/-! ### Axiom policy -/

/--
info: 'Gimle.Forseti.Hedging.Band.q_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Band.q_mul
/--
info: 'Gimle.Forseti.Hedging.Band.fair' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Band.fair
/--
info: 'Gimle.Forseti.Hedging.price_convexOn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_convexOn
/--
info: 'Gimle.Forseti.Hedging.convex_le_chord'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms convex_le_chord
/--
info: 'Gimle.Forseti.Hedging.step_dominates'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms step_dominates
/--
info: 'Gimle.Forseti.Hedging.wealth_ge_price'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wealth_ge_price
/--
info: 'Gimle.Forseti.Hedging.covers_hedge'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms covers_hedge
/--
info: 'Gimle.Forseti.Hedging.Covers.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Covers.mono
/--
info: 'Gimle.Forseti.Hedging.Extreme.inBand'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Extreme.inBand
/--
info: 'Gimle.Forseti.Hedging.wealth_shift'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wealth_shift
/--
info: 'Gimle.Forseti.Hedging.exists_extreme_shortfall'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exists_extreme_shortfall
/--
info: 'Gimle.Forseti.Hedging.not_covers_of_lt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms not_covers_of_lt

end Gimle.Forseti.Tests.Hedging
