module

public import Gimle.Forseti.Hedging

/-! Coverage for model-free super-hedging under a per-step move band.

Pinned here: the defining equations of the binomial price and of the wealth recursion, by
`rfl`; the claim forms `Band.InBand`, `Covers` and `Extreme`, unfolded; the band
`[S (1 - 1/4), S (1 + 1/2)]`, whose up-weight is `1/3` and for which the fair-bet identity
holds; the identity `price b id 2 S = S`, the fair bet applied twice; the super-hedge
`covers_hedge` on the call payoff `max (S - 1) 0` at spot `1` over three steps; the
monotonicity of `Covers` in the initial wealth, for any strategy; the lower bound
`not_covers_of_lt` on a one-step identity payoff started below its price; the payoffs
`call`, `put` and `straddle` with their convexity; the closed form `price_eq_sum` at one
step; the exact layer over `ℚ`, evaluated by the kernel, and its agreement with the real
definitions; and the axiom policy, asserted with `#guard_msgs`.
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

/-- The same on the concrete band, for the price with one step to go at spot `1`. -/
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

/-! ### Payoffs and the closed form -/

section Payoffs

example (K S : ℝ) : call K S = max (S - K) 0 := rfl
example (K S : ℝ) : put K S = max (K - S) 0 := rfl
example (K S : ℝ) : straddle K S = |S - K| := rfl

example (K : ℝ) : ConvexOn ℝ Set.univ (call K) := call_convexOn K
example (K : ℝ) : ConvexOn ℝ Set.univ (put K) := put_convexOn K
example (K : ℝ) : ConvexOn ℝ Set.univ (straddle K) := straddle_convexOn K

/-- The put and the straddle are covered like the call. -/
example : Covers band (put 1) 3 (hedge band (put 1) 3) (price band (put 1) 3 1) 1 :=
  covers_hedge band (put_convexOn 1) 3 one_pos

example : Covers band (straddle 1) 3 (hedge band (straddle 1) 3)
    (price band (straddle 1) 3 1) 1 :=
  covers_hedge band (straddle_convexOn 1) 3 one_pos

/-- The closed form at one step is the recursion. -/
example (b : Band) (g : ℝ → ℝ) (S : ℝ) :
    price b g 1 S = b.q * g (S * (1 + b.u)) + (1 - b.q) * g (S * (1 - b.d)) := by
  rw [price_eq_sum]
  simp [Finset.sum_range_succ]
  ring

end Payoffs

/-! ### The exact layer -/

section Exact

example : callQ 100 150 = 50 := by decide +kernel
example : putQ 100 150 = 0 := by decide +kernel
example : straddleQ 100 70 = 30 := by decide +kernel

/-- One step of a `2 %` band on both sides: the up-weight is `1/2`, so the call struck at
`100` from spot `100` is worth `1/2 * 2 + 1/2 * 0 = 1`. -/
example : priceQ (callQ 100) (1 / 50) (1 / 50) 1 100 = 1 := by decide +kernel

example : spotQ 100 (fun _ => 1 / 50) 0 = 100 := rfl
example (S₀ : ℚ) (r : ℕ → ℚ) (k : ℕ) : spotQ S₀ r (k + 1) = spotQ S₀ r k * (1 + r k) := rfl
example : spotQ 100 (fun _ => 1 / 50) 2 = 100 * (51 / 50) ^ 2 := by decide +kernel

example (g : ℚ → ℚ) (u d : ℚ) (n : ℕ) (S : ℚ) : priceQ g u d n S = sumQ g u d n S (n + 1) := rfl

example (g : ℚ → ℚ) (u d : ℚ) (n : ℕ) (S : ℚ) :
    deltaQ g u d n S
      = (priceQ g u d n (S * (1 + u)) - priceQ g u d n (S * (1 - d))) / (S * (u + d)) := rfl

example (g : ℚ → ℚ) (u d : ℚ) (N : ℕ) (S₀ : ℚ) (r : ℕ → ℚ) :
    wealthQ g u d N S₀ r 0 = priceQ g u d N S₀ := rfl

example (g : ℚ → ℚ) (u d : ℚ) (N : ℕ) (S₀ : ℚ) (r : ℕ → ℚ) (k : ℕ) :
    wealthQ g u d N S₀ r (k + 1)
      = wealthQ g u d N S₀ r k
        + deltaQ g u d (N - 1 - k) (spotQ S₀ r k) * (spotQ S₀ r (k + 1) - spotQ S₀ r k) := rfl

example (K S : ℚ) : call K S = callQ K S := call_cast K S
example (K S : ℚ) : put K S = putQ K S := put_cast K S
example (K S : ℚ) : straddle K S = straddleQ K S := straddle_cast K S

/-- The real price of the call on a rational band is the rational price, which the kernel
evaluates. -/
example :
    price (Band.ofRat (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num))
        (call ((100 : ℚ) : ℝ)) 1 ((100 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) := by
  rw [price_cast (fun S => call_cast 100 S)]
  exact_mod_cast (by decide +kernel : priceQ (callQ 100) (1 / 50) (1 / 50) 1 100 = 1)

/-- The hedged wealth on a rational band along a rational path is the rational wealth. -/
example {g : ℝ → ℝ} {gQ : ℚ → ℚ} (hg : ∀ x : ℚ, g x = gQ x) (r : ℕ → ℚ) :
    wealth (hedge (Band.ofRat (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num)) g 2)
        (price (Band.ofRat (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num)) g 2
          ((100 : ℚ) : ℝ))
        (fun k => ((spotQ 100 r k : ℚ) : ℝ)) 2
      = ((wealthQ gQ (1 / 50) (1 / 50) 2 100 r 2 : ℚ) : ℝ) :=
  wealth_hedge_cast hg (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num) 2 100 r 2

/-- A return inside `[-d, u]` is a move inside the band. -/
example : band.InBand 1 (1 * (1 + 1 / 4)) :=
  inBand_of_return band one_pos ⟨by norm_num [band], by norm_num [band]⟩

/-- Rational returns inside `[-d, u]` keep the rational spot in the band, step by step. -/
example (hr : ∀ k < 2, -(1 / 50 : ℚ) ≤ (fun _ : ℕ => (1 / 50 : ℚ)) k
      ∧ (fun _ : ℕ => (1 / 50 : ℚ)) k ≤ 1 / 50) :
    ∀ k < 2, (Band.ofRat (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num)).InBand
      ((spotQ 100 (fun _ => 1 / 50) k : ℚ) : ℝ) ((spotQ 100 (fun _ => 1 / 50) (k + 1) : ℚ) : ℝ) :=
  spotQ_inBand (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr

end Exact

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

/--
info: 'Gimle.Forseti.Hedging.price_eq_sum'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_eq_sum
/--
info: 'Gimle.Forseti.Hedging.price_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_cast
/--
info: 'Gimle.Forseti.Hedging.wealth_hedge_cast'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wealth_hedge_cast

end Gimle.Forseti.Tests.Hedging
