module

public import Gimle.Forseti.Examples.RobustCall

/-! Coverage for the at-the-money call hedged under a two percent band.

Pinned here: the data of the example, the two bands and the up-weight `1/2` of both; the
claim forms `covered`, `covered_from_premium` and `not_from_seven_halves` unfolded to their
`Covers` statements, with the initial wealth `7/2` below the price and the premium
`3555/1000` above it; the opening hedge ratio as the first position of the hedge, bracketed
by decimals; the put and the straddle covered like the call, and the straddle's price twice
the call's; the zigzag returns, inside the wide band and outside the narrow one, and the
recursion of the zigzag spot; the two sides of the narrow hedge, its price and its shortfall
on the zigzag path, with the refutation `narrow_hedge_not_within_four` as a claim form; the
price tables, each as the shape of its theorem and bracketed by decimals; and the axiom
policy, asserted with `#guard_msgs`.
-/

@[expose] public section

namespace Gimle.Forseti.Tests.RobustCall

open Gimle.Forseti.Hedging
open Gimle.Forseti.Examples.RobustCall

/-! ### The stable interface -/

example : strike = 100 := rfl
example : spot = 100 := rfl
example : steps = 20 := rfl

example : wide = Band.ofRat (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num) := rfl
example : narrow = Band.ofRat (1 / 100) (1 / 100) (by norm_num) (by norm_num) (by norm_num) :=
  rfl

example : wide.u = 1 / 50 ∧ wide.d = 1 / 50 := by norm_num [wide, Band.ofRat]
example : narrow.u = 1 / 100 ∧ narrow.d = 1 / 100 := by norm_num [narrow, Band.ofRat]

/-- The two ends of each band are symmetric, so the up-weight is `1/2`. -/
example : wide.q = 1 / 2 := by norm_num [Band.q, wide, Band.ofRat]
example : narrow.q = 1 / 2 := by norm_num [Band.q, narrow, Band.ofRat]

/-- The named data is the data of the stated theorems. -/
example : price wide (call strike) steps spot = price wide (call 100) 20 100 := by
  norm_num [strike, spot, steps]

/-! ### The call is covered from its price -/

example := (price_wide : price wide (call 100) 20 100 = _)

example : Covers wide (call 100) 20 (hedge wide (call 100) 20) (price wide (call 100) 20 100)
    100 := covered

example : Covers wide (call 100) 20 (hedge wide (call 100) 20) (3555 / 1000) 100 :=
  covered_from_premium

example : ∀ δ : ℕ → ℝ → ℝ, ¬ Covers wide (call 100) 20 δ (7 / 2) 100 := not_from_seven_halves

/-- The initial wealth `3.5`, from which no spot-feedback strategy covers, lies below the price,
and the premium `3.555`, the price rounded up to three places, from which the hedge covers,
lies above it. -/
example : (7 / 2 : ℝ) < price wide (call 100) 20 100 := by
  rw [price_wide]; norm_num

example : price wide (call 100) 20 100 < (3555 / 1000 : ℝ) := by
  rw [price_wide]; norm_num

/-- The hedge opens with the binomial hedge ratio with `20` steps to go, about `0.5176`. -/
example : hedge wide (call 100) 20 0 100 = delta wide (call 100) 19 100 := rfl

example := (opening_ratio : delta wide (call 100) 19 100 = _)

example : 0.5176 < hedge wide (call 100) 20 0 100 ∧ hedge wide (call 100) 20 0 100 < 0.5177 := by
  rw [show hedge wide (call 100) 20 0 100 = delta wide (call 100) 19 100 from rfl,
    opening_ratio]
  norm_num

/-- The hedge covers the call from any larger initial wealth too. -/
example : Covers wide (call 100) 20 (hedge wide (call 100) 20) 4 100 :=
  covered_from_premium.mono (by norm_num)

/-- The put and the straddle are covered like the call. -/
example : Covers wide (put 100) 20 (hedge wide (put 100) 20) (price wide (put 100) 20 100)
    100 := covers_hedge wide (put_convexOn 100) 20 (by norm_num)

example : Covers wide (straddle 100) 20 (hedge wide (straddle 100) 20)
    (price wide (straddle 100) 20 100) 100 :=
  covers_hedge wide (straddle_convexOn 100) 20 (by norm_num)

example : price wide (put 100) 20 100 = price wide (call 100) 20 100 := put_eq_call

/-- The straddle is the put and the call together, and so is priced at twice the call. -/
example : price wide (straddle 100) 20 100 = 2 * price wide (call 100) 20 100 := by
  rw [price_straddle, price_wide]; norm_num

/-! ### The zigzag path -/

example : zigzag 0 = 1 / 50 := by decide +kernel
example : zigzag 1 = -(1 / 50) := by decide +kernel
example : zigzag 19 = -(1 / 50) := by decide +kernel

example : ∀ k < 20, -(1 / 50 : ℚ) ≤ zigzag k ∧ zigzag k ≤ 1 / 50 := zigzag_inBand

/-- The zigzag leaves the narrow band: its first return is above `1/100`. -/
example : ¬ ∀ k < 20, -(1 / 100 : ℚ) ≤ zigzag k ∧ zigzag k ≤ 1 / 100 := by
  intro h
  have := (h 0 (by norm_num)).2
  revert this
  decide +kernel

example : zigzagSpot 0 = 100 := rfl
example (k : ℕ) : zigzagSpot (k + 1) = zigzagSpot k * (1 + zigzag k) := rfl

/-- Up two percent, then down two percent. -/
example : zigzagSpot 2 = 100 * (51 / 50) * (49 / 50) := by decide +kernel

example := (zigzag_ends : zigzagSpot 20 = _)

example : 99.6007 < zigzagSpot 20 ∧ zigzagSpot 20 < 99.6008 := by
  rw [zigzag_ends]; norm_num

/-! ### The narrow hedge on the wide band -/

example := (price_narrow : price narrow (call 100) 20 100 = _)

example : 1.7702 < price narrow (call 100) 20 100 ∧ price narrow (call 100) 20 100 < 1.7703 := by
  rw [price_narrow]; norm_num

example := (zigzag_shortfall : wealth (hedge narrow (call 100) 20)
    (price narrow (call 100) 20 100) (fun k => (zigzagSpot k : ℝ)) 20
      - call 100 (zigzagSpot 20) = _)

/-- The narrow hedge ends between `4.1129` and `4.1130` below the payoff on the zigzag. -/
example : -4.1130 < wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
      (fun k => (zigzagSpot k : ℝ)) 20 - call 100 (zigzagSpot 20) ∧
    wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
      (fun k => (zigzagSpot k : ℝ)) 20 - call 100 (zigzagSpot 20) < -4.1129 := by
  rw [zigzag_shortfall]; norm_num

example : ¬ ∀ S : ℕ → ℝ, S 0 = 100 → (∀ k < 20, wide.InBand (S k) (S (k + 1))) →
    -4 ≤ wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100) S 20
      - call 100 (S 20) := narrow_hedge_not_within_four

/-! ### The tables -/

example : 3.5548 < price wide (call 100) 20 100 ∧ price wide (call 100) 20 100 < 3.5549 := by
  rw [price_wide]; norm_num

/-- The band of three percent. -/
def band3 : Band := Band.ofRat (3 / 100) (3 / 100) (by norm_num) (by norm_num) (by norm_num)

example := (price_three_percent : price band3 (call 100) 20 100 = _)
example : 5.3506 < price band3 (call 100) 20 100 ∧ price band3 (call 100) 20 100 < 5.3507 := by
  rw [show price band3 (call 100) 20 100 = _ from price_three_percent]; norm_num

example : price wide (call 100) 5 100 = 93725003 / 50000000 := price_five_days
example := (price_sixty_days : price wide (call 100) 60 100 = _)
example : 6.1921 < price wide (call 100) 60 100 ∧ price wide (call 100) 60 100 < 6.1922 := by
  rw [price_sixty_days]; norm_num

example := (price_year : price wide (call 100) 250 100 = _)
example : 12.5704 < price wide (call 100) 250 100 ∧ price wide (call 100) 250 100 < 12.5705 := by
  rw [price_year]; norm_num

example := (price_straddle : price wide (straddle 100) 20 100 = _)
example : 7.1097 < price wide (straddle 100) 20 100 ∧ price wide (straddle 100) 20 100 < 7.1098 :=
  by rw [price_straddle]; norm_num

/-- The price grows with the horizon and with the width of the band, in the tables. -/
example : price wide (call 100) 5 100 < price wide (call 100) 20 100 := by
  rw [price_five_days, price_wide]; norm_num

example : price wide (call 100) 20 100 < price wide (call 100) 60 100 := by
  rw [price_wide, price_sixty_days]; norm_num

example : price wide (call 100) 60 100 < price wide (call 100) 250 100 := by
  rw [price_sixty_days, price_year]; norm_num

example : price narrow (call 100) 20 100 < price wide (call 100) 20 100 := by
  rw [price_narrow, price_wide]; norm_num

/-! ### Axiom policy -/

/--
info: 'Gimle.Forseti.Examples.RobustCall.price_wide'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_wide
/--
info: 'Gimle.Forseti.Examples.RobustCall.covered'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms covered
/--
info: 'Gimle.Forseti.Examples.RobustCall.covered_from_premium'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms covered_from_premium
/--
info: 'Gimle.Forseti.Examples.RobustCall.not_from_seven_halves'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms not_from_seven_halves
/--
info: 'Gimle.Forseti.Examples.RobustCall.opening_ratio'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms opening_ratio
/--
info: 'Gimle.Forseti.Examples.RobustCall.zigzag_shortfall'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms zigzag_shortfall
/--
info: 'Gimle.Forseti.Examples.RobustCall.narrow_hedge_not_within_four'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms narrow_hedge_not_within_four
/--
info: 'Gimle.Forseti.Examples.RobustCall.price_year'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_year
/--
info: 'Gimle.Forseti.Examples.RobustCall.put_eq_call'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms put_eq_call
/--
info: 'Gimle.Forseti.Examples.RobustCall.price_narrow'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_narrow
/--
info: 'Gimle.Forseti.Examples.RobustCall.zigzag_ends'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms zigzag_ends
/--
info: 'Gimle.Forseti.Examples.RobustCall.zigzag_inBand'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms zigzag_inBand
/--
info: 'Gimle.Forseti.Examples.RobustCall.price_three_percent'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_three_percent
/--
info: 'Gimle.Forseti.Examples.RobustCall.price_five_days'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_five_days
/--
info: 'Gimle.Forseti.Examples.RobustCall.price_sixty_days'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_sixty_days
/--
info: 'Gimle.Forseti.Examples.RobustCall.price_straddle'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms price_straddle

end Gimle.Forseti.Tests.RobustCall
