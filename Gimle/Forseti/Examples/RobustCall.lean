module

public import Gimle.Forseti.Hedging

/-! The at-the-money call hedged over twenty steps, each moving the spot by at most two
percent.

What this module proves, for a call struck at `100`, started at the spot `100`, with `20`
steps. A step is read as one trading day in the showcase; the statements are about steps and
prove nothing about days.

* The binomial price of the call in the band of two percent is
  `177744620736998422379605070486628497811 / 50000000000000000000000000000000000000`,
  about `3.5548924` (`price_wide`): an exact rational, which the kernel evaluates and the cast
  lemmas of `Hedging` carry to the real price.
* Started from that price and re-hedged once a step at the binomial ratio, the book ends at
  least at the payoff of the call on every path whose steps stay in the band (`covered`), and
  so from any larger initial wealth, such as `3.555` (`covered_from_premium`).
* From `3.5` no spot-feedback strategy covers the call on every such path
  (`not_from_seven_halves`), whatever units it holds as a function of the step and the spot.
  The price is the exact threshold: `not_covers_of_lt` rules out every initial wealth below
  it, and `covered` covers from it.
* The hedge built for the band of one percent, started from its own price `1.7702479`
  (`price_narrow`), falls more than `4` short of the payoff on one path of the band of two
  percent (`narrow_hedge_not_within_four`): on the zigzag path, whose steps are inside the
  wider band, it ends `4.1129056` below the payoff, the exact rational of `zigzag_shortfall`.
* The price tables, each an exact rational checked by the kernel and quoted here rounded to
  four places. By band at `20` steps: `1.7702` at one percent, `3.5549` at two (`price_wide`)
  and `5.3506` at three (`price_three_percent`). By horizon in the band of two percent:
  `1.8745` at `5` steps (`price_five_days`), `3.5549` at `20`, `6.1922` at `60`
  (`price_sixty_days`) and `12.5705` at `250` (`price_year`). The put at the money costs what
  the call does (`put_eq_call`), and the straddle at the money, `7.1098` (`price_straddle`),
  twice that.

The model. A `Band` says that from the spot `S` the next spot lies in `[S (1 - d), S (1 + u)]`;
`wide` has `u = d = 1/50` and `narrow` has `u = d = 1/100`; `strike`, `spot` and `days` name the
data of the statements, which are written with their values. The rate is zero, trading is free,
and the position is changed once a step: a strategy holds `δ k S` units over step `k` at the
spot `S`. The price is the backward recursion `price` of `Hedging`, which weights each end of a
symmetric band by `1/2`; the weight is a coefficient of the recursion and not the probability
of anything. The call is convex on the whole real line, so `covers_hedge` applies to it.
`zigzag k` is the return `+1/50` at an even step and `-1/50` at an odd one, so the zigzag path
`zigzagSpot` moves the spot by the full two percent, up and down in turn; after `20` steps it
is at about `99.6007` (`zigzag_ends`). Its returns are inside `[-1/50, 1/50]`
(`zigzag_inBand`), so it is a path of the wide band (`spotQ_inBand`); they leave the band of one
percent, so the narrow hedge has no claim on it. The numbers come from the exact layer of
`Hedging`: `decide +kernel` evaluates the rational price, and the cast lemmas make it a value
of the real definitions.

What is not claimed. Nothing about markets: the band is a hypothesis of each claim, never
fitted to prices, and the module attaches no probability, volatility or distribution to a
path. The zigzag is one path chosen to refute a hedge, not a typical one. There is no
interest, financing, dividend or transaction cost, and no bid-offer spread: the rate is zero
and trading is free. The lower bound `not_from_seven_halves` is for strategies that are
functions of the step and the current spot, and says nothing about a strategy that also reads
the path so far. Nothing is continuous: the position changes once a step, and a path that
leaves the band is outside every claim.

Kernel time. `lake build Gimle.Forseti.Examples.RobustCall` takes about 6 s of wall time from a
clean module on the development machine. The two slowest theorems are `price_year`, the
`251`-term binomial sum of the `250` steps over `ℚ`, at about 3 s of kernel time, and
`zigzag_shortfall`, the hedged wealth over the `20` zigzag steps, at about 0.5 s; every other
theorem is checked in well under a second. No `maxRecDepth` option is needed, and the module
elaborates under Lean's default options.
-/

@[expose] public section

namespace Gimle.Forseti.Examples.RobustCall

open Gimle.Forseti.Hedging

/-! ### The data -/

/-- The wide band: each step moves the spot by at most two percent, up or down. -/
def wide : Band := Band.ofRat (1 / 50) (1 / 50) (by norm_num) (by norm_num) (by norm_num)

/-- The narrow band: each step moves the spot by at most one percent, up or down. -/
def narrow : Band := Band.ofRat (1 / 100) (1 / 100) (by norm_num) (by norm_num) (by norm_num)

/-- The strike of the call. -/
def strike : ℚ := 100

/-- The spot at which the hedge starts. -/
def spot : ℚ := 100

/-- The number of steps. -/
def days : ℕ := 20

/-- A price of the call at spot `100` computed over `ℚ`, which the kernel evaluates, is the
price of the real recursion on the rational band. -/
private theorem price_call {u d : ℚ} (hu : 0 < u) (hd : 0 < d) (hd1 : d < 1) {n : ℕ} {p : ℚ}
    (h : priceQ (callQ 100) u d n 100 = p) :
    price (Band.ofRat u d hu hd hd1) (call 100) n 100 = p := by
  have := price_cast (fun S => call_cast 100 S) u d hu hd hd1 n 100
  rw [h] at this
  simpa using this

/-! ### The call is covered from its price -/

/-- The price of the call at the money over `20` steps in the wide band. -/
theorem price_wide : price wide (call 100) 20 100
    = 177744620736998422379605070486628497811 / 50000000000000000000000000000000000000 := by
  have h := price_call (u := 1 / 50) (d := 1 / 50) (by norm_num) (by norm_num) (by norm_num)
    (n := 20)
    (p := 177744620736998422379605070486628497811 / 50000000000000000000000000000000000000)
    (by decide +kernel)
  push_cast at h
  exact h

/-- Re-hedged at the binomial ratio once a step and started from the price, the call is covered
on every path whose twenty steps stay in the wide band. -/
theorem covered : Covers wide (call 100) 20 (hedge wide (call 100) 20)
    (price wide (call 100) 20 100) 100 :=
  covers_hedge wide (call_convexOn 100) 20 (by norm_num)

/-- The same hedge covers the call from `3.555`, which is above the price. -/
theorem covered_from_premium : Covers wide (call 100) 20 (hedge wide (call 100) 20)
    (3555 / 1000) 100 :=
  covered.mono (by rw [price_wide]; norm_num)

/-- From `3.5`, which is below the price, no spot-feedback strategy covers the call on every
path of the wide band. -/
theorem not_from_seven_halves : ∀ δ, ¬ Covers wide (call 100) 20 δ (7 / 2) 100 :=
  fun δ => not_covers_of_lt wide (call 100) 20 (by norm_num)
    (by rw [price_wide]; norm_num) δ

/-! ### The hedge built for the narrow band -/

/-- Returns of up two percent and down two percent in turn. -/
def zigzag (k : ℕ) : ℚ := if k % 2 = 0 then 1 / 50 else -(1 / 50)

/-- The first twenty zigzag returns lie within two percent. -/
theorem zigzag_inBand : ∀ k < 20, -(1 / 50 : ℚ) ≤ zigzag k ∧ zigzag k ≤ 1 / 50 := by
  decide +kernel

/-- The spot after the zigzag returns, from `100`. -/
def zigzagSpot : ℕ → ℚ := spotQ 100 zigzag

/-- The spot after twenty zigzag returns is about `99.6007`. -/
theorem zigzag_ends : zigzagSpot 20
    = 9498664782766088680076250281225001 / 95367431640625000000000000000000 := by
  decide +kernel

/-- The price of the call over `20` steps in the narrow band. -/
theorem price_narrow : price narrow (call 100) 20 100
    = 92811975455024694792484925524301923173991811
      / 52428800000000000000000000000000000000000000 := by
  have h := price_call (u := 1 / 100) (d := 1 / 100) (by norm_num) (by norm_num) (by norm_num)
    (n := 20)
    (p := 92811975455024694792484925524301923173991811
      / 52428800000000000000000000000000000000000000)
    (by decide +kernel)
  push_cast at h
  exact h

/-- Hedged for the narrow band from its price, the book ends about `4.1129` below the call
payoff on the zigzag path. -/
theorem zigzag_shortfall :
    wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100)
        (fun k => (zigzagSpot k : ℝ)) 20 - call 100 (zigzagSpot 20)
      = -215634705196340256271204096412694900382147731
        / 52428800000000000000000000000000000000000000 := by
  unfold narrow zigzagSpot
  have hw := wealth_hedge_cast (fun S => call_cast 100 S) (1 / 100) (1 / 100) (by norm_num)
    (by norm_num) (by norm_num) 20 100 zigzag 20
  have hc := call_cast 100 (spotQ 100 zigzag 20)
  simp only [Rat.cast_ofNat] at hw hc
  rw [hw, hc]
  have hk : wealthQ (callQ 100) (1 / 100) (1 / 100) 20 100 zigzag 20
      - callQ 100 (spotQ 100 zigzag 20)
      = -215634705196340256271204096412694900382147731
        / 52428800000000000000000000000000000000000000 := by
    decide +kernel
  have := congrArg (Rat.cast : ℚ → ℝ) hk
  push_cast at this
  exact this

/-- The hedge built for the narrow band is not within `4` of covering the call on the wide band:
on the zigzag path, whose returns stay within two percent, it ends more than `4` below the
payoff. -/
theorem narrow_hedge_not_within_four :
    ¬ ∀ S : ℕ → ℝ, S 0 = 100 → (∀ k < 20, wide.InBand (S k) (S (k + 1))) →
      -4 ≤ wealth (hedge narrow (call 100) 20) (price narrow (call 100) 20 100) S 20
        - call 100 (S 20) := by
  intro h
  have h0 : ((zigzagSpot 0 : ℚ) : ℝ) = 100 := by norm_num [zigzagSpot, spotQ]
  have key := h (fun k => (zigzagSpot k : ℝ)) h0
    (spotQ_inBand (S₀ := 100) (r := zigzag) (N := 20) (1 / 50) (1 / 50) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) zigzag_inBand)
  rw [zigzag_shortfall] at key
  norm_num at key

/-! ### The tables -/

/-- The price of the call over `20` steps in the band of three percent. -/
theorem price_three_percent :
    price (Band.ofRat (3 / 100) (3 / 100) (by norm_num) (by norm_num) (by norm_num))
        (call 100) 20 100
      = 280527566475729694345251341767966396584848211
        / 52428800000000000000000000000000000000000000 := by
  have h := price_call (u := 3 / 100) (d := 3 / 100) (by norm_num) (by norm_num) (by norm_num)
    (n := 20)
    (p := 280527566475729694345251341767966396584848211
      / 52428800000000000000000000000000000000000000)
    (by decide +kernel)
  push_cast at h
  exact h

/-- The price of the call in the wide band over `5` steps. -/
theorem price_five_days : price wide (call 100) 5 100 = 93725003 / 50000000 := by
  have h := price_call (u := 1 / 50) (d := 1 / 50) (by norm_num) (by norm_num) (by norm_num)
    (n := 5) (p := 93725003 / 50000000) (by decide +kernel)
  push_cast at h
  exact h

/-- The price of the call in the wide band over `60` steps. -/
theorem price_sixty_days : price wide (call 100) 60 100
    = 7740204077225901392687693475243966362502059724658876011196246631841053915910599539128475389852377431069849107037108161
      / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have h := price_call (u := 1 / 50) (d := 1 / 50) (by norm_num) (by norm_num) (by norm_num)
    (n := 60)
    (p := 7740204077225901392687693475243966362502059724658876011196246631841053915910599539128475389852377431069849107037108161
      / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
    (by decide +kernel)
  push_cast at h
  exact h

/-- The price of the call in the wide band over `250` steps. -/
theorem price_year : price wide (call 100) 250 100
    = 196413508890001877601402742993487333277858946908522069175178043484567127576519859534590792302391070299030794728454628793837041821746140280006170792998685767555590595230128299318609608756512450314566141046060150783276474867823616570105998802331390541283114832645034405304649827327519541122234688776011898030811704154004680321738106762452721922389184890645756616334287236705603397630866699433331704849696012278408182800686536437545362107535114619263555173531394317529799040037458290245565244608216209
      / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have h := price_call (u := 1 / 50) (d := 1 / 50) (by norm_num) (by norm_num) (by norm_num)
    (n := 250)
    (p := 196413508890001877601402742993487333277858946908522069175178043484567127576519859534590792302391070299030794728454628793837041821746140280006170792998685767555590595230128299318609608756512450314566141046060150783276474867823616570105998802331390541283114832645034405304649827327519541122234688776011898030811704154004680321738106762452721922389184890645756616334287236705603397630866699433331704849696012278408182800686536437545362107535114619263555173531394317529799040037458290245565244608216209
      / 15625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
    (by decide +kernel)
  push_cast at h
  exact h

/-- The put at the money is priced like the call at the money: the band is symmetric. -/
theorem put_eq_call : price wide (put 100) 20 100 = price wide (call 100) 20 100 := by
  have h := price_cast (fun S => put_cast 100 S) (1 / 50) (1 / 50) (by norm_num) (by norm_num)
    (by norm_num) 20 100
  have k : priceQ (putQ 100) (1 / 50) (1 / 50) 20 100
      = 177744620736998422379605070486628497811 / 50000000000000000000000000000000000000 := by
    decide +kernel
  rw [k] at h
  rw [price_wide]
  push_cast at h
  exact h

/-- The price of the straddle at the money over `20` steps in the wide band. -/
theorem price_straddle : price wide (straddle 100) 20 100
    = 177744620736998422379605070486628497811 / 25000000000000000000000000000000000000 := by
  have h := price_cast (fun S => straddle_cast 100 S) (1 / 50) (1 / 50) (by norm_num)
    (by norm_num) (by norm_num) 20 100
  have k : priceQ (straddleQ 100) (1 / 50) (1 / 50) 20 100
      = 177744620736998422379605070486628497811 / 25000000000000000000000000000000000000 := by
    decide +kernel
  rw [k] at h
  push_cast at h
  exact h

end Gimle.Forseti.Examples.RobustCall
