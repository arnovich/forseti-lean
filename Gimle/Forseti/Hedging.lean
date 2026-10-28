module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! Model-free super-hedging of a convex payoff under a daily move band.

A `Band` with up-move `u` and down-move `d` (`0 < u`, `0 < d < 1`) constrains one step of a
spot path: from `S` the next spot `S'` lies in `[S (1 - d), S (1 + u)]` (`Band.InBand`). No
probability is attached to the path. The weight `q = d / (u + d)` (`Band.q`) makes the two
ends of the band a fair bet, `q (1 + u) + (1 - q) (1 - d) = 1` (`Band.fair`); it is a
coefficient of the recursion below and is not the probability of anything.

`price b g n S` is the backward recursion of the payoff `g` over `n` steps: it is `g S` at
`n = 0`, and `q * price b g n (S (1 + u)) + (1 - q) * price b g n (S (1 - d))` at `n + 1`.
`delta b g n S` is the slope of the chord of `price b g n` between the two ends of the band
at `S`, the number of units held over a step with `n + 1` steps still to go. A strategy is a
function `δ k S` of the step `k` and the current spot `S` alone, and `wealth δ w S k` is the
wealth after `k` steps along the spot path `S` from initial wealth `w`, holding `δ j (S j)`
units over step `j`, with no interest and no cost. `Covers b g N δ w S₀` says that the
wealth ends at least at the payoff, `g (S N) ≤ wealth δ w S N`, on every path with
`S 0 = S₀` whose first `N` steps stay in the band.

* Convexity propagates (`price_convexOn`): if `g` is convex, so is `price b g n` for every
  `n`. A convex function lies below its chord (`convex_le_chord`).
* The upper bound (`step_dominates`, `wealth_ge_price`, `covers_hedge`): for a convex `g`, at
  a positive spot and for every move in the band, one hedged step dominates the next price,
  `price b g n S' ≤ price b g (n + 1) S + delta b g n S * (S' - S)`. Along any path in the
  band the wealth of the strategy `hedge b g N`, which holds `delta b g (N - 1 - k)` units
  over step `k`, started from `price b g N S₀`, never falls below the price with the steps
  still to go; at the end it covers the payoff. `Covers.mono` extends this to any larger
  initial wealth.
* The lower bound (`exists_extreme_shortfall`, `not_covers_of_lt`): for any payoff, any
  strategy and any initial wealth `w < price b g N S₀`, there is a path whose every step is
  to one end of the band (`Extreme`) and on which the wealth ends strictly short of the
  payoff, `wealth δ w S N < g (S N)`. The recursion chooses at each step the end whose price
  the strategy's wealth does not reach; the fair bet makes one of the two ends fail
  (`wealth_shift` moves the first step out of the wealth). An extreme path from a positive
  spot is a path in the band (`Extreme.inBand`), so from a positive spot no initial wealth
  below the price covers the payoff.

Together, for a convex payoff and a positive spot, `price b g N S₀` is the least initial
wealth from which some strategy of this form covers the payoff on every path in the band.

What is not claimed. The rate is zero: there is no interest, discounting or financing cost,
and trading is free. The upper bound is for convex payoffs; the lower bound uses no
convexity. The strategies in the lower bound are functions of the step and the current spot,
not of the path so far. The band is the same at every step and is a hypothesis of each claim,
never fitted to data; a path that leaves it is not covered. Nothing here has a probability,
a volatility or continuous trading: the spot moves in discrete steps and the position
changes once a step.
-/

@[expose] public section

namespace Gimle.Forseti.Hedging

/-- A band on one step's return: the next spot lies in `[S (1 - d), S (1 + u)]`. -/
structure Band where
  /-- The largest relative rise in one step. -/
  u : ℝ
  /-- The largest relative fall in one step. -/
  d : ℝ
  u_pos : 0 < u
  d_pos : 0 < d
  d_lt_one : d < 1

namespace Band

variable (b : Band)

/-- The up-weight that makes one step a fair bet: `q (1 + u) + (1 - q) (1 - d) = 1`. -/
noncomputable def q : ℝ := b.d / (b.u + b.d)

theorem ud_pos : 0 < b.u + b.d := by
  have := b.u_pos
  have := b.d_pos
  linarith

theorem q_pos : 0 < b.q := div_pos b.d_pos b.ud_pos

theorem q_lt_one : b.q < 1 := by
  rw [q, div_lt_one b.ud_pos]
  have := b.u_pos
  linarith

theorem q_nonneg : 0 ≤ b.q := b.q_pos.le

theorem one_sub_q_nonneg : 0 ≤ 1 - b.q := by
  have := b.q_lt_one
  linarith

/-- The up-weight times the width of the band is the down-move. -/
theorem q_mul : b.q * (b.u + b.d) = b.d := by
  have h := b.ud_pos.ne'
  rw [q]
  field_simp

/-- One step of the two ends of the band is a fair bet. -/
theorem fair : b.q * (1 + b.u) + (1 - b.q) * (1 - b.d) = 1 := by
  have h := b.ud_pos.ne'
  rw [q]
  field_simp
  ring

/-- One step's move stays inside the band. -/
def InBand (S S' : ℝ) : Prop := S * (1 - b.d) ≤ S' ∧ S' ≤ S * (1 + b.u)

/-- A spot that moves within the band from a positive spot is positive. -/
theorem pos_of_inBand {S S' : ℝ} (hS : 0 < S) (h : b.InBand S S') : 0 < S' :=
  lt_of_lt_of_le (mul_pos hS (by have := b.d_lt_one; linarith)) h.1

end Band

/-- The binomial price with `n` steps to go of the payoff `g`, at spot `S`. -/
noncomputable def price (b : Band) (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, S => g S
  | n + 1, S => b.q * price b g n (S * (1 + b.u)) + (1 - b.q) * price b g n (S * (1 - b.d))

/-- The hedge ratio with `n + 1` steps to go, at spot `S`: the slope of the chord of the price
with `n` steps to go between the two ends of the band. -/
noncomputable def delta (b : Band) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) : ℝ :=
  (price b g n (S * (1 + b.u)) - price b g n (S * (1 - b.d))) / (S * (b.u + b.d))

/-- Precomposition with `S ↦ S * c` keeps a function convex. -/
private theorem convexOn_comp_mul_right {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) (c : ℝ) :
    ConvexOn ℝ Set.univ (fun S => f (S * c)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := hf.2 (Set.mem_univ (x * c)) (Set.mem_univ (y * c)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  calc f ((a * x + b * y) * c) = f (a * (x * c) + b * (y * c)) := by ring_nf
    _ ≤ a * f (x * c) + b * f (y * c) := h

/-- Convexity of the payoff propagates backward through the price recursion. -/
theorem price_convexOn (b : Band) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (n : ℕ) :
    ConvexOn ℝ Set.univ (price b g n) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    have h1 := convexOn_comp_mul_right ih (1 + b.u)
    have h2 := convexOn_comp_mul_right ih (1 - b.d)
    have h := (h1.smul b.q_nonneg).add (h2.smul b.one_sub_q_nonneg)
    convert h using 1
    funext S
    simp only [Pi.add_apply, smul_eq_mul, price]

/-- A convex function lies below its chord. -/
theorem convex_le_chord {f : ℝ → ℝ} (hf : ConvexOn ℝ Set.univ f) {a c x : ℝ} (hac : a < c)
    (hx : a ≤ x) (hxc : x ≤ c) :
    f x ≤ f a + (f c - f a) / (c - a) * (x - a) := by
  have hca : 0 < c - a := by linarith
  set μ := (x - a) / (c - a) with hμ
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hca.le
  have hμ1 : μ ≤ 1 := by
    rw [hμ, div_le_one hca]
    linarith
  have hx' : x = (1 - μ) * a + μ * c := by
    rw [hμ]
    field_simp
    ring
  have h := hf.2 (Set.mem_univ a) (Set.mem_univ c) (by linarith : (0 : ℝ) ≤ 1 - μ) hμ0 (by ring)
  simp only [smul_eq_mul] at h
  calc f x = f ((1 - μ) * a + μ * c) := by rw [← hx']
    _ ≤ (1 - μ) * f a + μ * f c := h
    _ = f a + (f c - f a) / (c - a) * (x - a) := by
      rw [hμ]
      field_simp
      ring

/-- One hedged step dominates the next price, for every move in the band. -/
theorem step_dominates (b : Band) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (n : ℕ)
    {S S' : ℝ} (hS : 0 < S) (h : b.InBand S S') :
    price b g n S' ≤ price b g (n + 1) S + delta b g n S * (S' - S) := by
  have hf := price_convexOn b hg n
  have hu := b.u_pos
  have hd := b.d_pos
  have hac : S * (1 - b.d) < S * (1 + b.u) := by nlinarith
  have key := convex_le_chord hf hac h.1 h.2
  have hud := b.ud_pos.ne'
  have hud' : b.d + b.u ≠ 0 := by rw [add_comm]; exact hud
  have hS' := hS.ne'
  have hq := b.q_mul
  have hden : S * (1 + b.u) - S * (1 - b.d) = S * (b.u + b.d) := by ring
  rw [hden] at key
  calc price b g n S' ≤ _ := key
    _ = price b g (n + 1) S + delta b g n S * (S' - S) := by
        simp only [price, delta]
        field_simp
        linear_combination (S * (price b g n (S * (1 - b.d)) - price b g n (S * (1 + b.u)))) * hq

/-- Wealth along the path `S` from `w`, holding `δ k (S k)` units over step `k`. -/
noncomputable def wealth (δ : ℕ → ℝ → ℝ) (w : ℝ) (S : ℕ → ℝ) : ℕ → ℝ
  | 0 => w
  | k + 1 => wealth δ w S k + δ k (S k) * (S (k + 1) - S k)

/-- The binomial hedge over `N` steps: after step `k` there are `N - 1 - k` steps to go. -/
noncomputable def hedge (b : Band) (g : ℝ → ℝ) (N k : ℕ) (S : ℝ) : ℝ :=
  delta b g (N - 1 - k) S

/-- The strategy `δ`, started from wealth `w` at spot `S₀`, covers the payoff `g` over `N`
steps: on every path from `S₀` whose first `N` steps stay in the band, the wealth ends at
least at the payoff. -/
def Covers (b : Band) (g : ℝ → ℝ) (N : ℕ) (δ : ℕ → ℝ → ℝ) (w S₀ : ℝ) : Prop :=
  ∀ S : ℕ → ℝ, S 0 = S₀ → (∀ k < N, b.InBand (S k) (S (k + 1))) → g (S N) ≤ wealth δ w S N

/-- Wealth is monotone in the initial wealth. -/
private theorem wealth_mono (δ : ℕ → ℝ → ℝ) {w w' : ℝ} (h : w ≤ w') (S : ℕ → ℝ) :
    ∀ k, wealth δ w S k ≤ wealth δ w' S k
  | 0 => h
  | k + 1 => by
    have := wealth_mono δ h S k
    simp only [wealth]
    linarith

/-- More initial wealth keeps a covering. -/
theorem Covers.mono {b : Band} {g : ℝ → ℝ} {N : ℕ} {δ : ℕ → ℝ → ℝ} {w w' S₀ : ℝ}
    (h : w ≤ w') (hc : Covers b g N δ w S₀) : Covers b g N δ w' S₀ :=
  fun S h0 hband => (hc S h0 hband).trans (wealth_mono δ h S N)

/-- A path that stays in the band from a positive spot stays positive. -/
private theorem pos_along {b : Band} {S : ℕ → ℝ} {N : ℕ} (hpos : 0 < S 0)
    (hband : ∀ k < N, b.InBand (S k) (S (k + 1))) : ∀ k ≤ N, 0 < S k := by
  intro k
  induction k with
  | zero => intro _; exact hpos
  | succ k ih =>
    intro hk
    exact b.pos_of_inBand (ih (by omega)) (hband k (by omega))

/-- The invariant: the hedged wealth never falls below the price with the steps still to go. -/
theorem wealth_ge_price (b : Band) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (N : ℕ)
    (S : ℕ → ℝ) (hpos : 0 < S 0) (hband : ∀ k < N, b.InBand (S k) (S (k + 1))) :
    ∀ k ≤ N, price b g (N - k) (S k) ≤ wealth (hedge b g N) (price b g N (S 0)) S k := by
  intro k
  induction k with
  | zero => intro _; simp [wealth]
  | succ k ih =>
    intro hk
    have hk' : k < N := by omega
    have hsplit : N - k = (N - 1 - k) + 1 := by omega
    have hnext : N - (k + 1) = N - 1 - k := by omega
    have hdom := step_dominates b hg (N - 1 - k) (pos_along hpos hband k hk'.le) (hband k hk')
    rw [← hsplit] at hdom
    simp only [wealth, hedge]
    rw [hnext]
    have := ih hk'.le
    linarith

/-- The super-hedge: starting from the price, the re-hedged book covers a convex payoff on
every path inside the band. -/
theorem covers_hedge (b : Band) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (N : ℕ) {S₀ : ℝ}
    (hS₀ : 0 < S₀) : Covers b g N (hedge b g N) (price b g N S₀) S₀ := by
  intro S h0 hband
  subst h0
  have := wealth_ge_price b hg N S hS₀ hband N le_rfl
  simpa [price] using this

/-- Every move is to an end of the band. -/
def Extreme (b : Band) (S : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ k < N, S (k + 1) = S k * (1 + b.u) ∨ S (k + 1) = S k * (1 - b.d)

/-- A path of extreme moves from a positive spot is a path in the band. -/
theorem Extreme.inBand {b : Band} {S : ℕ → ℝ} {N : ℕ} (hS : 0 < S 0) (h : Extreme b S N) :
    ∀ k < N, b.InBand (S k) (S (k + 1)) := by
  have hpos : ∀ k ≤ N, 0 < S k := by
    intro k
    induction k with
    | zero => intro _; exact hS
    | succ k ih =>
      intro hk
      have hk' := ih (by omega)
      rcases h k (by omega) with e | e
      · rw [e]
        exact mul_pos hk' (by linarith [b.u_pos])
      · rw [e]
        exact mul_pos hk' (by linarith [b.d_lt_one])
  intro k hk
  have hk' := hpos k hk.le
  rcases h k hk with e | e
  · rw [e]
    exact ⟨mul_le_mul_of_nonneg_left (by linarith [b.u_pos, b.d_pos]) hk'.le, le_rfl⟩
  · rw [e]
    exact ⟨le_rfl, mul_le_mul_of_nonneg_left (by linarith [b.u_pos, b.d_pos]) hk'.le⟩

/-- The wealth after `n + 1` steps is the wealth after `n` steps of the shifted strategy and
path, started from the wealth after the first step. -/
theorem wealth_shift (δ : ℕ → ℝ → ℝ) (w : ℝ) (S : ℕ → ℝ) :
    ∀ n, wealth δ w S (n + 1)
      = wealth (fun k => δ (k + 1)) (w + δ 0 (S 0) * (S 1 - S 0)) (fun k => S (k + 1)) n
  | 0 => by simp [wealth]
  | n + 1 => by
    rw [wealth, wealth_shift δ w S n]
    rfl

/-- Below the price, no spot-feedback strategy covers the payoff on every extreme path: for
every strategy there is an extreme path on which the wealth ends short of the payoff. -/
theorem exists_extreme_shortfall (b : Band) (g : ℝ → ℝ) :
    ∀ (N : ℕ) (δ : ℕ → ℝ → ℝ) (S₀ w : ℝ), w < price b g N S₀ →
      ∃ S : ℕ → ℝ, S 0 = S₀ ∧ Extreme b S N ∧ wealth δ w S N < g (S N)
  | 0, δ, S₀, w, hw => ⟨fun _ => S₀, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), by
      simpa [wealth, price] using hw⟩
  | N + 1, δ, S₀, w, hw => by
    set c := S₀ * (1 + b.u) with hc
    set a := S₀ * (1 - b.d) with ha
    set wc := w + δ 0 S₀ * (c - S₀) with hwc
    set wa := w + δ 0 S₀ * (a - S₀) with hwa
    have hmix : b.q * wc + (1 - b.q) * wa = w := by
      rw [hwc, hwa, hc, ha]
      linear_combination (δ 0 S₀ * S₀) * b.fair
    have hcase : wc < price b g N c ∨ wa < price b g N a := by
      by_contra hcon
      simp only [not_or, not_lt] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have e1 := mul_le_mul_of_nonneg_left h1 b.q_nonneg
      have e2 := mul_le_mul_of_nonneg_left h2 b.one_sub_q_nonneg
      have : price b g (N + 1) S₀ = b.q * price b g N c + (1 - b.q) * price b g N a := rfl
      linarith
    rcases hcase with h | h
    · obtain ⟨T, hT0, hTx, hTw⟩ := exists_extreme_shortfall b g N (fun k => δ (k + 1)) c wc h
      refine ⟨fun k => Nat.casesOn k S₀ T, rfl, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => left; simp [hT0, hc]
        | succ k => exact hTx k (by omega)
      · rw [wealth_shift]
        simpa [hT0, hwc, hc] using hTw
    · obtain ⟨T, hT0, hTx, hTw⟩ := exists_extreme_shortfall b g N (fun k => δ (k + 1)) a wa h
      refine ⟨fun k => Nat.casesOn k S₀ T, rfl, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => right; simp [hT0, ha]
        | succ k => exact hTx k (by omega)
      · rw [wealth_shift]
        simpa [hT0, hwa, ha] using hTw

/-- From a positive spot, no initial wealth below the price covers the payoff: the extreme path
on which the wealth falls short is a path in the band. -/
theorem not_covers_of_lt (b : Band) (g : ℝ → ℝ) (N : ℕ) {S₀ w : ℝ} (hS₀ : 0 < S₀)
    (hw : w < price b g N S₀) (δ : ℕ → ℝ → ℝ) : ¬ Covers b g N δ w S₀ := by
  intro hc
  obtain ⟨S, h0, hext, hshort⟩ := exists_extreme_shortfall b g N δ S₀ w hw
  have hcover := hc S h0 (hext.inBand (by rw [h0]; exact hS₀))
  linarith

end Gimle.Forseti.Hedging
