module

public import Gimle.Forseti.Hedging
public import Gimle.Forseti.Stepped

/-! The hedged book of `Gimle.Forseti.Hedging` as a stepped system driven by simple returns.

The state of `book δ` is the step, the spot and the wealth, and its input is the simple return
`r` of the step: one step multiplies the spot by `1 + r` and adds `δ k S * (S * r)` to the
wealth, the position held over the step times the move. So `Stepped.run (book δ) (0, S₀, w) ω`,
the iteration of `Gimle.Forseti.Stepped`, is the book along the return path `ω` (`run_book`):
the step count, the spot path `spotOf S₀ ω` and the wealth of `δ` along that path. `Covers`
then gives a safety statement about this driven iteration (`covers_run`): from a positive spot,
if the first `N` returns lie in `[-d, u]`, the payoff of the final spot is at most the final
wealth.

What is not claimed. The return path is a given sequence: no probability and no law is
attached to it, and nothing here uses the measures of `Stepped`, only its iteration
`Stepped.run`.
-/

@[expose] public section

namespace Gimle.Forseti.Hedging

/-- One step of the hedged book. The state is `(step, spot, wealth)` and the input is the step
return `r`: the spot is multiplied by `1 + r`, and the wealth gains the units `δ k S` held over
step `k` at spot `S` times the move `S * r`. -/
def book (δ : ℕ → ℝ → ℝ) : ℕ × ℝ × ℝ → ℝ → ℕ × ℝ × ℝ :=
  fun x r => (x.1 + 1, x.2.1 * (1 + r), x.2.2 + δ x.1 x.2.1 * (x.2.1 * r))

/-- The spot after `k` steps from `S₀` with the step returns `ω`. -/
noncomputable def spotOf (S₀ : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => S₀
  | k + 1 => spotOf S₀ ω k * (1 + ω k)

/-- The stepped run of the book along the returns `ω` is the step count, the spot path
`spotOf S₀ ω` and the wealth of the strategy `δ` along that path. -/
theorem run_book (δ : ℕ → ℝ → ℝ) (S₀ w : ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    Stepped.run (book δ) (0, S₀, w) ω n
      = (n, spotOf S₀ ω n, wealth δ w (spotOf S₀ ω) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Stepped.run_succ, ih]
    simp only [book, spotOf, wealth, Prod.mk.injEq, true_and]
    ring

/-- A covering strategy is safe for the driven book: from a positive spot, along returns that
stay in `[-d, u]` for the first `N` steps, the payoff of the final spot of the stepped run is
at most its final wealth. -/
theorem covers_run {b : Band} {g : ℝ → ℝ} {N : ℕ} {δ : ℕ → ℝ → ℝ} {w S₀ : ℝ}
    (h : Covers b g N δ w S₀) (hS₀ : 0 < S₀) (ω : ℕ → ℝ)
    (hω : ∀ k < N, -b.d ≤ ω k ∧ ω k ≤ b.u) :
    g (Stepped.run (book δ) (0, S₀, w) ω N).2.1 ≤ (Stepped.run (book δ) (0, S₀, w) ω N).2.2 := by
  have hpos : ∀ k ≤ N, 0 < spotOf S₀ ω k := by
    intro k
    induction k with
    | zero => intro _; exact hS₀
    | succ k ih =>
      intro hk
      have hd := b.d_lt_one
      have hr := (hω k (by omega)).1
      exact mul_pos (ih (by omega)) (by linarith)
  have hband : ∀ k < N, b.InBand (spotOf S₀ ω k) (spotOf S₀ ω (k + 1)) :=
    fun k hk => inBand_of_return b (hpos k hk.le) (hω k hk)
  rw [run_book]
  exact h (spotOf S₀ ω) rfl hband

end Gimle.Forseti.Hedging
