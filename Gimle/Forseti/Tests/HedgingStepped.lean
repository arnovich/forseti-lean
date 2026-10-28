module

public import Gimle.Forseti.HedgingStepped
public import Gimle.Forseti.Tests.Hedging

/-! Coverage for the hedged book as a stepped system driven by simple returns.

Pinned here: the step map `book` and the spot `spotOf` by their defining equations; the
stepped run at marks `0` and `1` and at every mark (`run_book`), where the hedged book is the
iteration `Stepped.run` of the step map along a path of returns; the super-hedge of the call
read as a safety statement about that driven iteration (`covers_run`), on the band and the
call of `Tests/Hedging.lean`; and the axiom policy, asserted with `#guard_msgs`.
-/

@[expose] public section

namespace Gimle.Forseti.Tests.HedgingStepped

open Gimle.Forseti.Hedging
open Gimle.Forseti.Tests.Hedging

/-! ### The stepped bridge -/

section SteppedBridge

variable (δ : ℕ → ℝ → ℝ) (S₀ w : ℝ) (ω : ℕ → ℝ)

example : book δ (3, S₀, w) 0 = (4, S₀, w) := by simp [book]

example (x : ℕ × ℝ × ℝ) (r : ℝ) :
    book δ x r = (x.1 + 1, x.2.1 * (1 + r), x.2.2 + δ x.1 x.2.1 * (x.2.1 * r)) := rfl

example : spotOf S₀ ω 0 = S₀ := rfl
example (k : ℕ) : spotOf S₀ ω (k + 1) = spotOf S₀ ω k * (1 + ω k) := rfl

/-- The run at mark `0` is the start. -/
example : Stepped.run (book δ) (0, S₀, w) ω 0
    = (0, spotOf S₀ ω 0, wealth δ w (spotOf S₀ ω) 0) := by
  simp [Stepped.run, spotOf, wealth]

/-- The run at mark `1` is the first hedged step. -/
example : Stepped.run (book δ) (0, S₀, w) ω 1
    = (1, spotOf S₀ ω 1, wealth δ w (spotOf S₀ ω) 1) := by
  simp only [Stepped.run, book, spotOf, wealth, Prod.mk.injEq, true_and]
  ring

/-- The run is the spot and the wealth along the path of returns, at every mark. -/
example (n : ℕ) : Stepped.run (book δ) (0, S₀, w) ω n
    = (n, spotOf S₀ ω n, wealth δ w (spotOf S₀ ω) n) := run_book δ S₀ w ω n

end SteppedBridge

/-- The super-hedge of the call, read as a safety statement about a driven iteration: along
the zero-return path, which is inside the band, the book ends at least at the payoff. -/
example : (fun S : ℝ => max (S - 1) 0)
      (Stepped.run (book (hedge band (fun S : ℝ => max (S - 1) 0) 3)) (0, 1,
        price band (fun S : ℝ => max (S - 1) 0) 3 1) (fun _ => 0) 3).2.1
    ≤ (Stepped.run (book (hedge band (fun S : ℝ => max (S - 1) 0) 3)) (0, 1,
        price band (fun S : ℝ => max (S - 1) 0) 3 1) (fun _ => 0) 3).2.2 :=
  covers_run (covers_hedge band convexOn_call_one 3 one_pos) one_pos (fun _ => 0)
    (fun _ _ => ⟨by linarith [band.d_pos], by linarith [band.u_pos]⟩)

/-! ### Axiom policy -/

/--
info: 'Gimle.Forseti.Hedging.run_book'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms run_book
/--
info: 'Gimle.Forseti.Hedging.covers_run'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms covers_run

end Gimle.Forseti.Tests.HedgingStepped
