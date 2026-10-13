import Gimle.Forseti.Examples.AlgebraicCounterexamples

/-! Hostile algebraic witnesses, each rejected by the checker itself. -/

namespace Gimle.Forseti.Tests.AlgebraicWitness

open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Examples.AlgebraicCounterexamples

/-- The interval `[2, 3]` holds no root of `x² − 2`: no sign change. -/
example : Root.check ⟨squareMinus 2, ⟨2, 3⟩⟩ = false := by decide +kernel

/-- A reversed interval. -/
example : Root.check ⟨squareMinus 2, ⟨3 / 2, 7 / 5⟩⟩ = false := by decide +kernel

/-- `x³ − x` changes sign across `[−3/2, 3/2]` but has three roots there: its
derivative's enclosure contains zero. -/
example : Root.check ⟨.var 0 * .var 0 * .var 0 - .var 0, ⟨-3 / 2, 3 / 2⟩⟩ = false := by
  decide +kernel

/-- `x³`, which is not square-free, changes sign across `[−1, 1]` at its triple
root; the derivative vanishes there, so it is rejected. -/
example : Root.check ⟨.var 0 * .var 0 * .var 0, ⟨-1, 1⟩⟩ = false := by decide +kernel

/-- The accepted roots do check. -/
example : sqrtTwo.check = true ∧ minusSqrtTwo.check = true ∧ sqrtThree.check = true ∧
    (exactly (1 / 2)).check = true := by decide +kernel

/-- A sign the box does not establish: `x − 7/5` over `[7/5, 3/2]` touches zero,
so its enclosure cannot decide `x − 7/5 > 0`. -/
def touching : Goal :=
  ⟨line, .atom .eq (line.var "x" * line.var "x" - 2), .atom .le (line.var "x" - rational (7 / 5))⟩

example : algebraicRefutes touching ⟨[sqrtTwo], [.zero [1]], [.enclosure]⟩ = false := by
  decide +kernel

/-- A zero claimed with the wrong multiplier. -/
example : algebraicRefutes rootTwo ⟨[sqrtTwo], [.zero [2]], [.enclosure]⟩ = false := by
  decide +kernel

/-- A wrong interval for the point: `−√2` does not refute `x < 0`. -/
example : algebraicRefutes rootTwo ⟨[minusSqrtTwo], [.zero [1]], [.enclosure]⟩ = false := by
  decide +kernel

/-- A changed goal: `x² = 2 ⊨ x < 2` holds at √2, so the old witness fails. -/
def belowTwo : Goal :=
  ⟨line, .atom .eq (line.var "x" * line.var "x" - 2), .atom .lt (line.var "x" - 2)⟩

example : algebraicRefutes belowTwo ⟨[sqrtTwo], [.zero [1]], [.enclosure]⟩ = false := by
  decide +kernel

/-- Evidence must be used exactly: a spare piece is rejected. -/
example : algebraicRefutes rootTwo ⟨[sqrtTwo], [.zero [1], .enclosure], [.enclosure]⟩ =
    false := by decide +kernel

/-- One coordinate per context name. -/
example : algebraicRefutes rootTwo ⟨[sqrtTwo, sqrtTwo], [.zero [1, 0]], [.enclosure]⟩ =
    false := by decide +kernel

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Syntax.algebraicRefutes_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms algebraicRefutes_sound
/--
info: 'Gimle.Forseti.Syntax.Root.root_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Root.root_unique
/--
info: 'Gimle.Forseti.Examples.AlgebraicCounterexamples.rootTwo_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms rootTwo_refuted
/--
info: 'Gimle.Forseti.Examples.AlgebraicCounterexamples.product_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms product_refuted

end Gimle.Forseti.Tests.AlgebraicWitness
