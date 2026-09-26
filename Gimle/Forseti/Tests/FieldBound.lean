import Gimle.Forseti.Examples.HeatStripBound

/-! Hostile cases for field bounds over named coordinates and parameters.

A leaf certificate proves its goal as posed and nothing wider. Reusing it for a
wider domain or a changed profile is caught by the checker, and a
counterexample appears. Nonnegative coefficients are not a nonnegative field.

The axiom policy is asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.FieldBound

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.FieldBound
open Gimle.Forseti.Examples.HeatStripBound
open Gimle.Asgard

/-! ### The box lemma -/

/-- `R = 0`: the box is the point `0`. -/
example (x : ℝ) (lower : -0 ≤ x) (upper : x ≤ 0) : x * x ≤ 0 := by
  simpa using sq_le_sq_of_box lower upper

/-- Without the box constraint the general strip goal loses its certificate:
the upper bound's second multiplier has nothing to multiply. -/
def withoutBox : Goal :=
  ⟨strip, (Formula.atom .ge va).and ((Formula.atom .ge vc).and ((Formula.atom .ge (va * vt)).and
    (.atom .ge (va * (vT - vt))))), claim⟩

example : certificate.check withoutBox = false := by decide +kernel

/-! ### A narrowed domain reused as a wider claim -/

/-- The strip widened to `-2 ≤ x ≤ 2`, with the bound `3` of the unit strip. -/
def wideGoal : Goal :=
  ⟨plane, (Formula.atom .ge pt).and ((Formula.atom .le (pt - 1)).and
    ((Formula.atom .ge (px + 2)).and (.atom .le (px - 2)))),
    (unitGoal 3).consequent⟩

/-- The unit-strip certificate does not transfer, and `(t, x) = (0, 2)` refutes
the wider claim: `u = 4`. -/
example : unitCertificate.check wideGoal = false := by decide +kernel
example : ¬ wideGoal.Entailment := refutes_sound _ [("t", 0), ("x", 2)] (by decide +kernel)

/-! ### An altered initial profile -/

/-- The profile `2x²`, whose solution is `2x² + 4t`, claimed under the same bound. -/
def alteredGoal : Goal :=
  ⟨plane, unitStrip, (Formula.atom .ge (2 * px * px + 4 * pt)).and
    (.atom .le (2 * px * px + 4 * pt - 3))⟩

example : unitCertificate.check alteredGoal = false := by decide +kernel
example : ¬ alteredGoal.Entailment := refutes_sound _ [("t", 1), ("x", 1)] (by decide +kernel)

/-! ### Nonnegative coefficients do not make a nonnegative field -/

/-- The coefficients `c₀, c₁` of `u = c₀ + c₁·x`, and the coordinate `x`. -/
def line : Context := ⟨["c0", "c1", "x"], by decide, by decide, by decide⟩

/-- `c₀ ≥ 0 ∧ c₁ ≥ 0 ⊨ c₀ + c₁·x ≥ 0`. -/
def coefficientsToField : Goal :=
  ⟨line, (Formula.atom .ge (line.var "c0")).and (.atom .ge (line.var "c1")),
    .atom .ge (line.var "c0" + line.var "c1" * line.var "x")⟩

/-- **`u = x` at `x = -1`.** Its coefficients `0, 1` are nonnegative; the field
is `-1`. -/
example : ¬ coefficientsToField.Entailment :=
  refutes_sound _ [("c0", 0), ("c1", 1), ("x", -1)] (by decide +kernel)

/-! ### Axiom policy -/

/--
info: 'Gimle.Forseti.FieldBound.sq_le_sq_of_box'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms sq_le_sq_of_box
/--
info: 'Gimle.Forseti.FieldBound.box_constraint'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms box_constraint
/--
info: 'Gimle.Forseti.Examples.HeatStripBound.strip_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms strip_bound
/--
info: 'Gimle.Forseti.Examples.HeatStripBound.unit_bound_three'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unit_bound_three
/--
info: 'Gimle.Forseti.Examples.HeatStripBound.unit_bound_two_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unit_bound_two_refuted

end Gimle.Forseti.Tests.FieldBound
