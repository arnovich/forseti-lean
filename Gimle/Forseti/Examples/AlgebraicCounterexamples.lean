import Gimle.Forseti.Syntax.AlgebraicWitness

/-! Entailments refuted only at irrational points.

`x² = 2 ⊨ x < 0` has no rational counterexample: its only counterexamples are
`±√2`. Each goal here is refuted by a checked algebraic witness — a box of
rational intervals, a polynomial per coordinate with one root in its interval,
and evidence for each atom — through `algebraicRefutes_sound`. The witnesses
are written by hand, as fixtures; finding them is gimle-forseti task 033's
producer.
-/

namespace Gimle.Forseti.Examples.AlgebraicCounterexamples

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Asgard

/-- `[x]`. -/
def line : Context := ⟨["x"], by decide, by decide, by decide⟩
/-- `[x, y]`. -/
def plane : Context := ⟨["x", "y"], by decide, by decide, by decide⟩

/-- `t² − c`, in the one variable of a root. -/
def squareMinus (c : ℚ) : Polynomial.Expr 1 := .var 0 * .var 0 - rational c

/-- `t − q`: a rational coordinate. -/
def exactly (q : ℚ) : Root := ⟨.var 0 - rational q, ⟨q, q⟩⟩

/-- √2 in `[7/5, 3/2]`, and −√2 in `[−3/2, −7/5]`. -/
def sqrtTwo : Root := ⟨squareMinus 2, ⟨7 / 5, 3 / 2⟩⟩
def minusSqrtTwo : Root := ⟨squareMinus 2, ⟨-3 / 2, -7 / 5⟩⟩
/-- √3 in `[17/10, 9/5]`. -/
def sqrtThree : Root := ⟨squareMinus 3, ⟨17 / 10, 9 / 5⟩⟩

/-! ### `x² = 2 ⊨ x < 0`, refuted at √2 -/

def rootTwo : Goal where
  context := line
  antecedent := .atom .eq (line.var "x" * line.var "x" - 2)
  consequent := .atom .lt (line.var "x")

/-- The antecedent is zero by `x² − 2 = 1 · (x² − 2)`; the consequent's `x` is
enclosed in `[7/5, 3/2]`, so it is positive. -/
def rootTwoWitness : AlgebraicWitness line.dimension :=
  ⟨[sqrtTwo], [.zero [1]], [.enclosure]⟩

theorem rootTwo_refuted : ¬ rootTwo.Entailment :=
  algebraicRefutes_sound rootTwo rootTwoWitness (by decide +kernel)

/-- No rational point refutes it: the antecedent has no rational solution,
and a rational witness is rejected. -/
example : refutes rootTwo [("x", 7 / 5)] = false := by decide +kernel

/-! ### A negative root: `x² = 2 ⊨ x > 0`, refuted at −√2 -/

def rootTwoPositive : Goal where
  context := line
  antecedent := rootTwo.antecedent
  consequent := .atom .gt (line.var "x")

theorem rootTwoPositive_refuted : ¬ rootTwoPositive.Entailment :=
  algebraicRefutes_sound rootTwoPositive ⟨[minusSqrtTwo], [.zero [1]], [.enclosure]⟩
    (by decide +kernel)

/-! ### One coordinate in several atoms: `x² = 2 ∧ x > 0 ⊨ x³ < 2` -/

def cube : Goal where
  context := line
  antecedent := (Formula.atom .eq (line.var "x" * line.var "x" - 2)).and
    (.atom .gt (line.var "x"))
  consequent := .atom .lt (line.var "x" * line.var "x" * line.var "x" - 2)

theorem cube_refuted : ¬ cube.Entailment :=
  algebraicRefutes_sound cube ⟨[sqrtTwo], [.zero [1], .enclosure], [.enclosure]⟩
    (by decide +kernel)

/-! ### Independent coordinates: `x² = 2 ∧ y² = 3 ⊨ x·y < 2`, at (√2, √3) -/

def product : Goal where
  context := plane
  antecedent := (Formula.atom .eq (plane.var "x" * plane.var "x" - 2)).and
    (.atom .eq (plane.var "y" * plane.var "y" - 3))
  consequent := .atom .lt (plane.var "x" * plane.var "y" - 2)

theorem product_refuted : ¬ product.Entailment :=
  algebraicRefutes_sound product
    ⟨[sqrtTwo, sqrtThree], [.zero [1, 0], .zero [0, 1]], [.enclosure]⟩ (by decide +kernel)

/-! ### A rational coordinate beside an algebraic one: `(√2, 1/2)` -/

def mixed : Goal where
  context := plane
  antecedent := (Formula.atom .eq (plane.var "x" * plane.var "x" - 2)).and
    (.atom .eq (plane.var "y" + plane.var "y" - 1))
  consequent := .atom .lt (plane.var "x" * plane.var "y")

theorem mixed_refuted : ¬ mixed.Entailment :=
  algebraicRefutes_sound mixed
    ⟨[sqrtTwo, exactly (1 / 2)], [.zero [1, 0], .zero [0, 2]], [.enclosure]⟩
    (by decide +kernel)

/-! ### Equality on the boundary: `x² = 2 ⊨ x² − 2 < 0` -/

def boundary : Goal where
  context := line
  antecedent := rootTwo.antecedent
  consequent := .atom .lt (line.var "x" * line.var "x" - 2)

/-- The consequent's polynomial is exactly zero at √2, so `< 0` fails there. -/
theorem boundary_refuted : ¬ boundary.Entailment :=
  algebraicRefutes_sound boundary ⟨[sqrtTwo], [.zero [1]], [.zero [1]]⟩ (by decide +kernel)

end Gimle.Forseti.Examples.AlgebraicCounterexamples
