import Gimle.Forseti.Syntax.Context

/-! Coverage for ordered formula contexts.

Pinned here: construction rejects what it must with the error it should, the
dimension comes from the names, products keep each coordinate's name, the same
shape over different names is a different named formula, and an answer read by
name lands on the right coordinates whatever order it arrives in.
-/

namespace Gimle.Forseti.Tests.Context

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Asgard

/-- The error a construction reported, or none if it succeeded. -/
def failure {α : Type} : Except ContextError α → Option ContextError
  | .error reason => some reason
  | .ok _ => none

/-! ### Construction -/

example : failure (Context.make ["x", "y"]) = none := by decide
example : failure (Context.make []) = some .empty := by decide
example : failure (Context.make ["x", "y", "x"]) = some (.duplicateName "x") := by
  decide
example : failure (Context.make ["x", ""]) = some (.blankName 1) := by decide

/-- `[x, y]`. -/
def xy : Context := ⟨["x", "y"], by decide, by decide, by decide⟩
/-- `[y, x]`: the same names in the other order. -/
def yx : Context := ⟨["y", "x"], by decide, by decide, by decide⟩
/-- `[z]`. -/
def z : Context := ⟨["z"], by decide, by decide, by decide⟩

/-- The dimension is the number of names; there is no second source for it. -/
example : xy.dimension = 2 := rfl
example : xy.name ⟨0, by decide⟩ = "x" ∧ xy.name ⟨1, by decide⟩ = "y" := ⟨rfl, rfl⟩

/-- Order is part of a context. -/
example : xy ≠ yx := by decide

/-- `x ≤ 0` over `[x, y]`: a formula of dimension 2 reading coordinate 0. -/
def xNonpositive : Formula 2 := .atom .le (.var 0)

example : failure (NamedFormula.make xy xNonpositive) = none := by decide
/-- A formula whose dimension differs from the context is refused, with both
numbers. -/
example : failure (NamedFormula.make z xNonpositive) =
    some (.dimensionMismatch 2 1) := by decide

/-! ### Equality in the presence of contexts

Two named formulas are equal exactly when they have the same names in the same
order and the same formula (`NamedFormula.ext_iff'`). The same shape over other
names, or the same names in another order, is a different claim. -/

/-- `x ≤ 0` over `[x, y]`. -/
def overXY : NamedFormula := ⟨xy, xNonpositive⟩
/-- The same syntax over `[y, x]` constrains `y`, not `x`. -/
def overYX : NamedFormula := ⟨yx, xNonpositive⟩

example : overXY ≠ overYX := by decide
example : overXY = ⟨xy, .atom .le (.var ⟨0, by decide⟩)⟩ := by decide
/-- The bare formulas are equal; only the context tells them apart. -/
example : overXY.formula = overYX.formula := rfl

/-! ### Products keep every coordinate's name -/

/-- `z ≥ 0` over `[z]`. -/
def zNonnegative : NamedFormula := ⟨z, .atom .ge (.var ⟨0, by decide⟩)⟩

/-- The product of `[x, y]` and `[z]` is over `[x, y, z]`. -/
example : (overXY.product zNonnegative).map (·.context.names) = .ok ["x", "y", "z"] :=
  rfl

/-- A shared name is refused rather than read as two coordinates. -/
example : failure (overXY.product overYX) = some (.duplicateName "x") := by decide

/-- Where each factor's coordinates went, by name: the general statement is
`Context.append_name_left` and `append_name_right`; here it is instantiated. -/
example (joined : Context) (built : xy.append z = .ok joined) :
    joined.name (Fin.cast (Context.append_dimension built).symm
      (Fin.natAdd xy.dimension (⟨0, by decide⟩ : Fin z.dimension))) = "z" :=
  Context.append_name_right built ⟨0, by decide⟩

/-! ### Answers are read back by name -/

/-- The value each coordinate got, in context order. -/
def values {context : Context}
    (read : Except ContextError (Fin context.dimension → ℚ)) : Option (List ℚ) :=
  match read with
  | .ok point => some (List.ofFn point)
  | .error _ => none

/-- A solver's answer, in its own order. -/
def answer : Context.Assignment := [("y", 2), ("x", -1)]

example : values (xy.read answer) = some [-1, 2] := by decide
/-- The same answer read in the other context puts the values the other way. -/
example : values (yx.read answer) = some [2, -1] := by decide

example : failure (xy.read [("x", 1)]) = some (.missingName "y") := by decide
example : failure (xy.read [("x", 1), ("y", 2), ("x", 3)]) =
    some (.repeatedName "x") := by decide
example : failure (xy.read [("x", 1), ("y", 2), ("w", 0)]) =
    some (.unknownName "w") := by decide

/-- Naming a point and reading it back is the identity, by the general theorem. -/
example (point : Fin xy.dimension → ℚ) : xy.read (xy.assign point) = .ok point :=
  Context.read_assign xy point

/-- A formula is read at the point its answer names: `x ≤ 0` holds at
`y = 2, x = -1` whatever order the answer lists them in. -/
example (point : Fin xy.dimension → ℚ) (read_ok : xy.read answer = .ok point) :
    overXY.holds fun i => (point i : ℝ) := by
  have first := Context.read_mem read_ok ⟨0, by decide⟩
  have value : point (0 : Fin 2) = -1 := by
    simp [answer, Context.name, xy] at first
    exact first
  simp [overXY, NamedFormula.holds, xNonpositive, Formula.holds, Relation.holds,
    Polynomial.Expr.eval, value]

/-! ### Coordinates by name -/

/-- `y ≤ 0` over `[x, y]`, written by name: the lookup is checked by `decide`. -/
def yNonpositive : Formula xy.dimension := .atom .le (xy.var "y")

example : xy.coordinate "y" = ⟨1, by decide⟩ := by decide
example : yNonpositive = .atom .le (.var ⟨1, by decide⟩) := by decide
/-- A name the context does not have has no coordinate. -/
example : (xy.position? "w").isSome = false := by decide

/-! ### Goals over one context -/

/-- `y ≤ 0` as a named formula over `[x, y]`. -/
def yOverXY : NamedFormula := ⟨xy, yNonpositive⟩

example : failure (Goal.ofNamed overXY yOverXY) = none := by decide
/-- The same shape over another context cannot be posed against it. -/
example : failure (Goal.ofNamed overXY overYX) = some .contextMismatch := by decide

/-- `x ≤ 0 ⊨ y ≤ 0` over `[x, y]` is false: the point `x = 0, y = 1`. -/
example (goal : Goal) (posed : Goal.ofNamed overXY yOverXY = .ok goal) :
    ¬ goal.Entailment := by
  obtain ⟨_, _, reading⟩ := Goal.ofNamed_entailment posed
  rw [reading]
  intro claim
  have := claim ![0, 1] (by
    simp [overXY, NamedFormula.holds, xNonpositive, Formula.holds, Relation.holds,
      Polynomial.Expr.eval])
  simp [yOverXY, NamedFormula.holds, yNonpositive, Relation.holds,
    Polynomial.Expr.eval, Context.var, Context.coordinate, Context.position?,
    xy] at this
  exact absurd (show (1 : ℝ) ≤ 0 from this) (by norm_num)

end Gimle.Forseti.Tests.Context
