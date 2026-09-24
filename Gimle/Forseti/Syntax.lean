import Gimle.Forseti
import Gimle.Asgard.Compile.Polynomial

/-! Semi-algebraic syntax for Forseti predicates.

`Predicate` carries an arbitrary `Point n → Prop`. That is the right semantic
notion — the approximation layer wraps regions it receives from Asgard, and
callers state domains as ordinary lambdas — but nothing can be handed to a
decision procedure, because there is no syntax to hand it.

This module adds the syntax beside the semantics rather than replacing it. A
`Formula` is a quantifier-free boolean combination of polynomial comparisons
over exact rational coefficients. Its polynomials are Asgard's
`Polynomial.Expr`, not a second expression type.

`Formula` is indexed **uniformly** by its dimension, so it supports case
analysis at a concrete dimension and derives `DecidableEq`. Products over
disjoint coordinate blocks are a *definition* built from renaming, not a
constructor: a constructor `Formula l → Formula r → Formula (l + r)` would make
the index non-uniform, which blocks both eliminators and decidable equality,
because `Nat.add` does not determine its summands.

**No authority is granted or transferred here.** `Formula.toPredicate` produces
data, not a claim. `FormulaEntailment` is a *synonym* for `PredicateEntailment`
on denoted predicates and `formulaEntailment_iff` holds by `Iff.rfl`; it records
that the synonym is faithful and asserts nothing about any particular formula.
There is no certificate type, no validity check and no transfer mechanism. See
`docs/properties.md` for what a solver integration would still require.
-/

namespace Gimle.Forseti.Syntax

open Gimle.Forseti
open Gimle.Asgard

/-- The closed set of supported polynomial comparisons, each against zero. -/
inductive Relation where
  | eq
  | le
  | lt
  | ge
  | gt
  deriving Repr, DecidableEq

/-- Interpretation of one comparison. Every relation compares against zero, so
a constraint `p ⋈ q` is written by forming `p - q`. -/
def Relation.holds : Relation → ℝ → Prop
  | .eq, value => value = 0
  | .le, value => value ≤ 0
  | .lt, value => value < 0
  | .ge, value => 0 ≤ value
  | .gt, value => 0 < value

/-- Rename the variables of a polynomial along a coordinate map. This is the
mechanism behind `Formula.product`: it reads a formula over one coordinate
block in a larger context. -/
def rename {source target : Nat} (map : Fin source → Fin target) :
    Polynomial.Expr source → Polynomial.Expr target
  | .var coordinate => .var (map coordinate)
  | .constant value => .constant value
  | .add left right => .add (rename map left) (rename map right)
  | .mul left right => .mul (rename map left) (rename map right)
  | .neg argument => .neg (rename map argument)

/-- Renaming a polynomial reindexes the point it is evaluated at. -/
@[simp] theorem rename_eval {source target : Nat} (map : Fin source → Fin target)
    (polynomial : Polynomial.Expr source) (point : Point target) :
    (rename map polynomial).eval point = polynomial.eval (fun i => point (map i)) := by
  induction polynomial with
  | var coordinate => rfl
  | constant value => rfl
  | add left right leftIH rightIH =>
      simp [rename, Polynomial.Expr.eval, leftIH, rightIH]
  | mul left right leftIH rightIH =>
      simp [rename, Polynomial.Expr.eval, leftIH, rightIH]
  | neg argument argumentIH => simp [rename, Polynomial.Expr.eval, argumentIH]

/-- Quantifier-free semi-algebraic syntax over exact rational polynomials.

The dimension is a parameter, not a computed index, so `cases` works at a
concrete dimension and `DecidableEq` derives. -/
inductive Formula (dimension : Nat) where
  | tru
  | fls
  | atom (relation : Relation) (polynomial : Polynomial.Expr dimension)
  | and (left right : Formula dimension)
  | or (left right : Formula dimension)
  | not (argument : Formula dimension)
  deriving Repr, DecidableEq

/-- The semi-algebraic set a formula denotes. -/
def Formula.holds {dimension : Nat} : Formula dimension → Point dimension → Prop
  | .tru, _ => True
  | .fls, _ => False
  | .atom relation polynomial, point => relation.holds (polynomial.eval point)
  | .and left right, point => left.holds point ∧ right.holds point
  | .or left right, point => left.holds point ∨ right.holds point
  | .not argument, point => ¬ argument.holds point

/-- Read a formula as the predicate it denotes. This produces data, not a
claim, and grants no authority of its own. -/
def Formula.toPredicate {dimension : Nat} (formula : Formula dimension) :
    Predicate dimension :=
  ⟨formula.holds⟩

/-- Unfold a denoted predicate back to the formula's own semantics. -/
@[simp] theorem Formula.toPredicate_holds {dimension : Nat}
    (formula : Formula dimension) (point : Point dimension) :
    formula.toPredicate.holds point ↔ formula.holds point :=
  Iff.rfl

/-! ### The connectives mean what they should -/

/-- `tru` denotes the whole space. -/
@[simp] theorem Formula.holds_tru {n : Nat} (point : Point n) :
    (Formula.tru : Formula n).holds point ↔ True := Iff.rfl

/-- `fls` denotes the empty set. -/
@[simp] theorem Formula.holds_fls {n : Nat} (point : Point n) :
    (Formula.fls : Formula n).holds point ↔ False := Iff.rfl

/-- An atom denotes its comparison against zero. -/
@[simp] theorem Formula.holds_atom {n : Nat} (relation : Relation)
    (polynomial : Polynomial.Expr n) (point : Point n) :
    (Formula.atom relation polynomial).holds point ↔
      relation.holds (polynomial.eval point) := Iff.rfl

/-- Conjunction denotes intersection. -/
@[simp] theorem Formula.holds_and {n : Nat} (left right : Formula n)
    (point : Point n) :
    (left.and right).holds point ↔ left.holds point ∧ right.holds point := Iff.rfl

/-- Disjunction denotes union. -/
@[simp] theorem Formula.holds_or {n : Nat} (left right : Formula n)
    (point : Point n) :
    (left.or right).holds point ↔ left.holds point ∨ right.holds point := Iff.rfl

/-- Negation denotes complement. -/
@[simp] theorem Formula.holds_not {n : Nat} (argument : Formula n)
    (point : Point n) :
    argument.not.holds point ↔ ¬ argument.holds point := Iff.rfl

/-! ### Products over disjoint coordinate blocks

`product` is a definition, not a constructor, so the dimension stays a
parameter. It keeps the fragment closed under the parallel composition the
monoidal Hoare rules use. -/

/-- Rename a formula along a coordinate map. -/
def Formula.rename {source target : Nat} (map : Fin source → Fin target) :
    Formula source → Formula target
  | .tru => .tru
  | .fls => .fls
  | .atom relation polynomial => .atom relation (Syntax.rename map polynomial)
  | .and left right => .and (left.rename map) (right.rename map)
  | .or left right => .or (left.rename map) (right.rename map)
  | .not argument => .not (argument.rename map)

/-- Renaming a formula reindexes the point it is read at. -/
@[simp] theorem Formula.rename_holds {source target : Nat}
    (map : Fin source → Fin target) (formula : Formula source)
    (point : Point target) :
    (formula.rename map).holds point ↔ formula.holds (fun i => point (map i)) := by
  induction formula with
  | tru => rfl
  | fls => rfl
  | atom relation polynomial => simp [Formula.rename, Formula.holds]
  | and left right leftIH rightIH =>
      simp [Formula.rename, Formula.holds, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [Formula.rename, Formula.holds, leftIH, rightIH]
  | not argument argumentIH => simp [Formula.rename, Formula.holds, argumentIH]

/-- Constrain the left coordinate block with `first` and the right with
`second`. -/
def Formula.product {left right : Nat}
    (first : Formula left) (second : Formula right) : Formula (left + right) :=
  (first.rename (Fin.castAdd right)).and (second.rename (Fin.natAdd left))

/-- A product reads each factor on its own coordinate block. -/
@[simp] theorem Formula.holds_product {left right : Nat}
    (first : Formula left) (second : Formula right)
    (point : Point (left + right)) :
    (first.product second).holds point ↔
      first.holds (pointLeft point) ∧ second.holds (pointRight point) := by
  simp only [Formula.product, Formula.holds, Formula.rename_holds]
  rfl

/-- A syntactic product denotes exactly the semantic product already used by the
monoidal Hoare rules. -/
theorem Formula.toPredicate_product {left right : Nat}
    (first : Formula left) (second : Formula right) :
    PredicateEquality (first.product second).toPredicate
      (productPredicate first.toPredicate second.toPredicate) := by
  intro point
  simp [productPredicate]

/-! ### Stating entailment on syntax

These are **synonyms**, introduced so a question can be phrased without
mentioning `Predicate`. `formulaEntailment_iff` and `formulaEquality_iff` hold
by `Iff.rfl`: they record that the synonym is faithful and assert nothing about
any particular formula. They are not a transfer mechanism, and no solver answer
becomes a theorem by crossing them. -/

/-- Entailment phrased on formulas; a synonym for `PredicateEntailment` on the
denoted predicates. -/
def FormulaEntailment {n : Nat} (antecedent consequent : Formula n) : Prop :=
  ∀ point, antecedent.holds point → consequent.holds point

/-- The synonym is faithful. This is a definitional identity, not a transfer of
authority. -/
theorem formulaEntailment_iff {n : Nat} (antecedent consequent : Formula n) :
    FormulaEntailment antecedent consequent ↔
      PredicateEntailment antecedent.toPredicate consequent.toPredicate :=
  Iff.rfl

/-- Equality phrased on formulas, for the same reason. -/
def FormulaEquality {n : Nat} (left right : Formula n) : Prop :=
  ∀ point, left.holds point ↔ right.holds point

/-- The equality synonym is faithful, on the same terms. -/
theorem formulaEquality_iff {n : Nat} (left right : Formula n) :
    FormulaEquality left right ↔
      PredicateEquality left.toPredicate right.toPredicate :=
  Iff.rfl

/-! ### Metric fattening

Deliberately **outside** the quantifier-free fragment: its semantics is
existential, and this module eliminates that existential only under explicit
hypotheses.

That is a capability limit, not a soundness one. By Tarski–Seidenberg the
projection of a semi-algebraic set is semi-algebraic, so an equivalent
quantifier-free formula exists and is computable by quantifier elimination.
This repository has no verified elimination procedure, so the node keeps its
existential and carries its witness.

What *would* be unsound is replacing the existential with a distance test.
`dist∞(point, core) ≤ radius` tests membership of the *closure* of the core
fattened by the radius, and the infimum need not be attained when the core is
not closed: with core `(0,1)` and radius `1`, the distance from `2` is exactly
`1`, yet no point of the core is within `1` of `2`. An empty core separates them
again — Mathlib's `Metric.infDist x ∅ = 0` junk value would admit every point,
while the existential admits none. Both cases are pinned in `Tests/Syntax.lean`.
-/

/-- An exact metric fattening of a quantifier-free formula. -/
structure Fattened (dimension : Nat) where
  /-- The quantifier-free core being fattened. -/
  core : Formula dimension
  /-- Exact fattening radius. -/
  radius : ℚ
  /-- Radii are non-negative; a negative radius has no reading. -/
  nonnegative : 0 ≤ radius

/-- Existential semantics: a point is in the fattening when some point of the
core is within the radius of it. -/
def Fattened.holds {n : Nat} (fattened : Fattened n) (point : Point n) : Prop :=
  ∃ ideal, fattened.core.holds ideal ∧ LinfClose (fattened.radius : ℝ) point ideal

/-- Read a fattening as the predicate it denotes. -/
def Fattened.toPredicate {n : Nat} (fattened : Fattened n) : Predicate n :=
  ⟨fattened.holds⟩

/-- Unfold a denoted fattening back to its own semantics. -/
@[simp] theorem Fattened.toPredicate_holds {n : Nat} (fattened : Fattened n)
    (point : Point n) :
    fattened.toPredicate.holds point ↔ fattened.holds point :=
  Iff.rfl

/-- The core entails its own fattening: every point of the core witnesses
itself. -/
theorem Fattened.core_entails {n : Nat} (fattened : Fattened n) :
    PredicateEntailment fattened.core.toPredicate fattened.toPredicate := by
  intro point hypothesis
  refine ⟨point, hypothesis, ?_⟩
  intro coordinate
  have nonneg : (0 : ℝ) ≤ (fattened.radius : ℝ) := by
    exact_mod_cast fattened.nonnegative
  simpa [LinfClose] using nonneg

/-- At radius zero the fattening collapses onto its core. A sound elimination,
under the explicit hypothesis that the radius vanishes. -/
theorem Fattened.zero_radius {n : Nat} (fattened : Fattened n)
    (vanishing : fattened.radius = 0) :
    PredicateEntailment fattened.toPredicate fattened.core.toPredicate := by
  rintro point ⟨ideal, held, close⟩
  have agree : point = ideal := by
    funext coordinate
    have bound := close coordinate
    rw [vanishing] at bound
    have zero : |point coordinate - ideal coordinate| = 0 :=
      le_antisymm (by simpa using bound) (abs_nonneg _)
    have := abs_eq_zero.mp zero
    linarith [sub_eq_zero.mp this]
  simpa [agree] using held

/-- Enlarging the radius weakens the fattening. -/
theorem Fattened.radius_mono {n : Nat} (small large : Fattened n)
    (sameCore : small.core = large.core) (ordered : small.radius ≤ large.radius) :
    PredicateEntailment small.toPredicate large.toPredicate := by
  rintro point ⟨ideal, held, close⟩
  refine ⟨ideal, by rw [← sameCore]; exact held, ?_⟩
  intro coordinate
  have widen : (small.radius : ℝ) ≤ (large.radius : ℝ) := by exact_mod_cast ordered
  exact le_trans (close coordinate) widen

/-- Fattening is definitionally the existential shape of quantitative
entailment, so the node needs no separate judgment. Stated for an arbitrary
antecedent, because the fact is about the fattening rather than about whether
the antecedent has syntax. -/
theorem Fattened.quantitativeEntailment {n : Nat} (fattened : Fattened n)
    (antecedent : Predicate n) :
    PredicateEntailment antecedent fattened.toPredicate ↔
      QuantitativePredicateEntailment antecedent fattened.core.toPredicate
        (fattened.radius : ℝ) :=
  Iff.rfl

/-! ### Axiom reports

These are reports, not a gate: `#print axioms` emits information and `lake
build` does not fail on it. The checks that actually fail live in
`Tests/Syntax.lean`. -/

#print axioms Formula.holds_product
#print axioms Formula.toPredicate_product
#print axioms Formula.rename_holds
#print axioms Fattened.core_entails
#print axioms Fattened.zero_radius
#print axioms Fattened.radius_mono

end Gimle.Forseti.Syntax
