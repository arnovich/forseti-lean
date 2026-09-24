import Gimle.Forseti.Syntax

/-! Coverage for the semi-algebraic predicate syntax.

Three things are pinned here, in order of importance.

* Each relation denotes what it should, including `eq`, which no other check
  reaches — `Formula.holds_atom` is `Iff.rfl` and cannot catch a transcription
  error in `Relation.holds`.
* The uniform index really does admit case analysis and decidable equality,
  which is the property the `product`-as-definition design exists to preserve.
* The fattening's existential is not interchangeable with a distance test. The
  discriminating case needs an **open** core; a closed one cannot separate them.
-/

namespace Gimle.Forseti.Tests.Syntax

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Asgard

-- Everything a denotation check needs to unfold: the formula constructors, the
-- relation table, and Asgard's polynomial evaluator.
attribute [local simp] Formula.holds Relation.holds Polynomial.Expr.eval

/-- `x₀ - 1 ≤ 0`, the unit upper bound written against zero. -/
def upperBound : Formula 1 :=
  .atom .le (.add (.var 0) (.constant (-1)))

/-- `0 ≤ x₀`. -/
def lowerBound : Formula 1 :=
  .atom .ge (.var 0)

/-- The closed unit interval as a conjunction. -/
def unitInterval : Formula 1 := lowerBound.and upperBound

example : unitInterval.holds ![0] := by
  norm_num [unitInterval, lowerBound, upperBound]

example : unitInterval.holds ![1] := by
  norm_num [unitInterval, lowerBound, upperBound]

example : ¬ unitInterval.holds ![2] := by
  norm_num [unitInterval, lowerBound, upperBound]

example : ¬ unitInterval.holds ![-1] := by
  norm_num [unitInterval, lowerBound, upperBound]

/-- `tru` and `fls` are the constants, not an encoding that could be refuted. -/
example (point : Point 1) : (Formula.tru : Formula 1).holds point := trivial
example (point : Point 1) : ¬ (Formula.fls : Formula 1).holds point := id

/-! ### Every relation is pinned

`.eq` is the one a reader is most likely to transcribe wrongly, and it is
reachable by no other check in this file. -/

/-- `x₀ = 0` accepts only the origin. -/
def originOnly : Formula 1 := .atom .eq (.var 0)

example : originOnly.holds ![0] := by norm_num [originOnly]
example : ¬ originOnly.holds ![1] := by norm_num [originOnly]
example : ¬ originOnly.holds ![-1] := by norm_num [originOnly]

/-- Strict and non-strict relations are distinguished at the boundary. -/
example : (Formula.atom .ge (.var 0) : Formula 1).holds ![0] := by norm_num
example : ¬ (Formula.atom .gt (.var 0) : Formula 1).holds ![0] := by norm_num
example : (Formula.atom .le (.var 0) : Formula 1).holds ![0] := by norm_num
example : ¬ (Formula.atom .lt (.var 0) : Formula 1).holds ![0] := by norm_num

/-- Disjunction and negation denote what they should. -/
example : (lowerBound.or (Formula.atom .lt (.var 0))).holds ![-3] := by
  refine Or.inr ?_
  norm_num

example : (Formula.not lowerBound).holds ![-1] := by
  norm_num [lowerBound]

/-- Negation of a compound formula, not merely of an atom. -/
example : (Formula.not unitInterval).holds ![2] := by
  norm_num [unitInterval, lowerBound, upperBound]

/-! ### Nonlinear atoms

Without a `mul`, every atom would be affine and the fragment would be linear
arithmetic rather than semi-algebraic. This is the doc's worked example. -/

/-- `2 ≤ x₀²` together with `0 ≤ x₀`, which denotes `√2 ≤ x₀`. -/
def rootTwoBound : Formula 1 :=
  (Formula.atom .ge (.add (.mul (.var 0) (.var 0)) (.constant (-2)))).and
    (Formula.atom .ge (.var 0))

example : rootTwoBound.holds ![2] := by
  refine ⟨?_, ?_⟩ <;> norm_num [rootTwoBound]

example : ¬ rootTwoBound.holds ![1] := by
  rintro ⟨square, -⟩
  norm_num [rootTwoBound] at square

/-- The negative branch is excluded, which is what the second conjunct is for:
`(-2)² = 4 ≥ 2` alone would admit it. -/
example : ¬ rootTwoBound.holds ![-2] := by
  rintro ⟨-, sign⟩
  norm_num [rootTwoBound] at sign

/-! ### The uniform index is usable

These are the properties the `product`-as-definition design exists to preserve.
A constructor `Formula l → Formula r → Formula (l + r)` would break both. -/

/-- Case analysis works at a concrete dimension. -/
example (formula : Formula 1) : True := by cases formula <;> trivial

/-- Formulas have decidable equality, so a caller can check that an answer came
back about the formula that was sent. -/
example : DecidableEq (Formula 1) := inferInstance

example : lowerBound ≠ upperBound := by decide

example : unitInterval = lowerBound.and upperBound := rfl

/-! ### Products read each factor on its own block -/

/-- Left block in `[0,1]`, right block at the origin — deliberately asymmetric,
so a swapped `pointLeft`/`pointRight` is caught. -/
def asymmetric : Formula 2 := unitInterval.product originOnly

example : asymmetric.holds ![1, 0] := by
  rw [asymmetric, Formula.holds_product]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    norm_num [unitInterval, lowerBound, upperBound, originOnly,
      pointLeft, pointRight]

/-- Swapping the two coordinates breaks it: `0` is in the left factor but `1`
is not in the right. This is what distinguishes the blocks. -/
example : ¬ asymmetric.holds ![0, 1] := by
  rw [asymmetric, Formula.holds_product]
  rintro ⟨-, origin⟩
  norm_num [originOnly, pointRight] at origin

/-- A syntactic product denotes the semantic product the monoidal rules use. -/
example :
    PredicateEquality asymmetric.toPredicate
      (productPredicate unitInterval.toPredicate originOnly.toPredicate) :=
  Formula.toPredicate_product unitInterval originOnly

/-! ### The synonyms are faithful

They are definitional identities; the point of testing them is that a caller
can move between the two phrasings, not that anything is proved by crossing. -/

example :
    PredicateEntailment unitInterval.toPredicate lowerBound.toPredicate := by
  rw [← formulaEntailment_iff]
  rintro point ⟨lower, -⟩
  exact lower

example (left right : Formula 1) :
    FormulaEntailment left right ↔
      PredicateEntailment left.toPredicate right.toPredicate :=
  formulaEntailment_iff left right

/-! ### Fattening keeps its existential

The central design claim. A **closed** core cannot test it: on `[0,1]` the
existential and a distance test agree exactly, so the discriminating case below
uses an open core. -/

def fattenedUnit : Fattened 1 := ⟨unitInterval, 1, by norm_num⟩

/-- A point outside the core is inside its fattening, witnessed by a core
point. -/
example : fattenedUnit.holds ![2] := by
  refine ⟨![1], ?_, ?_⟩
  · norm_num [fattenedUnit, unitInterval, lowerBound, upperBound]
  · intro coordinate
    fin_cases coordinate
    norm_num [LinfClose, fattenedUnit]

/-- Far enough away, no witness exists. -/
example : ¬ fattenedUnit.holds ![5] := by
  rintro ⟨ideal, ⟨-, upper⟩, close⟩
  have bound := close 0
  norm_num [fattenedUnit, upperBound] at upper bound
  rw [abs_le] at bound
  linarith [bound.1, bound.2, upper]

/-- The **open** unit interval, `0 < x₀ ∧ x₀ - 1 < 0`. -/
def openInterval : Formula 1 :=
  (Formula.atom .gt (.var 0)).and (Formula.atom .lt (.add (.var 0) (.constant (-1))))

def fattenedOpen : Fattened 1 := ⟨openInterval, 1, by norm_num⟩

/-- The discriminating case. `dist∞(2, (0,1)) = 1 ≤ 1`, so a distance-to-closure
test admits `2`; the existential rejects it, because every `q ∈ (0,1)` has
`|2 - q| > 1`. A closed core cannot separate these, which is why this test uses
an open one. -/
example : ¬ fattenedOpen.holds ![2] := by
  rintro ⟨ideal, ⟨-, upper⟩, close⟩
  have bound := close 0
  norm_num [fattenedOpen, openInterval] at upper bound
  rw [abs_le] at bound
  linarith [bound.2, upper]

/-- An empty core fattens to the empty set, not to a ball. Mathlib's
`Metric.infDist x ∅ = 0` would admit everything here. -/
def fattenedEmpty : Fattened 1 := ⟨(Formula.fls : Formula 1), 1, by norm_num⟩

example (point : Point 1) : ¬ fattenedEmpty.holds point := by
  rintro ⟨ideal, held, -⟩
  exact held

/-! ### The proved fattening rules -/

/-- The core always entails its own fattening. -/
example : PredicateEntailment fattenedUnit.core.toPredicate fattenedUnit.toPredicate :=
  Fattened.core_entails fattenedUnit

/-- At radius zero the fattening collapses onto its core. -/
def fattenedExact : Fattened 1 := ⟨unitInterval, 0, le_refl 0⟩

example : PredicateEntailment fattenedExact.toPredicate fattenedExact.core.toPredicate :=
  Fattened.zero_radius fattenedExact rfl

/-- Enlarging the radius weakens the fattening. -/
def fattenedWide : Fattened 1 := ⟨unitInterval, 2, by norm_num⟩

example : PredicateEntailment fattenedUnit.toPredicate fattenedWide.toPredicate :=
  Fattened.radius_mono fattenedUnit fattenedWide rfl (by norm_num [fattenedUnit, fattenedWide])

/-! ### The fragment is hostage to Asgard's polynomial type

This match is exhaustive over `Polynomial.Expr`'s constructors. It stops
compiling the moment a constructor is added upstream — which is exactly when
`docs/properties.md`'s claim that coefficients are rational and atoms are
polynomial would silently stop being true. -/
example {n : Nat} (expression : Polynomial.Expr n) : True :=
  match expression with
  | .var _ => trivial
  | .constant _ => trivial
  | .add _ _ => trivial
  | .mul _ _ => trivial
  | .neg _ => trivial

end Gimle.Forseti.Tests.Syntax
