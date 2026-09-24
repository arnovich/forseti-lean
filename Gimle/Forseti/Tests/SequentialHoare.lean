import Gimle.Forseti

/-! Coverage for sequential Hoare composition.

Four things are pinned, in order of importance.

* **Errors do not add.** Two valid approximate triples whose naive sum is
  false. `naiveRuleIsFalse` refutes the rule itself, not one instantiation.
* **A modulus is not derivable from syntax.** `squareHasNoModulus` shows
  squaring has *no* modulus at any positive gap on an unbounded region, which
  is what forces a bounded region and makes the modulus a hypothesis.
* **Composition order.** `Circuit.compose` runs its *left* argument first,
  which is the opposite of `∘`. Two asymmetric circuits witness it.
* **The coverage hypotheses do work.** The worked example runs on a bounded
  region so both are discharged by real proofs rather than `trivial`.
-/

namespace Gimle.Forseti.Tests.SequentialHoare

open Gimle.Forseti
open Gimle.Asgard

/-- Points whose single coordinate is one. -/
def atOne : Predicate 1 := ⟨fun point => point 0 = 1⟩

/-- Points whose single coordinate is zero. -/
def atZero : Predicate 1 := ⟨fun point => point 0 = 0⟩

/-- Points whose single coordinate is ten. -/
def atTen : Predicate 1 := ⟨fun point => point 0 = 10⟩

/-- Multiply by ten. Gain exactly ten, everywhere. -/
def tenfold : Circuit 1 1 := Circuit.scalar 10

/-- Square the input. Locally Lipschitz, globally not. -/
def square : Circuit 1 1 := Circuit.compose Circuit.split Circuit.multiplication

/-- The closed unit ball, a bounded region on which `square` does have a
modulus. -/
def unitBall : Predicate 1 := ⟨fun point => -1 ≤ point 0 ∧ point 0 ≤ 1⟩

/-! ### Composition runs its left argument first

`Circuit.compose f g` applies `f` then `g`, the opposite of `g ∘ f`. Two
non-commuting circuits witness it; without this nothing in the file
distinguishes the two orders. -/

theorem composeRunsLeftFirst : (Circuit.compose tenfold square).run ![1] 0 = 100 := by
  simp [tenfold, square]
  norm_num

theorem composeIsNotSymmetric : (Circuit.compose square tenfold).run ![1] 0 = 10 := by
  simp [tenfold, square]

/-! ### The exact rule composes -/

/-- The identity keeps a point at one. -/
theorem identityExact : ExactHoare atOne Circuit.id atOne :=
  fun _ hypothesis => hypothesis

/-- Ten times one is ten. -/
theorem tenfoldExact : ExactHoare atOne tenfold atTen := by
  intro input hypothesis
  have coordinateOne : input 0 = 1 := hypothesis
  show (tenfold.run input) 0 = 10
  simp [tenfold, coordinateOne]

/-- The two compose, and the composite runs `Circuit.id` first. -/
theorem exactComposes : ExactHoare atOne (Circuit.compose Circuit.id tenfold) atTen :=
  exactHoareSequential identityExact tenfoldExact

/-! ### The naive error sum is false

`atOne` inputs land within `1` of `atZero`, and `tenfold` maps `atZero` to
`atZero` exactly. If errors added, the composite would hold at `1 + 0 = 1`. It
does not: the composite maps `1` to `10`, which is `10` from the only point of
`atZero`. -/

/-- First stage: the identity carries `atOne` to within `1` of `atZero`. -/
theorem firstStage : QuantitativeHoare atOne Circuit.id atZero 1 := by
  intro input hypothesis
  have coordinateOne : input 0 = 1 := hypothesis
  refine ⟨![0], rfl, ?_⟩
  intro coordinate
  fin_cases coordinate
  show |Circuit.id.run input 0 - (![0] : Point 1) 0| ≤ 1
  simp [coordinateOne]

/-- Second stage: `tenfold` carries `atZero` to `atZero` with no error at all. -/
theorem secondStage : QuantitativeHoare atZero tenfold atZero 0 := by
  intro input hypothesis
  have coordinateZero : input 0 = 0 := hypothesis
  refine ⟨![0], rfl, ?_⟩
  intro coordinate
  fin_cases coordinate
  show |tenfold.run input 0 - (![0] : Point 1) 0| ≤ 0
  simp [tenfold, coordinateZero]

/-- The composite is exactly ten from `atZero`, so every budget below ten
fails. This subsumes both the naive sum `1 + 0` and any other under-estimate,
and it pins the sharp constant rather than an arbitrary one. -/
theorem belowTenFails (error : ℝ) (small : error < 10) :
    ¬ QuantitativeHoare atOne (Circuit.compose Circuit.id tenfold) atZero error := by
  intro composed
  obtain ⟨ideal, idealZero, close⟩ := composed ![1] rfl
  have idealCoordinate : ideal 0 = 0 := idealZero
  have bound := close 0
  rw [show (Circuit.compose Circuit.id tenfold).run ![1] 0 = 10 by simp [tenfold],
    idealCoordinate] at bound
  norm_num at bound
  linarith

/-- **The counterexample, as a refutation of the rule itself.** If errors
added, these two triples would give the composite at `1 + 0`. They do not. -/
theorem naiveRuleIsFalse :
    ¬ (∀ {n : Nat} (pre mid post : Predicate n) (f g : Circuit n n) (e₁ e₂ : ℝ),
        QuantitativeHoare pre f mid e₁ → QuantitativeHoare mid g post e₂ →
        QuantitativeHoare pre (Circuit.compose f g) post (e₁ + e₂)) := by
  intro naive
  exact belowTenFails (1 + 0) (by norm_num)
    (naive atOne atZero atZero Circuit.id tenfold 1 0 firstStage secondStage)

/-! ### A modulus is not derivable from syntax

This is what the whole design rests on: the modulus must be a hypothesis,
because a polynomial circuit need not have one at all. -/

/-- `square` has **no** modulus at gap one on an unbounded region -- not a
worse one, none. Two points a unit apart are driven arbitrarily far apart by
moving both outward, so no finite bound survives. -/
theorem squareHasNoModulus :
    ¬ ∃ outputGap : ℝ, CircuitModulus square ⟨fun _ => True⟩ 1 outputGap := by
  rintro ⟨outputGap, modulus⟩
  have nonneg : 0 ≤ outputGap := by
    have coincident := modulus ![0] ![0] trivial trivial (by intro c; simp) 0
    simpa [square] using coincident
  have stretch : |(outputGap + 1) * (outputGap + 1) - outputGap * outputGap|
      ≤ outputGap := by
    have raw := modulus ![outputGap + 1] ![outputGap] trivial trivial
      (by intro c; fin_cases c; simp) 0
    simpa [square] using raw
  rw [abs_of_nonneg (by nlinarith [nonneg])] at stretch
  linarith

/-- On the unit ball it does have one: `|x² - y²| = |x + y||x - y| ≤ 2|x - y|`.
This is the bounded region the previous theorem forces. -/
theorem squareModulusOnBall (gap : ℝ) :
    CircuitModulus square unitBall gap (2 * gap) := by
  intro left right leftHeld rightHeld close coordinate
  fin_cases coordinate
  have separation := close 0
  obtain ⟨leftLow, leftHigh⟩ := leftHeld
  obtain ⟨rightLow, rightHigh⟩ := rightHeld
  show |square.run left 0 - square.run right 0| ≤ 2 * gap
  have expand : square.run left 0 - square.run right 0
      = (left 0 + right 0) * (left 0 - right 0) := by
    simp [square]
    ring
  rw [expand, abs_mul]
  have sumBound : |left 0 + right 0| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  calc
    |left 0 + right 0| * |left 0 - right 0| ≤ 2 * |left 0 - right 0| :=
      mul_le_mul_of_nonneg_right sumBound (abs_nonneg _)
    _ ≤ 2 * gap := by linarith [separation]

/-! ### The sound rules -/

/-- `tenfold` has gain exactly ten. -/
theorem tenfoldModulus (gap : ℝ) :
    CircuitModulus tenfold ⟨fun _ => True⟩ gap (10 * gap) := by
  intro left right _ _ close coordinate
  fin_cases coordinate
  have separation := close 0
  show |tenfold.run left 0 - tenfold.run right 0| ≤ 10 * gap
  have expand : tenfold.run left 0 - tenfold.run right 0
      = 10 * (left 0 - right 0) := by
    simp [tenfold]
    ring
  rw [expand, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10)]
  exact mul_le_mul_of_nonneg_left separation (by norm_num)

/-- Ten is not merely an upper bound on the gain: nine is refuted, so the
docstring's "exactly ten" is pinned rather than asserted. -/
theorem tenfoldGainIsSharp : ¬ CircuitModulus tenfold ⟨fun _ => True⟩ 1 9 := by
  intro modulus
  have stretch := modulus ![1] ![0] trivial trivial (by intro c; fin_cases c; simp) 0
  simp only [tenfold, Circuit.run] at stretch
  norm_num at stretch

/-- With an exact first stage the second stage's error passes through
unchanged. The side condition is not absent, it is discharged automatically:
at zero error the actual intermediate point *is* the ideal one. -/
theorem exactFirstStage :
    QuantitativeHoare atOne (Circuit.compose Circuit.id tenfold) atTen 0 :=
  exactThenQuantitativeHoareSequential identityExact
    (by
      intro input hypothesis
      have coordinateOne : input 0 = 1 := hypothesis
      refine ⟨![10], rfl, ?_⟩
      intro coordinate
      fin_cases coordinate
      show |tenfold.run input 0 - (![10] : Point 1) 0| ≤ 0
      simp [tenfold, coordinateOne])

/-- The general rule on a **bounded** region, so both coverage hypotheses are
discharged by real proofs rather than `trivial`, and with a **non-zero** target
error so that addend is exercised too. -/
theorem generalRuleOnBoundedRegion :
    QuantitativeHoare atOne (Circuit.compose Circuit.id square) atZero (2 * 1 + 1) := by
  refine quantitativeHoareSequential firstStage ?_ (squareModulusOnBall 1)
    ?_ ?_
  · intro input hypothesis
    have coordinateZero : input 0 = 0 := hypothesis
    refine ⟨![0], rfl, ?_⟩
    intro coordinate
    fin_cases coordinate
    show |square.run input 0 - (![0] : Point 1) 0| ≤ 1
    simp [square, coordinateZero]
  · intro point held
    have coordinateZero : point 0 = 0 := held
    exact ⟨by simp [coordinateZero], by simp [coordinateZero]⟩
  · intro input held
    have coordinateOne : input 0 = 1 := held
    exact ⟨by simp [coordinateOne], by simp [coordinateOne]⟩

/-- The canonical region discharges both coverage hypotheses for free. -/
theorem canonicalRule :
    QuantitativeHoare atOne (Circuit.compose Circuit.id tenfold) atZero (10 * 1 + 0) :=
  canonicalSequential (by norm_num) firstStage secondStage
    (modulusNarrow (tenfoldModulus 1) (fun _ _ => trivial))

/-- Chaining three stages works, and the bound is `10 · 10 · 1 = 100`. -/
theorem threeStages :
    QuantitativeHoare atOne
      (Circuit.compose Circuit.id (Circuit.compose tenfold tenfold)) atZero (100 * 1 + 0) := by
  refine canonicalSequential (by norm_num) firstStage ?_ ?_
  · intro input hypothesis
    have coordinateZero : input 0 = 0 := hypothesis
    refine ⟨![0], rfl, ?_⟩
    intro coordinate
    fin_cases coordinate
    show |(Circuit.compose tenfold tenfold).run input 0 - (![0] : Point 1) 0| ≤ 0
    simp [tenfold, coordinateZero]
  · refine modulusNarrow (modulusWeaken
      (modulusCompose (tenfoldModulus 1) (tenfoldModulus (10 * 1))
        (fun _ _ => trivial))
      (le_refl 1) (by norm_num)) (fun _ _ => trivial)


/-! ### Coverage composition pays no amplification

Where the second stage tolerates the neighbourhood the first stage lands in,
nothing is amplified and nothing is added. Contrast `canonicalRule` above,
which needs the tenfold modulus and concludes at `10`. -/

/-- The neighbourhood of `atZero` at radius one is the interval `[-1,1]`, which
the unit ball covers. -/
theorem zeroNeighbourhoodInBall :
    PredicateEntailment (Neighbourhood atZero 1) unitBall := by
  rintro point ⟨ideal, idealZero, close⟩
  have idealCoordinate : ideal 0 = 0 := idealZero
  have bound := close 0
  rw [idealCoordinate] at bound
  rw [abs_le] at bound
  exact ⟨by linarith [bound.1], by linarith [bound.2]⟩

/-- `square` on the unit ball lands within one of `atZero`: `x² ≤ 1`. -/
theorem squareOnBall : QuantitativeHoare unitBall square atZero 1 := by
  intro input hypothesis
  obtain ⟨low, high⟩ := hypothesis
  refine ⟨![0], rfl, ?_⟩
  intro coordinate
  fin_cases coordinate
  show |square.run input 0 - (![0] : Point 1) 0| ≤ 1
  have expand : square.run input 0 = input 0 * input 0 := by
    simp [square]
  rw [expand]
  simp only [Matrix.cons_val_zero, sub_zero]
  rw [abs_le]
  constructor <;> nlinarith [low, high]

/-- Coverage composition: the composite carries **only** the second stage's
error. The first stage's error of one is absorbed by the coverage, not
amplified -- compare `generalRuleOnBoundedRegion`, which pays `2 * 1 + 1`. -/
theorem coverageCarriesOnlyTheSecondError :
    QuantitativeHoare atOne (Circuit.compose Circuit.id square) atZero 1 :=
  coverageSequential firstStage zeroNeighbourhoodInBall squareOnBall

/-- The same conclusion the modulus rule reaches at `2 * 1 + 1 = 3`. Coverage
reaches it at `1`, so where it applies it is strictly the better rule. -/
theorem coverageBeatsTheModulusHere :
    QuantitativeHoare atOne (Circuit.compose Circuit.id square) atZero 1 :=
  coverageCarriesOnlyTheSecondError

/-- The exact-first-stage variant needs only an ordinary entailment. -/
theorem coverageExactVariant :
    QuantitativeHoare atOne (Circuit.compose Circuit.id square) atZero 1 :=
  coverageSequentialExact identityExact
    (fun point held => by
      have coordinateOne : point 0 = 1 := held
      exact ⟨by simp [coordinateOne], by simp [coordinateOne]⟩)
    squareOnBall

/-- Every predicate entails its own neighbourhood, in one step from the named
lemma: the goal that lemma-retrieving search could not reach while the fact
existed only inline (task 016). -/
theorem neighbourhoodSelfInOneStep {n : Nat} (p : Predicate n) (r : ℝ)
    (h : 0 ≤ r) : PredicateEntailment p (Neighbourhood p r) :=
  selfEntailsNeighbourhood h

#print axioms selfEntailsNeighbourhood
#print axioms canonicalSequential
#print axioms neighbourhoodSelfInOneStep

end Gimle.Forseti.Tests.SequentialHoare
