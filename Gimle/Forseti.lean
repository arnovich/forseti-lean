import Gimle.Asgard

/-! Forseti property support over the single Asgard circuit implementation.
Compatibility names below are aliases, not a second syntax or interpreter. -/

namespace Gimle.Forseti

export Gimle.Asgard (Point pointLeft pointRight pointAppend
  pointLeft_pointAppend pointRight_pointAppend Circuit LinfClose
  GlobalCircuitEquivalence circuitReflexivity circuitSymmetry circuitTransitivity)

namespace Circuit
export Gimle.Asgard.Circuit (id const scalar add multiplication split swap terminal
  compose parallel run)
end Circuit

structure Predicate (dimension : Nat) where
  holds : Point dimension → Prop

def QuantitativeCircuitEquivalence {inputDegree outputDegree : Nat}
    (source target : Circuit inputDegree outputDegree)
    (region : Predicate inputDegree) (epsilon : ℝ) : Prop :=
  Gimle.Asgard.QuantitativeCircuitEquivalence source target region.holds epsilon

def PredicateEquality {dimension : Nat}
    (left right : Predicate dimension) : Prop :=
  ∀ point, left.holds point ↔ right.holds point

def PredicateEntailment {dimension : Nat}
    (antecedent consequent : Predicate dimension) : Prop :=
  ∀ point, antecedent.holds point → consequent.holds point

def QuantitativePredicateEntailment {dimension : Nat}
    (antecedent consequent : Predicate dimension) (epsilon : ℝ) : Prop :=
  ∀ point, antecedent.holds point →
    ∃ ideal, consequent.holds ideal ∧ LinfClose epsilon point ideal

def ExactHoare {inputDegree outputDegree : Nat}
    (precondition : Predicate inputDegree)
    (circuit : Circuit inputDegree outputDegree)
    (postcondition : Predicate outputDegree) : Prop :=
  ∀ input, precondition.holds input → postcondition.holds (circuit.run input)

def QuantitativeHoare {inputDegree outputDegree : Nat}
    (precondition : Predicate inputDegree)
    (circuit : Circuit inputDegree outputDegree)
    (postcondition : Predicate outputDegree) (epsilon : ℝ) : Prop :=
  ∀ input, precondition.holds input →
    ∃ ideal, postcondition.holds ideal ∧ LinfClose epsilon (circuit.run input) ideal

def parallelCircuit {leftInput leftOutput rightInput rightOutput : Nat}
    (left : Circuit leftInput leftOutput)
    (right : Circuit rightInput rightOutput) :
    Circuit (leftInput + rightInput) (leftOutput + rightOutput) :=
  Circuit.parallel left right

def productPredicate {leftDimension rightDimension : Nat}
    (left : Predicate leftDimension) (right : Predicate rightDimension) :
    Predicate (leftDimension + rightDimension) where
  holds := fun point =>
    left.holds (pointLeft point) ∧ right.holds (pointRight point)

theorem predicateReflexivity {dimension : Nat} (predicate : Predicate dimension) :
    PredicateEquality predicate predicate := by
  intro point
  rfl

theorem predicateSymmetry {dimension : Nat}
    {left right : Predicate dimension}
    (premise : PredicateEquality left right) : PredicateEquality right left := by
  intro point
  exact (premise point).symm

theorem predicateTransitivity {dimension : Nat}
    {first second third : Predicate dimension}
    (left : PredicateEquality first second)
    (right : PredicateEquality second third) : PredicateEquality first third := by
  intro point
  exact (left point).trans (right point)

theorem predicateEntailmentFromEquality {dimension : Nat}
    {left right : Predicate dimension}
    (premise : PredicateEquality left right) : PredicateEntailment left right := by
  intro point hypothesis
  exact (premise point).mp hypothesis

theorem predicateEntailmentTransitivity {dimension : Nat}
    {first second third : Predicate dimension}
    (left : PredicateEntailment first second)
    (right : PredicateEntailment second third) : PredicateEntailment first third := by
  intro point hypothesis
  exact right point (left point hypothesis)

theorem predicateEqualityFromEntailments {dimension : Nat}
    {left right : Predicate dimension}
    (forward : PredicateEntailment left right)
    (reverse : PredicateEntailment right left) : PredicateEquality left right := by
  intro point
  exact ⟨forward point, reverse point⟩

theorem quantitativePredicateEntailmentWeakening {dimension : Nat}
    {antecedent consequent : Predicate dimension} {epsilon : ℝ}
    (nonnegative : 0 ≤ epsilon)
    (premise : PredicateEntailment antecedent consequent) :
    QuantitativePredicateEntailment antecedent consequent epsilon := by
  intro point hypothesis
  refine ⟨point, premise point hypothesis, ?_⟩
  intro coordinate
  simpa [LinfClose] using nonnegative

theorem exactHoareToQuantitativeZero {inputDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {circuit : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree}
    (premise : ExactHoare precondition circuit postcondition) :
    QuantitativeHoare precondition circuit postcondition 0 := by
  intro input hypothesis
  refine ⟨circuit.run input, premise input hypothesis, ?_⟩
  intro coordinate
  simp

theorem exactCircuitSubstitution {inputDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {source target : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree}
    (sourceProof : ExactHoare precondition source postcondition)
    (equivalence : GlobalCircuitEquivalence source target) :
    ExactHoare precondition target postcondition := by
  intro input hypothesis
  simpa [← equivalence input] using sourceProof input hypothesis

theorem approximateCircuitTransportExact {inputDegree outputDegree : Nat}
    {precondition region : Predicate inputDegree}
    {source target : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree} {epsilon : ℝ}
    (sourceProof : ExactHoare precondition source postcondition)
    (approximation : QuantitativeCircuitEquivalence source target region epsilon)
    (coverage : PredicateEntailment precondition region) :
    QuantitativeHoare precondition target postcondition epsilon := by
  intro input hypothesis
  refine ⟨source.run input, sourceProof input hypothesis, ?_⟩
  intro coordinate
  simpa [abs_sub_comm] using approximation input (coverage input hypothesis) coordinate

theorem quantitativeHoareZeroIsExact {inputDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {circuit : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree}
    (premise : QuantitativeHoare precondition circuit postcondition 0) :
    ExactHoare precondition circuit postcondition := by
  intro input hypothesis
  obtain ⟨ideal, idealPostcondition, close⟩ := premise input hypothesis
  have equal : circuit.run input = ideal := by
    funext coordinate
    have zeroAbsolute : |circuit.run input coordinate - ideal coordinate| = 0 :=
      le_antisymm (close coordinate) (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp zeroAbsolute)
  simpa [equal] using idealPostcondition

theorem approximateCircuitTransportZero {inputDegree outputDegree : Nat}
    {precondition region : Predicate inputDegree}
    {source target : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree}
    (sourceProof : ExactHoare precondition source postcondition)
    (approximation : QuantitativeCircuitEquivalence source target region 0)
    (coverage : PredicateEntailment precondition region) :
    ExactHoare precondition target postcondition :=
  quantitativeHoareZeroIsExact
    (approximateCircuitTransportExact sourceProof approximation coverage)

theorem approximateCircuitTransportQuantitative {inputDegree outputDegree : Nat}
    {precondition region : Predicate inputDegree}
    {source target : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree} {sourceError approximationError : ℝ}
    (sourceProof : QuantitativeHoare precondition source postcondition sourceError)
    (approximation :
      QuantitativeCircuitEquivalence source target region approximationError)
    (coverage : PredicateEntailment precondition region) :
    QuantitativeHoare precondition target postcondition
      (sourceError + approximationError) := by
  intro input hypothesis
  obtain ⟨ideal, idealPostcondition, sourceClose⟩ := sourceProof input hypothesis
  refine ⟨ideal, idealPostcondition, ?_⟩
  intro coordinate
  calc
    |target.run input coordinate - ideal coordinate| ≤
        |target.run input coordinate - source.run input coordinate| +
          |source.run input coordinate - ideal coordinate| := abs_sub_le _ _ _
    _ ≤ approximationError + sourceError :=
      add_le_add
        (by simpa [abs_sub_comm] using
          approximation input (coverage input hypothesis) coordinate)
        (sourceClose coordinate)
    _ = sourceError + approximationError := add_comm _ _

theorem hoareConsequence {inputDegree outputDegree : Nat}
    {strong weak : Predicate inputDegree}
    {circuit : Circuit inputDegree outputDegree}
    {narrow broad : Predicate outputDegree}
    (source : ExactHoare weak circuit narrow)
    (precondition : PredicateEntailment strong weak)
    (postcondition : PredicateEntailment narrow broad) :
    ExactHoare strong circuit broad := by
  intro input hypothesis
  exact postcondition _ (source input (precondition input hypothesis))

theorem exactHoareMonoidal
    {leftInput leftOutput rightInput rightOutput : Nat}
    {leftPrecondition : Predicate leftInput}
    {rightPrecondition : Predicate rightInput}
    {leftPostcondition : Predicate leftOutput}
    {rightPostcondition : Predicate rightOutput}
    {leftCircuit : Circuit leftInput leftOutput}
    {rightCircuit : Circuit rightInput rightOutput}
    (left : ExactHoare leftPrecondition leftCircuit leftPostcondition)
    (right : ExactHoare rightPrecondition rightCircuit rightPostcondition) :
    ExactHoare
      (productPredicate leftPrecondition rightPrecondition)
      (parallelCircuit leftCircuit rightCircuit)
      (productPredicate leftPostcondition rightPostcondition) := by
  intro input hypothesis
  constructor
  · simpa [parallelCircuit, pointAppend, pointLeft, Fin.addCases_left] using
      left (pointLeft input) hypothesis.1
  · simpa [parallelCircuit, pointAppend, pointRight, Fin.addCases_right] using
      right (pointRight input) hypothesis.2

theorem quantitativeHoareMonoidal
    {leftInput leftOutput rightInput rightOutput : Nat}
    {leftPrecondition : Predicate leftInput}
    {rightPrecondition : Predicate rightInput}
    {leftPostcondition : Predicate leftOutput}
    {rightPostcondition : Predicate rightOutput}
    {leftCircuit : Circuit leftInput leftOutput}
    {rightCircuit : Circuit rightInput rightOutput}
    {leftError rightError : ℝ}
    (left : QuantitativeHoare
      leftPrecondition leftCircuit leftPostcondition leftError)
    (right : QuantitativeHoare
      rightPrecondition rightCircuit rightPostcondition rightError) :
    QuantitativeHoare
      (productPredicate leftPrecondition rightPrecondition)
      (parallelCircuit leftCircuit rightCircuit)
      (productPredicate leftPostcondition rightPostcondition)
      (max leftError rightError) := by
  intro input hypothesis
  obtain ⟨leftIdeal, leftPost, leftClose⟩ := left _ hypothesis.1
  obtain ⟨rightIdeal, rightPost, rightClose⟩ := right _ hypothesis.2
  refine ⟨pointAppend leftIdeal rightIdeal, ?_, ?_⟩
  · constructor
    · simpa [pointAppend, pointLeft, Fin.addCases_left] using leftPost
    · simpa [pointAppend, pointRight, Fin.addCases_right] using rightPost
  intro coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro leftCoordinate
    simpa [parallelCircuit, pointAppend, pointLeft] using
      le_trans (leftClose leftCoordinate) (le_max_left _ _)
  · intro rightCoordinate
    simpa [parallelCircuit, pointAppend, pointRight] using
      le_trans (rightClose rightCoordinate) (le_max_right _ _)

/-! ### Sequential composition

Running one circuit after another. `Circuit.compose first second` runs `first`
first, matching Asgard.

The exact rule is the expected one. The quantitative rule is **not**: composing
two approximate triples does not add their errors, and the reason is worth
stating precisely.

`QuantitativeHoare pre f mid e` says the *actual* output `f.run input` is within
`e` of some *ideal* point satisfying `mid`. The second triple's guarantee applies
at points satisfying `mid` — that is, at the ideal one. But the circuit that runs
next is fed the actual one. Nothing relates `second.run actual` to
`second.run ideal` unless something bounds how `second` amplifies the gap, and a
polynomial circuit can amplify it without limit. `Tests/SequentialHoare.lean`
exhibits a pair of valid triples whose naive sum is false by a factor of ten.

Two families of sound rule follow, and they pay for the gap differently.

`exactThenQuantitativeHoareSequential` needs no side condition, because an exact
first stage makes the actual point *be* the ideal one.

`quantitativeHoareSequential` bounds the amplification with an explicit modulus.
`canonicalSequential` is the form to reach for, taking the neighbourhood of
`middle` as the modulus region so both coverage hypotheses are discharged.

`coverageSequential` instead requires the second stage's precondition to cover
that neighbourhood. Then no amplification happens at all and the composite
carries only the second stage's error. Where the coverage can be established
this is the better rule, and it is the one the deleted Python checker used. -/

/-- Sequential composition of exact triples. -/
theorem exactHoareSequential {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    (source : ExactHoare precondition first middle)
    (target : ExactHoare middle second postcondition) :
    ExactHoare precondition (Circuit.compose first second) postcondition := by
  intro input hypothesis
  exact target _ (source input hypothesis)

/-- An exact first stage composes with an approximate second stage, carrying the
second stage's error unchanged.

No side condition is needed: the first stage's output satisfies `middle` on the
nose, so the second stage's guarantee applies to the point actually produced. -/
theorem exactThenQuantitativeHoareSequential
    {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {error : ℝ}
    (source : ExactHoare precondition first middle)
    (target : QuantitativeHoare middle second postcondition error) :
    QuantitativeHoare precondition (Circuit.compose first second)
      postcondition error := by
  intro input hypothesis
  exact target _ (source input hypothesis)

/-- A bound on how far a circuit separates two nearby points of a region.

This is the side condition sequential composition needs, and it is a real
obligation: it must be established for the specific circuit and region. It is
not derivable from a circuit's syntax in general, because a polynomial is not
globally Lipschitz -- `Tests/SequentialHoare.lean` proves squaring has no
modulus at all on an unbounded region.

Note the notion is vacuous on an empty or singleton region, where any gap is
admitted, including a negative one. That is exactly why
`quantitativeHoareSequential` needs both coverage hypotheses; dropping either
one lets a vacuous modulus through.

Asgard's `Gimle.Asgard.Approximation.LipschitzOn` is the affine-in-delta
special case, and `Gimle/Forseti/Approximation.lean` bridges to it. This
definition is kept separate because it admits non-linear moduli and because
importing Asgard's approximation layer here would pull `Budget`, `Claim`,
`Sample` and `Observation` into the module a foreign candidate may import. -/
def CircuitModulus {inputDegree outputDegree : Nat}
    (circuit : Circuit inputDegree outputDegree)
    (region : Predicate inputDegree) (inputGap outputGap : ℝ) : Prop :=
  ∀ left right, region.holds left → region.holds right →
    LinfClose inputGap left right →
      LinfClose outputGap (circuit.run left) (circuit.run right)

/-- Sequential composition of quantitative triples.

The errors do not add. What is carried is the second circuit's *response* to the
first stage's error — `amplified`, supplied by the modulus — plus the second
stage's own error. Both the ideal intermediate point and the one actually
produced must lie in the modulus region, which is what the two coverage
hypotheses require. -/
theorem quantitativeHoareSequential
    {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle region : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {sourceError amplified targetError : ℝ}
    (source : QuantitativeHoare precondition first middle sourceError)
    (target : QuantitativeHoare middle second postcondition targetError)
    (modulus : CircuitModulus second region sourceError amplified)
    (idealCovered : PredicateEntailment middle region)
    (actualCovered :
      ∀ input, precondition.holds input → region.holds (first.run input)) :
    QuantitativeHoare precondition (Circuit.compose first second)
      postcondition (amplified + targetError) := by
  intro input hypothesis
  obtain ⟨ideal, idealMiddle, sourceClose⟩ := source input hypothesis
  obtain ⟨final, finalPost, targetClose⟩ := target ideal idealMiddle
  refine ⟨final, finalPost, ?_⟩
  intro coordinate
  have separation :
      LinfClose amplified (second.run (first.run input)) (second.run ideal) :=
    modulus _ _ (actualCovered input hypothesis) (idealCovered ideal idealMiddle)
      sourceClose
  calc
    |(Circuit.compose first second).run input coordinate - final coordinate| =
        |second.run (first.run input) coordinate - final coordinate| := by rfl
    _ ≤ |second.run (first.run input) coordinate - second.run ideal coordinate| +
          |second.run ideal coordinate - final coordinate| := abs_sub_le _ _ _
    _ ≤ amplified + targetError :=
      add_le_add (separation coordinate) (targetClose coordinate)

/-! ### The modulus is a small theory, not a bare hypothesis -/

/-- Every circuit maps coincident points to coincident points. -/
theorem modulusZero {inputDegree outputDegree : Nat}
    (circuit : Circuit inputDegree outputDegree) (region : Predicate inputDegree) :
    CircuitModulus circuit region 0 0 := by
  intro left right _ _ close
  have agree : left = right := by
    funext coordinate
    have bound := close coordinate
    have zero : |left coordinate - right coordinate| = 0 :=
      le_antisymm (by simpa using bound) (abs_nonneg _)
    linarith [sub_eq_zero.mp (abs_eq_zero.mp zero)]
  intro coordinate
  simp [agree]

/-- A modulus may be weakened in either gap: tighten what goes in, loosen what
comes out. This is what lets a modulus proved at one radius be reused at the
radius a particular triple happens to supply. -/
theorem modulusWeaken {inputDegree outputDegree : Nat}
    {circuit : Circuit inputDegree outputDegree} {region : Predicate inputDegree}
    {inputGap outputGap tighterInput looserOutput : ℝ}
    (modulus : CircuitModulus circuit region inputGap outputGap)
    (narrower : tighterInput ≤ inputGap) (wider : outputGap ≤ looserOutput) :
    CircuitModulus circuit region tighterInput looserOutput :=
  fun left right leftHeld rightHeld close coordinate =>
    (modulus left right leftHeld rightHeld
      (fun i => (close i).trans narrower) coordinate).trans wider

/-- A modulus holds on any subregion of one it holds on. Regions shrink
freely; it is the gaps that cost something. -/
theorem modulusNarrow {inputDegree outputDegree : Nat}
    {circuit : Circuit inputDegree outputDegree}
    {wide narrow : Predicate inputDegree} {inputGap outputGap : ℝ}
    (modulus : CircuitModulus circuit wide inputGap outputGap)
    (inclusion : PredicateEntailment narrow wide) :
    CircuitModulus circuit narrow inputGap outputGap :=
  fun left right leftHeld rightHeld =>
    modulus left right (inclusion left leftHeld) (inclusion right rightHeld)

/-- Moduli compose, given that the first circuit carries its region into the
second's. So a chain of stages has a modulus whenever its links do. -/
theorem modulusCompose {inputDegree middleDegree outputDegree : Nat}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {region : Predicate inputDegree} {middleRegion : Predicate middleDegree}
    {inputGap middleGap outputGap : ℝ}
    (firstModulus : CircuitModulus first region inputGap middleGap)
    (secondModulus : CircuitModulus second middleRegion middleGap outputGap)
    (coverage :
      ∀ point, region.holds point → middleRegion.holds (first.run point)) :
    CircuitModulus (Circuit.compose first second) region inputGap outputGap :=
  fun left right leftHeld rightHeld close =>
    secondModulus _ _ (coverage left leftHeld) (coverage right rightHeld)
      (firstModulus left right leftHeld rightHeld close)

/-! ### Utility rules the sequential rules need

These are general facts about `QuantitativeHoare` that had no home before. -/

/-- A quantitative triple may be restated at any larger error. -/
theorem quantitativeHoareWeaken {inputDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {circuit : Circuit inputDegree outputDegree}
    {postcondition : Predicate outputDegree} {error larger : ℝ}
    (source : QuantitativeHoare precondition circuit postcondition error)
    (ordered : error ≤ larger) :
    QuantitativeHoare precondition circuit postcondition larger := by
  intro input hypothesis
  obtain ⟨ideal, held, close⟩ := source input hypothesis
  exact ⟨ideal, held, fun coordinate => (close coordinate).trans ordered⟩

/-- The quantitative counterpart of `hoareConsequence`. Strengthening the
precondition and weakening the postcondition preserve a quantitative triple. -/
theorem quantitativeHoareConsequence {inputDegree outputDegree : Nat}
    {strong weak : Predicate inputDegree}
    {circuit : Circuit inputDegree outputDegree}
    {narrow broad : Predicate outputDegree} {error : ℝ}
    (source : QuantitativeHoare weak circuit narrow error)
    (precondition : PredicateEntailment strong weak)
    (postcondition : PredicateEntailment narrow broad) :
    QuantitativeHoare strong circuit broad error := by
  intro input hypothesis
  obtain ⟨ideal, held, close⟩ := source input (precondition input hypothesis)
  exact ⟨ideal, postcondition _ held, close⟩

/-! ### The canonical region

`Neighbourhood post error` is the set of points within `error` of `post`. It
makes the error in a quantitative triple visible as a fattened postcondition,
which is what `QuantitativeHoare` already means:
`quantitativeIsExactIntoNeighbourhood` records that identity.

Taking it as the modulus region discharges both coverage hypotheses of
`quantitativeHoareSequential`, and is the form a caller should reach for. -/

/-- Points within `radius` of the core. This is the semantic fattening; the
syntactic `Fattened` in `Gimle/Forseti/Syntax.lean` is its counterpart one
layer up, and cannot be used here because that module imports this one. -/
def Neighbourhood {dimension : Nat} (core : Predicate dimension) (radius : ℝ) :
    Predicate dimension :=
  ⟨fun point => ∃ ideal, core.holds ideal ∧ LinfClose radius point ideal⟩

/-- Every predicate entails its own neighbourhood at a non-negative radius:
each point is its own witness, at distance zero.

`Fattened.core_entails` in `Gimle/Forseti/Syntax.lean` is the syntactic
counterpart, for a `Fattened` node. -/
theorem selfEntailsNeighbourhood {dimension : Nat} {core : Predicate dimension}
    {radius : ℝ} (nonnegative : 0 ≤ radius) :
    PredicateEntailment core (Neighbourhood core radius) :=
  fun point held => ⟨point, held, fun _ => by simpa using nonnegative⟩

/-- A quantitative triple *is* an exact triple into a fattened postcondition.
This is why `exactThenQuantitativeHoareSequential` needs no side condition: at
that postcondition it is `exactHoareSequential`. -/
theorem quantitativeIsExactIntoNeighbourhood {inputDegree outputDegree : Nat}
    (precondition : Predicate inputDegree)
    (circuit : Circuit inputDegree outputDegree)
    (postcondition : Predicate outputDegree) (error : ℝ) :
    QuantitativeHoare precondition circuit postcondition error ↔
      ExactHoare precondition circuit (Neighbourhood postcondition error) :=
  Iff.rfl

/-- Sequential composition at the canonical region. Both coverage hypotheses
are discharged: the actual intermediate point is covered by the source triple
itself, and the ideal one by each point witnessing itself. Only the modulus
remains, and it must hold on a *neighbourhood* of `middle` rather than on
`middle` -- which is the real content of the general rule. -/
theorem canonicalSequential {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {sourceError amplified targetError : ℝ}
    (nonnegative : 0 ≤ sourceError)
    (source : QuantitativeHoare precondition first middle sourceError)
    (target : QuantitativeHoare middle second postcondition targetError)
    (modulus :
      CircuitModulus second (Neighbourhood middle sourceError) sourceError amplified) :
    QuantitativeHoare precondition (Circuit.compose first second)
      postcondition (amplified + targetError) :=
  quantitativeHoareSequential source target modulus
    (selfEntailsNeighbourhood nonnegative)
    (fun input held => source input held)

/-- Sequential composition paid for by **coverage** rather than by a modulus.

If the second stage's precondition already covers the neighbourhood the first
stage's output can land in, then the second stage's guarantee applies at the
point actually produced. Nothing is amplified and nothing is added: the
composite carries the second stage's error alone.

This is the rule the deleted Python checker used, and where it applies it is
strictly better than `quantitativeHoareSequential` -- no modulus, so no bounded
region and no interval propagation. The two are complementary: this one wants a
second stage tolerant of a neighbourhood, the modulus rule wants a second stage
with a tight precondition.

Discharging the coverage obligation is an ordinary predicate entailment, which
is exactly what the semi-algebraic syntax in `Gimle/Forseti/Syntax.lean` exists
to hand to a decision procedure. -/
theorem coverageSequential {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle nextPrecondition : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {sourceError targetError : ℝ}
    (source : QuantitativeHoare precondition first middle sourceError)
    (coverage :
      PredicateEntailment (Neighbourhood middle sourceError) nextPrecondition)
    (target : QuantitativeHoare nextPrecondition second postcondition targetError) :
    QuantitativeHoare precondition (Circuit.compose first second)
      postcondition targetError := by
  intro input hypothesis
  exact target _ (coverage _ (source input hypothesis))

/-- The exact case of coverage composition: an exact first stage needs only
that its postcondition entails the next precondition. -/
theorem coverageSequentialExact {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle nextPrecondition : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {targetError : ℝ}
    (source : ExactHoare precondition first middle)
    (coverage : PredicateEntailment middle nextPrecondition)
    (target : QuantitativeHoare nextPrecondition second postcondition targetError) :
    QuantitativeHoare precondition (Circuit.compose first second)
      postcondition targetError := by
  intro input hypothesis
  exact target _ (coverage _ (source input hypothesis))

/-- Quantitative then exact. Error on the second stage is free; error on the
first is what costs a modulus. Stated for completeness, because "two sound
rules" otherwise reads as though this combination were unsupported. -/
theorem quantitativeThenExactSequential
    {inputDegree middleDegree outputDegree : Nat}
    {precondition : Predicate inputDegree}
    {middle region : Predicate middleDegree}
    {postcondition : Predicate outputDegree}
    {first : Circuit inputDegree middleDegree}
    {second : Circuit middleDegree outputDegree}
    {sourceError amplified : ℝ}
    (source : QuantitativeHoare precondition first middle sourceError)
    (target : ExactHoare middle second postcondition)
    (modulus : CircuitModulus second region sourceError amplified)
    (idealCovered : PredicateEntailment middle region)
    (actualCovered :
      ∀ input, precondition.holds input → region.holds (first.run input)) :
    QuantitativeHoare precondition (Circuit.compose first second)
      postcondition amplified := by
  have chained := quantitativeHoareSequential source
    (exactHoareToQuantitativeZero target) modulus idealCovered actualCovered
  simpa using chained

end Gimle.Forseti
