import Gimle.Forseti.StreamObservation
import Gimle.Forseti.FieldBound
import Gimle.Asgard.Streams.Realization

/-! Evaluated real fields of stream circuit outputs, checked by polynomial
certificates.

`StreamObservation` reads formulas on finitely many exact output
*coefficients*. This module reads them on the *values* of the real function an
output stream represents, and it goes through asgard-lean 024: a stream has an
evaluated field only when its **whole** coefficient family is that of one
rational polynomial (`Streams.Realizes`, equivalently `Streams.FiniteSupport`),
and the field is that polynomial evaluated at real points (`Streams.field`).

A `FieldSpec` names the formula coordinates: the `d` space-time axes, in the
stream's axis order, then `k` fixed parameters, then one name for the field
value. `FieldSpec.Observes basis port θ domain post` is the stream predicate

  *output port `port` is realized by some rational polynomial `q`, and at every
  real space-time point `x` where `domain` holds, `post` holds, both read at
  `(x, θ, q(x))`.*

It names the finite polynomial class (the realization witness is part of the
claim, for the whole stream; a window or prefix is not one), the analytic
interpretation (`Streams.field`), the fixed parameters and the stated domain.
The original circuit, its full input streams and the initial profile are named
by the `StreamHoare` precondition the predicate is used with.

**The field transfer rule.** `lift`: a total contract that the output port is
realized by `q`, and a bound on `q`'s field over the domain, give the field
contract. `leaf_bound` gets that bound from a 017 entailment (`leafGoal`) whose
consequent is `post` with the field-value coordinate replaced by a polynomial
expression, *together with* a proof that this expression evaluates to
`q`'s field (`agrees`) — the bridge. Coefficient constraints on the output are
never an input to this rule: `u = x` has nonnegative coefficients and a
negative field (`Tests/FieldObservation.lean`).

**Refutation.** `refutes_root` refutes a field contract only through an
admitted full input, its related output, a realization of the observed port,
and a point of the domain where the postcondition fails on the realized field.
`refutes_root_answer` lifts a 017 leaf counterexample the same way.
-/

namespace Gimle.Forseti.FieldObservation

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Stream
open Gimle.Asgard

variable {basis : Streams.Basis} {d n m k : Nat}

/-- The formula coordinates of a field claim, in order: axes, parameters, value. -/
def fieldNames (axes : Fin d → String) (parameters : Fin k → String) (value : String) :
    List String :=
  List.ofFn axes ++ List.ofFn parameters ++ [value]

/-- The named coordinates of a field claim: the stream's axes in axis order, the
fixed parameters, then the field value. The context is bound to those names
(`named`), so a formula written by name reads what the name describes. -/
structure FieldSpec (d k : Nat) where
  /-- The space-time axis names, in the stream's axis order. -/
  axes : Fin d → String
  /-- The fixed parameter names. -/
  parameters : Fin k → String
  /-- The name of the field value. -/
  value : String
  /-- The formula context. -/
  context : Syntax.Context
  /-- The context is exactly axes, then parameters, then the value. -/
  named : context.names = fieldNames axes parameters value

namespace FieldSpec

variable (spec : FieldSpec d k)

/-- One coordinate per axis, per parameter, and one for the value. -/
theorem dimension_eq : spec.context.dimension = d + k + 1 := by
  simp [Context.dimension, spec.named, fieldNames]; omega

/-- The formula point for space-time point `x`, parameters `θ` and value `v`. -/
def point (x : Fin d → ℝ) (θ : Fin k → ℝ) (v : ℝ) : Point spec.context.dimension :=
  fun i =>
    let j := (Fin.cast spec.dimension_eq i).val
    if axis : j < d then x ⟨j, axis⟩
    else if parameter : j < d + k then θ ⟨j - d, by omega⟩
    else v

/-- The field-value coordinate. -/
def valueCoordinate : Fin spec.context.dimension :=
  Fin.cast spec.dimension_eq.symm (Fin.last (d + k))

@[simp] theorem point_value (x : Fin d → ℝ) (θ : Fin k → ℝ) (v : ℝ) :
    spec.point x θ v spec.valueCoordinate = v := by
  simp [point, valueCoordinate]

/-- The formula point of a realized field: parameters cast from ℚ, value
`q(x)`. -/
noncomputable def fieldPoint (x : Fin d → ℝ) (θ : Fin k → ℚ) (q : Streams.Poly d) :
    Point spec.context.dimension :=
  spec.point x (fun i => (θ i : ℝ)) (Streams.field q x)

/-- **The evaluated-field predicate.** The observed port is realized, as a whole
stream, by a rational polynomial `q`; at every real space-time point where the
domain holds, the postcondition holds at `(x, θ, q(x))`. -/
def Observes (basis : Streams.Basis) (port : Fin m) (θ : Fin k → ℚ)
    (domain post : Formula spec.context.dimension) : StreamPredicate d m :=
  fun y => ∃ q : Streams.Poly d, Streams.Realizes basis (y port) q ∧
    ∀ x, domain.holds (spec.fieldPoint x θ q) → post.holds (spec.fieldPoint x θ q)

/-- A stream is realized by at most one polynomial. -/
theorem realizes_unique {a : Streams.Stream d} {p q : Streams.Poly d}
    (hp : Streams.Realizes basis a p) (hq : Streams.Realizes basis a q) : p = q :=
  Streams.ofPoly_injective basis (hp.symm.trans hq)

/-- Once the port is known to be realized by `q`, the predicate is the bound on
`q`'s field. -/
theorem observes_iff {port : Fin m} {θ : Fin k → ℚ}
    {domain post : Formula spec.context.dimension} {y : Streams.StreamPoint d m}
    {q : Streams.Poly d}
    (realized : Streams.Realizes basis (y port) q) :
    spec.Observes basis port θ domain post y ↔
      ∀ x, domain.holds (spec.fieldPoint x θ q) → post.holds (spec.fieldPoint x θ q) := by
  constructor
  · rintro ⟨q', realized', bound⟩
    rwa [realizes_unique realized realized'] at *
  · exact fun bound => ⟨q, realized, bound⟩

/-- The predicate requires finite support of the **whole** observed stream. -/
theorem observes_finiteSupport {port : Fin m} {θ : Fin k → ℚ}
    {domain post : Formula spec.context.dimension} {y : Streams.StreamPoint d m}
    (holds : spec.Observes basis port θ domain post y) : Streams.FiniteSupport (y port) :=
  let ⟨q, realized, _⟩ := holds
  (Streams.finiteSupport_iff basis _).mpr ⟨q, realized⟩

/-- An unrealized port — an infinite tail, whatever its prefix — has no field,
and the predicate fails. -/
theorem not_observes {port : Fin m} {θ : Fin k → ℚ}
    {domain post : Formula spec.context.dimension} {y : Streams.StreamPoint d m}
    (unrealized : ¬ ∃ q, Streams.Realizes basis (y port) q) :
    ¬ spec.Observes basis port θ domain post y :=
  fun ⟨q, realized, _⟩ => unrealized ⟨q, realized⟩

/-! ### The transfer rule -/

/-- **A bound on the realized field is a field contract over the circuit.** Every
input admitted by `pre` is in the circuit's domain and its output port is
realized by `q` (`realized`, a total stream contract); `q`'s field satisfies
the postcondition on the domain (`bound`). -/
theorem lift {pre : StreamPredicate d n} {circuit : Streams.Circuit basis d n m}
    {port : Fin m} {θ : Fin k → ℚ} {domain post : Formula spec.context.dimension}
    {q : Streams.Poly d}
    (realized : StreamHoare pre circuit fun y => Streams.Realizes basis (y port) q)
    (bound : ∀ x, domain.holds (spec.fieldPoint x θ q) → post.holds (spec.fieldPoint x θ q)) :
    StreamHoare pre circuit (spec.Observes basis port θ domain post) :=
  fun x admitted =>
    let ⟨defined, realizes⟩ := realized x admitted
    ⟨defined, q, realizes, bound⟩

/-- Replace the field-value coordinate by an expression; keep every other
coordinate. -/
def valueAs (expression : Polynomial.Expr spec.context.dimension) :
    Fin spec.context.dimension → Polynomial.Expr spec.context.dimension :=
  fun i => if i = spec.valueCoordinate then expression else .var i

/-- **The leaf question.** Over the claim's own context: does `antecedent`
entail `post` with the field value replaced by `expression`? An ordinary 017
`Goal`; a certificate or counterexample is checked against it as posed. -/
def leafGoal (antecedent post : Formula spec.context.dimension)
    (expression : Polynomial.Expr spec.context.dimension) : Goal :=
  ⟨spec.context, antecedent, post.substitute (spec.valueAs expression)⟩

/-- Where the expression evaluates to the value coordinate, substituting it
changes nothing. -/
theorem valueAs_eval {expression : Polynomial.Expr spec.context.dimension}
    {z : Point spec.context.dimension} (agrees : expression.eval z = z spec.valueCoordinate) :
    (fun i => (spec.valueAs expression i).eval z) = z := by
  funext i
  by_cases h : i = spec.valueCoordinate
  · subst h; simpa [valueAs] using agrees
  · simp [valueAs, h]

/-- **The bridge.** A checked leaf entailment bounds the realized field, given
that the leaf's expression *is* that field (`agrees`) and that the stated
domain implies the leaf antecedent at the realized points (`strengthen`, e.g.
a box bound). -/
theorem leaf_bound {θ : Fin k → ℚ} {domain antecedent post : Formula spec.context.dimension}
    {expression : Polynomial.Expr spec.context.dimension} {q : Streams.Poly d}
    (entails : (spec.leafGoal antecedent post expression).Entailment)
    (agrees : ∀ x, expression.eval (spec.fieldPoint x θ q) = Streams.field q x)
    (strengthen : ∀ x, domain.holds (spec.fieldPoint x θ q) →
      antecedent.holds (spec.fieldPoint x θ q)) :
    ∀ x, domain.holds (spec.fieldPoint x θ q) → post.holds (spec.fieldPoint x θ q) := by
  intro x inside
  have holds := entails _ (strengthen x inside)
  simp only [leafGoal, Formula.substitute_holds] at holds
  rwa [spec.valueAs_eval (by rw [agrees]; simp [fieldPoint])] at holds

/-- **The field transfer rule, end to end.** A realization contract, a 017
certificate that checks against the leaf goal, the field bridge and the domain
strengthening give the field contract over the original circuit. -/
theorem lift_certificate {pre : StreamPredicate d n} {circuit : Streams.Circuit basis d n m}
    {port : Fin m} {θ : Fin k → ℚ} {domain antecedent post : Formula spec.context.dimension}
    {expression : Polynomial.Expr spec.context.dimension} {q : Streams.Poly d}
    (realized : StreamHoare pre circuit fun y => Streams.Realizes basis (y port) q)
    (certificate : EntailmentCertificate spec.context.dimension)
    (valid : certificate.check (spec.leafGoal antecedent post expression) = true)
    (agrees : ∀ x, expression.eval (spec.fieldPoint x θ q) = Streams.field q x)
    (strengthen : ∀ x, domain.holds (spec.fieldPoint x θ q) →
      antecedent.holds (spec.fieldPoint x θ q)) :
    StreamHoare pre circuit (spec.Observes basis port θ domain post) :=
  spec.lift realized
    (spec.leaf_bound (EntailmentCertificate.sound _ certificate valid) agrees strengthen)

/-! ### Refutation -/

/-- **A field contract is refuted only through an admitted full input.** It
must be admitted by `pre`, related by the circuit to an output whose observed
port is realized by `q`, and `q`'s field must fail the postcondition at a
point of the domain. -/
theorem refutes_root {pre : StreamPredicate d n} {circuit : Streams.Circuit basis d n m}
    {port : Fin m} {θ : Fin k → ℚ} {domain post : Formula spec.context.dimension}
    (x : Streams.StreamPoint d n) (admitted : pre x) {y : Streams.StreamPoint d m}
    (related : circuit.Rel x y)
    {q : Streams.Poly d} (realized : Streams.Realizes basis (y port) q) (z : Fin d → ℝ)
    (inside : domain.holds (spec.fieldPoint z θ q))
    (fails : ¬ post.holds (spec.fieldPoint z θ q)) :
    ¬ StreamHoare pre circuit (spec.Observes basis port θ domain post) := by
  intro hoare
  obtain ⟨_, output⟩ := (circuit.rel_iff x y).mp related
  have holds := (hoare x admitted).2
  rw [← output, spec.observes_iff realized] at holds
  exact fails (holds z inside)

end FieldSpec

/-- What a counterexample that checks says, at the point it names. -/
theorem refutes_at {goal : Goal} {answer : Syntax.Context.Assignment}
    (valid : refutes goal answer = true) :
    goal.antecedent.holds (fun i =>
        (((Syntax.Context.valueOf answer (goal.context.name i)).getD 0 : ℚ) : ℝ)) ∧
      ¬ goal.consequent.holds (fun i =>
        (((Syntax.Context.valueOf answer (goal.context.name i)).getD 0 : ℚ) : ℝ)) := by
  unfold refutes at valid
  split at valid
  · rename_i point read
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at valid
    rw [Syntax.Context.read_eq read] at valid
    refine ⟨(Formula.holdsQ_iff _ _).mp valid.1, fun holds => ?_⟩
    have back := (Formula.holdsQ_iff _ _).mpr holds
    exact absurd (valid.2.symm.trans back) (by decide)
  · cases valid

namespace FieldSpec

variable (spec : FieldSpec d k)

/-- **A leaf counterexample lifted to the root.** The answer refutes the leaf
goal as posed (antecedent: the stated domain); an admitted full input is
related to an output whose port is realized by `q`; the answer names
`(z, θ, q(z))` coordinate by coordinate (`reads`); and the leaf's expression is
`q`'s field there (`agrees`). Then the field contract over the circuit fails. -/
theorem refutes_root_answer {pre : StreamPredicate d n}
    {circuit : Streams.Circuit basis d n m} {port : Fin m} {θ : Fin k → ℚ}
    {domain post : Formula spec.context.dimension}
    {expression : Polynomial.Expr spec.context.dimension} {answer : Syntax.Context.Assignment}
    (valid : refutes (spec.leafGoal domain post expression) answer = true)
    (x : Streams.StreamPoint d n) (admitted : pre x) {y : Streams.StreamPoint d m}
    (related : circuit.Rel x y)
    {q : Streams.Poly d} (realized : Streams.Realizes basis (y port) q) (z : Fin d → ℝ)
    (reads : ∀ i, spec.fieldPoint z θ q i =
      (((Syntax.Context.valueOf answer (spec.context.name i)).getD 0 : ℚ) : ℝ))
    (agrees : expression.eval (spec.fieldPoint z θ q) = Streams.field q z) :
    ¬ StreamHoare pre circuit (spec.Observes basis port θ domain post) := by
  obtain ⟨inside, fails⟩ := refutes_at valid
  have same : (fun i => (((Syntax.Context.valueOf answer (spec.context.name i)).getD 0 : ℚ) : ℝ))
      = spec.fieldPoint z θ q := (funext reads).symm
  simp only [leafGoal] at inside fails
  rw [same] at inside fails
  refine spec.refutes_root x admitted related realized z inside fun holds => fails ?_
  rw [Formula.substitute_holds, spec.valueAs_eval (by rw [agrees]; simp [fieldPoint])]
  exact holds

end FieldSpec

#print axioms FieldSpec.observes_iff
#print axioms FieldSpec.lift
#print axioms FieldSpec.leaf_bound
#print axioms FieldSpec.lift_certificate
#print axioms FieldSpec.refutes_root
#print axioms FieldSpec.refutes_root_answer

end Gimle.Forseti.FieldObservation
