import Gimle.Forseti.Examples.HeatFieldBound

/-! Hostile cases for field contracts over stream circuits.

Each is stated at the circuit level, as a failing `StreamHoare` field contract
refuted through an admitted full input, its related output and a realized
field:

* an altered initial profile (`2x²`) under the bound proved for `x²`;
* the unit-strip bound reused on a wider strip;
* a boundary known only on a finite window presented as the full profile, and
  an infinite-tailed stream with a polynomial prefix, which has no field;
* `u = x`, whose output coefficients are all nonnegative, refuted as a
  nonnegative field at `x = -1`.

The axiom policy is asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.FieldObservation

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Stream
open Gimle.Forseti.FieldObservation
open Gimle.Forseti.Examples.HeatFieldBound
open Gimle.Asgard

/-! ### An altered initial profile -/

/-- The profile `2x²` has the solution `2x² + 4t`; the bound `3` proved for
`x²` fails for it at `(t, x) = (1, 1)`, where `u = 6`. -/
theorem altered_profile (basis : Streams.Basis) :
    ¬ StreamHoare (Solves basis (profile 2 0)) (Streams.Heat.circuit basis)
      (unitSpec.Observes basis 1 ![] unitDomain (unitPost 3)) := by
  refine unitSpec.refutes_root _ (solves_solution basis _ 0)
    (Streams.Heat.circuit_solution basis _ 0) (q := Streams.Heat.solution _) rfl ![1, 1] ?_ ?_
  · simp only [unitDomain, Formula.holds, Relation.holds, eval_add, eval_sub, eval_ofNat, ut_eval,
      ux_eval]
    norm_num
  · simp only [unitPost, Formula.holds, Relation.holds, eval_sub, eval_rational, uu_eval,
      field_solution]
    norm_num

/-- The `x²` leaf certificate does not check against the altered field. -/
example : unitCertificate.check
    (unitSpec.leafGoal unitAntecedent (unitPost 3) (2 * ux * ux + 4 * ut)) = false := by
  decide +kernel

/-! ### A narrowed domain reused as a wider claim -/

/-- `0 ≤ t ≤ 1`, `-2 ≤ x ≤ 2`. -/
def wideDomain : Formula unitSpec.context.dimension :=
  (Formula.atom .ge ut).and ((Formula.atom .le (ut - 1)).and
    ((Formula.atom .ge (ux + 2)).and (.atom .le (ux - 2))))

/-- The unit-strip bound `3` on the wider strip fails at `(t, x) = (0, 2)`:
`u = 4`. -/
theorem wider_domain (basis : Streams.Basis) :
    ¬ StreamHoare (Solves basis (_root_.Polynomial.X ^ 2)) (Streams.Heat.circuit basis)
      (unitSpec.Observes basis 1 ![] wideDomain (unitPost 3)) := by
  refine unitSpec.refutes_root _ (solves_solution basis _ 0)
    (Streams.Heat.circuit_solution basis _ 0) (q := Streams.Heat.solution _) rfl ![0, 2] ?_ ?_
  · simp only [wideDomain, Formula.holds, Relation.holds, eval_add, eval_sub, eval_ofNat,
      ut_eval, ux_eval]
    norm_num
  · simp only [unitPost, Formula.holds, Relation.holds, eval_sub, eval_rational, uu_eval,
      unit_field]
    norm_num

/-! ### A finite prefix presented as a full stream -/

/-- The circuit's reconstruction with the boundary known only on the window
`degree < (5, 5)`. -/
def WindowSolves (p : Streams.Heat.Profile) : StreamPredicate 2 3 :=
  fun x => Window ![5, 5] 1 (Streams.Heat.boundary .ogf p) x ∧
    ∃ v, (Streams.Heat.circuit .ogf).Rel x ![v, x 0]

/-- `x² + 3x⁵`: the same window as `x²`, a different profile. -/
noncomputable def tailedProfile : Streams.Heat.Profile :=
  _root_.Polynomial.X ^ 2 + _root_.Polynomial.C 3 * _root_.Polynomial.X ^ 5

theorem same_window :
    Streams.truncate ![5, 5] (Streams.Heat.boundary .ogf tailedProfile) =
      Streams.truncate ![5, 5] (Streams.Heat.boundary .ogf (_root_.Polynomial.X ^ 2)) := by
  funext n
  simp only [Streams.truncate]
  split_ifs with inside
  · have far : MvPolynomial.coeff n (MvPolynomial.X (1 : Fin 2) ^ 5 : Streams.Poly 2) = 0 := by
      rw [MvPolynomial.coeff_X_pow, if_neg]
      intro same
      have bound := inside 1
      rw [← same] at bound
      simp at bound
    simp [Streams.Heat.boundary, Streams.ofPoly_ogf_apply, Streams.Heat.lift, tailedProfile, far]
  · rfl

/-- **A window of the boundary is not the full profile.** The full input for
`x² + 3x⁵` agrees with `x²`'s boundary on the window and is reconstructed by
the circuit, and its field at `(0, 1)` is `4 > 3`. -/
theorem window_not_full :
    ¬ StreamHoare (WindowSolves (_root_.Polynomial.X ^ 2)) (Streams.Heat.circuit .ogf)
      (unitSpec.Observes .ogf 1 ![] unitDomain (unitPost 3)) := by
  have admitted : WindowSolves (_root_.Polynomial.X ^ 2)
      ![Streams.Heat.stream .ogf tailedProfile, Streams.Heat.boundary .ogf tailedProfile, 0] :=
    ⟨same_window, _, Streams.Heat.circuit_solution .ogf _ 0⟩
  refine unitSpec.refutes_root _ admitted (Streams.Heat.circuit_solution .ogf _ 0)
    (q := Streams.Heat.solution _) rfl ![0, 1] ?_ ?_
  · simp only [unitDomain, Formula.holds, Relation.holds, eval_add, eval_sub, eval_ofNat,
      ut_eval, ux_eval]
    norm_num
  · simp only [unitPost, Formula.holds, Relation.holds, eval_sub, eval_rational, uu_eval]
    rw [Streams.Heat.solution_initial]
    norm_num [tailedProfile]

/-- An infinite tail behind a polynomial prefix has no field: asgard-lean's
`tailed` agrees with `x² + 2t` on a window, and the field predicate fails on it
whatever the domain and postcondition. -/
example (domain post : Formula unitSpec.context.dimension) :
    ¬ unitSpec.Observes .ogf 0 ![] domain post
      ![Gimle.Asgard.Examples.PolynomialHeat.tailed] :=
  unitSpec.not_observes Gimle.Asgard.Examples.PolynomialHeat.tailed_not_realized

/-! ### Nonnegative coefficients, negative field -/

/-- The axis variable `x` on axes `[t, x]`, as a stream circuit. -/
def line (basis : Streams.Basis) : Streams.Circuit basis 2 0 1 := .axisVariable 1

theorem line_related (basis : Streams.Basis) (x : Streams.StreamPoint 2 0) :
    (line basis).Rel x ![Streams.axisVariable basis 1] :=
  ((line basis).rel_iff _ _).mpr ⟨trivial, rfl⟩

/-- Every output coefficient of `u = x` is nonnegative, in either basis… -/
theorem line_coefficients (basis : Streams.Basis) :
    StreamHoare (fun _ => True) (line basis) fun y => ∀ index, 0 ≤ y 0 index := by
  intro x _
  refine ⟨trivial, fun index => ?_⟩
  show 0 ≤ Streams.axisVariable basis 1 index
  have coefficient :
      0 ≤ MvPolynomial.coeff index (MvPolynomial.X (1 : Fin 2) : Streams.Poly 2) := by
    rw [MvPolynomial.coeff_X]
    split_ifs <;> norm_num
  rw [Streams.axisVariable_eq_ofPoly]
  cases basis with
  | ogf => rw [Streams.ofPoly_ogf_apply]; exact coefficient
  | egf =>
      rw [Streams.ofPoly_egf_apply]
      exact mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) coefficient

/-- `-1 ≤ x ≤ 1`. -/
def lineDomain : Formula unitSpec.context.dimension :=
  (Formula.atom .ge (ux + 1)).and (.atom .le (ux - 1))

/-- …and its field is not nonnegative: at `x = -1` it is `-1`. The coefficient
contract above is no evidence for the field contract. -/
theorem line_field_refuted (basis : Streams.Basis) :
    ¬ StreamHoare (fun _ => True) (line basis)
      (unitSpec.Observes basis 0 ![] lineDomain (.atom .ge uu)) := by
  refine unitSpec.refutes_root ![] trivial (line_related basis ![]) (q := MvPolynomial.X 1)
    (Streams.axisVariable_eq_ofPoly basis 1) ![0, -1] ?_ ?_
  · simp only [lineDomain, Formula.holds, Relation.holds, eval_add, eval_sub, eval_ofNat, ux_eval]
    norm_num
  · simp only [Formula.holds, Relation.holds, uu_eval, Streams.field_X]
    norm_num

/-! ### Axiom policy -/

/--
info: 'Gimle.Forseti.FieldObservation.FieldSpec.observes_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms FieldSpec.observes_iff
/--
info: 'Gimle.Forseti.FieldObservation.FieldSpec.lift'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms FieldSpec.lift
/--
info: 'Gimle.Forseti.FieldObservation.FieldSpec.leaf_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms FieldSpec.leaf_bound
/--
info: 'Gimle.Forseti.FieldObservation.FieldSpec.lift_certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms FieldSpec.lift_certificate
/--
info: 'Gimle.Forseti.FieldObservation.FieldSpec.refutes_root'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms FieldSpec.refutes_root
/--
info: 'Gimle.Forseti.FieldObservation.FieldSpec.refutes_root_answer'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms FieldSpec.refutes_root_answer
/--
info: 'Gimle.Forseti.FieldObservation.refutes_at'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms refutes_at
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.solves_iff'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms solves_iff
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.solution_realized'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms solution_realized
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.field_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms field_solution
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.heat_strip_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms heat_strip_bound
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.unit_field'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unit_field
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.unit_heat_bound_three'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unit_heat_bound_three
/--
info: 'Gimle.Forseti.Examples.HeatFieldBound.unit_heat_bound_two_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unit_heat_bound_two_refuted
/--
info: 'Gimle.Forseti.Tests.FieldObservation.altered_profile'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms altered_profile
/--
info: 'Gimle.Forseti.Tests.FieldObservation.wider_domain'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms wider_domain
/--
info: 'Gimle.Forseti.Tests.FieldObservation.window_not_full'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms window_not_full
/--
info: 'Gimle.Forseti.Tests.FieldObservation.line_coefficients'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms line_coefficients
/--
info: 'Gimle.Forseti.Tests.FieldObservation.line_field_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms line_field_refuted

end Gimle.Forseti.Tests.FieldObservation
