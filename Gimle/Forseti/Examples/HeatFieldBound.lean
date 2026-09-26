import Gimle.Forseti.FieldObservation
import Gimle.Forseti.Examples.HeatStripBound
import Gimle.Asgard.Examples.PolynomialHeat

/-! The heat strip bound as a property of Asgard's heat circuit.

`HeatStripBound` (task 020) bounds the explicit candidate `a·x² + c + 2·a·t`.
Here the same bound is a total field contract over the **original**
derivative/integration heat circuit `Streams.Heat.circuit basis` of
asgard-lean 024, in either basis, through `FieldObservation`:

* **Admitted full inputs** (`Solves basis p`): the boundary port carries the
  full initial profile `p`, and the circuit reconstructs port `0` from it. By
  024's existence (`circuit_solution`) and uniqueness (`candidate_stream`) the
  only admitted port `0` is `Streams.Heat.stream basis p` (`solves_iff`); the
  third port is arbitrary. Uniqueness is among formal streams; the field
  reading is within the finite polynomial class.
* **The observed field**: output port `1`, realized by
  `Streams.Heat.solution p` (`solution_realized`), evaluated by
  `Streams.field`.
* **The algebraic leaves** are task 017 certificates over the claim's own named
  coordinates, with the field value replaced by the solution's polynomial; the
  bridge (`field_solution`) is proved from 024's `field_unique`, not from
  coefficients.

`heat_strip_bound` is the general strip bound for the profile `a·x² + c`.
`unit_heat_bound_three` and `unit_heat_bound_two_refuted` are the concrete
`u = x² + 2t` case on `[0, 1] × [-1, 1]`: bound `3` holds, and bound `2` is
refuted at `(t, x) = (1, 1)` through an admitted full input, its related output
and the failing root postcondition.
-/

namespace Gimle.Forseti.Examples.HeatFieldBound

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Stream
open Gimle.Forseti.FieldBound
open Gimle.Forseti.FieldObservation
open Gimle.Forseti.Examples.HeatStripBound (unused weight square)
open Gimle.Asgard

/-! ### The heat solution class -/

/-- **Admitted full inputs** `[u, boundary, unused]` for the profile `p`: the
boundary port is the full profile, and the circuit's reconstruction (output
port `1`) returns port `0`. -/
def Solves (basis : Streams.Basis) (p : Streams.Heat.Profile) : StreamPredicate 2 3 :=
  fun x => x 1 = Streams.Heat.boundary basis p ∧
    ∃ v, (Streams.Heat.circuit basis).Rel x ![v, x 0]

private theorem eta3 (x : Streams.StreamPoint 2 3) : x = ![x 0, x 1, x 2] := by
  funext i; fin_cases i <;> rfl

/-- **Existence and uniqueness.** The admitted inputs are exactly those whose
first port is the constructed heat stream and whose boundary is the profile. -/
theorem solves_iff (basis : Streams.Basis) (p : Streams.Heat.Profile)
    (x : Streams.StreamPoint 2 3) :
    Solves basis p x ↔
      x 0 = Streams.Heat.stream basis p ∧ x 1 = Streams.Heat.boundary basis p := by
  constructor
  · rintro ⟨boundary, v, related⟩
    refine ⟨?_, boundary⟩
    have full : (Streams.Heat.circuit basis).Rel
        ![x 0, Streams.Heat.boundary basis p, x 2] ![v, x 0] := by
      rw [← boundary, ← eta3 x]
      exact related
    exact Streams.Heat.candidate_stream basis p (x 0) (x 2) v full
  · rintro ⟨stream, boundary⟩
    have related := Streams.Heat.circuit_solution basis p (x 2)
    rw [← stream, ← boundary, ← eta3 x] at related
    exact ⟨boundary, _, related⟩

/-- The constructed full input is admitted, whatever the unused port holds. -/
theorem solves_solution (basis : Streams.Basis) (p : Streams.Heat.Profile)
    (unused : Streams.Stream 2) :
    Solves basis p ![Streams.Heat.stream basis p, Streams.Heat.boundary basis p, unused] :=
  (solves_iff basis p _).mpr ⟨rfl, rfl⟩

/-- **Every admitted input's output port `1` is realized**, as a whole stream, by
the heat polynomial of the profile. -/
theorem solution_realized (basis : Streams.Basis) (p : Streams.Heat.Profile) :
    StreamHoare (Solves basis p) (Streams.Heat.circuit basis)
      fun y => Streams.Realizes basis (y 1) (Streams.Heat.solution p) := by
  intro x admitted
  obtain ⟨boundary, v, related⟩ := admitted
  obtain ⟨defined, output⟩ := ((Streams.Heat.circuit basis).rel_iff x _).mp related
  refine ⟨defined, ?_⟩
  show Streams.Realizes basis ((Streams.Heat.circuit basis).value x 1) _
  rw [← output]
  exact ((solves_iff basis p x).mp ⟨boundary, v, related⟩).1

/-! ### The quadratic profile and its field -/

/-- The initial profile `a·x² + c`. -/
noncomputable def profile (a c : ℚ) : Streams.Heat.Profile :=
  _root_.Polynomial.C a * _root_.Polynomial.X ^ 2 + _root_.Polynomial.C c

/-- `a·x² + c + 2·a·t` on axes `[t, x]`. -/
noncomputable def solutionPoly (a c : ℚ) : Streams.Poly 2 :=
  MvPolynomial.C a * MvPolynomial.X 1 ^ 2 + MvPolynomial.C c +
    2 * MvPolynomial.C a * MvPolynomial.X 0

/-- 024's heat solution of `a·x² + c` is `a·x² + c + 2·a·t`, by its uniqueness
theorem for polynomial fields. -/
theorem solution_profile (a c : ℚ) :
    Streams.Heat.solution (profile a c) = solutionPoly a c := by
  symm
  apply Streams.Heat.field_unique
  · have two : ∀ i, MvPolynomial.pderiv i (2 : Streams.Poly 2) = 0 := fun i => by
      rw [← map_ofNat MvPolynomial.C 2, MvPolynomial.pderiv_C]
    refine (Streams.Heat.field_pde_iff _).mpr ?_
    simp [solutionPoly, two, Derivation.leibniz, Derivation.leibniz_pow]
    ring
  · intro x
    simp [solutionPoly, profile, Streams.field]

/-- **The bridge**: the evaluated field of the heat solution is the candidate. -/
theorem field_solution (a c : ℚ) (y : Fin 2 → ℝ) :
    Streams.field (Streams.Heat.solution (profile a c)) y = a * y 1 ^ 2 + c + 2 * a * y 0 := by
  rw [solution_profile]
  simp [solutionPoly]

/-- The same, in 020's notation. -/
theorem field_solution_candidate (a c : ℚ) (t x : ℝ) :
    Streams.field (Streams.Heat.solution (profile a c)) ![t, x] =
      HeatStripBound.candidate a c t x := by
  rw [field_solution]
  rfl

/-! ### The general strip bound -/

/-- Axes `[t, x]`, parameters `[a, c, R, T]`, field value `u`. -/
def stripSpec : FieldSpec 2 4 :=
  ⟨!["t", "x"], !["a", "c", "R", "T"], "u",
    ⟨["t", "x", "a", "c", "R", "T", "u"], by decide, by decide, by decide⟩, rfl⟩

abbrev st : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "t"
abbrev sx : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "x"
abbrev sa : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "a"
abbrev sc : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "c"
abbrev sR : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "R"
abbrev sT : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "T"
abbrev su : Polynomial.Expr stripSpec.context.dimension := stripSpec.context.var "u"

section
variable (y : Fin 2 → ℝ) (θ : Fin 4 → ℚ) (q : Streams.Poly 2)
theorem st_eval : st.eval (stripSpec.fieldPoint y θ q) = y 0 := rfl
theorem sx_eval : sx.eval (stripSpec.fieldPoint y θ q) = y 1 := rfl
theorem sa_eval : sa.eval (stripSpec.fieldPoint y θ q) = θ 0 := rfl
theorem sc_eval : sc.eval (stripSpec.fieldPoint y θ q) = θ 1 := rfl
theorem sR_eval : sR.eval (stripSpec.fieldPoint y θ q) = θ 2 := rfl
theorem sT_eval : sT.eval (stripSpec.fieldPoint y θ q) = θ 3 := rfl
theorem su_eval : su.eval (stripSpec.fieldPoint y θ q) = Streams.field q y := rfl
end

/-- The stated domain: the strip `0 ≤ t ≤ T`, `-R ≤ x ≤ R`. -/
def stripDomain : Formula stripSpec.context.dimension :=
  (Formula.atom .ge st).and ((Formula.atom .le (st - sT)).and
    ((Formula.atom .ge (sx + sR)).and (.atom .le (sx - sR))))

/-- `0 ≤ u ≤ c + a·R² + 2·a·T`. -/
def stripPost : Formula stripSpec.context.dimension :=
  (Formula.atom .ge su).and (.atom .le (su - (sc + sa * sR * sR + 2 * sa * sT)))

/-- The leaf antecedent: `a, c ≥ 0` and the products the strip gives with `a`,
among them the box bound `a·(R² - x²) ≥ 0`. -/
def stripAntecedent : Formula stripSpec.context.dimension :=
  (Formula.atom .ge sa).and ((Formula.atom .ge sc).and ((Formula.atom .ge (sa * st)).and
    ((Formula.atom .ge (sa * (sR * sR - sx * sx))).and (.atom .ge (sa * (sT - st))))))

/-- The solution's polynomial, over the claim's coordinates. -/
def stripExpr : Polynomial.Expr stripSpec.context.dimension := sa * sx * sx + sc + 2 * sa * st

/-- `u = x²·a + c + 2·(a·t)` and `bound - u = a·(R² - x²) + 2·(a·(T - t))`. -/
def stripCertificate : EntailmentCertificate stripSpec.context.dimension :=
  ⟨[⟨unused, [square 1 sx, weight 1, weight 2, unused, unused]⟩,
    ⟨unused, [unused, unused, unused, weight 1, weight 2]⟩]⟩

/-- **The strip bound on the heat circuit.** For rationals `a, c ≥ 0` and every
rational `R, T`, in either basis: every full input admitted for the profile
`a·x² + c` has output port `1` realized by a polynomial whose field satisfies
`0 ≤ u(t, x) ≤ c + a·R² + 2·a·T` on `0 ≤ t ≤ T`, `-R ≤ x ≤ R`. -/
theorem heat_strip_bound (basis : Streams.Basis) (a c R T : ℚ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    StreamHoare (Solves basis (profile a c)) (Streams.Heat.circuit basis)
      (stripSpec.Observes basis 1 ![a, c, R, T] stripDomain stripPost) := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  refine stripSpec.lift_certificate (antecedent := stripAntecedent) (expression := stripExpr)
    (solution_realized basis _) stripCertificate
    (by decide +kernel) (fun y => ?_) (fun y inside => ?_)
  · simp only [stripExpr, eval_add, eval_mul, eval_ofNat, st_eval, sx_eval, sa_eval, sc_eval,
      field_solution]
    simp
    ring
  · simp only [stripDomain, stripAntecedent, Formula.holds, Relation.holds, eval_add, eval_mul,
      eval_sub, st_eval, sx_eval, sa_eval, sc_eval, sR_eval, sT_eval] at inside ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at inside ⊢
    obtain ⟨start, stop, lower, upper⟩ := inside
    exact ⟨ha', hc', mul_nonneg ha' start, box_constraint ha' (by linarith) (by linarith),
      mul_nonneg ha' (by linarith)⟩

/-! ### The unit case: `u = x² + 2t` on `[0, 1] × [-1, 1]` -/

/-- Axes `[t, x]`, no parameters, field value `u`. -/
def unitSpec : FieldSpec 2 0 :=
  ⟨!["t", "x"], ![], "u", ⟨["t", "x", "u"], by decide, by decide, by decide⟩, rfl⟩

abbrev ut : Polynomial.Expr unitSpec.context.dimension := unitSpec.context.var "t"
abbrev ux : Polynomial.Expr unitSpec.context.dimension := unitSpec.context.var "x"
abbrev uu : Polynomial.Expr unitSpec.context.dimension := unitSpec.context.var "u"

section
variable (y : Fin 2 → ℝ) (q : Streams.Poly 2)
theorem ut_eval : ut.eval (unitSpec.fieldPoint y ![] q) = y 0 := rfl
theorem ux_eval : ux.eval (unitSpec.fieldPoint y ![] q) = y 1 := rfl
theorem uu_eval : uu.eval (unitSpec.fieldPoint y ![] q) = Streams.field q y := rfl
end

/-- The unit strip `0 ≤ t ≤ 1`, `-1 ≤ x ≤ 1`. -/
def unitDomain : Formula unitSpec.context.dimension :=
  (Formula.atom .ge ut).and ((Formula.atom .le (ut - 1)).and
    ((Formula.atom .ge (ux + 1)).and (.atom .le (ux - 1))))

/-- `0 ≤ u ≤ bound`. -/
def unitPost (bound : ℚ) : Formula unitSpec.context.dimension :=
  (Formula.atom .ge uu).and (.atom .le (uu - rational bound))

/-- The leaf antecedent: the time interval and the box bound `1 - x² ≥ 0`. -/
def unitAntecedent : Formula unitSpec.context.dimension :=
  (Formula.atom .ge ut).and ((Formula.atom .le (ut - 1)).and (.atom .ge (1 - ux * ux)))

/-- `x² + 2t`, over the claim's coordinates. -/
def unitExpr : Polynomial.Expr unitSpec.context.dimension := ux * ux + 2 * ut

/-- `u = x² + 2·t` and `3 - u = 2·(1 - t) + (1 - x²)`: constant multipliers. -/
def unitCertificate : EntailmentCertificate unitSpec.context.dimension :=
  ⟨[⟨square 1 ux, [weight 2, unused, unused]⟩, ⟨unused, [unused, weight 2, weight 1]⟩]⟩

/-- The field of the `x²` heat solution at every point is `x² + 2t` (asgard-lean
`PolynomialHeat.square_field`). -/
theorem unit_field (y : Fin 2 → ℝ) :
    Streams.field (Streams.Heat.solution (_root_.Polynomial.X ^ 2)) y = y 1 ^ 2 + 2 * y 0 := by
  have eta : y = ![y 0, y 1] := by funext j; fin_cases j <;> rfl
  rw [eta, Gimle.Asgard.Examples.PolynomialHeat.square_field]
  rfl

/-- **Bound `3` holds on the heat circuit**, in either basis. -/
theorem unit_heat_bound_three (basis : Streams.Basis) :
    StreamHoare (Solves basis (_root_.Polynomial.X ^ 2)) (Streams.Heat.circuit basis)
      (unitSpec.Observes basis 1 ![] unitDomain (unitPost 3)) := by
  refine unitSpec.lift_certificate (antecedent := unitAntecedent) (expression := unitExpr)
    (solution_realized basis _) unitCertificate
    (by decide +kernel) (fun y => ?_) (fun y inside => ?_)
  · simp only [unitExpr, eval_add, eval_mul, eval_ofNat, ut_eval, ux_eval, unit_field]
    push_cast
    ring
  · simp only [unitDomain, unitAntecedent, Formula.holds, Relation.holds, eval_add, eval_mul,
      eval_sub, eval_ofNat, ut_eval, ux_eval] at inside ⊢
    obtain ⟨start, stop, lower, upper⟩ := inside
    have box := sq_le_sq_of_box (x := y 1) (R := 1) (by push_cast at lower ⊢; linarith)
      (by push_cast at upper ⊢; linarith)
    push_cast at stop ⊢
    exact ⟨start, stop, by linarith⟩

/-- The leaf counterexample to bound `2`: `(t, x, u) = (1, 1, 3)`. -/
def unitAnswer : Syntax.Context.Assignment := [("t", 1), ("x", 1), ("u", 3)]

/-- **Bound `2` is refuted on the heat circuit**, in either basis: the full input
`[x² + 2t, x², 0]` is admitted, the circuit relates it to `[2, x² + 2t]`,
port `1` is realized by the heat solution, and at `(t, x) = (1, 1)` its field is
`3 > 2`. The leaf counterexample is lifted only through those facts. -/
theorem unit_heat_bound_two_refuted (basis : Streams.Basis) :
    ¬ StreamHoare (Solves basis (_root_.Polynomial.X ^ 2)) (Streams.Heat.circuit basis)
      (unitSpec.Observes basis 1 ![] unitDomain (unitPost 2)) := by
  refine unitSpec.refutes_root_answer (expression := unitExpr) (answer := unitAnswer)
    (by decide +kernel) _ (solves_solution basis _ 0)
    (Streams.Heat.circuit_solution basis _ 0) (q := Streams.Heat.solution _) rfl ![1, 1]
    (fun i => ?_) ?_
  · have values : ∀ i, (Syntax.Context.valueOf unitAnswer (unitSpec.context.name i)).getD 0 =
        ![1, 1, 3] (Fin.cast (by decide +kernel) i) := by decide +kernel
    rw [values]
    fin_cases i <;> norm_num [FieldSpec.fieldPoint, FieldSpec.point, unit_field]
  · simp only [unitExpr, eval_add, eval_mul, eval_ofNat, ut_eval, ux_eval, unit_field]
    push_cast
    ring

/-- The same contract on the hand-written fixture circuit, which asgard-lean
proves is literally the general heat circuit at OGF. -/
example : StreamHoare (Solves .ogf (_root_.Polynomial.X ^ 2))
    Gimle.Asgard.Examples.FormalHeat.circuit
    (unitSpec.Observes .ogf 1 ![] unitDomain (unitPost 3)) := by
  rw [Gimle.Asgard.Examples.PolynomialHeat.original_circuit]
  exact unit_heat_bound_three .ogf

end Gimle.Forseti.Examples.HeatFieldBound
