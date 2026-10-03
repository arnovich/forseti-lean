import Gimle.Forseti.PolynomialTrapping
import Gimle.Forseti.Examples.GalerkinNS.K5Below6

/-! Coverage for trapping with a polynomial `V` and a bounded sublevel set.

Each `example` restates one of `PolynomialTrapping`'s exported theorems with its
exact statement, the symbolic derivative is checked on small expressions, the
5-mode instance below `E ≤ 6` is pinned by its data, and the axiom policy is
asserted with `#guard_msgs`. -/

namespace Gimle.Forseti.Tests.PolynomialTrapping

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Asgard.Model Gimle.Asgard.Polynomial Gimle.Forseti
open Gimle.Forseti.Nonlinear Gimle.Forseti.Trajectory

/-! ### The symbolic derivative -/

/-- `∂/∂x₀ (x₀ · x₁) = 1 · x₁ + x₀ · 0`, evaluated: `x₁`. -/
example (x : Point 2) :
    (Expr.diff 0 (Expr.mul (.var 0) (.var 1))).eval x = x 1 := by
  simp [Expr.diff, Expr.eval]

/-- `∂/∂x₁ (x₀² − 3)` evaluates to `0`. -/
example (x : Point 2) :
    (Expr.diff 1 (Expr.add (.mul (.var 0) (.var 0)) (.neg (.constant 3)))).eval x = 0 := by
  simp [Expr.diff, Expr.eval]

/-- `∂/∂x₀ (−x₀) = −1`, and a constant differentiates to `0`. -/
example (x : Point 2) : (Expr.diff 0 (Expr.neg (.var 0))).eval x = -1 := by
  simp [Expr.diff, Expr.eval]
example (x : Point 2) : (Expr.diff 0 (Expr.constant 7)).eval x = 0 := by
  simp [Expr.diff, Expr.eval]

/-- The chain rule, with its exact statement. -/
example {n : Nat} (e : Expr n) (state : Signal n) (v : Point n) (s : Set ℝ) (t : ℝ)
    (derivative : ∀ i, HasDerivWithinAt (fun t => state t i) (v i) s t) :
    HasDerivWithinAt (fun t => e.eval (state t)) (∑ k, (Expr.diff k e).eval (state t) * v k) s t :=
  Expr.eval_hasDerivWithinAt e state v s t derivative

/-! ### The theorem, for a raw field -/

example {n : Nat} (P : PolynomialTrapping n) (F : Point n → Point n) (decrease : P.Decreases F)
    (time : TimeDomain) (x₀ : Point n) (initial : P.energy x₀ ≤ P.bound)
    (state : Signal n) (h : Solves F time x₀ state) :
    ∀ t ∈ time.domain, P.energy (state t) ≤ P.bound :=
  P.invariant F decrease time x₀ initial state h

example {n : Nat} (P : PolynomialTrapping n) (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : P.Decreases F) (time : TimeDomain) (x₀ : Point n)
    (initial : P.energy x₀ ≤ P.bound) : ∃ state, Solves F time x₀ state :=
  P.exists_solution F smooth decrease time x₀ initial

example {n : Nat} (P : PolynomialTrapping n) (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : P.Decreases F) (time : TimeDomain) (x₀ : Point n)
    (initial : P.energy x₀ ≤ P.bound) {x y : Signal n}
    (hx : Solves F time x₀ x) (hy : Solves F time x₀ y) : Set.EqOn x y time.domain :=
  P.unique F smooth decrease time x₀ initial hx hy

/-- The decrease hypothesis is asked on the set only. -/
example {n : Nat} (P : PolynomialTrapping n) (F : Point n → Point n) :
    P.Decreases F ↔ ∀ x, P.energy x ≤ P.bound → P.rate F x ≤ P.alpha * (P.inner - P.energy x) :=
  Iff.rfl

/-- `V` is the expression evaluated, and the rate is `Σₖ ∂ₖV · Fₖ`. -/
example {n : Nat} (P : PolynomialTrapping n) (x : Point n) : P.energy x = P.poly.eval x := rfl
example {n : Nat} (P : PolynomialTrapping n) (F : Point n → Point n) (x : Point n) :
    P.rate F x = ∑ k, (Expr.diff k P.poly).eval x * F x k := rfl

example {n : Nat} (P : PolynomialTrapping n) : P.inner < P.bound := P.margin

/-- A global decrease is a local one. -/
example {n : Nat} (P : PolynomialTrapping n) (F : Point n → Point n)
    (global : ∀ x, P.rate F x ≤ P.alpha * (P.inner - P.energy x)) : P.Decreases F :=
  fun x _ => global x

/-- The set lies in the box, which is why the clamp is shared. -/
example {n : Nat} (P : PolynomialTrapping n) (x : Point n) (h : P.energy x ≤ P.bound) :
    x ∈ P.box.box :=
  P.mem_box_of_energy h

/-! ### The compiled-model shape -/

example {b : Body} {e : Evolution} (M : ContinuousModel b e) (P : PolynomialTrapping e.states.length)
    (k : Fin b.observations.length) (lo hi : ℝ) (decrease : P.Decreases (field M))
    (initial : P.energy M.initial ≤ P.bound)
    (bounded : ∀ state, M.Realizes state → ∀ t ∈ e.time.domain,
      lo ≤ M.outputs.circuit.run (state t) k ∧ M.outputs.circuit.run (state t) k ≤ hi) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => lo ≤ observation k ∧ observation k ≤ hi) :=
  poly_bounded_contract M P k lo hi decrease initial bounded

example : ∃ state, Examples.GalerkinNS.K5.compiled.Realizes state :=
  poly_compiled_exists Examples.GalerkinNS.K5.compiled Examples.GalerkinNS.K5.below6
    Examples.GalerkinNS.K5.decreases_below6 Examples.GalerkinNS.K5.initial_below6

/-! ### The 5-mode member below `E ≤ 6` -/

example : Examples.GalerkinNS.K5.below6.bound = 1 := rfl
example : Examples.GalerkinNS.K5.below6.radius = 6 := rfl
example : Examples.GalerkinNS.K5.below6.centre = 0 := rfl
example : Examples.GalerkinNS.K5.below6.inner < 1 := Examples.GalerkinNS.K5.below6.margin
example : Examples.GalerkinNS.K5.below6.poly = Examples.GalerkinNS.K5.tubeExpr := rfl
example : Examples.GalerkinNS.K5.below6.alpha = 237921 / 10000 := rfl
example : Examples.GalerkinNS.K5.below6.inner = 237911 / 237921 := rfl

/-- The rate is the library's derivative of `tubeExpr` along the compiled field, not a
written-out polynomial, and the energy is the expression evaluated. -/
example (x : Point 5) :
    Examples.GalerkinNS.K5.below6.rate (Nonlinear.field Examples.GalerkinNS.K5.compiled) x =
      Examples.GalerkinNS.K5.Vdot x :=
  Examples.GalerkinNS.K5.rate_eq_below6 x
example (x : Point 5) :
    Examples.GalerkinNS.K5.below6.energy x = Examples.GalerkinNS.K5.V x :=
  Examples.GalerkinNS.K5.energy_eq_below6 x

/-- `6` is below the laminar energy `25/2` and the family bound `13`. -/
example : (6 : ℝ) < Examples.GalerkinNS.K5.trapping.inner ∧
    Examples.GalerkinNS.K5.trapping.inner < Examples.GalerkinNS.K5.trapping.bound := by
  constructor <;> norm_num [Examples.GalerkinNS.K5.trapping]

/-- The laminar point `(0, 0, 5, 0, 0)` is an equilibrium outside the set, and the start
is inside: no global decrease could give this. -/
example : Examples.GalerkinNS.K5.field ![0, 0, 5, 0, 0] = 0 :=
  Examples.GalerkinNS.K5.laminar_equilibrium
example : 1 < Examples.GalerkinNS.K5.V ![0, 0, 5, 0, 0] := Examples.GalerkinNS.K5.laminar_outside
example : Examples.GalerkinNS.K5.V ![1, 1, 1, 1, 1] < 1 := Examples.GalerkinNS.K5.start_inside

example : Contract Examples.GalerkinNS.K5.observed Examples.GalerkinNS.K5.evolution.time
    Examples.GalerkinNS.K5.admitted
    (Always Examples.GalerkinNS.K5.evolution.time fun observation =>
      0 ≤ observation Examples.GalerkinNS.K5.energyIndex ∧
        observation Examples.GalerkinNS.K5.energyIndex ≤ 6) :=
  Examples.GalerkinNS.K5.below6_contract

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Nonlinear.Expr.eval_hasDerivWithinAt'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Expr.eval_hasDerivWithinAt

/--
info: 'Gimle.Forseti.Nonlinear.PolynomialTrapping.invariant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PolynomialTrapping.invariant

/--
info: 'Gimle.Forseti.Nonlinear.PolynomialTrapping.exists_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PolynomialTrapping.exists_solution

/--
info: 'Gimle.Forseti.Nonlinear.PolynomialTrapping.unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PolynomialTrapping.unique

/--
info: 'Gimle.Forseti.Nonlinear.poly_bounded_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms poly_bounded_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.below6_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.below6_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.K5.decreases_below6'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.K5.decreases_below6

end Gimle.Forseti.Tests.PolynomialTrapping
