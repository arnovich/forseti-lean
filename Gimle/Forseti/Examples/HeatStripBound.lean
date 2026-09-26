import Gimle.Forseti.FieldBound

/-! A certified strip bound for the heat solution with a quadratic initial
profile, as a property of the candidate field.

For fixed rationals `a, c ≥ 0` the initial profile `p(x) = a·x² + c` has the
heat solution `u(t, x) = a·x² + c + 2·a·t`. On the strip `0 ≤ t ≤ T`,
`-R ≤ x ≤ R`, `strip_bound` proves `0 ≤ u(t, x) ≤ c + a·R² + 2·a·T`.

The algebra is a 017 certificate over the context `[t, x, a, c, R, T]`: the
coordinates and the fixed parameters, not coefficient slots. The domain enters
as constraints, among them the box bound `a·(R² - x²) ≥ 0`, which
`FieldBound.box_constraint` derives; with it the upper bound is
`a·(R² - x²) + 2·a·(T - t) ≥ 0`, with constant multipliers.

**What this does not yet prove.** `candidate` is the polynomial function
written here. That it is the evaluated field of Asgard's formal heat circuit on
the full input streams with profile `p` — and the unique one in the finite
polynomial solution class — is asgard-lean 024's theorem, and binding this bound
to the circuit is task 021. Until then this is a bound on a candidate, and the
refutation of bound `2` below refutes only the candidate, not the circuit.
-/

namespace Gimle.Forseti.Examples.HeatStripBound

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.FieldBound
open Gimle.Asgard

/-- An unused multiplier slot. -/
def unused {k : Nat} : SquareSum k := ⟨[]⟩

/-- A weight on a constant square: `w · 1²`. -/
def weight {k : Nat} (w : ℚ) : SquareSum k := ⟨[(w, .constant 1)]⟩

/-- A weighted square: `w · g²`. -/
def square {k : Nat} (w : ℚ) (g : Polynomial.Expr k) : SquareSum k := ⟨[(w, g)]⟩

/-! ### The general strip bound -/

/-- Space-time coordinates `t, x`, then the fixed parameters `a, c, R, T`. -/
def strip : Context := ⟨["t", "x", "a", "c", "R", "T"], by decide, by decide, by decide⟩

abbrev vt : Polynomial.Expr strip.dimension := strip.var "t"
abbrev vx : Polynomial.Expr strip.dimension := strip.var "x"
abbrev va : Polynomial.Expr strip.dimension := strip.var "a"
abbrev vc : Polynomial.Expr strip.dimension := strip.var "c"
abbrev vR : Polynomial.Expr strip.dimension := strip.var "R"
abbrev vT : Polynomial.Expr strip.dimension := strip.var "T"

/-- The candidate field `u = a·x² + c + 2·a·t`. -/
def field : Polynomial.Expr strip.dimension := va * vx * vx + vc + 2 * va * vt

/-- The claimed upper bound `c + a·R² + 2·a·T`. -/
def bound : Polynomial.Expr strip.dimension := vc + va * vR * vR + 2 * va * vT

/-- The domain as constraints: `a ≥ 0`, `c ≥ 0`, and the three products the box
and the time interval give with `a`. -/
def domain : Formula strip.dimension :=
  (Formula.atom .ge va).and ((Formula.atom .ge vc).and ((Formula.atom .ge (va * vt)).and
    ((Formula.atom .ge (va * (vR * vR - vx * vx))).and (.atom .ge (va * (vT - vt))))))

/-- `0 ≤ u ≤ c + a·R² + 2·a·T`. -/
def claim : Formula strip.dimension := (Formula.atom .ge field).and (.atom .le (field - bound))

def goal : Goal := ⟨strip, domain, claim⟩

/-- `u = x²·a + c + 2·(a·t)` and `bound - u = a·(R² - x²) + 2·(a·(T - t))`. -/
def certificate : EntailmentCertificate strip.dimension :=
  ⟨[⟨unused, [square 1 vx, weight 1, weight 2, unused, unused]⟩,
    ⟨unused, [unused, unused, unused, weight 1, weight 2]⟩]⟩

theorem goal_holds : goal.Entailment :=
  EntailmentCertificate.sound goal certificate (by decide +kernel)

/-- The candidate field, as a real function of `t` and `x`. -/
def candidate (a c : ℚ) (t x : ℝ) : ℝ := a * x ^ 2 + c + 2 * a * t

/-- The real point `(t, x, a, c, R, T)`, in the context's order. -/
def at6 (t x a c R T : ℝ) : Point strip.dimension := ![t, x, a, c, R, T]

theorem vt_eval (t x a c R T : ℝ) : vt.eval (at6 t x a c R T) = t := rfl
theorem vx_eval (t x a c R T : ℝ) : vx.eval (at6 t x a c R T) = x := rfl
theorem va_eval (t x a c R T : ℝ) : va.eval (at6 t x a c R T) = a := rfl
theorem vc_eval (t x a c R T : ℝ) : vc.eval (at6 t x a c R T) = c := rfl
theorem vR_eval (t x a c R T : ℝ) : vR.eval (at6 t x a c R T) = R := rfl
theorem vT_eval (t x a c R T : ℝ) : vT.eval (at6 t x a c R T) = T := rfl

/-- **The strip bound**, for fixed rational `a, c ≥ 0` and every rational `R, T`:
on `0 ≤ t ≤ T`, `-R ≤ x ≤ R`, the candidate satisfies
`0 ≤ u(t, x) ≤ c + a·R² + 2·a·T`. `R ≥ 0` and `T ≥ 0` follow from the strip. -/
theorem strip_bound (a c R T : ℚ) (ha : 0 ≤ a) (hc : 0 ≤ c) (t x : ℝ)
    (start : 0 ≤ t) (stop : t ≤ T) (lower : -R ≤ x) (upper : x ≤ R) :
    0 ≤ candidate a c t x ∧ candidate a c t x ≤ c + a * R ^ 2 + 2 * a * T := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have holds := goal_holds (at6 t x a c R T) (by
    simp only [goal, domain, Formula.holds, Relation.holds, eval_mul, eval_sub, vt_eval,
      vx_eval, va_eval, vc_eval, vR_eval, vT_eval]
    exact ⟨ha', hc', mul_nonneg ha' start, box_constraint ha' lower upper,
      mul_nonneg ha' (sub_nonneg.mpr stop)⟩)
  simp only [goal, claim, field, bound, Formula.holds, Relation.holds, eval_add, eval_mul,
    eval_sub, eval_ofNat, vt_eval, vx_eval, va_eval, vc_eval, vR_eval, vT_eval] at holds
  obtain ⟨nonneg, below⟩ := holds
  constructor
  · unfold candidate; push_cast at nonneg ⊢; nlinarith
  · unfold candidate; push_cast at below ⊢; nlinarith

/-! ### The concrete case `a = 1, c = 0, R = 1, T = 1` -/

/-- `[t, x]`. -/
def plane : Context := ⟨["t", "x"], by decide, by decide, by decide⟩

abbrev pt : Polynomial.Expr plane.dimension := plane.var "t"
abbrev px : Polynomial.Expr plane.dimension := plane.var "x"

/-- `u = x² + 2t`. -/
def unitField : Polynomial.Expr plane.dimension := px * px + 2 * pt

/-- The unit strip as four linear constraints. -/
def unitStrip : Formula plane.dimension :=
  (Formula.atom .ge pt).and ((Formula.atom .le (pt - 1)).and
    ((Formula.atom .ge (px + 1)).and (.atom .le (px - 1))))

/-- `0 ≤ u ≤ bound` on the unit strip. -/
def unitGoal (bound : ℚ) : Goal :=
  ⟨plane, unitStrip, (Formula.atom .ge unitField).and (.atom .le (unitField - rational bound))⟩

/-- Directly from the linear strip, with degree-two multipliers:
`3 - x² - 2t = 2·(1 - t) + ½(1 - x)²·(x + 1) + ½(1 + x)²·(1 - x)`. -/
def unitCertificate : EntailmentCertificate plane.dimension :=
  ⟨[⟨square 1 px, [weight 2, unused, unused, unused]⟩,
    ⟨unused, [unused, weight 2, square (1/2) (1 - px), square (1/2) (1 + px)]⟩]⟩

/-- **Bound `3` succeeds.** -/
theorem unit_bound_three : (unitGoal 3).Entailment :=
  EntailmentCertificate.sound _ unitCertificate (by decide +kernel)

/-- The same bound as an instance of the general strip bound. -/
example (t x : ℝ) (start : 0 ≤ t) (stop : t ≤ 1) (lower : -1 ≤ x) (upper : x ≤ 1) :
    0 ≤ candidate 1 0 t x ∧ candidate 1 0 t x ≤ 3 := by
  have := strip_bound 1 0 1 1 (by norm_num) le_rfl t x start (by exact_mod_cast stop)
    (by exact_mod_cast lower) (by exact_mod_cast upper)
  norm_num at this ⊢
  exact this

/-- **Bound `2` is refuted at the leaf**, at `(t, x) = (1, 1)`… -/
theorem unit_bound_two_refuted : ¬ (unitGoal 2).Entailment :=
  refutes_sound _ [("t", 1), ("x", 1)] (by decide +kernel)

/-- …and the certificate for `3` does not check against it. -/
example : unitCertificate.check (unitGoal 2) = false := by decide +kernel

/-- The candidate field itself exceeds `2` there. This refutes the candidate;
it becomes a refutation of the circuit only through task 021. -/
example : 2 < candidate 1 0 1 1 := by norm_num [candidate]

end Gimle.Forseti.Examples.HeatStripBound
