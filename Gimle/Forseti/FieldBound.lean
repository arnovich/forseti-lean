import Gimle.Forseti.Syntax.Certificate

/-! Reading certified polynomial formulas as bounds on real fields.

A field claim is about values, not coefficients: its formula variables denote
physical coordinates such as `t` and `x`, and explicitly fixed parameters, and
it is read at real points. The 017 checker needs nothing new for that; what a
field claim needs is the algebra that turns a stated domain into constraints a
certificate can use, and the evaluation of the notation the claims are written
in. Both are here.

**`sq_le_sq_of_box`**: on the box `-R ≤ x ≤ R`, `x² ≤ R²` — including `R = 0`,
where the box is the single point `0`. A certificate over linear box
constraints needs degree-two multipliers to find this bound; this lemma lets a
caller add `R² - x² ≥ 0`, or a product with a nonnegative parameter, as an
antecedent constraint, so a leaf can use it with constant multipliers.

**Which field.** A theorem proved here is about the polynomial function written
in the formula. That this function is the field some stream circuit represents
— its evaluated output for given full input streams — is a separate bridge,
`FieldObservation` (through asgard-lean 024). Nonnegative coefficients do not by
themselves make a field nonnegative: `Tests/FieldBound.lean` refutes it with
`u = x` at `x = -1`.
-/

namespace Gimle.Forseti.Syntax.ExprNotation

open Gimle.Asgard

variable {n : Nat}

@[simp] theorem eval_add (p q : Polynomial.Expr n) (z : Point n) :
    (p + q).eval z = p.eval z + q.eval z := rfl

@[simp] theorem eval_mul (p q : Polynomial.Expr n) (z : Point n) :
    (p * q).eval z = p.eval z * q.eval z := rfl

@[simp] theorem eval_neg (p : Polynomial.Expr n) (z : Point n) :
    (-p).eval z = -p.eval z := rfl

@[simp] theorem eval_sub (p q : Polynomial.Expr n) (z : Point n) :
    (p - q).eval z = p.eval z - q.eval z := by
  show p.eval z + -q.eval z = _
  ring

@[simp] theorem eval_ofNat (k : Nat) (z : Point n) :
    (no_index (OfNat.ofNat k) : Polynomial.Expr n).eval z = (k : ℝ) := by
  show (((k : ℚ)) : ℝ) = _
  simp

@[simp] theorem eval_rational (value : ℚ) (z : Point n) :
    (rational value : Polynomial.Expr n).eval z = (value : ℝ) := rfl

@[simp] theorem eval_var (i : Fin n) (z : Point n) :
    (Polynomial.Expr.var i).eval z = z i := rfl

end Gimle.Forseti.Syntax.ExprNotation

namespace Gimle.Forseti.FieldBound

/-- **The box bound.** On `-R ≤ x ≤ R`, `x² ≤ R²`. No sign of `R` is assumed:
the box forces `R ≥ 0`, and at `R = 0` it is the point `x = 0`. -/
theorem sq_le_sq_of_box {x R : ℝ} (lower : -R ≤ x) (upper : x ≤ R) : x * x ≤ R * R := by
  nlinarith

/-- A nonnegative parameter times the box bound: `a · (R² - x²) ≥ 0`. -/
theorem box_constraint {a x R : ℝ} (nonneg : 0 ≤ a) (lower : -R ≤ x) (upper : x ≤ R) :
    0 ≤ a * (R * R - x * x) :=
  mul_nonneg nonneg (sub_nonneg.mpr (sq_le_sq_of_box lower upper))

/-- At `R = 0` the box is a point, and the bound is equality. -/
example {x : ℝ} (lower : -0 ≤ x) (upper : x ≤ 0) : x * x ≤ 0 * 0 := sq_le_sq_of_box lower upper

#print axioms sq_le_sq_of_box
#print axioms box_constraint

end Gimle.Forseti.FieldBound
