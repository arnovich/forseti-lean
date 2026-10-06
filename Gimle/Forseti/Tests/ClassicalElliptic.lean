import Gimle.Forseti.ClassicalVorticity.SquareCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Regression statements for the physical-space comparison estimates. -/
namespace Gimle.Forseti.Tests.ClassicalElliptic
open Gimle.Forseti.ClassicalVorticity Set

/-- The spatial estimate admits arbitrary offsets and contains both coordinates. -/
theorem affine_poincare (a b c L : ℝ) (hL : 0 < L) :
    squareAverage L (fun p =>
      (a * p.1 + b * p.2 + c - squareAverage L (fun q => a * q.1 + b * q.2 + c)) ^ 2)
      ≤ 2 * L ^ 2 * squareAverage L (fun _ => a ^ 2 + b ^ 2) := by
  apply square_poincare hL (fx := fun _ => a) (fy := fun _ => b)
  · fun_prop
  · exact continuous_const
  · exact continuous_const
  · intro x y
    simpa using (((hasDerivAt_id x).const_mul a).add_const (b * y)).add_const c
  · intro x y
    simpa using (((hasDerivAt_id y).const_mul b).const_add (a * x)).add_const c

/-- A genuinely two-dimensional mode exercises both derivatives and periodic edges. -/
theorem mixed_mode_elliptic :
    squareAverage (2 * Real.pi) (fun p =>
      Real.cos (p.1 + p.2) ^ 2 + Real.cos (p.1 + p.2) ^ 2) ≤
      2 * (2 * Real.pi) ^ 2 * squareAverage (2 * Real.pi)
        (fun p => (-Real.sin (p.1 + p.2) + -Real.sin (p.1 + p.2)) ^ 2) := by
  apply periodic_elliptic_estimate (f := fun p => Real.sin (p.1 + p.2))
    (mul_pos (by norm_num) Real.pi_pos)
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · intro x y; simpa using ((hasDerivAt_id x).add_const y).sin
  · intro x y; simpa using ((hasDerivAt_id y).const_add x).sin
  · intro x y; simpa using ((hasDerivAt_id x).add_const y).cos
  · intro x y; simpa using ((hasDerivAt_id y).const_add x).cos
  · intro y; simp [add_comm]
  · intro x; simp
  · intro y; simp [add_comm]
  · intro x; simp

#print axioms affine_poincare
#print axioms mixed_mode_elliptic
end Gimle.Forseti.Tests.ClassicalElliptic
