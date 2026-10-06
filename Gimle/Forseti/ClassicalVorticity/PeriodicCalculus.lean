import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Elementary periodic integration identities used by a physical-space
vorticity comparison. Endpoint cancellation is proved, never assumed as an
energy identity. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set MeasureTheory
open scoped Interval

/-- Integration by parts on a period: the product's boundary term vanishes. -/
theorem periodic_integration_by_parts {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hdf : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hdg : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hfi : IntervalIntegrable f' volume a b) (hgi : IntervalIntegrable g' volume a b)
    (hfp : f b = f a) (hgp : g b = g a) :
    (∫ x in a..b, f x * g' x) = -(∫ x in a..b, f' x * g x) := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hf hg hdf hdg hfi hgi
  simpa only [hfp, hgp, sub_self, zero_sub] using h

/-- The periodic Laplacian has nonpositive quadratic pairing. -/
theorem periodic_laplacian_pairing {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) (hdf : ContinuousOn f' (uIcc a b))
    (hd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hdd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f' (f'' x) x)
    (hddi : IntervalIntegrable f'' volume a b)
    (hfp : f b = f a) (hdfp : f' b = f' a) :
    (∫ x in a..b, f x * f'' x) = -(∫ x in a..b, (f' x) ^ 2) := by
  simpa only [pow_two] using periodic_integration_by_parts hf hdf hd hdd
    hdf.intervalIntegrable hddi hfp hdfp

/-- Viscosity contributes a nonpositive term on an ordered period. -/
theorem periodic_laplacian_nonpos {f f' f'' : ℝ → ℝ} {a b ν : ℝ}
    (hab : a ≤ b) (hν : 0 ≤ ν)
    (hf : ContinuousOn f (uIcc a b)) (hdf : ContinuousOn f' (uIcc a b))
    (hd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hdd : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f' (f'' x) x)
    (hddi : IntervalIntegrable f'' volume a b)
    (hfp : f b = f a) (hdfp : f' b = f' a) :
    ν * (∫ x in a..b, f x * f'' x) ≤ 0 := by
  rw [periodic_laplacian_pairing hf hdf hd hdd hddi hfp hdfp]
  exact mul_nonpos_of_nonneg_of_nonpos hν (neg_nonpos.mpr
    (intervalIntegral.integral_nonneg_of_forall hab (fun _ => sq_nonneg _)))

/-- A transport pairing reduces to the derivative of its velocity component.
The two spatial components cancel when the velocity is divergence free. -/
theorem periodic_transport_pairing {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b))
    (hfc : ContinuousOn f' (uIcc a b)) (hgc : ContinuousOn g' (uIcc a b))
    (hdf : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x)
    (hdg : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt g (g' x) x)
    (hfp : f b = f a) (hgp : g b = g a) :
    (∫ x in a..b, f x * g x * f' x) =
      -(1 / 2 : ℝ) * (∫ x in a..b, (f x) ^ 2 * g' x) := by
  have hd : ∀ x ∈ Ioo (min a b) (max a b),
      HasDerivAt (fun y => (f y) ^ 2) (2 * f x * f' x) x := by
    intro x hx
    convert! (hdf x hx).pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have h := periodic_integration_by_parts (hf.pow 2) hg hd hdg
    ((continuousOn_const.mul hf).mul hfc).intervalIntegrable hgc.intervalIntegrable
    (congrArg (fun r => r ^ 2) hfp) hgp
  have he : (fun x => (2 * f x * f' x) * g x) =
      (fun x => 2 * (f x * g x * f' x)) := by funext x; ring
  rw [he, intervalIntegral.integral_const_mul] at h
  simp only [Pi.pow_apply] at h
  linarith

#print axioms periodic_laplacian_pairing
#print axioms periodic_transport_pairing
end Gimle.Forseti.ClassicalVorticity
