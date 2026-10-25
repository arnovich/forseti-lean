import Gimle.Forseti.ClassicalVorticity.EnergyCalculus
import Gimle.Forseti.ErrorEnvelope

/-!
# Residual error bounds for a nonlinear periodic PDE

The independent scalar fields satisfy forced viscous Burgers on the periodic
square: `u_t + u*u_x = ν*Δu + forcing`. A reconstruction satisfies this equation
with an explicit additive residual. Periodic integration by parts and the actual
PDE equations imply a differential inequality for the normalized squared spatial
L2 error. The scalar error-envelope theorem then bounds the whole closed interval.

The error quantity is the squared normalized L2 norm, `mean((u-v)^2)`. The
regularity, forcing, viscosity, initial error, candidate slope and residual
bounds are explicit. This module asserts neither existence for arbitrary data
nor an automatic production-checker admission rule. Each application supplies
the actual fields and their classical derivative witnesses.
-/
namespace Gimle.Forseti.ResidualPDE
open Set Real
open Gimle.Forseti.ClassicalVorticity

/-- A classical periodic scalar Burgers field with an explicit residual.
Zero residual describes an exact solution. Derivatives are needed only in the
open time interval; fields and derivative witnesses are continuous on its closure. -/
structure Burgers (ν T : ℝ) (forcing residual : Field)
    (u : SpatialJet) (dt : Field) : Prop where
  regular : Regular u T
  periodic : Periodic u.value T
  deriv_time : ∀ t ∈ Ioo 0 T, ∀ p, HasDerivAt (fun s => u.value s p) (dt t p) t
  continuous_dt : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => dt z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  equation : ∀ t ∈ Ioo 0 T, ∀ p,
    dt t p + u.value t p * u.dx t p =
      ν * (u.dxx t p + u.dyy t p) + forcing t p + residual t p

/-- Normalized squared spatial L2 error on the periodic square. -/
noncomputable def energy (u v : SpatialJet) (t : ℝ) : ℝ :=
  squareAverage (2 * π) (fun p => (u.value t p - v.value t p) ^ 2)

/-- The squared error is nonnegative without a PDE premise. -/
theorem energy_nonneg (u v : SpatialJet) (t : ℝ) : 0 ≤ energy u v t :=
  squareAverage_nonneg (mul_pos (by norm_num) pi_pos) (fun _ => sq_nonneg _)

/-- A periodic cubic flux integrates to zero. -/
theorem cubic_flux_zero {e : SpatialJet} {T t : ℝ}
    (hr : Regular e T) (hp : Periodic e.value T) (ht : t ∈ Icc 0 T) :
    squareAverage (2 * π) (fun p => e.value t p ^ 2 * e.dx t p) = 0 := by
  have hc := continuous_slice hr.continuous_value ht
  have hcx := continuous_slice hr.continuous_dx ht
  have hi := square_integration_by_parts_x
    (f := fun p => e.value t p ^ 2)
    (fx := fun p => 2 * e.value t p * e.dx t p)
    (hc.pow 2) hc ((continuous_const.mul hc).mul hcx) hcx
    (fun x y => by
      convert! (hr.deriv_x t ht (x,y)).pow 2 using 1
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one])
    (fun x y => hr.deriv_x t ht (x,y))
    (fun y => by simpa using congrArg (fun a => a ^ 2) (hp t ht (0,y)).1)
    (fun y => by simpa using (hp t ht (0,y)).1)
  have he : (fun p => (2 * e.value t p * e.dx t p) * e.value t p) =
      (fun p => 2 * (e.value t p ^ 2 * e.dx t p)) := by
    funext p; ring
  rw [he, squareAverage_mul] at hi
  linarith only [hi]

/-- The nonlinear difference depends only on the reconstruction's slope after
periodic cancellation; no bound on the unknown exact solution's slope is used. -/
theorem burgers_flux_pairing {u v : SpatialJet} {T t : ℝ}
    (hu : Regular u T) (hv : Regular v T)
    (hup : Periodic u.value T) (hvp : Periodic v.value T) (ht : t ∈ Icc 0 T) :
    2 * squareAverage (2 * π) (fun p => (u.value t p - v.value t p) *
      (u.value t p * u.dx t p - v.value t p * v.dx t p)) =
      squareAverage (2 * π) (fun p => v.dx t p * (u.value t p - v.value t p) ^ 2) := by
  let e := u.sub v
  have hr : Regular e T := hu.sub hv
  have hp : Periodic e.value T := hup.sub hvp
  have hc := continuous_slice hr.continuous_value ht
  have hcx := continuous_slice hr.continuous_dx ht
  have hvc := continuous_slice hv.continuous_value ht
  have hvcx := continuous_slice hv.continuous_dx ht
  have hi := square_integration_by_parts_x
    (f := fun p => e.value t p ^ 2)
    (fx := fun p => 2 * e.value t p * e.dx t p)
    (hc.pow 2) hvc ((continuous_const.mul hc).mul hcx) hvcx
    (fun x y => by
      convert! (hr.deriv_x t ht (x,y)).pow 2 using 1
      simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one])
    (fun x y => hv.deriv_x t ht (x,y))
    (fun y => by simpa using congrArg (fun a => a ^ 2) (hp t ht (0,y)).1)
    (fun y => by simpa using (hvp t ht (0,y)).1)
  let A := fun p => e.value t p ^ 2 * e.dx t p
  let B := fun p => e.value t p * e.dx t p * v.value t p
  let C := fun p => v.dx t p * e.value t p ^ 2
  have hA : Continuous A := (hc.pow 2).mul hcx
  have hB : Continuous B := (hc.mul hcx).mul hvc
  have hC : Continuous C := hvcx.mul (hc.pow 2)
  have hleft : (fun p => e.value t p ^ 2 * v.dx t p) = C := by
    funext p; dsimp [C]; ring
  have hright : (fun p => (2 * e.value t p * e.dx t p) * v.value t p) =
      (fun p => 2 * B p) := by funext p; dsimp [B]; ring
  rw [hleft, hright, squareAverage_mul] at hi
  have hz : squareAverage (2 * π) A = 0 := cubic_flux_zero hr hp ht
  have he : (fun p => (u.value t p - v.value t p) *
      (u.value t p * u.dx t p - v.value t p * v.dx t p)) =
      (fun p => A p + B p + C p) := by
    funext p; dsimp [A, B, C, e, SpatialJet.sub]; ring
  rw [he, squareAverage_add (f := fun p => A p + B p) (hA.add hB) hC,
    squareAverage_add hA hB, hz]
  change 2 * (0 + squareAverage (2 * π) B + squareAverage (2 * π) C) =
    squareAverage (2 * π) C
  linarith only [hi]

/-- Subtract the actual PDEs and retain the full reconstruction residual. -/
theorem Burgers.energy_identity {ν T : ℝ} {forcing residual : Field}
    {u v : SpatialJet} {ut vt : Field}
    (hu : Burgers ν T forcing (fun _ _ => 0) u ut)
    (hv : Burgers ν T forcing residual v vt)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hrc : Continuous (residual t)) :
    2 * squareAverage (2 * π) (fun p =>
      (u.value t p - v.value t p) * (ut t p - vt t p)) =
      -2 * ν * squareAverage (2 * π) (fun p =>
        (u.dx t p - v.dx t p) ^ 2 + (u.dy t p - v.dy t p) ^ 2) -
      squareAverage (2 * π) (fun p => v.dx t p * (u.value t p - v.value t p) ^ 2) -
      2 * squareAverage (2 * π) (fun p => (u.value t p - v.value t p) * residual t p) := by
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  let e := u.sub v
  have hr : Regular e T := hu.regular.sub hv.regular
  have hp : Periodic e.value T := hu.periodic.sub hv.periodic
  let A := fun p => e.value t p * (e.dxx t p + e.dyy t p)
  let B := fun p => e.value t p * (u.value t p * u.dx t p - v.value t p * v.dx t p)
  let C := fun p => e.value t p * residual t p
  have hc := continuous_slice hr.continuous_value htc
  have hA : Continuous A := hc.mul ((continuous_slice hr.continuous_dxx htc).add
    (continuous_slice hr.continuous_dyy htc))
  have hB : Continuous B := hc.mul
    (((continuous_slice hu.regular.continuous_value htc).mul
      (continuous_slice hu.regular.continuous_dx htc)).sub
      ((continuous_slice hv.regular.continuous_value htc).mul
        (continuous_slice hv.regular.continuous_dx htc)))
  have hC : Continuous C := hc.mul hrc
  have he : (fun p => e.value t p * (ut t p - vt t p)) =
      (fun p => ν * A p - B p - C p) := by
    funext p
    dsimp [A, B, C, e, SpatialJet.sub]
    linear_combination (u.value t p - v.value t p) * hu.equation t ht p -
      (u.value t p - v.value t p) * hv.equation t ht p
  have heint := congrArg (squareAverage (2 * π)) he
  rw [squareAverage_sub (f := fun p => ν * A p - B p)
      ((continuous_const.mul hA).sub hB) hC,
    squareAverage_sub (f := fun p => ν * A p) (continuous_const.mul hA) hB,
    squareAverage_mul] at heint
  have hdiff := hr.laplacian_pairing hp htc
  have hflux := burgers_flux_pairing hu.regular hv.regular hu.periodic hv.periodic htc
  change squareAverage (2 * π) A = -squareAverage (2 * π)
    (fun p => e.dx t p ^ 2 + e.dy t p ^ 2) at hdiff
  change 2 * squareAverage (2 * π) B = _ at hflux
  rw [hdiff] at heint
  change 2 * squareAverage (2 * π) (fun p => e.value t p * (ut t p - vt t p)) = _
  rw [heint]
  dsimp only [C, e, SpatialJet.sub]
  linarith only [hflux]

/-- Differentiation of the actual normalized squared field error. -/
theorem Burgers.hasDerivAt_energy {ν T : ℝ} {forcing r₁ r₂ : Field}
    {u v : SpatialJet} {ut vt : Field}
    (hu : Burgers ν T forcing r₁ u ut) (hv : Burgers ν T forcing r₂ v vt)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (energy u v)
      (2 * squareAverage (2 * π) (fun p =>
        (u.value t p - v.value t p) * (ut t p - vt t p))) t := by
  have hc := hu.regular.continuous_value.sub hv.regular.continuous_value
  have hdt := hu.continuous_dt.sub hv.continuous_dt
  have h := hasDerivAt_squareAverage
    (f := fun s p => (u.value s p - v.value s p) ^ 2)
    (dt := fun s p => 2 * (u.value s p - v.value s p) * (ut s p - vt s p))
    (L := 2 * π) (mul_pos (by norm_num) pi_pos)
    (hc.pow 2) ((continuousOn_const.mul hc).mul hdt)
    (fun s hs p => by
      convert! ((hu.deriv_time s hs p).sub (hv.deriv_time s hs p)).pow 2 using 1
      all_goals simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply]) ht
  have he : (fun p => 2 * (u.value t p - v.value t p) * (ut t p - vt t p)) =
      (fun p => 2 * ((u.value t p - v.value t p) * (ut t p - vt t p))) := by
    funext p; ring
  change HasDerivAt (energy u v)
    (squareAverage (2 * π) (fun p =>
      2 * (u.value t p - v.value t p) * (ut t p - vt t p))) t at h
  rw [he, squareAverage_mul] at h
  exact h

/-- Candidate slope and complete residual bounds imply the scalar premise.
Viscosity is discarded only after its nonnegative sign has been checked. -/
theorem Burgers.energy_derivative_le {ν T M R : ℝ} {forcing residual : Field}
    {u v : SpatialJet} {ut vt : Field}
    (hu : Burgers ν T forcing (fun _ _ => 0) u ut)
    (hv : Burgers ν T forcing residual v vt) (hν : 0 ≤ ν)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hrc : Continuous (residual t))
    (hslope : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π), -v.dx t (x,y) ≤ M)
    (hres : squareAverage (2 * π) (fun p => residual t p ^ 2) ≤ R ^ 2) :
    2 * squareAverage (2 * π) (fun p =>
      (u.value t p - v.value t p) * (ut t p - vt t p)) ≤
      (M + 1) * energy u v t + R ^ 2 := by
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hc : Continuous (fun p => u.value t p - v.value t p) :=
    (continuous_slice hu.regular.continuous_value htc).sub
      (continuous_slice hv.regular.continuous_value htc)
  have hvx := continuous_slice hv.regular.continuous_dx htc
  have hg := squareAverage_nonneg hL (fun p => add_nonneg
    (sq_nonneg (u.dx t p - v.dx t p)) (sq_nonneg (u.dy t p - v.dy t p)))
  have hdiff := mul_nonneg hν hg
  have hs := squareAverage_mono hL
    (f := fun p => -1 * (v.dx t p * (u.value t p - v.value t p) ^ 2))
    (g := fun p => M * (u.value t p - v.value t p) ^ 2)
    (continuous_const.mul (hvx.mul (hc.pow 2))) (continuous_const.mul (hc.pow 2))
    (fun x hx y hy => show -1 * (v.dx t (x,y) * (u.value t (x,y) - v.value t (x,y)) ^ 2) ≤
      M * (u.value t (x,y) - v.value t (x,y)) ^ 2 by
      nlinarith only [mul_nonneg (sub_nonneg.mpr (hslope x hx y hy))
        (sq_nonneg (u.value t (x,y) - v.value t (x,y)))])
  rw [squareAverage_mul, squareAverage_mul] at hs
  have hr := squareAverage_mono hL
    (f := fun p => -2 * ((u.value t p - v.value t p) * residual t p))
    (g := fun p => (u.value t p - v.value t p) ^ 2 + residual t p ^ 2)
    (continuous_const.mul (hc.mul hrc))
    ((hc.pow 2).add (hrc.pow 2))
    (fun x _ y _ => show -2 * ((u.value t (x,y) - v.value t (x,y)) * residual t (x,y)) ≤
      (u.value t (x,y) - v.value t (x,y)) ^ 2 + residual t (x,y) ^ 2 by
      nlinarith only [sq_nonneg ((u.value t (x,y) - v.value t (x,y)) + residual t (x,y))])
  rw [squareAverage_mul, squareAverage_add (f := fun p => (u.value t p - v.value t p) ^ 2)
    (g := fun p => residual t p ^ 2) (hc.pow 2) (hrc.pow 2)] at hr
  rw [hu.energy_identity hv ht hrc]
  dsimp [energy] at *
  nlinarith only [hs, hr, hres, hdiff]

/-- Whole-interval error for independent exact and approximate Burgers fields.
The initial budget and all spatial bounds are supplied separately from the PDE. -/
theorem Burgers.error_le_envelope {ν T δ M R : ℝ} {forcing residual : Field}
    {u v : SpatialJet} {ut vt : Field}
    (hu : Burgers ν T forcing (fun _ _ => 0) u ut)
    (hv : Burgers ν T forcing residual v vt) (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hinit : energy u v 0 ≤ δ)
    (hrc : ∀ t ∈ Ioo 0 T, Continuous (residual t))
    (hslope : ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc 0 (2 * π),
      ∀ y ∈ Icc 0 (2 * π), -v.dx t (x,y) ≤ M)
    (hres : ∀ t ∈ Ioo 0 T,
      squareAverage (2 * π) (fun p => residual t p ^ 2) ≤ R ^ 2) :
    ∀ t ∈ Icc 0 T, energy u v t ≤ gronwallBound δ (M + 1) (R ^ 2) t := by
  have hc := hu.regular.continuous_value.sub hv.regular.continuous_value
  have h := ErrorEnvelope.affine_comparison (a := 0) (b := T)
    (e := energy u v)
    (e' := fun t => 2 * squareAverage (2 * π) (fun p =>
      (u.value t p - v.value t p) * (ut t p - vt t p))) hT
    (continuousOn_squareAverage (hc.pow 2) _) (fun t ht => hu.hasDerivAt_energy hv ht)
    hinit (fun t ht => hu.energy_derivative_le hv hν ht (hrc t ht) (hslope t ht) (hres t ht))
  simpa only [sub_zero] using h

#print axioms cubic_flux_zero
#print axioms energy_nonneg
#print axioms burgers_flux_pairing
#print axioms Burgers.energy_identity
#print axioms Burgers.hasDerivAt_energy
#print axioms Burgers.energy_derivative_le
#print axioms Burgers.error_le_envelope
end Gimle.Forseti.ResidualPDE
