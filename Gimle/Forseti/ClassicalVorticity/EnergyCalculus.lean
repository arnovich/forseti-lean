import Gimle.Forseti.ClassicalVorticity.TimeCalculus

/-! Physical-space energy identities for the independent classical fields. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set Real

/-- Periodic diffusion has the expected negative quadratic pairing. -/
theorem Regular.laplacian_pairing {f : SpatialJet} {T t : ℝ} (hr : Regular f T)
    (hp : Periodic f.value T) (ht : t ∈ Icc 0 T) :
    squareAverage (2 * π) (fun p => f.value t p * (f.dxx t p + f.dyy t p)) =
      -squareAverage (2 * π) (fun p => f.dx t p ^ 2 + f.dy t p ^ 2) := by
  have hf := continuous_slice hr.continuous_value ht
  have hfx := continuous_slice hr.continuous_dx ht
  have hfy := continuous_slice hr.continuous_dy ht
  have hfxx := continuous_slice hr.continuous_dxx ht
  have hfyy := continuous_slice hr.continuous_dyy ht
  have hx := square_integration_by_parts_x (L := 2 * π) hf hfx hfx hfxx
    (fun x y => hr.deriv_x t ht (x,y)) (fun x y => hr.deriv_xx t ht (x,y))
    (fun y => by simpa using (hp t ht (0,y)).1)
    (fun y => by simpa using (hp.dx hr t ht (0,y)).1)
  have hy := square_integration_by_parts_y (L := 2 * π) hf hfy hfy hfyy
    (fun x y => hr.deriv_y t ht (x,y)) (fun x y => hr.deriv_yy t ht (x,y))
    (fun x => by simpa using (hp t ht (x,0)).2)
    (fun x => by simpa using (hp.dy hr t ht (x,0)).2)
  simp_rw [mul_add]
  rw [squareAverage_add (f := fun p => f.value t p * f.dxx t p)
    (g := fun p => f.value t p * f.dyy t p) (hf.mul hfxx) (hf.mul hfyy), hx, hy,
    squareAverage_add (f := fun p => f.dx t p ^ 2) (g := fun p => f.dy t p ^ 2)
      (hfx.pow 2) (hfy.pow 2)]
  simp only [pow_two]
  ring

/-- Incompressible stream-function transport contributes zero to squared energy. -/
theorem Regular.transport_pairing {f ψ : SpatialJet} {T t : ℝ}
    (hf : Regular f T) (hψ : Regular ψ T)
    (hfp : Periodic f.value T) (hψp : Periodic ψ.value T) (ht : t ∈ Icc 0 T) :
    squareAverage (2 * π) (fun p => f.value t p *
      (-ψ.dy t p * f.dx t p + ψ.dx t p * f.dy t p)) = 0 := by
  have hc := continuous_slice hf.continuous_value ht
  have hcx := continuous_slice hf.continuous_dx ht
  have hcy := continuous_slice hf.continuous_dy ht
  have hpx := continuous_slice hψ.continuous_dx ht
  have hpy := continuous_slice hψ.continuous_dy ht
  have hpxy := continuous_slice hψ.continuous_dxy ht
  have hdx : ∀ x y, HasDerivAt (fun s => f.value t (s,y) ^ 2)
      (2 * f.value t (x,y) * f.dx t (x,y)) x := by
    intro x y
    convert! (hf.deriv_x t ht (x,y)).pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hdy : ∀ x y, HasDerivAt (fun s => f.value t (x,s) ^ 2)
      (2 * f.value t (x,y) * f.dy t (x,y)) y := by
    intro x y
    convert! (hf.deriv_y t ht (x,y)).pow 2 using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  have hx := square_integration_by_parts_x (L := 2 * π)
    (hc.pow 2) hpy ((continuous_const.mul hc).mul hcx) hpxy hdx
    (fun x y => hψ.deriv_yx t ht (x,y))
    (fun y => by simpa using congrArg (fun z => z ^ 2) (hfp t ht (0,y)).1)
    (fun y => by simpa using (hψp.dy hψ t ht (0,y)).1)
  have hy := square_integration_by_parts_y (L := 2 * π)
    (hc.pow 2) hpx ((continuous_const.mul hc).mul hcy) hpxy hdy
    (fun x y => hψ.deriv_xy t ht (x,y))
    (fun x => by simpa using congrArg (fun z => z ^ 2) (hfp t ht (x,0)).2)
    (fun x => by simpa using (hψp.dx hψ t ht (x,0)).2)
  have hex : (fun p => (2 * f.value t p * f.dx t p) * ψ.dy t p) =
      (fun p => 2 * (f.value t p * ψ.dy t p * f.dx t p)) := by funext p; ring
  have hey : (fun p => (2 * f.value t p * f.dy t p) * ψ.dx t p) =
      (fun p => 2 * (f.value t p * ψ.dx t p * f.dy t p)) := by funext p; ring
  change squareAverage (2 * π) (fun p => f.value t p ^ 2 * ψ.dxy t p) =
    -squareAverage (2 * π) (fun p => (2 * f.value t p * f.dx t p) * ψ.dy t p) at hx
  change squareAverage (2 * π) (fun p => f.value t p ^ 2 * ψ.dxy t p) =
    -squareAverage (2 * π) (fun p => (2 * f.value t p * f.dy t p) * ψ.dx t p) at hy
  rw [hex, squareAverage_mul] at hx
  rw [hey, squareAverage_mul] at hy
  have he : (fun p => f.value t p * (-ψ.dy t p * f.dx t p + ψ.dx t p * f.dy t p)) =
      (fun p => f.value t p * ψ.dx t p * f.dy t p - f.value t p * ψ.dy t p * f.dx t p) := by
    funext p; ring
  rw [he, squareAverage_sub (f := fun p => f.value t p * ψ.dx t p * f.dy t p)
    (g := fun p => f.value t p * ψ.dy t p * f.dx t p)
    ((hc.mul hpx).mul hcy) ((hc.mul hpy).mul hcx)]
  linarith only [hx, hy]

/-- Young's inequality bounds the remaining transport difference. -/
theorem nonlinear_pairing_le {L M : ℝ} (hL : 0 < L)
    {d vx vy gx gy : ℝ × ℝ → ℝ}
    (hd : Continuous d) (hvx : Continuous vx) (hvy : Continuous vy)
    (hgx : Continuous gx) (hgy : Continuous gy)
    (hM : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, gx (x,y) ^ 2 + gy (x,y) ^ 2 ≤ M) :
    -2 * squareAverage L (fun p => d p * (vx p * gx p + vy p * gy p)) ≤
      M * squareAverage L (fun p => d p ^ 2) +
        squareAverage L (fun p => vx p ^ 2 + vy p ^ 2) := by
  have hm := squareAverage_mono hL
    (continuous_const.mul (hd.mul ((hvx.mul hgx).add (hvy.mul hgy))))
    ((continuous_const.mul (hd.pow 2)).add ((hvx.pow 2).add (hvy.pow 2)))
    (fun x hx y hy => show -2 * (d (x,y) * (vx (x,y) * gx (x,y) + vy (x,y) * gy (x,y))) ≤
        M * d (x,y) ^ 2 + (vx (x,y) ^ 2 + vy (x,y) ^ 2) by
      nlinarith only [sq_nonneg (d (x,y) * gx (x,y) + vx (x,y)),
        sq_nonneg (d (x,y) * gy (x,y) + vy (x,y)),
        mul_nonneg (sq_nonneg (d (x,y))) (sub_nonneg.mpr (hM x hx y hy))])
  change squareAverage L (fun p => -2 * (d p * (vx p * gx p + vy p * gy p))) ≤
    squareAverage L (fun p => M * d p ^ 2 + (vx p ^ 2 + vy p ^ 2)) at hm
  rw [squareAverage_mul, squareAverage_add (f := fun p => M * d p ^ 2)
    (g := fun p => vx p ^ 2 + vy p ^ 2)
    (continuous_const.mul (hd.pow 2)) ((hvx.pow 2).add (hvy.pow 2)), squareAverage_mul] at hm
  exact hm

#print axioms Regular.transport_pairing
#print axioms nonlinear_pairing_le
end Gimle.Forseti.ClassicalVorticity
