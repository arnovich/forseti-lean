import Gimle.Forseti.ClassicalVorticity.SquareEstimates

/-! Periodic integration by parts on a square and the elliptic estimate that
controls stream-function velocity by vorticity. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set MeasureTheory
open scoped Interval

/-- Integration by parts in the second coordinate, including boundary cancellation. -/
theorem square_integration_by_parts_y {L : ℝ} {f g fy gy : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfy : Continuous fy) (hgy : Continuous gy)
    (hdf : ∀ x y, HasDerivAt (fun s => f (x,s)) (fy (x,y)) y)
    (hdg : ∀ x y, HasDerivAt (fun s => g (x,s)) (gy (x,y)) y)
    (hfp : ∀ x, f (x,L) = f (x,0)) (hgp : ∀ x, g (x,L) = g (x,0)) :
    squareAverage L (fun p => f p * gy p) =
      -squareAverage L (fun p => fy p * g p) := by
  have hi : ∀ x, average L (fun y => f (x,y) * gy (x,y)) =
      -average L (fun y => fy (x,y) * g (x,y)) := by
    intro x
    unfold average
    rw [periodic_integration_by_parts (f := fun y => f (x,y)) (g := fun y => g (x,y))
      (hf.comp (continuous_const.prodMk continuous_id)).continuousOn
      (hg.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun y _ => hdf x y) (fun y _ => hdg x y)
      ((hfy.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hgy.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      (hfp x) (hgp x), neg_div]
  unfold squareAverage
  dsimp only
  simp only [hi]
  simp only [average, intervalIntegral.integral_neg, neg_div]

/-- Integration by parts in the first coordinate, by Fubini. -/
theorem square_integration_by_parts_x {L : ℝ} {f g fx gx : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfx : Continuous fx) (hgx : Continuous gx)
    (hdf : ∀ x y, HasDerivAt (fun s => f (s,y)) (fx (x,y)) x)
    (hdg : ∀ x y, HasDerivAt (fun s => g (s,y)) (gx (x,y)) x)
    (hfp : ∀ y, f (L,y) = f (0,y)) (hgp : ∀ y, g (L,y) = g (0,y)) :
    squareAverage L (fun p => f p * gx p) =
      -squareAverage L (fun p => fx p * g p) := by
  rw [squareAverage_swap (f := fun p => f p * gx p) (hf.mul hgx) L,
    squareAverage_swap (f := fun p => fx p * g p) (hfx.mul hg) L]
  exact square_integration_by_parts_y
    (hf.comp continuous_swap) (hg.comp continuous_swap)
    (hfx.comp continuous_swap) (hgx.comp continuous_swap)
    (fun x y => hdf y x) (fun x y => hdg y x) hfp hgp

/-- The periodic elliptic estimate. The left side is squared velocity and the
right side squared vorticity when `u = (-f_y,f_x)` and `ω = Δf`.
No mean-zero condition on `f`, Fourier representation, or symmetry is assumed. -/
theorem periodic_elliptic_estimate {L : ℝ} (hL : 0 < L)
    {f fx fy fxx fyy : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hfx : Continuous fx) (hfy : Continuous fy)
    (hfxx : Continuous fxx) (hfyy : Continuous fyy)
    (hdx : ∀ x y, HasDerivAt (fun s => f (s,y)) (fx (x,y)) x)
    (hdy : ∀ x y, HasDerivAt (fun s => f (x,s)) (fy (x,y)) y)
    (hdxx : ∀ x y, HasDerivAt (fun s => fx (s,y)) (fxx (x,y)) x)
    (hdyy : ∀ x y, HasDerivAt (fun s => fy (x,s)) (fyy (x,y)) y)
    (hpx : ∀ y, f (L,y) = f (0,y)) (hpy : ∀ x, f (x,L) = f (x,0))
    (hpxx : ∀ y, fx (L,y) = fx (0,y)) (hpyy : ∀ x, fy (x,L) = fy (x,0)) :
    squareAverage L (fun p => fx p ^ 2 + fy p ^ 2) ≤
      2 * L ^ 2 * squareAverage L (fun p => (fxx p + fyy p) ^ 2) := by
  let c := squareAverage L f
  let C := 2 * L ^ 2
  have hC : 0 < C := mul_pos (by norm_num) (sq_pos_of_pos hL)
  have hx := square_integration_by_parts_x (L := L) (hf.sub continuous_const) hfx hfx hfxx
    (fun x y => (hdx x y).sub_const c) hdxx
    (fun y => congrArg (fun z => z - c) (hpx y)) hpxx
  have hy := square_integration_by_parts_y (L := L) (hf.sub continuous_const) hfy hfy hfyy
    (fun x y => (hdy x y).sub_const c) hdyy
    (fun x => congrArg (fun z => z - c) (hpy x)) hpyy
  have hp : squareAverage L (fun p => (f p - c) * (fxx p + fyy p)) =
      -squareAverage L (fun p => fx p ^ 2 + fy p ^ 2) := by
    simp_rw [mul_add]
    simp only [Pi.sub_apply] at hx hy
    rw [squareAverage_add (f := fun p => (f p - c) * fxx p)
      (g := fun p => (f p - c) * fyy p) ((hf.sub continuous_const).mul hfxx)
      ((hf.sub continuous_const).mul hfyy), hx, hy,
      squareAverage_add (f := fun p => fx p ^ 2) (g := fun p => fy p ^ 2)
        (hfx.pow 2) (hfy.pow 2)]
    simp only [pow_two]
    ring
  have hq := square_poincare hL hf hfx hfy hdx hdy
  have hm := squareAverage_mono hL
    (continuous_const.mul ((hf.sub continuous_const).mul (hfxx.add hfyy)))
    (((hf.sub continuous_const).pow 2).add (continuous_const.mul ((hfxx.add hfyy).pow 2)))
    (fun x _ y _ => show -2 * C * ((f (x,y) - c) * (fxx (x,y) + fyy (x,y))) ≤
        (f (x,y) - c) ^ 2 + C ^ 2 * (fxx (x,y) + fyy (x,y)) ^ 2 by
      nlinarith [sq_nonneg ((f (x,y) - c) + C * (fxx (x,y) + fyy (x,y)))])
  change squareAverage L (fun p => -2 * C * ((f p - c) * (fxx p + fyy p))) ≤
    squareAverage L (fun p => (f p - c) ^ 2 + C ^ 2 * (fxx p + fyy p) ^ 2) at hm
  rw [squareAverage_mul, hp,
    squareAverage_add (f := fun p => (f p - c) ^ 2)
      (g := fun p => C ^ 2 * (fxx p + fyy p) ^ 2) ((hf.sub continuous_const).pow 2)
      (continuous_const.mul ((hfxx.add hfyy).pow 2)), squareAverage_mul] at hm
  change squareAverage L (fun p => (f p - c) ^ 2) ≤
    C * squareAverage L (fun p => fx p ^ 2 + fy p ^ 2) at hq
  change squareAverage L (fun p => fx p ^ 2 + fy p ^ 2) ≤
    C * squareAverage L (fun p => (fxx p + fyy p) ^ 2)
  apply (mul_le_mul_iff_right₀ hC).mp
  nlinarith

#print axioms square_integration_by_parts_x
#print axioms periodic_elliptic_estimate
end Gimle.Forseti.ClassicalVorticity
