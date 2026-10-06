import Gimle.Forseti.ClassicalVorticity.IntervalEstimates
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! Square averages and a coarse two-dimensional Poincare estimate. The
estimates apply to arbitrary continuously differentiable fields. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set MeasureTheory
open scoped Interval

/-- Normalized area integral over the square of side length `L`. -/
noncomputable def squareAverage (L : ℝ) (f : ℝ × ℝ → ℝ) : ℝ :=
  average L (fun x => average L (fun y => f (x, y)))

/-- Integrating a continuous field over a fixed interval preserves continuity. -/
theorem continuous_average {X : Type*} [TopologicalSpace X] {f : X × ℝ → ℝ} (hf : Continuous f) (L : ℝ) :
    Continuous (fun x => average L (fun y => f (x, y))) :=
  (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x y => f (x,y)) hf 0 L).div_const L

/-- Fubini for the normalized square average. -/
theorem squareAverage_swap {f : ℝ × ℝ → ℝ} (hf : Continuous f) (L : ℝ) :
    squareAverage L f = squareAverage L (fun p => f (p.2, p.1)) := by
  have hi : IntegrableOn f (uIoc 0 L ×ˢ uIoc 0 L) :=
    (hf.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have h := intervalIntegral_intervalIntegral_swap (F := fun x y => f (x,y)) hi
  simpa only [squareAverage, average, intervalIntegral.integral_div] using
    congrArg (fun z : ℝ => z / L / L) h

@[simp] theorem squareAverage_const {L : ℝ} (hL : 0 < L) (c : ℝ) :
    squareAverage L (fun _ => c) = c := by
  simp [squareAverage, average_const hL]

theorem squareAverage_add {L : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    squareAverage L (fun p => f p + g p) = squareAverage L f + squareAverage L g := by
  have hi : ∀ x, average L (fun y => f (x,y) + g (x,y)) =
      average L (fun y => f (x,y)) + average L (fun y => g (x,y)) := fun x =>
    average_add (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id))
  simp only [squareAverage, hi]
  exact average_add (continuous_average hf L) (continuous_average hg L)

theorem squareAverage_mul (L c : ℝ) (f : ℝ × ℝ → ℝ) :
    squareAverage L (fun p => c * f p) = c * squareAverage L f := by
  simp only [squareAverage, average_mul]

theorem squareAverage_mono {L : ℝ} (hL : 0 < L) {f g : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L, f (x,y) ≤ g (x,y)) :
    squareAverage L f ≤ squareAverage L g := by
  apply average_mono hL (continuous_average hf L) (continuous_average hg L)
  intro x hx
  exact average_mono hL (hf.comp (continuous_const.prodMk continuous_id))
    (hg.comp (continuous_const.prodMk continuous_id)) (hfg x hx)

theorem squareAverage_nonneg {L : ℝ} (hL : 0 < L) {f : ℝ × ℝ → ℝ}
    (hf : ∀ p, 0 ≤ f p) : 0 ≤ squareAverage L f :=
  average_nonneg hL (fun _ => average_nonneg hL (fun _ => hf _))

/-- Subtraction commutes with averaging continuous fields. -/
theorem squareAverage_sub {L : ℝ} {f g : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    squareAverage L (fun p => f p - g p) = squareAverage L f - squareAverage L g := by
  have hi : ∀ x, average L (fun y => f (x,y) - g (x,y)) =
      average L (fun y => f (x,y)) - average L (fun y => g (x,y)) := fun x =>
    average_sub (hf.comp (continuous_const.prodMk continuous_id))
      (hg.comp (continuous_const.prodMk continuous_id))
  simp only [squareAverage, hi]
  exact average_sub (continuous_average hf L) (continuous_average hg L)

/-- A continuous field with zero squared average vanishes on the closed square. -/
theorem eq_zero_of_squareAverage_sq_eq_zero {L : ℝ} (hL : 0 < L)
    {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hzero : squareAverage L (fun p => f p ^ 2) = 0)
    {x y : ℝ} (hx : x ∈ Icc 0 L) (hy : y ∈ Icc 0 L) : f (x,y) = 0 := by
  by_contra hn
  have hinner : 0 < average L (fun v => f (x,v) ^ 2) := by
    apply div_pos _ hL
    exact intervalIntegral.integral_pos hL
      ((hf.comp (continuous_const.prodMk continuous_id)).pow 2).continuousOn
      (fun _ _ => sq_nonneg _) ⟨y, hy, sq_pos_of_ne_zero hn⟩
  have houter : 0 < squareAverage L (fun p => f p ^ 2) := by
    apply div_pos _ hL
    exact intervalIntegral.integral_pos hL (continuous_average (hf.pow 2) L).continuousOn
      (fun _ _ => average_nonneg hL (fun _ => sq_nonneg _)) ⟨x, hx, hinner⟩
  linarith

/-- A coarse Poincare inequality on the square. Periodic boundary conditions
are unnecessary for this estimate; subtracting the area mean removes constants. -/
theorem square_poincare {L : ℝ} (hL : 0 < L) {f fx fy : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hfx : Continuous fx) (hfy : Continuous fy)
    (hdx : ∀ x y, HasDerivAt (fun s => f (s,y)) (fx (x,y)) x)
    (hdy : ∀ x y, HasDerivAt (fun s => f (x,s)) (fy (x,y)) y) :
    squareAverage L (fun p => (f p - squareAverage L f) ^ 2) ≤
      2 * L ^ 2 * squareAverage L (fun p => fx p ^ 2 + fy p ^ 2) := by
  let c := squareAverage L f
  let A := fun y => average L (fun x => f (x,y))
  have hpoint : ∀ x ∈ Icc 0 L, ∀ y ∈ Icc 0 L,
      (f (x,y) - c) ^ 2 ≤
        2 * L ^ 2 * average L (fun u => fx (u,y) ^ 2) +
        2 * L ^ 2 * squareAverage L (fun p => fy p ^ 2) := by
    intro x hx y hy
    have hxest := poincare_pointwise hL
      (hf.comp (continuous_id.prodMk continuous_const))
      (hfx.comp (continuous_id.prodMk continuous_const)) (fun u => hdx u y) hx
    have he : A y - c = average L (fun u => f (u,y) - average L (fun v => f (u,v))) := by
      symm
      exact average_sub (hf.comp (continuous_id.prodMk continuous_const)) (continuous_average hf L)
    have hyest : (A y - c) ^ 2 ≤ L ^ 2 * squareAverage L (fun p => fy p ^ 2) := by
      rw [he]
      apply (average_sq_le hL
        ((hf.comp (continuous_id.prodMk continuous_const)).sub (continuous_average hf L))).trans
      have hm := average_mono hL
        (((hf.comp (continuous_id.prodMk continuous_const)).sub (continuous_average hf L)).pow 2)
        (continuous_const.mul (continuous_average (hfy.pow 2) L))
        (fun u _ => poincare_pointwise hL
          (hf.comp (continuous_const.prodMk continuous_id))
          (hfy.comp (continuous_const.prodMk continuous_id)) (hdy u) hy)
      change average L (fun u => (f (u,y) - average L (fun v => f (u,v))) ^ 2) ≤
        average L (fun u => L ^ 2 * average L (fun v => fy (u,v) ^ 2)) at hm
      rw [average_mul] at hm
      exact hm
    change (f (x,y) - A y) ^ 2 ≤ L ^ 2 * average L (fun u => fx (u,y) ^ 2) at hxest
    nlinarith [sq_nonneg ((f (x,y) - A y) - (A y - c))]
  have hq := squareAverage_mono hL ((hf.sub continuous_const).pow 2)
    ((continuous_const.mul ((continuous_average ((hfx.pow 2).comp continuous_swap) L).comp
      continuous_snd)).add continuous_const) hpoint
  have hright : squareAverage L (fun p =>
      2 * L ^ 2 * average L (fun u => fx (u,p.2) ^ 2) +
      2 * L ^ 2 * squareAverage L (fun p => fy p ^ 2)) =
      2 * L ^ 2 * squareAverage L (fun p => fx p ^ 2 + fy p ^ 2) := by
    have hcont : Continuous (fun p : ℝ × ℝ =>
        2 * L ^ 2 * average L (fun u => fx (u,p.2) ^ 2)) :=
      continuous_const.mul ((continuous_average ((hfx.pow 2).comp continuous_swap) L).comp
        continuous_snd)
    rw [squareAverage_add hcont continuous_const, squareAverage_const hL]
    rw [squareAverage_mul, squareAverage_add (f := fun p => fx p ^ 2) (g := fun p => fy p ^ 2)
      (hfx.pow 2) (hfy.pow 2)]
    have he : squareAverage L (fun p => average L (fun u => fx (u,p.2) ^ 2)) =
        squareAverage L (fun p => fx p ^ 2) := by
      unfold squareAverage
      dsimp only
      rw [average_const hL]
      exact (squareAverage_swap (hfx.pow 2) L).symm
    rw [he]
    ring
  exact hq.trans_eq hright

#print axioms square_poincare
end Gimle.Forseti.ClassicalVorticity
