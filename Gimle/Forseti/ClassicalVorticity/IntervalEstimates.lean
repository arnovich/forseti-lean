import Gimle.Forseti.ClassicalVorticity.PeriodicCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp

/-! Elementary square-integral estimates, with explicit constants, for the
periodic elliptic comparison. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set MeasureTheory
open scoped Interval

/-- A scalar Cauchy--Schwarz estimate against the constant function. -/
theorem integral_sq_le_length_mul {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * (∫ x in a..b, (f x) ^ 2) := by
  let m := (∫ x in a..b, f x) / (b - a)
  have hc : ContinuousOn f (uIcc a b) := by simpa [uIcc_of_le hab.le] using hf
  have hi : IntervalIntegrable f volume a b := hc.intervalIntegrable
  have hs : IntervalIntegrable (fun x => f x ^ 2) volume a b := (hc.pow 2).intervalIntegrable
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le (fun x => sq_nonneg (f x - m))
  have he : (fun x => (f x - m) ^ 2) =
      (fun x => (f x) ^ 2 - 2 * m * f x + m ^ 2) := by funext x; ring
  rw [he, intervalIntegral.integral_add (hs.sub (hi.const_mul _))
    intervalIntegrable_const, intervalIntegral.integral_sub hs (hi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hm : m * (b - a) = ∫ x in a..b, f x := div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hp := mul_nonneg (sub_pos.mpr hab).le hn
  nlinarith [sq_nonneg ((b - a) * m - ∫ x in a..b, f x)]

/-- Spatial average on a positive-length interval. -/
noncomputable def average (L : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in 0..L, f x) / L

@[simp] theorem average_const {L : ℝ} (hL : 0 < L) (c : ℝ) :
    average L (fun _ => c) = c := by
  simp [average, hL.ne']

/-- Addition commutes with the interval average. -/
theorem average_add {L : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    average L (fun x => f x + g x) = average L f + average L g := by
  simp only [average, intervalIntegral.integral_add (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), add_div]

/-- Subtraction commutes with the interval average. -/
theorem average_sub {L : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    average L (fun x => f x - g x) = average L f - average L g := by
  simp only [average, intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _), sub_div]

/-- A scalar factor commutes with the interval average. -/
theorem average_mul (L c : ℝ) (f : ℝ → ℝ) :
    average L (fun x => c * f x) = c * average L f := by
  simp only [average, intervalIntegral.integral_const_mul, mul_div_assoc]

/-- Pointwise order on the interval is preserved by its average. -/
theorem average_mono {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ x ∈ Icc 0 L, f x ≤ g x) :
    average L f ≤ average L g := by
  exact div_le_div_of_nonneg_right
    (intervalIntegral.integral_mono_on hL.le (hf.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _) hfg) hL.le

/-- The average of a nonnegative function is nonnegative. -/
theorem average_nonneg {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ average L f :=
  div_nonneg (intervalIntegral.integral_nonneg_of_forall hL.le hf) hL.le

/-- Jensen's square inequality for the interval average. -/
theorem average_sq_le {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : Continuous f) :
    (average L f) ^ 2 ≤ average L (fun x => f x ^ 2) := by
  have h := integral_sq_le_length_mul hL hf.continuousOn
  simp only [sub_zero] at h
  unfold average
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  calc
    _ ≤ L * (∫ x in 0..L, f x ^ 2) := h
    _ = ((∫ x in 0..L, f x ^ 2) / L) * L ^ 2 := by field_simp

/-- The fundamental theorem of calculus bounds oscillation by the derivative's
square integral. No periodicity or zero-mean hypothesis is needed. -/
theorem oscillation_sq_le {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hc : Continuous f') (hd : ∀ x, HasDerivAt f (f' x) x)
    {x y : ℝ} (hx : x ∈ Icc 0 L) (hy : y ∈ Icc 0 L) :
    (f x - f y) ^ 2 ≤ L ^ 2 * average L (fun z => f' z ^ 2) := by
  suffices ho : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      (f b - f a) ^ 2 ≤ L * (∫ z in 0..L, f' z ^ 2) by
    have he : L ^ 2 * average L (fun z => f' z ^ 2) =
        L * (∫ z in 0..L, f' z ^ 2) := by unfold average; field_simp
    rw [he]
    rcases le_total x y with hxy | hyx
    · simpa only [sub_sq_comm] using ho x hx y hy hxy
    · exact ho y hy x hx hyx
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · simpa using mul_nonneg hL.le
      (intervalIntegral.integral_nonneg_of_forall (μ := volume) hL.le
        (fun z => sq_nonneg (f' z)))
  have hcs := integral_sq_le_length_mul hab hc.continuousOn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ => hd z) (hc.intervalIntegrable a b)] at hcs
  have hi := intervalIntegral.integral_mono_interval (μ := volume) ha.1 hab.le hb.2
    (Filter.Eventually.of_forall (fun z => sq_nonneg (f' z)))
    ((hc.pow 2).intervalIntegrable 0 L)
  have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab.le
    (fun z => sq_nonneg (f' z))
  calc
    _ ≤ (b - a) * (∫ z in a..b, f' z ^ 2) := hcs
    _ ≤ L * (∫ z in a..b, f' z ^ 2) := mul_le_mul_of_nonneg_right (by linarith [ha.1, hb.2]) hn
    _ ≤ L * (∫ z in 0..L, f' z ^ 2) := mul_le_mul_of_nonneg_left hi hL.le

/-- A coarse one-dimensional Poincare estimate, pointwise relative to the mean. -/
theorem poincare_pointwise {L : ℝ} (hL : 0 < L) {f f' : ℝ → ℝ}
    (hf : Continuous f) (hc : Continuous f') (hd : ∀ x, HasDerivAt f (f' x) x)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    (f x - average L f) ^ 2 ≤ L ^ 2 * average L (fun z => f' z ^ 2) := by
  have he : f x - average L f = average L (fun y => f x - f y) := by
    rw [average_sub continuous_const hf, average_const hL]
  rw [he]
  exact (average_sq_le hL (continuous_const.sub hf)).trans
    ((average_mono hL ((continuous_const.sub hf).pow 2) continuous_const
      (fun y hy => oscillation_sq_le hL hc hd hx hy)).trans_eq (average_const hL _))

#print axioms integral_sq_le_length_mul
#print axioms poincare_pointwise
end Gimle.Forseti.ClassicalVorticity
