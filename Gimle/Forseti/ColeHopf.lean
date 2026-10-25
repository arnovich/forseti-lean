import Gimle.Forseti.ResidualPDE

/-!
# Positive heat profiles and periodic Burgers fields

A positive one-dimensional heat profile, together with its actual derivative
witnesses, constructs a classical unforced Burgers solution on the periodic
square. The second spatial coordinate is inactive. Positivity is a domain
condition for the quotient, not a numerical check. The construction supplies
existence for its explicit initial profile; a separate uniqueness theorem
compares it with arbitrary admitted classical Burgers fields. This is a theorem
about real fields and derivatives; formal power-series constructions require
their own correspondence to these fields.
-/
namespace Gimle.Forseti.ColeHopf
open Set Real
open Gimle.Forseti.ClassicalVorticity Gimle.Forseti.ResidualPDE

/-- A heat profile and three spatial derivative witnesses. -/
structure HeatJet where
  value : ℝ → ℝ → ℝ
  dx : ℝ → ℝ → ℝ
  dxx : ℝ → ℝ → ℝ
  dxxx : ℝ → ℝ → ℝ

/-- Analytic obligations for the positive periodic heat profile on a closed strip. -/
structure HeatJet.Valid (h : HeatJet) (ν T : ℝ) : Prop where
  deriv_x : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (h.value t) (h.dx t x) x
  deriv_xx : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (h.dx t) (h.dxx t x) x
  deriv_xxx : ∀ t ∈ Icc 0 T, ∀ x, HasDerivAt (h.dxx t) (h.dxxx t x) x
  deriv_time : ∀ t ∈ Ioo 0 T, ∀ x,
    HasDerivAt (fun s => h.value s x) (ν * h.dxx t x) t
  deriv_time_dx : ∀ t ∈ Ioo 0 T, ∀ x,
    HasDerivAt (fun s => h.dx s x) (ν * h.dxxx t x) t
  continuous_value : ContinuousOn (fun z : ℝ × ℝ => h.value z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dx : ContinuousOn (fun z : ℝ × ℝ => h.dx z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dxx : ContinuousOn (fun z : ℝ × ℝ => h.dxx z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dxxx : ContinuousOn (fun z : ℝ × ℝ => h.dxxx z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  positive : ∀ t ∈ Icc 0 T, ∀ x, 0 < h.value t x
  periodic_value : ∀ t ∈ Icc 0 T, Function.Periodic (h.value t) (2 * π)
  periodic_dx : ∀ t ∈ Icc 0 T, Function.Periodic (h.dx t) (2 * π)

/-- The Cole–Hopf quotient and its physical spatial derivatives. -/
noncomputable def HeatJet.burgersJet (h : HeatJet) (ν : ℝ) : SpatialJet where
  value := fun t p => -2 * ν * (h.dx t p.1 / h.value t p.1)
  dx := fun t p => -2 * ν * (h.dxx t p.1 / h.value t p.1 -
    h.dx t p.1 ^ 2 / h.value t p.1 ^ 2)
  dy := fun _ _ => 0
  dxx := fun t p => -2 * ν * (h.dxxx t p.1 / h.value t p.1 -
    3 * (h.dx t p.1 * h.dxx t p.1) / h.value t p.1 ^ 2 +
    2 * h.dx t p.1 ^ 3 / h.value t p.1 ^ 3)
  dyy := fun _ _ => 0
  dxy := fun _ _ => 0

/-- The quotient's time derivative, using the heat equation and its x derivative. -/
noncomputable def HeatJet.burgersDt (h : HeatJet) (ν : ℝ) : Field :=
  fun t p => -2 * ν ^ 2 * (h.dxxx t p.1 / h.value t p.1 -
    (h.dx t p.1 * h.dxx t p.1) / h.value t p.1 ^ 2)

private theorem lift_continuous {f : ℝ → ℝ → ℝ} {T : ℝ}
    (hc : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) {z | z.1 ∈ Icc 0 T}) :
    ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1) {z | z.1 ∈ Icc 0 T} :=
  hc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
    (fun _ hz => hz)

/-- Spatial regularity follows by differentiating the quotient, with no denominator clearing
until its nonvanishing has been established. -/
theorem HeatJet.Valid.regular {h : HeatJet} {ν T : ℝ} (hv : h.Valid ν T) :
    Regular (h.burgersJet ν) T := by
  have hc0 := lift_continuous hv.continuous_value
  have hc1 := lift_continuous hv.continuous_dx
  have hc2 := lift_continuous hv.continuous_dxx
  have hc3 := lift_continuous hv.continuous_dxxx
  have hn (z : ℝ × (ℝ × ℝ)) (hz : z.1 ∈ Icc 0 T) : h.value z.1 z.2.1 ≠ 0 :=
    ne_of_gt (hv.positive z.1 hz z.2.1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, continuousOn_const, ?_,
    continuousOn_const, continuousOn_const⟩
  · intro t ht p
    have hn0 := ne_of_gt (hv.positive t ht p.1)
    convert! ((hv.deriv_xx t ht p.1).div (hv.deriv_x t ht p.1) hn0).const_mul (-2 * ν) using 1
    dsimp [HeatJet.burgersJet]
    field_simp
  · intro t ht p
    exact hasDerivAt_const p.2 (-2 * ν * (h.dx t p.1 / h.value t p.1))
  · intro t ht p
    have hn0 := ne_of_gt (hv.positive t ht p.1)
    convert! (((hv.deriv_xxx t ht p.1).div (hv.deriv_x t ht p.1) hn0).sub
      (((hv.deriv_xx t ht p.1).pow 2).div ((hv.deriv_x t ht p.1).pow 2)
        (pow_ne_zero 2 hn0))).const_mul (-2 * ν) using 1
    dsimp [HeatJet.burgersJet]
    field_simp
    ring
  · intros; exact hasDerivAt_const _ _
  · intros; exact hasDerivAt_const _ _
  · intro t ht p
    exact hasDerivAt_const p.2 (-2 * ν * (h.dxx t p.1 / h.value t p.1 -
      h.dx t p.1 ^ 2 / h.value t p.1 ^ 2))
  · exact continuousOn_const.mul (hc1.div hc0 hn)
  · exact continuousOn_const.mul ((hc2.div hc0 hn).sub
      ((hc1.pow 2).div (hc0.pow 2) (fun z hz => pow_ne_zero 2 (hn z hz))))
  · exact continuousOn_const.mul (((hc3.div hc0 hn).sub
      ((continuousOn_const.mul (hc1.mul hc2)).div (hc0.pow 2)
        (fun z hz => pow_ne_zero 2 (hn z hz)))).add
      ((continuousOn_const.mul (hc1.pow 3)).div (hc0.pow 3)
        (fun z hz => pow_ne_zero 3 (hn z hz))))

/-- Every admitted heat profile gives an exact, unforced periodic Burgers solution. -/
theorem HeatJet.Valid.burgers {h : HeatJet} {ν T : ℝ} (hv : h.Valid ν T) :
    Burgers ν T (fun _ _ => 0) (fun _ _ => 0) (h.burgersJet ν) (h.burgersDt ν) := by
  have hc0 := lift_continuous hv.continuous_value
  have hc1 := lift_continuous hv.continuous_dx
  have hc2 := lift_continuous hv.continuous_dxx
  have hc3 := lift_continuous hv.continuous_dxxx
  have hn (z : ℝ × (ℝ × ℝ)) (hz : z.1 ∈ Icc 0 T) : h.value z.1 z.2.1 ≠ 0 :=
    ne_of_gt (hv.positive z.1 hz z.2.1)
  refine ⟨hv.regular, ?_, ?_, ?_, ?_⟩
  · intro t ht p
    constructor
    · dsimp [HeatJet.burgersJet]
      rw [hv.periodic_dx t ht p.1, hv.periodic_value t ht p.1]
    · rfl
  · intro t ht p
    have hn0 := ne_of_gt (hv.positive t ⟨ht.1.le, ht.2.le⟩ p.1)
    convert! ((hv.deriv_time_dx t ht p.1).div (hv.deriv_time t ht p.1) hn0).const_mul
      (-2 * ν) using 1
    dsimp [HeatJet.burgersJet, HeatJet.burgersDt]
    field_simp
  · exact continuousOn_const.mul ((hc3.div hc0 hn).sub
      ((hc1.mul hc2).div (hc0.pow 2) (fun z hz => pow_ne_zero 2 (hn z hz))))
  · intro t ht p
    have hn0 := ne_of_gt (hv.positive t ⟨ht.1.le, ht.2.le⟩ p.1)
    dsimp [HeatJet.burgersJet, HeatJet.burgersDt]
    field_simp
    ring

/-- A one-sided Burgers slope bound discards a nonpositive square. -/
theorem HeatJet.slope_le (h : HeatJet) {ν m B t x : ℝ} (hν : 0 ≤ ν)
    (hm : 0 < m) (hden : m ≤ h.value t x) (hsecond : |h.dxx t x| ≤ B) :
    -(h.burgersJet ν).dx t (x,0) ≤ 2 * ν * B / m := by
  have hp : 0 < h.value t x := hm.trans_le hden
  have hB : 0 ≤ B := (abs_nonneg _).trans hsecond
  have hratio : h.dxx t x / h.value t x ≤ B / m :=
    (div_le_div_of_nonneg_right ((le_abs_self _).trans hsecond) hp.le).trans
      (div_le_div_of_nonneg_left hB hm hden)
  have hs : 0 ≤ h.dx t x ^ 2 / h.value t x ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfactor : 0 ≤ 2 * ν := mul_nonneg (by norm_num) hν
  have hh := mul_le_mul_of_nonneg_left
    (sub_le_self (h.dxx t x / h.value t x) hs) hfactor
  have hb := mul_le_mul_of_nonneg_left hratio hfactor
  calc
    -(h.burgersJet ν).dx t (x,0) =
        2 * ν * (h.dxx t x / h.value t x - h.dx t x ^ 2 / h.value t x ^ 2) := by
      dsimp [HeatJet.burgersJet]
      ring
    _ ≤ 2 * ν * (h.dxx t x / h.value t x) := hh
    _ ≤ 2 * ν * (B / m) := hb
    _ = 2 * ν * B / m := by ring

/-- A pointwise quotient-difference budget with explicit positive denominators. -/
theorem HeatJet.value_difference_le (a b : HeatJet) {ν t x mA mB D0 D1 B1 : ℝ}
    (hν : 0 ≤ ν) (hmA : 0 < mA) (hmB : 0 < mB)
    (ha : mA ≤ a.value t x) (hb : mB ≤ b.value t x)
    (hD0 : |a.value t x - b.value t x| ≤ D0)
    (hD1 : |a.dx t x - b.dx t x| ≤ D1) (hB1 : |b.dx t x| ≤ B1) :
    |(a.burgersJet ν).value t (x,0) - (b.burgersJet ν).value t (x,0)| ≤
      2 * ν * (D1 / mA + B1 * D0 / (mA * mB)) := by
  have hpa : 0 < a.value t x := hmA.trans_le ha
  have hpb : 0 < b.value t x := hmB.trans_le hb
  have hD0n : 0 ≤ D0 := (abs_nonneg _).trans hD0
  have hD1n : 0 ≤ D1 := (abs_nonneg _).trans hD1
  have hB1n : 0 ≤ B1 := (abs_nonneg _).trans hB1
  have hid : a.dx t x / a.value t x - b.dx t x / b.value t x =
      (a.dx t x - b.dx t x) / a.value t x +
      b.dx t x * (b.value t x - a.value t x) / (a.value t x * b.value t x) := by
    field_simp
    ring
  have hfirst : |(a.dx t x - b.dx t x) / a.value t x| ≤ D1 / mA := by
    rw [abs_div, abs_of_pos hpa]
    exact (div_le_div_of_nonneg_right hD1 hpa.le).trans
      (div_le_div_of_nonneg_left hD1n hmA ha)
  have hnum : |b.dx t x * (b.value t x - a.value t x)| ≤ B1 * D0 := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hB1 hD0 (abs_nonneg _) hB1n
  have hsecond : |b.dx t x * (b.value t x - a.value t x) /
      (a.value t x * b.value t x)| ≤ B1 * D0 / (mA * mB) := by
    rw [abs_div, abs_of_pos (mul_pos hpa hpb)]
    exact (div_le_div_of_nonneg_right hnum (mul_pos hpa hpb).le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hB1n hD0n) (mul_pos hmA hmB)
        (mul_le_mul ha hb hmB.le hpa.le))
  have hquot := (abs_add_le _ _).trans (add_le_add hfirst hsecond)
  rw [← hid] at hquot
  have hh := mul_le_mul_of_nonneg_left hquot (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hν)
  have hfactor : (a.burgersJet ν).value t (x,0) - (b.burgersJet ν).value t (x,0) =
      (-2 * ν) * (a.dx t x / a.value t x - b.dx t x / b.value t x) := by
    dsimp [HeatJet.burgersJet]; ring
  rw [hfactor, abs_mul, abs_mul, abs_of_nonneg hν]
  norm_num only [abs_neg] at *
  exact hh

/-- An explicit bounded-slope comparison solution identifies every classical solution
with the same initial field. The conclusion is derived from the PDE energy estimate. -/
theorem burgers_unique_of_slope_bound {ν T M : ℝ} {u v : SpatialJet} {ut vt : Field}
    (hu : Burgers ν T (fun _ _ => 0) (fun _ _ => 0) u ut)
    (hv : Burgers ν T (fun _ _ => 0) (fun _ _ => 0) v vt)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) (hinit : ∀ p, u.value 0 p = v.value 0 p)
    (hslope : ∀ t ∈ Ioo 0 T, ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π),
      -v.dx t (x,y) ≤ M) :
    ∀ t ∈ Icc 0 T, ∀ p, u.value t p = v.value t p := by
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hi : energy u v 0 ≤ 0 := by
    simp only [energy, hinit, sub_self, zero_pow (by decide : 2 ≠ 0), squareAverage_const hL]
    exact le_rfl
  have hbound := hu.error_le_envelope hv (δ := 0) (M := M) (R := 0) hν hT hi
    (fun _ _ => continuous_const) hslope
    (by intros; simp [squareAverage_const hL])
  intro t ht p
  have he : energy u v t = 0 := le_antisymm
    (by simpa only [zero_pow (by decide : 2 ≠ 0), gronwallBound_ε0_δ0] using hbound t ht) (energy_nonneg u v t)
  apply sub_eq_zero.mp
  exact (hu.periodic.sub hv.periodic).eq_zero_of_squareAverage_sq_eq_zero ht
    ((continuous_slice hu.regular.continuous_value ht).sub
      (continuous_slice hv.regular.continuous_value ht)) he p

#print axioms HeatJet.Valid.burgers
#print axioms HeatJet.slope_le
#print axioms HeatJet.value_difference_le
#print axioms burgers_unique_of_slope_bound
end Gimle.Forseti.ColeHopf
