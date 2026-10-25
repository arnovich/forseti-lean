import Gimle.Forseti.ResidualPDE

/-! Regression contracts for residual-certified scalar Burgers fields. -/
namespace Gimle.Forseti.Tests.ResidualPDE
open Set Real
open Gimle.Forseti.ClassicalVorticity Gimle.Forseti.ResidualPDE

/-- A nonzero time-varying field with no spatial dependence. -/
def ramp : SpatialJet where
  value := fun t _ => t
  dx := fun _ _ => 0
  dy := fun _ _ => 0
  dxx := fun _ _ => 0
  dyy := fun _ _ => 0
  dxy := fun _ _ => 0

/-- A zero reconstruction, with a nonzero residual against unit forcing. -/
def zero : SpatialJet where
  value := fun _ _ => 0
  dx := fun _ _ => 0
  dy := fun _ _ => 0
  dxx := fun _ _ => 0
  dyy := fun _ _ => 0
  dxy := fun _ _ => 0

theorem ramp_regular (T : ℝ) : Regular ramp T where
  deriv_x := fun _ _ _ => hasDerivAt_const _ _
  deriv_y := fun _ _ _ => hasDerivAt_const _ _
  deriv_xx := fun _ _ _ => hasDerivAt_const _ _
  deriv_yy := fun _ _ _ => hasDerivAt_const _ _
  deriv_yx := fun _ _ _ => hasDerivAt_const _ _
  deriv_xy := fun _ _ _ => hasDerivAt_const _ _
  continuous_value := continuous_fst.continuousOn
  continuous_dx := continuousOn_const
  continuous_dy := continuousOn_const
  continuous_dxx := continuousOn_const
  continuous_dyy := continuousOn_const
  continuous_dxy := continuousOn_const

theorem zero_regular (T : ℝ) : Regular zero T where
  deriv_x := fun _ _ _ => hasDerivAt_const _ _
  deriv_y := fun _ _ _ => hasDerivAt_const _ _
  deriv_xx := fun _ _ _ => hasDerivAt_const _ _
  deriv_yy := fun _ _ _ => hasDerivAt_const _ _
  deriv_yx := fun _ _ _ => hasDerivAt_const _ _
  deriv_xy := fun _ _ _ => hasDerivAt_const _ _
  continuous_value := continuousOn_const
  continuous_dx := continuousOn_const
  continuous_dy := continuousOn_const
  continuous_dxx := continuousOn_const
  continuous_dyy := continuousOn_const
  continuous_dxy := continuousOn_const

theorem ramp_solves (T : ℝ) :
    Burgers 1 T (fun _ _ => 1) (fun _ _ => 0) ramp (fun _ _ => 1) where
  regular := ramp_regular T
  periodic := fun _ _ _ => ⟨rfl, rfl⟩
  deriv_time := fun _ _ _ => hasDerivAt_id _
  continuous_dt := continuousOn_const
  equation := by intros; norm_num [ramp]

theorem zero_reconstruction (T : ℝ) :
    Burgers 1 T (fun _ _ => 1) (fun _ _ => -1) zero (fun _ _ => 0) where
  regular := zero_regular T
  periodic := fun _ _ _ => ⟨rfl, rfl⟩
  deriv_time := fun _ _ _ => hasDerivAt_const _ _
  continuous_dt := continuousOn_const
  equation := by intros; norm_num [zero]

theorem nonzero_error (t : ℝ) : energy ramp zero t = t ^ 2 := by
  simp [energy, ramp, zero, squareAverage_const (show 0 < 2 * π from mul_pos (by norm_num) pi_pos)]

/-- The zero reconstruction is certified against a nonzero-residual forced PDE. -/
theorem ramp_enclosure :
    ∀ t ∈ Icc (0 : ℝ) 1, energy ramp zero t ≤ gronwallBound 0 1 1 t := by
  have h := (ramp_solves 1).error_le_envelope (zero_reconstruction 1)
    (M := 0) (R := 1) (δ := 0) (by norm_num) (by norm_num)
    (by rw [nonzero_error]; norm_num)
    (fun _ _ => continuous_const)
    (by intros; norm_num [zero])
    (by intros; norm_num [squareAverage_const (show 0 < 2 * π from mul_pos (by norm_num) pi_pos)])
  norm_num only [zero_add, one_pow] at h
  exact h

/-- The concrete example has a real nonzero error, not inconsistent premises. -/
theorem ramp_error_one : energy ramp zero 1 = 1 := by
  rw [nonzero_error]; norm_num

/-- The zero reconstruction cannot be relabeled an exact solution under unit forcing. -/
theorem zero_not_exact :
    ¬ Burgers 1 1 (fun _ _ => 1) (fun _ _ => 0) zero (fun _ _ => 0) := by
  intro h
  have he := h.equation (1 / 2) (by constructor <;> norm_num) (0,0)
  norm_num [zero] at he

/-- A spatially varying field exercising the nonlinear Burgers term. -/
noncomputable def sine : SpatialJet where
  value := fun _ p => sin p.1
  dx := fun _ p => cos p.1
  dy := fun _ _ => 0
  dxx := fun _ p => -sin p.1
  dyy := fun _ _ => 0
  dxy := fun _ _ => 0

theorem sine_regular (T : ℝ) : Regular sine T where
  deriv_x := fun _ _ p => hasDerivAt_sin p.1
  deriv_y := fun _ _ p => by simpa only [sine] using hasDerivAt_const p.2 (sin p.1)
  deriv_xx := fun _ _ p => hasDerivAt_cos p.1
  deriv_yy := fun _ _ _ => hasDerivAt_const _ _
  deriv_yx := fun _ _ _ => hasDerivAt_const _ _
  deriv_xy := fun _ _ p => by simpa only [sine] using hasDerivAt_const p.2 (cos p.1)
  continuous_value := (continuous_sin.comp (continuous_fst.comp continuous_snd)).continuousOn
  continuous_dx := (continuous_cos.comp (continuous_fst.comp continuous_snd)).continuousOn
  continuous_dy := continuousOn_const
  continuous_dxx := ((continuous_sin.comp (continuous_fst.comp continuous_snd)).neg).continuousOn
  continuous_dyy := continuousOn_const
  continuous_dxy := continuousOn_const

noncomputable def sineForcing : Field := fun _ p => sin p.1 * cos p.1 + sin p.1

theorem sine_solves (T : ℝ) :
    Burgers 1 T sineForcing (fun _ _ => 0) sine (fun _ _ => 0) where
  regular := sine_regular T
  periodic := by intro t ht p; simp [sine, sin_add_two_pi]
  deriv_time := fun t _ p => by simpa only [sine] using hasDerivAt_const t (sin p.1)
  continuous_dt := continuousOn_const
  equation := by intros; dsimp [sine, sineForcing]; ring

theorem sine_zero_reconstruction (T : ℝ) :
    Burgers 1 T sineForcing (fun t p => -sineForcing t p) zero (fun _ _ => 0) where
  regular := zero_regular T
  periodic := fun _ _ _ => ⟨rfl, rfl⟩
  deriv_time := fun _ _ _ => hasDerivAt_const _ _
  continuous_dt := continuousOn_const
  equation := by intros; dsimp [zero]; ring

theorem sineForcing_sq_le (t : ℝ) (p : ℝ × ℝ) : sineForcing t p ^ 2 ≤ (2 : ℝ) ^ 2 := by
  apply sq_le_sq.mpr
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    |sineForcing t p| ≤ |sin p.1 * cos p.1| + |sin p.1| := abs_add_le _ _
    _ = |sin p.1| * |cos p.1| + |sin p.1| := by rw [abs_mul]
    _ ≤ 1 * 1 + 1 := add_le_add
      (mul_le_mul (abs_sin_le_one _) (abs_cos_le_one _) (abs_nonneg _) (by norm_num))
      (abs_sin_le_one _)
    _ = 2 := by norm_num

/-- A second concrete application has nonconstant forcing and nonzero nonlinear flux. -/
theorem sine_enclosure :
    ∀ t ∈ Icc (0 : ℝ) 1, energy sine zero t ≤ gronwallBound 1 1 4 t := by
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hinitial : energy sine zero 0 ≤ 1 := by
    have h := squareAverage_mono hL
      (f := fun p => sin p.1 ^ 2) (g := fun _ => (1 : ℝ))
      ((continuous_sin.comp continuous_fst).pow 2) continuous_const
      (fun x _ y _ => show sin x ^ 2 ≤ (1 : ℝ) by
        simpa using (sq_le_sq.mpr (by simpa using abs_sin_le_one x) : sin x ^ 2 ≤ (1 : ℝ) ^ 2))
    simpa [energy, sine, zero, squareAverage_const hL] using h
  have h := (sine_solves 1).error_le_envelope (sine_zero_reconstruction 1)
    (M := 0) (R := 2) (δ := 1) (by norm_num) (by norm_num) hinitial
    (fun _ _ => (((continuous_sin.comp continuous_fst).mul
      (continuous_cos.comp continuous_fst)).add (continuous_sin.comp continuous_fst)).neg)
    (by intros; norm_num [zero])
    (fun t _ => by
      have hm := squareAverage_mono hL
        (f := fun p => (-sineForcing t p) ^ 2) (g := fun _ => (2 : ℝ) ^ 2)
        (((((continuous_sin.comp continuous_fst).mul (continuous_cos.comp continuous_fst)).add
          (continuous_sin.comp continuous_fst)).neg).pow 2) continuous_const
        (fun x _ y _ => by simpa only [neg_sq] using sineForcing_sq_le t (x,y))
      simpa [sineForcing, squareAverage_const hL] using hm)
  norm_num only [zero_add] at h
  exact h

/-- Missing residual allowance cannot prove the desired false conclusion. -/
example : ¬ (∀ t ∈ Icc (0 : ℝ) 1, energy ramp zero t ≤ gronwallBound 0 1 0 t) := by
  intro h
  have hc := h 1 ⟨by norm_num, le_rfl⟩
  rw [ramp_error_one, gronwallBound_ε0_δ0] at hc
  norm_num at hc

/-- Forgetting the initial error would make a nonzero initial field vanish. -/
example : ¬ (∀ t ∈ Icc (0 : ℝ) 1, energy ramp zero (t + 1) ≤ gronwallBound 0 1 0 t) := by
  intro h
  have hc := h 0 ⟨le_rfl, by norm_num⟩
  norm_num [nonzero_error, gronwallBound_x0] at hc

#print axioms ramp_enclosure
#print axioms sine_enclosure

end Gimle.Forseti.Tests.ResidualPDE
