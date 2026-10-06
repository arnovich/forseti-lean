import Gimle.Forseti.ClassicalVorticity.EnergyCalculus

/-! Uniqueness among independent periodic classical vorticity solutions.
The differential estimate is derived from the PDE and spatial calculus;
it is not a premise of the comparison solution class. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set Real

/-- Normalized squared vorticity difference. -/
noncomputable def differenceEnergy (ω₁ ω₂ : SpatialJet) (t : ℝ) : ℝ :=
  squareAverage (2 * π) (fun p => (ω₁.value t p - ω₂.value t p) ^ 2)

/-- The exact physical-space energy identity for two independent solutions. -/
theorem Solves.difference_energy_identity {ν T : ℝ} {initial₁ initial₂ : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T initial₁ ω₁ ψ₁ dt₁) (h₂ : Solves ν T initial₂ ω₂ ψ₂ dt₂)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    2 * squareAverage (2 * π) (fun p =>
      (ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p)) =
      -2 * ν * squareAverage (2 * π) (fun p =>
        (ω₁.dx t p - ω₂.dx t p) ^ 2 + (ω₁.dy t p - ω₂.dy t p) ^ 2) -
      2 * squareAverage (2 * π) (fun p => (ω₁.value t p - ω₂.value t p) *
        (-(ψ₁.dy t p - ψ₂.dy t p) * ω₂.dx t p +
          (ψ₁.dx t p - ψ₂.dx t p) * ω₂.dy t p)) := by
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  let d := ω₁.sub ω₂
  have hr := h₁.vorticity_regular.sub h₂.vorticity_regular
  have hp := h₁.vorticity_periodic.sub h₂.vorticity_periodic
  let A := fun p => d.value t p * (d.dxx t p + d.dyy t p)
  let B := fun p => d.value t p * (-ψ₁.dy t p * d.dx t p + ψ₁.dx t p * d.dy t p)
  let F := fun p => d.value t p * (-(ψ₁.dy t p - ψ₂.dy t p) * ω₂.dx t p +
    (ψ₁.dx t p - ψ₂.dx t p) * ω₂.dy t p)
  have hc := continuous_slice hr.continuous_value htc
  have hA : Continuous A := hc.mul ((continuous_slice hr.continuous_dxx htc).add
    (continuous_slice hr.continuous_dyy htc))
  have hB : Continuous B := hc.mul
    (((continuous_slice h₁.stream_regular.continuous_dy htc).neg.mul
      (continuous_slice hr.continuous_dx htc)).add
      ((continuous_slice h₁.stream_regular.continuous_dx htc).mul
        (continuous_slice hr.continuous_dy htc)))
  have hF : Continuous F := hc.mul
    ((((continuous_slice h₁.stream_regular.continuous_dy htc).sub
      (continuous_slice h₂.stream_regular.continuous_dy htc)).neg.mul
        (continuous_slice h₂.vorticity_regular.continuous_dx htc)).add
      (((continuous_slice h₁.stream_regular.continuous_dx htc).sub
        (continuous_slice h₂.stream_regular.continuous_dx htc)).mul
          (continuous_slice h₂.vorticity_regular.continuous_dy htc)))
  have he : (fun p => d.value t p * (dt₁ t p - dt₂ t p)) =
      (fun p => ν * A p - B p - F p) := by
    funext p
    dsimp [A, B, F, d, SpatialJet.sub]
    linear_combination (ω₁.value t p - ω₂.value t p) * h₁.equation t ht p -
      (ω₁.value t p - ω₂.value t p) * h₂.equation t ht p
  have heint := congrArg (squareAverage (2 * π)) he
  rw [squareAverage_sub (f := fun p => ν * A p - B p) (g := F)
      ((continuous_const.mul hA).sub hB) hF,
    squareAverage_sub (f := fun p => ν * A p) (g := B) (continuous_const.mul hA) hB,
    squareAverage_mul] at heint
  have hdiff := hr.laplacian_pairing hp htc
  have htrans := hr.transport_pairing h₁.stream_regular hp h₁.stream_periodic htc
  change squareAverage (2 * π) A = -squareAverage (2 * π)
    (fun p => d.dx t p ^ 2 + d.dy t p ^ 2) at hdiff
  change squareAverage (2 * π) B = 0 at htrans
  rw [hdiff, htrans] at heint
  change 2 * squareAverage (2 * π) (fun p => d.value t p * (dt₁ t p - dt₂ t p)) =
    -2 * ν * squareAverage (2 * π) (fun p => d.dx t p ^ 2 + d.dy t p ^ 2) -
      2 * squareAverage (2 * π) F
  rw [heint]
  ring

/-- The squared difference has the classical integral time derivative. -/
theorem Solves.hasDerivAt_differenceEnergy {ν T : ℝ} {initial₁ initial₂ : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T initial₁ ω₁ ψ₁ dt₁) (h₂ : Solves ν T initial₂ ω₂ ψ₂ dt₂)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (differenceEnergy ω₁ ω₂)
      (2 * squareAverage (2 * π) (fun p =>
        (ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p))) t := by
  have hc := h₁.vorticity_regular.continuous_value.sub h₂.vorticity_regular.continuous_value
  have hdt := h₁.continuous_dt.sub h₂.continuous_dt
  have h := hasDerivAt_squareAverage
    (f := fun s p => (ω₁.value s p - ω₂.value s p) ^ 2)
    (dt := fun s p => 2 * (ω₁.value s p - ω₂.value s p) * (dt₁ s p - dt₂ s p))
    (L := 2 * π) (mul_pos (by norm_num) pi_pos)
    (hc.pow 2) ((continuousOn_const.mul hc).mul hdt)
    (fun s hs p => by
      convert! ((h₁.deriv_time s hs p).sub (h₂.deriv_time s hs p)).pow 2 using 1
      all_goals simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.sub_apply]) ht
  have he : (fun p => 2 * (ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p)) =
      (fun p => 2 * ((ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p))) := by
    funext p; ring
  change HasDerivAt (differenceEnergy ω₁ ω₂)
    (squareAverage (2 * π) (fun p =>
      2 * (ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p))) t at h
  rw [he, squareAverage_mul] at h
  exact h

/-- The PDE gives a one-sided energy difference estimate on each interior slice. -/
theorem Solves.difference_energy_le {ν T M : ℝ} {initial₁ initial₂ : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T initial₁ ω₁ ψ₁ dt₁) (h₂ : Solves ν T initial₂ ω₂ ψ₂ dt₂)
    (hν : 0 ≤ ν) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hM : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π),
      ω₂.dx t (x,y) ^ 2 + ω₂.dy t (x,y) ^ 2 ≤ M) :
    2 * squareAverage (2 * π) (fun p =>
      (ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p)) ≤
      (M + 2 * (2 * π) ^ 2) * differenceEnergy ω₁ ω₂ t := by
  have htc : t ∈ Icc 0 T := ⟨ht.1.le, ht.2.le⟩
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hnl := nonlinear_pairing_le hL
    ((continuous_slice h₁.vorticity_regular.continuous_value htc).sub
      (continuous_slice h₂.vorticity_regular.continuous_value htc))
    (((continuous_slice h₁.stream_regular.continuous_dy htc).sub
      (continuous_slice h₂.stream_regular.continuous_dy htc)).neg)
    ((continuous_slice h₁.stream_regular.continuous_dx htc).sub
      (continuous_slice h₂.stream_regular.continuous_dx htc))
    (continuous_slice h₂.vorticity_regular.continuous_dx htc)
    (continuous_slice h₂.vorticity_regular.continuous_dy htc) hM
  change -2 * squareAverage (2 * π) (fun p => (ω₁.value t p - ω₂.value t p) *
    (-(ψ₁.dy t p - ψ₂.dy t p) * ω₂.dx t p +
      (ψ₁.dx t p - ψ₂.dx t p) * ω₂.dy t p)) ≤
      M * differenceEnergy ω₁ ω₂ t + squareAverage (2 * π) (fun p =>
        (-(ψ₁.dy t p - ψ₂.dy t p)) ^ 2 + (ψ₁.dx t p - ψ₂.dx t p) ^ 2) at hnl
  simp only [neg_sq] at hnl
  have he : (fun p => (ψ₁.dy t p - ψ₂.dy t p) ^ 2 + (ψ₁.dx t p - ψ₂.dx t p) ^ 2) =
      (fun p => (ψ₁.dx t p - ψ₂.dx t p) ^ 2 + (ψ₁.dy t p - ψ₂.dy t p) ^ 2) := by
    funext p; ring
  rw [he] at hnl
  have hell := h₁.velocity_difference_sq_le h₂ htc
  have hn := squareAverage_nonneg hL (fun p => add_nonneg
    (sq_nonneg (ω₁.dx t p - ω₂.dx t p)) (sq_nonneg (ω₁.dy t p - ω₂.dy t p)))
  have hdiff := mul_nonneg hν hn
  rw [h₁.difference_energy_identity h₂ ht]
  dsimp [differenceEnergy] at *
  nlinarith only [hnl, hell, hdiff]

/-- Uniqueness of vorticity among all fields in the independent classical class,
on the common closed interval, for nonnegative viscosity. Stream functions
remain free up to a time-dependent spatial constant. -/
theorem Solves.vorticity_unique {ν T : ℝ} {initial : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T initial ω₁ ψ₁ dt₁) (h₂ : Solves ν T initial ω₂ ψ₂ dt₂)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, ∀ p, ω₁.value t p = ω₂.value t p := by
  let K := Icc (0 : ℝ) (2 * π) ×ˢ Icc (0 : ℝ) (2 * π)
  have hcgrad := (h₂.vorticity_regular.continuous_dx.pow 2).add
    (h₂.vorticity_regular.continuous_dy.pow 2)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).bddAbove_image
    (hcgrad.mono (show Icc (0 : ℝ) T ×ˢ K ⊆ {z : ℝ × (ℝ × ℝ) | z.1 ∈ Icc 0 T} from
      fun _ hz => hz.1))
  have hc := h₁.vorticity_regular.continuous_value.sub h₂.vorticity_regular.continuous_value
  have hzero := difference_eq_zero (D := differenceEnergy ω₁ ω₂)
    (D' := fun t => 2 * squareAverage (2 * π) (fun p =>
      (ω₁.value t p - ω₂.value t p) * (dt₁ t p - dt₂ t p)))
    (C := M + 2 * (2 * π) ^ 2) hT (continuousOn_squareAverage (hc.pow 2) _)
    (fun t ht => h₁.hasDerivAt_differenceEnergy h₂ ht)
    (fun _ _ => squareAverage_nonneg (mul_pos (by norm_num) pi_pos) (fun _ => sq_nonneg _))
    (by
      unfold differenceEnergy
      simp only [h₁.initial_value, h₂.initial_value, sub_self, zero_pow (by decide : 2 ≠ 0)]
      exact squareAverage_const (mul_pos (by norm_num) pi_pos) 0)
    (fun t ht => h₁.difference_energy_le h₂ hν ht (fun x hx y hy =>
      by
        apply hM
        exact ⟨(t,(x,y)), ⟨⟨ht.1.le, ht.2.le⟩, hx, hy⟩, rfl⟩))
  intro t ht p
  apply sub_eq_zero.mp
  exact (h₁.vorticity_periodic.sub h₂.vorticity_periodic).eq_zero_of_squareAverage_sq_eq_zero
    ht (continuous_slice (f := fun s p => ω₁.value s p - ω₂.value s p) hc ht) (hzero t ht) p

/-- The associated zero-mean velocities are unique as well. No equality of the
stream functions themselves is asserted, since their spatial constants are free. -/
theorem Solves.velocity_unique {ν T : ℝ} {initial : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T initial ω₁ ψ₁ dt₁) (h₂ : Solves ν T initial ω₂ ψ₂ dt₂)
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, ∀ p, (-ψ₁.dy t p, ψ₁.dx t p) = (-ψ₂.dy t p, ψ₂.dx t p) := by
  intro t ht p
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  have hr := h₁.stream_regular.sub h₂.stream_regular
  have hp := h₁.stream_periodic.sub h₂.stream_periodic
  have hcX := continuous_slice hr.continuous_dx ht
  have hcY := continuous_slice hr.continuous_dy ht
  have hv := h₁.vorticity_unique h₂ hν hT
  have hell := h₁.velocity_difference_sq_le h₂ ht
  simp only [hv t ht, sub_self, zero_pow (by decide : 2 ≠ 0), squareAverage_const hL,
    mul_zero] at hell
  have hxle := squareAverage_mono hL (hcX.pow 2) ((hcX.pow 2).add (hcY.pow 2))
    (fun x _ y _ => le_add_of_nonneg_right (sq_nonneg ((ψ₁.sub ψ₂).dy t (x,y))))
  have hyle := squareAverage_mono hL (hcY.pow 2) ((hcX.pow 2).add (hcY.pow 2))
    (fun x _ y _ => le_add_of_nonneg_left (sq_nonneg ((ψ₁.sub ψ₂).dx t (x,y))))
  have hxzero : squareAverage (2 * π) (fun q => (ψ₁.dx t q - ψ₂.dx t q) ^ 2) = 0 :=
    le_antisymm (hxle.trans hell) (squareAverage_nonneg hL (fun _ => sq_nonneg _))
  have hyzero : squareAverage (2 * π) (fun q => (ψ₁.dy t q - ψ₂.dy t q) ^ 2) = 0 :=
    le_antisymm (hyle.trans hell) (squareAverage_nonneg hL (fun _ => sq_nonneg _))
  have hx := (hp.dx hr).eq_zero_of_squareAverage_sq_eq_zero ht hcX hxzero p
  have hy := (hp.dy hr).eq_zero_of_squareAverage_sq_eq_zero ht hcY hyzero p
  change ψ₁.dx t p - ψ₂.dx t p = 0 at hx
  change ψ₁.dy t p - ψ₂.dy t p = 0 at hy
  rw [sub_eq_zero.mp hx, sub_eq_zero.mp hy]

#print axioms Solves.difference_energy_identity
#print axioms Solves.vorticity_unique
#print axioms Solves.velocity_unique
end Gimle.Forseti.ClassicalVorticity
