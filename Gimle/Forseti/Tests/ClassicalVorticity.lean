import Gimle.Forseti.ClassicalVorticity
import Gimle.Forseti.ClassicalVorticity.PeriodicCalculus
import Gimle.Forseti.MildVorticity
import Gimle.Asgard.Examples.MildBand

/-! Regression proofs for the independent classical comparison interface. -/
namespace Gimle.Forseti.Tests.ClassicalVorticity
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild
open Gimle.Forseti.ClassicalVorticity

/-- An actual certified circuit field inhabits the independent solution class. -/
theorem certified_field {ν : ℚ} {P : Torus.TrigPoly} {T : ℝ} {output : Point 1}
    (h : MildVorticity.Certified ν P T output) :
    Solves (ν : ℝ) T (RealPoly.field (realEmbed P))
      (mildJet ν (output 0)) (mildJet ν (psi (output 0)))
      (seriesDt ν (output 0)) :=
  of_mild h.classical

/-- The concrete NavierStokes notebook trajectory belongs to the same class. -/
theorem notebook_field :
    Solves (1 / 10) (1 / 5760)
      (RealPoly.field (realEmbed Gimle.Asgard.Examples.EulerThreeMode.ω₀))
      (mildJet (1 / 10) (Gimle.Asgard.Examples.MildBand.ω (1 / 10)))
      (mildJet (1 / 10) (psi (Gimle.Asgard.Examples.MildBand.ω (1 / 10))))
      (seriesDt (1 / 10) (Gimle.Asgard.Examples.MildBand.ω (1 / 10))) := by
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    of_mild Gimle.Asgard.Examples.MildBand.classical

/-- The scalar comparison includes the upper endpoint. -/
theorem zero_difference {D D' : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn D (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ioo 0 T, HasDerivAt D (D' t) t)
    (hn : ∀ t ∈ Set.Icc 0 T, 0 ≤ D t) (h0 : D 0 = 0)
    (hle : ∀ t ∈ Set.Ioo 0 T, D' t ≤ C * D t) : D T = 0 :=
  difference_eq_zero hT hc hd hn h0 hle T ⟨hT, le_rfl⟩

end Gimle.Forseti.Tests.ClassicalVorticity

namespace Gimle.Forseti.Tests.ClassicalVorticity
open Gimle.Forseti.ClassicalVorticity Set Real

/-- A stationary shear with sine vorticity; no evenness assumption is present. -/
noncomputable def sineJet : SpatialJet where
  value := fun _ x => sin x.1
  dx := fun _ x => cos x.1
  dy := fun _ _ => 0
  dxx := fun _ x => -sin x.1
  dyy := fun _ _ => 0
  dxy := fun _ _ => 0

/-- Its periodic stream function has the opposite sign. -/
noncomputable def sinePsi : SpatialJet where
  value := fun _ x => -sin x.1
  dx := fun _ x => -cos x.1
  dy := fun _ _ => 0
  dxx := fun _ x => sin x.1
  dyy := fun _ _ => 0
  dxy := fun _ _ => 0

private theorem sine_regular (T : ℝ) : Regular sineJet T where
  deriv_x := fun _ _ x => hasDerivAt_sin x.1
  deriv_y := fun _ _ x => hasDerivAt_const x.2 (sin x.1)
  deriv_xx := fun _ _ x => hasDerivAt_cos x.1
  deriv_yy := fun _ _ x => hasDerivAt_const x.2 (0 : ℝ)
  deriv_yx := fun _ _ x => hasDerivAt_const x.1 (0 : ℝ)
  deriv_xy := fun _ _ x => by
    change HasDerivAt (fun _ : ℝ => cos x.1) 0 x.2
    exact hasDerivAt_const x.2 (cos x.1)
  continuous_value := by exact (continuous_sin.comp (continuous_fst.comp continuous_snd)).continuousOn
  continuous_dx := by exact (continuous_cos.comp (continuous_fst.comp continuous_snd)).continuousOn
  continuous_dy := continuous_const.continuousOn
  continuous_dxx := by exact (continuous_sin.comp (continuous_fst.comp continuous_snd)).neg.continuousOn
  continuous_dyy := continuous_const.continuousOn
  continuous_dxy := continuous_const.continuousOn

private theorem sine_psi_regular (T : ℝ) : Regular sinePsi T where
  deriv_x := fun _ _ x => (hasDerivAt_sin x.1).neg
  deriv_y := fun _ _ x => hasDerivAt_const x.2 (-sin x.1)
  deriv_xx := fun _ _ x => by
    convert! (hasDerivAt_cos x.1).neg using 1
    simp [sinePsi]
  deriv_yy := fun _ _ x => hasDerivAt_const x.2 (0 : ℝ)
  deriv_yx := fun _ _ x => hasDerivAt_const x.1 (0 : ℝ)
  deriv_xy := fun _ _ x => by
    change HasDerivAt (fun _ : ℝ => -cos x.1) 0 x.2
    exact hasDerivAt_const x.2 (-cos x.1)
  continuous_value := by exact (continuous_sin.comp (continuous_fst.comp continuous_snd)).neg.continuousOn
  continuous_dx := by exact (continuous_cos.comp (continuous_fst.comp continuous_snd)).neg.continuousOn
  continuous_dy := continuous_const.continuousOn
  continuous_dxx := by exact (continuous_sin.comp (continuous_fst.comp continuous_snd)).continuousOn
  continuous_dyy := continuous_const.continuousOn
  continuous_dxy := continuous_const.continuousOn

/-- The independent class admits an odd Euler solution on every finite interval. -/
theorem sine_euler (T : ℝ) :
    Solves 0 T (fun x => sin x.1) sineJet sinePsi (fun _ _ => 0) where
  vorticity_regular := sine_regular T
  stream_regular := sine_psi_regular T
  vorticity_periodic := fun _ _ x => ⟨sin_add_two_pi x.1, rfl⟩
  stream_periodic := fun _ _ x => ⟨congrArg Neg.neg (sin_add_two_pi x.1), rfl⟩
  deriv_time := fun t _ x => hasDerivAt_const t (sin x.1)
  continuous_dt := continuous_const.continuousOn
  initial_value := fun _ => rfl
  laplacian := by intros; simp [sinePsi, sineJet]
  equation := by intros; simp [sinePsi, sineJet]

/-- A continuous gauge, even one with a corner in time, preserves the solution. -/
theorem sine_gauge (T : ℝ) :
    Solves 0 T (fun x => sin x.1) sineJet
      (sinePsi.addGauge (fun t => |t - T / 2|)) (fun _ _ => 0) :=
  (sine_euler T).addGauge (continuous_id.sub continuous_const).abs.continuousOn

/-- The sine profile is genuinely outside the even cosine comparison class. -/
theorem sine_not_even : sineJet.value 0 (-(π / 2), 0) ≠ sineJet.value 0 (π / 2, 0) := by
  norm_num [sineJet, sin_neg, sin_pi_div_two]

/-- An unrelated initial condition cannot be substituted into this solution. -/
theorem sine_wrong_initial (T : ℝ) :
    ¬ Solves 0 T (fun _ => 0) sineJet sinePsi (fun _ _ => 0) := by
  intro h
  have hi := h.initial_value (π / 2, 0)
  norm_num [sineJet, sin_pi_div_two] at hi

/-- The comparison theorem also covers a collapsed interval without derivatives. -/
theorem zero_horizon (D D' : ℝ → ℝ) (h0 : D 0 = 0) :
    ∀ t ∈ Icc (0 : ℝ) 0, D t = 0 := by
  apply difference_eq_zero (D' := D') (C := 0) le_rfl
  · simpa only [Icc_self] using continuousOn_singleton D 0
  · simp
  · intro t ht
    have : t = 0 := le_antisymm ht.2 ht.1
    simp [this, h0]
  · exact h0
  · simp

/-- The viscous sign lemma applies to an actual periodic sine profile. -/
theorem sine_viscous_nonpos (ν : ℝ) (hν : 0 ≤ ν) :
    ν * (∫ x in (0 : ℝ)..2 * π, sin x * (-sin x)) ≤ 0 := by
  apply periodic_laplacian_nonpos (f' := cos) (by positivity) hν
    continuous_sin.continuousOn continuous_cos.continuousOn
    (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
    (continuous_sin.neg.intervalIntegrable _ _)
  · simp
  · simp

#print axioms notebook_field
#print axioms certified_field
#print axioms sine_euler
#print axioms zero_difference
end Gimle.Forseti.Tests.ClassicalVorticity
