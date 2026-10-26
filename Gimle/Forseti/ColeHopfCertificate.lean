module

public import Gimle.Forseti.ColeHopfFinite

/-!
# Exact budgets for finite Burgers compression

The data contains the original and candidate coefficients, frequency map,
viscosity, closed time horizon and normalized spatial L2 tolerance. Validity is
an exact arithmetic proposition about that data. It does not trust a proposed
error number or a searcher's acceptance flag. Soundness follows the actual
unforced Burgers equations through the shared residual comparison theorem.

The rational exponential cap is deliberately sufficient, not optimal. Its
domain is checked explicitly. Candidate selection and production-checker
enrollment are outside this module.
-/

@[expose] public section

namespace Gimle.Forseti.ColeHopfCertificate
open Set Real
open Gimle.Forseti.ClassicalVorticity Gimle.Forseti.ResidualPDE

/-- All inputs determining the mathematical accuracy request. -/
structure Data (n : ℕ) where
  frequencies : Fin n → ℕ
  original : Fin n → ℝ
  retained : Fin n → ℝ
  viscosity : ℝ
  horizon : ℝ
  tolerance : ℝ

/-- The original nonlinear PDE field, reconstructed from the full heat profile. -/
noncomputable def Data.source {n : ℕ} (d : Data n) : SpatialJet :=
  (ColeHopfFinite.profile d.viscosity d.frequencies d.original).burgersJet d.viscosity

/-- The proposed reduced field, reconstructed with the same interpretation. -/
noncomputable def Data.candidate {n : ℕ} (d : Data n) : SpatialJet :=
  (ColeHopfFinite.profile d.viscosity d.frequencies d.retained).burgersJet d.viscosity

/-- The actual original field's time derivative. -/
noncomputable def Data.sourceDt {n : ℕ} (d : Data n) : Field :=
  (ColeHopfFinite.profile d.viscosity d.frequencies d.original).burgersDt d.viscosity

/-- Recomputed guards and accuracy budget, distinct from proposed data. -/
structure Data.Valid {n : ℕ} (d : Data n) : Prop where
  viscosity_nonneg : 0 ≤ d.viscosity
  horizon_nonneg : 0 ≤ d.horizon
  tolerance_nonneg : 0 ≤ d.tolerance
  original_safe : ColeHopfFinite.moment d.frequencies d.original 0 < 1
  candidate_safe : ColeHopfFinite.moment d.frequencies d.retained 0 < 1
  growth_nonneg : 0 ≤ ColeHopfFinite.growth d.viscosity d.frequencies d.retained + 1
  cap_domain :
    (ColeHopfFinite.growth d.viscosity d.frequencies d.retained + 1) * d.horizon < 1
  budget :
    ColeHopfFinite.initialRadius d.viscosity d.frequencies d.original d.retained ^ 2 /
      (1 - (ColeHopfFinite.growth d.viscosity d.frequencies d.retained + 1) * d.horizon)
      ≤ d.tolerance ^ 2

/-- The scalar exponential is bounded throughout the requested closed interval. -/
theorem affine_zero_residual_cap {δ g T t : ℝ} (hδ : 0 ≤ δ) (hg : 0 ≤ g)
    (hT : 0 ≤ T) (hcap : g * T < 1) (ht : t ∈ Icc 0 T) :
    gronwallBound δ g 0 t ≤ δ / (1 - g * T) := by
  rw [gronwallBound_ε0]
  have he := exp_bound_div_one_sub_of_interval (mul_nonneg hg hT) hcap
  have hmono : exp (g * t) ≤ exp (g * T) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hg)
  calc
    δ * exp (g * t) ≤ δ * (1 / (1 - g * T)) :=
      mul_le_mul_of_nonneg_left (hmono.trans he) hδ
    _ = δ / (1 - g * T) := by ring

/-- Valid source data supplies a real PDE solution, establishing nonvacuity. -/
theorem Data.source_solves {n : ℕ} (d : Data n) (h : d.Valid) :
    Burgers d.viscosity d.horizon (fun _ _ => 0) (fun _ _ => 0)
      d.source d.sourceDt :=
  (ColeHopfFinite.valid d.viscosity d.horizon d.frequencies d.original
    h.viscosity_nonneg h.original_safe).burgers

/-- Accuracy for any admitted independent classical solution with the fixed start. -/
theorem Data.sound_against {n : ℕ} (d : Data n) (h : d.Valid)
    {u : SpatialJet} {ut : Field}
    (hu : Burgers d.viscosity d.horizon (fun _ _ => 0) (fun _ _ => 0) u ut)
    (hinit : ∀ p, u.value 0 p = d.source.value 0 p) :
    ∀ t ∈ Icc (0 : ℝ) d.horizon, energy u d.candidate t ≤ d.tolerance ^ 2 := by
  intro t ht
  have he := ColeHopfFinite.comparison_against d.viscosity d.horizon d.frequencies
    d.original d.retained h.viscosity_nonneg h.original_safe h.candidate_safe
    h.horizon_nonneg hu hinit t ht
  exact he.trans ((affine_zero_residual_cap (sq_nonneg _) h.growth_nonneg
    h.horizon_nonneg h.cap_domain ht).trans h.budget)

/-- A closed error statement for the explicit original and reduced fields. -/
theorem Data.sound {n : ℕ} (d : Data n) (h : d.Valid) :
    ∀ t ∈ Icc (0 : ℝ) d.horizon,
      energy d.source d.candidate t ≤ d.tolerance ^ 2 :=
  d.sound_against h (d.source_solves h) (fun _ => rfl)

/-- The squared certificate also bounds the normalized spatial L2 norm itself. -/
theorem Data.l2_sound {n : ℕ} (d : Data n) (h : d.Valid)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) d.horizon) :
    sqrt (energy d.source d.candidate t) ≤ d.tolerance := by
  exact (sqrt_le_iff).mpr ⟨h.tolerance_nonneg, d.sound h t ht⟩

#print axioms affine_zero_residual_cap
#print axioms Data.source_solves
#print axioms Data.sound_against
#print axioms Data.sound
#print axioms Data.l2_sound
end Gimle.Forseti.ColeHopfCertificate
