import Gimle.Forseti.ClassicalVorticity.Uniqueness
import Gimle.Forseti.Tests.ClassicalVorticity

/-! Regression proofs for classical PDE uniqueness, including the certified
notebook field, odd data and stream-function gauge freedom. -/
namespace Gimle.Forseti.Tests.ClassicalUniqueness
open Gimle.Forseti.ClassicalVorticity Set Real
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild

/-- Every comparison solution for the notebook's data equals its constructed field. -/
theorem notebook_unique {ω ψ : SpatialJet} {dt : Field}
    (h : Solves (1 / 10) (1 / 5760)
      (RealPoly.field
        (realEmbed Gimle.Asgard.Examples.EulerThreeMode.ω₀)) ω ψ dt) :
    ∀ t ∈ Icc 0 (1 / 5760), ∀ p,
      ω.value t p =
        (mildJet (1 / 10) (Gimle.Asgard.Examples.MildBand.ω (1 / 10))).value t p :=
  h.vorticity_unique ClassicalVorticity.notebook_field (by norm_num) (by norm_num)

/-- Zero viscosity and odd initial data are inside the comparison theorem. -/
theorem sine_unique {T : ℝ} (hT : 0 ≤ T) {ω ψ : SpatialJet} {dt : Field}
    (h : Solves 0 T (fun p => sin p.1) ω ψ dt) :
    ∀ t ∈ Icc 0 T, ∀ p, ω.value t p = sin p.1 :=
  h.vorticity_unique (ClassicalVorticity.sine_euler T) le_rfl hT

/-- The conclusion covers arbitrary points outside the fundamental square. -/
theorem sine_outside_cell {T : ℝ} (hT : 0 ≤ T) {ω ψ : SpatialJet} {dt : Field}
    (h : Solves 0 T (fun p => sin p.1) ω ψ dt) :
    ω.value T (-17 * π, 23 * π) = sin (-17 * π) :=
  sine_unique hT h T ⟨hT, le_rfl⟩ _

/-- A collapsed time interval requires no interior derivative. -/
theorem zero_horizon_unique {ν : ℝ} (hν : 0 ≤ ν) {initial : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν 0 initial ω₁ ψ₁ dt₁) (h₂ : Solves ν 0 initial ω₂ ψ₂ dt₂) (p : ℝ × ℝ) :
    ω₁.value 0 p = ω₂.value 0 p :=
  h₁.vorticity_unique h₂ hν le_rfl 0 ⟨le_rfl, le_rfl⟩ p

/-- A continuous gauge with a time corner is permitted in the uniqueness theorem. -/
theorem gauge_unique {T : ℝ} (hT : 0 ≤ T) {ω ψ : SpatialJet} {dt : Field}
    (h : Solves 0 T (fun p => sin p.1) ω ψ dt) :
    ∀ t ∈ Icc 0 T, ∀ p, ω.value t p = sin p.1 :=
  h.vorticity_unique
    ((ClassicalVorticity.sine_euler T).addGauge
      (c := fun t => |t - T / 2|) (continuous_id.sub continuous_const).abs.continuousOn)
    le_rfl hT

/-- Velocity comparison also permits the stream-function gauge with a time corner. -/
theorem gauge_velocity_unique {T : ℝ} (hT : 0 ≤ T) {ω ψ : SpatialJet} {dt : Field}
    (h : Solves 0 T (fun p => sin p.1) ω ψ dt) :
    ∀ t ∈ Icc 0 T, ∀ p,
      (-ψ.dy t p, ψ.dx t p) = (0, -cos p.1) := by
  simpa only [SpatialJet.addGauge, ClassicalVorticity.sinePsi, neg_zero] using h.velocity_unique
    ((ClassicalVorticity.sine_euler T).addGauge
      (c := fun t => |t - T / 2|) (continuous_id.sub continuous_const).abs.continuousOn)
    le_rfl hT

#print axioms notebook_unique
#print axioms sine_unique
#print axioms gauge_velocity_unique
end Gimle.Forseti.Tests.ClassicalUniqueness
