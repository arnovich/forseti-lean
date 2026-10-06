import Gimle.Forseti.ClassicalVorticity.MildComparison
import Gimle.Asgard.Examples.MildBand

/-! The NavierStokes notebook's bounds for every independent classical solution
of its periodic initial-value problem, with velocity `(-ψ_y, ψ_x)`. -/
namespace Gimle.Forseti.Examples.ClassicalNavierStokes
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild
open Gimle.Forseti.ClassicalVorticity
open Gimle.Asgard.Examples

/-- For viscosity `1/10` and the three-mode notebook start, every classical
comparison solution agrees with the constructed field through time `1/5760`. -/
theorem unique {ω ψ : SpatialJet} {dt : Field}
    (h : Solves (1 / 10) (1 / 5760) (RealPoly.field (realEmbed EulerThreeMode.ω₀)) ω ψ dt) :
    ∀ t ∈ Set.Icc 0 (1 / 5760), ∀ p,
      ω.value t p = analyticField (1 / 10) (MildBand.ω (1 / 10)) t p := by
  have hm := of_mild MildBand.classical
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hm
  exact h.vorticity_unique hm (by norm_num) (by norm_num)

/-- The certified physical band applies to every classical comparison solution. -/
theorem band {ω ψ : SpatialJet} {dt : Field}
    (h : Solves (1 / 10) (1 / 5760) (RealPoly.field (realEmbed EulerThreeMode.ω₀)) ω ψ dt) :
    ∀ t ∈ Set.Icc 0 (1 / 5760), ∀ p, |ω.value t p| ≤ 3519 / 1000 := by
  intro t ht p
  rw [unique h t ht p]
  exact MildBand.band t ht p

/-- Four interaction terms approximate every classical comparison solution,
with the same certified error and the same closed interval. -/
theorem truncation {ω ψ : SpatialJet} {dt : Field}
    (h : Solves (1 / 10) (1 / 5760) (RealPoly.field (realEmbed EulerThreeMode.ω₀)) ω ψ dt) :
    ∀ t ∈ Set.Icc 0 (1 / 5760), ∀ p,
      |ω.value t p - windowField (1 / 10) 4 (MildBand.ω (1 / 10)) t p| ≤ 21 / 1024 := by
  intro t ht p
  rw [unique h t ht p]
  exact (MildBand.truncation t ht p).2

#print axioms unique
#print axioms band
#print axioms truncation
end Gimle.Forseti.Examples.ClassicalNavierStokes
