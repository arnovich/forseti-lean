import Gimle.Forseti.ColeHopf

/-! Positive heat profiles yield genuine periodic Burgers solutions. -/
namespace Gimle.Forseti.Tests.ColeHopf
open Set Real
open Gimle.Forseti.ColeHopf Gimle.Forseti.ResidualPDE
open Gimle.Forseti.ClassicalVorticity

/-- The constant positive heat profile reconstructs the zero Burgers field. -/
def constantProfile : HeatJet where
  value := fun _ _ => 1
  dx := fun _ _ => 0
  dxx := fun _ _ => 0
  dxxx := fun _ _ => 0

theorem constant_valid (ν T : ℝ) : constantProfile.Valid ν T where
  deriv_x := fun _ _ _ => hasDerivAt_const _ _
  deriv_xx := fun _ _ _ => hasDerivAt_const _ _
  deriv_xxx := fun _ _ _ => hasDerivAt_const _ _
  deriv_time := by intro t ht x; simpa [constantProfile] using hasDerivAt_const t (1 : ℝ)
  deriv_time_dx := by intro t ht x; simpa [constantProfile] using hasDerivAt_const t (0 : ℝ)
  continuous_value := continuousOn_const
  continuous_dx := continuousOn_const
  continuous_dxx := continuousOn_const
  continuous_dxxx := continuousOn_const
  positive := by intros; norm_num [constantProfile]
  periodic_value := fun _ _ _ => rfl
  periodic_dx := fun _ _ _ => rfl

theorem constant_burgers (ν T : ℝ) :
    Burgers ν T (fun _ _ => 0) (fun _ _ => 0)
      (constantProfile.burgersJet ν) (constantProfile.burgersDt ν) :=
  (constant_valid ν T).burgers

/-- A denominator which vanishes is outside the admitted heat profiles. -/
def zeroProfile : HeatJet where
  value := fun _ _ => 0
  dx := fun _ _ => 0
  dxx := fun _ _ => 0
  dxxx := fun _ _ => 0

theorem zero_profile_rejected : ¬ zeroProfile.Valid 1 1 := by
  intro h
  have := h.positive 0 (by norm_num) 0
  norm_num [zeroProfile] at this

/-- Positivity alone does not turn an arbitrary profile into a heat solution. -/
def wrongHeatProfile : HeatJet where
  value := fun t _ => 1 + t
  dx := fun _ _ => 0
  dxx := fun _ _ => 0
  dxxx := fun _ _ => 0

theorem wrong_heat_equation_rejected : ¬ wrongHeatProfile.Valid 1 1 := by
  intro h
  have hd := h.deriv_time (1/2) (by constructor <;> norm_num) 0
  have actual : HasDerivAt (fun t : ℝ => 1 + t) 1 (1/2) :=
    (hasDerivAt_id (1/2 : ℝ)).const_add 1
  have he := hd.unique actual
  norm_num [wrongHeatProfile] at he

/-- The one-sided bound is zero for a constant profile. -/
theorem constant_slope : -(constantProfile.burgersJet 1).dx 0 (0,0) ≤ 0 := by
  have h := constantProfile.slope_le (ν := 1) (m := 1) (B := 0) (t := 0) (x := 0)
    (by norm_num) (by norm_num) (by norm_num [constantProfile])
    (by norm_num [constantProfile])
  simpa using h

/-- Every independent classical solution with zero start agrees with the explicit one. -/
theorem zero_solution_unique {u : SpatialJet} {ut : Field}
    (hu : Burgers 1 1 (fun _ _ => 0) (fun _ _ => 0) u ut)
    (hi : ∀ p, u.value 0 p = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ p, u.value t p = 0 := by
  have h := burgers_unique_of_slope_bound (M := 0) hu (constant_valid 1 1).burgers
    (by norm_num) (by norm_num)
    (by intro p; simpa [HeatJet.burgersJet, constantProfile] using hi p)
    (by intros; norm_num [HeatJet.burgersJet, constantProfile])
  simpa [HeatJet.burgersJet, constantProfile] using h

#print axioms constant_burgers
#print axioms zero_profile_rejected
#print axioms wrong_heat_equation_rejected
#print axioms constant_slope
#print axioms zero_solution_unique
end Gimle.Forseti.Tests.ColeHopf
