import Gimle.Forseti.Examples.AIFFiniteExistence

/-! Finite-horizon existence and coordinate-clamp regressions. -/
namespace Gimle.Forseti.Tests.AIFFiniteExistence
open Gimle.Forseti.Examples AIFFiniteExistence AIFPhysicalCoordinates

/-- The horizon `[0, 100]` has a physical solution for every eta in `[8, 12]`. -/
theorem horizon_100 (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) 12) :
    ∃ state : ℝ → Fin 4 → ℝ, state 0 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 100, ∀ i,
        HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
          (Set.Icc (0 : ℝ) 100) t := by
  exact finite_solution eta (by linarith [heta.1]) 100

/-- Eta zero and a zero-length horizon are admitted by the existence interface. -/
theorem zero_horizon :
    ∃ state : ℝ → Fin 4 → ℝ, state 0 = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 0, ∀ i,
        HasDerivWithinAt (fun s => state s i) (physicalField 0 (state t) i)
          (Set.Icc (0 : ℝ) 0) t := by
  simpa only [Nat.cast_zero] using! finite_solution 0 le_rfl 0

/-- Clamping has the correct original species order and both saturation directions. -/
theorem clamp_values :
    (coordinateBox 4 (by norm_num)).clamp ![-1,2,4,7] = ![0,2,4,4] := by
  ext i
  fin_cases i <;> norm_num [clamp_apply]

/-- The auxiliary field really differs outside its box; unclamping is necessary. -/
theorem outside_field_differs :
    (coordinateBox 1 (by norm_num)).clamped (physicalField 8) ![0,0,2,0] 0 ≠
      physicalField 8 ![0,0,2,0] 0 := by
  change (coordinateBox 1 (by norm_num)).clamp ![0,0,2,0] 2 -
    (coordinateBox 1 (by norm_num)).clamp ![0,0,2,0] 0 ≠ (2 : ℝ) - 0
  norm_num [clamp_apply, Matrix.cons_val_two]

/-- info: 'Gimle.Forseti.Tests.AIFFiniteExistence.outside_field_differs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms outside_field_differs
/-- info: 'Gimle.Forseti.Tests.AIFFiniteExistence.horizon_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms horizon_100
/-- info: 'Gimle.Forseti.Tests.AIFFiniteExistence.zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_horizon
/-- info: 'Gimle.Forseti.Tests.AIFFiniteExistence.clamp_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms clamp_values
end Gimle.Forseti.Tests.AIFFiniteExistence
