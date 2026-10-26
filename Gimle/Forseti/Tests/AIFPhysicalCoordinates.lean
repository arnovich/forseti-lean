module

public import Gimle.Forseti.Examples.AIFPhysicalCoordinates

/-! Regressions for the physical state order and parameter-dependent scale. -/

@[expose] public section

namespace Gimle.Forseti.Tests.AIFPhysicalCoordinates
open Gimle.Forseti.Examples AIFPhysicalCoordinates

example (eta : ℝ) : physicalField eta 0 = ![0,0,2,0] := by
  ext i
  fin_cases i <;> simp [physicalField]

example (eta : ℝ) : shift eta 0 = ![-2,-2,-2,-1] := shift_zero eta

example (eta : ℝ) (h : eta ∈ Set.Icc (8 : ℝ) 12) (x : Fin 4 → ℝ) :
    unshift eta (shift eta x) = x :=
  unshift_shift eta (by linarith [h.1]) x

/-- Omitting eta from the fourth velocity is detectably wrong inside the given range. -/
theorem unscaled_velocity_rejected :
    physicalField 8 ![0,1,0,0] 3 ≠
      AIFDriftModel.field 8 (shift 8 ![0,1,0,0]) 3 := by
  change (1 : ℝ) - 8*0*0 ≠
    8*((1-2)-(0-2)-(2+(0-2))*(8*0-1))
  norm_num

/-- The inverse cannot recover a fourth coordinate when eta is zero. -/
theorem zero_parameter_loses_state :
    unshift 0 (shift 0 ![0,0,0,1]) ≠ ![0,0,0,1] := by
  intro h
  have := congrFun h 3
  norm_num [unshift, shift, Matrix.cons_val_three] at this

-- The physical output is coordinate one, not controller coordinate two.
example (eta : ℝ) : (shift eta ![0,16/5,10,0]) 1 = 6/5 := by
  norm_num [shift]

/-- info: 'Gimle.Forseti.Tests.AIFPhysicalCoordinates.unscaled_velocity_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unscaled_velocity_rejected
/-- info: 'Gimle.Forseti.Tests.AIFPhysicalCoordinates.zero_parameter_loses_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_parameter_loses_state
end Gimle.Forseti.Tests.AIFPhysicalCoordinates
