import Gimle.Forseti.Examples.AIFCircuitBinding

/-! The circuit binding's realization relation needs both the zero start and the
ODE, the observation reads `x₂`, and the binding uses only the standard axioms. -/
namespace Gimle.Forseti.Tests.AIFCircuitBinding
open Gimle.Asgard Gimle.Forseti.Examples

/-- The constant equilibrium solves the ODE but does not start at zero, so it is
not a realization. -/
theorem equilibrium_not_realization :
    ¬ Gimle.Asgard.Examples.AIF.Realizes 1 (fun _ => ![2, 2, 2, 1]) := by
  intro h
  have := congrFun ((AIFCircuitBinding.realizes_iff_physical 1 _).mp h).1 0
  norm_num at this

/-- The zero signal starts at zero but violates the `z₁` equation, so it is not a
realization either. -/
theorem zero_signal_not_realization (eta : ℝ) :
    ¬ Gimle.Asgard.Examples.AIF.Realizes eta (fun _ => 0) := by
  intro h
  have hd := ((AIFCircuitBinding.realizes_iff_physical eta _).mp h).2 0 Set.self_mem_Ici 2
  have hc : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 (Set.Ici 0) 0 :=
    hasDerivWithinAt_const _ _ _
  have := (uniqueDiffOn_Ici (0 : ℝ) 0 Set.self_mem_Ici).eq_deriv _ hd hc
  norm_num [AIFPhysicalCoordinates.physicalField, Matrix.cons_val_two] at this

/-- The observation reads `x₂`, not another species. -/
example : Gimle.Asgard.Examples.AIF.output.run ![0, 16/5, 7, 7] 0 ≤ 16/5 ∧
    ¬ Gimle.Asgard.Examples.AIF.output.run ![0, 17/5, 0, 0] 0 ≤ 16/5 := by
  simp only [Gimle.Asgard.Examples.AIF.output_correct]
  norm_num

/--
info: 'Gimle.Forseti.Tests.AIFCircuitBinding.equilibrium_not_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms equilibrium_not_realization

/--
info: 'Gimle.Forseti.Tests.AIFCircuitBinding.zero_signal_not_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms zero_signal_not_realization

/-- info: 'Gimle.Forseti.Examples.AIFCircuitBinding.exists_realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AIFCircuitBinding.exists_realization

/-- info: 'Gimle.Forseti.Examples.AIFCircuitBinding.realization_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AIFCircuitBinding.realization_unique

/--
info: 'Gimle.Forseti.Examples.AIFCircuitBinding.realization_nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AIFCircuitBinding.realization_nonnegative

/--
info: 'Gimle.Forseti.Examples.AIFCircuitBinding.compiled_output_bound_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AIFCircuitBinding.compiled_output_bound_iff

end Gimle.Forseti.Tests.AIFCircuitBinding
