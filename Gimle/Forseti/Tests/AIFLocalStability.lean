module

public import Gimle.Forseti.Examples.AIFLocalStability

/-! Regressions for local continuation, parameter endpoints and entry assumptions. -/

@[expose] public section

namespace Gimle.Forseti.Tests.AIFLocalStability
open Gimle.Forseti.Examples AIFLocalStability AIFPhysicalCoordinates

theorem parameter_endpoints (a b c d : ℝ) (h : energy a b c d ≤ 1/100) :
    rate 8 c a b c d ≤ -(1/25)*normSq a b c d ∧
    rate 12 c a b c d ≤ -(1/25)*normSq a b c d := by
  exact ⟨(local_bounds 8 a b c d (by norm_num) (by norm_num) h).2.2.2,
    (local_bounds 12 a b c d (by norm_num) (by norm_num) h).2.2.2⟩

theorem equilibrium_energy : energy 0 0 0 0 = 0 := by norm_num [energy]

/-- The zero physical initial state does not already lie in the local region. -/
theorem zero_start_outside (eta : ℝ) :
    1/100 < energy (shift eta 0 0) (shift eta 0 1)
      (shift eta 0 2) (shift eta 0 3) := by
  rw [shift_zero]
  norm_num [energy, Matrix.cons_val_two, Matrix.cons_val_three]

/-- A concrete horizon retains an explicit, nontrivial entry premise at time thirty. -/
theorem output_at_100 (eta : ℝ) (heta : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : ℝ → Fin 4 → ℝ)
    (derivative : ∀ t ∈ Set.Icc (30 : ℝ) 100, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Icc (30 : ℝ) 100) t)
    (entry : energy (shift eta (state 30) 0) (shift eta (state 30) 1)
      (shift eta (state 30) 2) (shift eta (state 30) 3) ≤ 1/100) :
    state 100 1 ≤ 5/2 :=
  physical_output_bound eta heta state 30 100 derivative entry 100 (by norm_num)

/-- info: 'Gimle.Forseti.Tests.AIFLocalStability.parameter_endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms parameter_endpoints
/-- info: 'Gimle.Forseti.Tests.AIFLocalStability.equilibrium_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equilibrium_energy
/-- info: 'Gimle.Forseti.Tests.AIFLocalStability.zero_start_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_start_outside
/-- info: 'Gimle.Forseti.Tests.AIFLocalStability.output_at_100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms output_at_100
end Gimle.Forseti.Tests.AIFLocalStability
