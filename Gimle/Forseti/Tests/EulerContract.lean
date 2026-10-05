import Gimle.Forseti.Examples.EulerContract

/-! Euler is now a total contract over the actual Fourier feedback circuit. -/
namespace Gimle.Forseti.Tests.EulerContract

open Gimle.Asgard.Streams Gimle.Forseti.Fourier
open Gimle.Forseti.Examples.EulerContract

example : Contract circuit admitted certified := euler_contract

/-- Initial data alone suffice, with no supplied candidate solution. -/
example : ∃ y, circuit.Rel ![Gimle.Asgard.Examples.EulerThreeMode.start] y ∧ certified y :=
  euler_contract.exists_safe _ rfl

/-- A false postcondition cannot be established vacuously through the loop. -/
example : ¬ Contract circuit admitted (fun _ => False) := by
  intro h
  obtain ⟨y, _, impossible⟩ := h.exists_safe ![Gimle.Asgard.Examples.EulerThreeMode.start] rfl
  exact impossible

/-- The formal interface also covers EGF and positive viscosity, without
claiming analytic convergence of the viscous time series. -/
example (b : TrigStream) :
    Contract (NS.vorticityCircuit .egf (1 / 10))
      (fun x => x 0 0 = b 0) (fun y => y = ![NS.stream .egf (1 / 10) b]) :=
  solution_contract _ _ b

/--
info: 'Gimle.Forseti.Examples.EulerContract.euler_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.EulerContract.euler_contract

end Gimle.Forseti.Tests.EulerContract
