import Gimle.Forseti.Examples.EquationWorkflow

namespace Gimle.Forseti.Tests.EquationWorkflow
open Gimle.Asgard.Examples.EquationModels
open Gimle.Forseti.EquationWorkflow

example : ¬ ExactHoare inputBox energy (⟨fun y => y 0 ≤ 3⟩ : Predicate 1) := by
  intro h
  have impossible := energySharp 3 h
  norm_num at impossible

/-- The oscillator proof speaks about this compiled feedback, not an unrelated field. -/
example (state : Gimle.Asgard.Dynamics.Signal 2) (h : Realizes state) :
    energy.run (state 1) 0 ≤ 2 := (oscillatorEnergyBound state h 1 (by norm_num)).2

#print axioms oscillatorEnergyBound
end Gimle.Forseti.Tests.EquationWorkflow
