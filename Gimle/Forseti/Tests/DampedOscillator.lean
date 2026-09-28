import Gimle.Forseti.Examples.DampedOscillatorContract

/-! Coverage for the damped oscillator's trajectory contract.

Pinned here: the stable IDs and shapes a downstream renderer cites (the energy
observation's port, the initial-wire IDs, the axis, and a reducible start time);
that the declared start is the only constraint on the initial wires; and the
axiom policy, asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.DampedOscillator

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Forseti.Examples.DampedOscillator
open Gimle.Forseti.Examples.DampedOscillatorContract

/-! ### The interface a renderer cites -/

example : (body.observations.get energyIndex).port.id = "obs-e" := by decide
example : body.observations.map (·.port.id) = ["obs-x", "obs-v", "obs-e"] := by decide
example : evolution.states.map (·.initialId) = ["initial-x", "initial-v"] := by decide
example : evolution.axis.id = "time" := by decide
example : evolution.time.start = 0 := by simp [Gimle.Asgard.Model.Evolution.time, evolution]
example : compiled.initial = ![1, 0] := initial_eq
example : compiled.outputs.circuit.run compiled.initial energyIndex = 2 := energy_at_initial
example : ∃ state, compiled.Realizes state := compiled_exists

example (input : Dynamics.Signal (0 + states)) (admit : admitted input)
    (state : Dynamics.Signal states) :
    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state :=
  feedback_reads input admit state

example : Contract observed evolution.time admitted
    (Always evolution.time fun o => 0 ≤ o energyIndex ∧ o energyIndex ≤ 2) :=
  energy_contract

/-- An admitted input only fixes its initial wires at the start: other values
after it are allowed, and the contract still yields an output. -/
example : ∃ output, observed.Rel evolution.time
    (Dynamics.signalAppend Model.noDrivers fun t =>
      if t = evolution.time.start then compiled.initial else fun _ => 100) output := by
  apply energy_contract.realizable
  refine ⟨trivial, ?_⟩
  simp

/-- A different initial state is not admitted. -/
example : ¬ admitted (Dynamics.signalAppend Model.noDrivers fun _ => fun _ => 0) := by
  intro h
  have := congrFun h.2 ⟨0, by decide⟩
  rw [initial_eq] at this
  change (0 : ℝ) = (![1, 0] : Point 2) 0 at this
  norm_num at this

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Examples.DampedOscillator.initial_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms initial_eq
/--
info: 'Gimle.Forseti.Examples.DampedOscillator.energy_at_initial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms energy_at_initial
/--
info: 'Gimle.Forseti.Examples.DampedOscillator.certificate_valid'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms certificate_valid
/--
info: 'Gimle.Forseti.Examples.DampedOscillator.compiled_exists'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms compiled_exists
/--
info: 'Gimle.Forseti.Examples.DampedOscillator.compiled_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms compiled_unique
/--
info: 'Gimle.Forseti.Examples.DampedOscillator.compiled_energy_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms compiled_energy_bound
/--
info: 'Gimle.Forseti.Examples.DampedOscillatorContract.feedback_reads'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms feedback_reads
/--
info: 'Gimle.Forseti.Examples.DampedOscillatorContract.energy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms energy_contract
/--
info: 'Gimle.Forseti.Examples.DampedOscillatorContract.one_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms one_refuted

end Gimle.Forseti.Tests.DampedOscillator
