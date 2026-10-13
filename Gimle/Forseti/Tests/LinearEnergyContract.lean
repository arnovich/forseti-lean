import Gimle.Forseti.Examples.HarmonicOscillator
import Gimle.Forseti.Examples.DampedOscillatorContract

/-! Coverage for the generic linear-energy contract construction: a second model
has the same interface shapes a renderer cites, and the axiom policy holds. -/

namespace Gimle.Forseti.Tests.LinearEnergyContract

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Forseti.Examples.HarmonicOscillator

/-! ### The harmonic oscillator's interface, in the renderer's shapes -/

example : (body.observations.get energyIndex).port.id = "obs-e" := by decide
example : evolution.states.map (·.initialId) = ["initial-x", "initial-v"] := by decide
example : evolution.axis.id = "time" := by decide
example : evolution.time.start = 0 := by simp [Gimle.Asgard.Model.Evolution.time, evolution]

example (input : Signal (0 + evolution.states.length))
    (admit : admitted input) (state : Signal evolution.states.length) :
    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state :=
  LinearEnergyContract.feedback_reads compiled input admit state

/-! ### Axioms -/

/--
info: 'Gimle.Forseti.LinearEnergyContract.Spec.energy_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms LinearEnergyContract.Spec.energy_contract

/--
info: 'Gimle.Forseti.LinearEnergyContract.Spec.refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms LinearEnergyContract.Spec.refuted

/--
info: 'Gimle.Forseti.Examples.HarmonicOscillator.energy_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms energy_contract

/--
info: 'Gimle.Forseti.Examples.HarmonicOscillator.half_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms half_refuted

/--
info: 'Gimle.Forseti.Examples.DampedOscillatorContract.energy_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Forseti.Examples.DampedOscillatorContract.energy_contract

end Gimle.Forseti.Tests.LinearEnergyContract
