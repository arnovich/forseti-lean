import Gimle.Forseti.LinearEnergyContract
import Gimle.Forseti.Examples.DampedOscillator

/-! The damped oscillator as one well-posed trajectory contract.

`Examples/DampedOscillator.lean` proves the pieces separately: a solution
exists, it is unique from the start, and the energy `E = 2x² + v²` stays in
`[0, 2]`. Here they become one `Contract` about the original compiled circuit —
the feedback loop asgard-lean compiled from the source equations, followed by
the observation circuit that computes `[x, v, E]` — for every input whose
initial wires start at the declared state `(1, 0)`, at every time `t ≥ 0`.

Every piece comes from `LinearEnergyContract`, the generic construction for
compiled linear models, applied to `DampedOscillator.spec`: the model's linear
view, its energy observation, `P = diag(2, 1)` and the certificate. The names
and statements are those gimle-forseti's trajectory registry cites, in the
shape of `ThreeStateContract`.

The damping `c = 3` and stiffness `k = 2` are compiled into `compiled`; the
input predicate binds only the (absent) drivers and the initial wires.
-/

namespace Gimle.Forseti.Examples.DampedOscillatorContract

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Forseti.Examples.DampedOscillator

/-- The compiled loop followed by the compiled observations `[x, v, E]`. -/
def observed := LinearEnergyContract.observed compiled

/-- The state dimension, as the model declares it. -/
abbrev states : Nat := evolution.states.length

/-- The energy the observation circuit computes from a state. -/
noncomputable def energy (state : Point states) : ℝ :=
  compiled.outputs.circuit.run state energyIndex

/-- Inputs: no drivers, and initial wires starting at the declared state. -/
def admitted : SignalPredicate (0 + states) := LinearEnergyContract.admitted compiled

/-- The loop reads an admitted input as the model's own initial state. -/
theorem feedback_reads (input : Signal (0 + states)) (admit : admitted input)
    (state : Signal states) :
    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state :=
  LinearEnergyContract.feedback_reads compiled input admit state

/-- The time domain is `t ≥ 0`. -/
theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t :=
  DampedOscillator.domain_iff t

/-- The loop alone: unique solutions whose energy stays in `[0, 2]`. -/
theorem loop_contract :
    Contract compiled.feedback evolution.time admitted
      (Always evolution.time fun state => 0 ≤ energy state ∧ energy state ≤ 2) :=
  spec.loop_contract 2 (le_of_eq energy_at_initial)

/-- **The observed energy never leaves `[0, 2]`.** For every admitted input the
compiled system has an output, all outputs agree for `t ≥ 0`, and every one of
them has `0 ≤ E ≤ 2` at every `t ≥ 0`. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 2) :=
  spec.energy_contract 2 (le_of_eq energy_at_initial)

/-- The declared input is admitted, so the contract is not vacuous. -/
theorem declared_input_admitted :
    admitted (signalAppend Model.noDrivers fun _ => compiled.initial) :=
  LinearEnergyContract.declared_input_admitted compiled

/-- **One is not a bound.** Some output of the admitted declared input has
`E = 2` at the start. The refutation comes from the admitted initial state, not
from a proof attempt that failed. -/
theorem one_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 1) :=
  spec.refuted 1 (by
    show (1 : ℝ) < compiled.outputs.circuit.run compiled.initial energyIndex
    rw [energy_at_initial]; norm_num)

end Gimle.Forseti.Examples.DampedOscillatorContract
