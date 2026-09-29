import Gimle.Forseti.LinearEnergyContract
import Gimle.Forseti.Examples.ThreeState

/-! The three-state model as one well-posed trajectory contract.

`Examples/ThreeState.lean` proves the pieces separately: a solution exists, it
is unique from the start, and the energy `V` stays in `[0, 6]`. Here they
become one `Contract` about the original compiled circuit — the feedback loop
Asgard compiled from the source equations, followed by the observation circuit
that computes `V` — for every input whose initial wires start at the declared
state `(1, 2, −1)`, at every time `t ≥ 2`.

Every piece comes from `LinearEnergyContract`, the generic construction for
compiled linear models, applied to `ThreeState.spec`: the model's linear view,
its energy observation `V`, `P = I` and the certificate for its dissipation
`diag(2/3, 1, 4)`. The names and statements are those gimle-forseti's trajectory
registry cites; `Tests/ThreeState.lean` pins them.

The damping parameters `(1/3, 1/2, 2)` are compiled into `model`; the input
predicate binds only the (absent) drivers and the initial wires.
-/

namespace Gimle.Forseti.Examples.ThreeStateContract

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Examples.ThreeState
open Gimle.Forseti.Examples.ThreeState

/-- The compiled loop followed by the compiled observations `[z, x, y, V]`. -/
def observed := LinearEnergyContract.observed model

/-- The state dimension, as the model declares it. -/
abbrev states : Nat := evolution.states.length

/-- The energy the observation circuit computes from a state. -/
noncomputable def energy (state : Point states) : ℝ :=
  model.outputs.circuit.run state energyIndex

/-- Inputs: no drivers, and initial wires starting at the declared state. -/
def admitted : SignalPredicate (0 + states) := LinearEnergyContract.admitted model

/-- The loop reads an admitted input as the model's own initial state. -/
theorem feedback_reads (input : Signal (0 + states)) (admit : admitted input)
    (state : Signal states) :
    model.feedback.Rel evolution.time input state ↔ model.Realizes state :=
  LinearEnergyContract.feedback_reads model input admit state

/-- The time domain is `t ≥ 2`. -/
theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 2 ≤ t :=
  ThreeState.domain_iff t

/-- The loop alone: unique solutions whose energy stays in `[0, 6]`. -/
theorem loop_contract :
    Contract model.feedback evolution.time admitted
      (Always evolution.time fun state => 0 ≤ energy state ∧ energy state ≤ 6) :=
  spec.loop_contract 6 (le_of_eq energy_at_initial)

/-- **The observed energy never leaves `[0, 6]`.** For every admitted input the
compiled system has an output, all outputs agree for `t ≥ 2`, and every one of
them has `0 ≤ V ≤ 6` at every `t ≥ 2`. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 6) :=
  spec.energy_contract 6 (le_of_eq energy_at_initial)

/-- The declared input is admitted, so the contract is not vacuous. -/
theorem declared_input_admitted :
    admitted (signalAppend Model.noDrivers fun _ => model.initial) :=
  LinearEnergyContract.declared_input_admitted model

/-- **Five is not a bound.** Some output of the admitted declared input has
`V = 6` at the start. The refutation comes from the admitted initial state, not
from a proof attempt that failed. -/
theorem five_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 5) :=
  spec.refuted 5 (by
    show (5 : ℝ) < model.outputs.circuit.run model.initial energyIndex
    rw [energy_at_initial]; norm_num)

#print axioms energy_contract
#print axioms five_refuted

end Gimle.Forseti.Examples.ThreeStateContract
