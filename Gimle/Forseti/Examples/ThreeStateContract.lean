import Gimle.Forseti.Trajectory
import Gimle.Forseti.Examples.ThreeState

/-! The three-state model as one well-posed trajectory contract.

`Examples/ThreeState.lean` proves the pieces separately: a solution exists, it
is unique from the start, and the energy `V` stays in `[0, 6]`. Here they
become one `Contract` about the original compiled circuit — the feedback loop
Asgard compiled from the source equations, followed by the observation circuit
that computes `V` — for every input whose initial wires start at the declared
state `(1, 2, −1)`, at every time `t ≥ 2`.

The contract is assembled with the general rules: a contract for the loop,
`Contract.lift` for the observation circuit, and `Contract.compose` with
`DomainRespecting.lift`, since the loop's output is unique only from `t = 2` on.

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
def observed :=
  Dynamics.Circuit.compose model.feedback (.lift model.outputs.circuit)

/-- The state dimension, as the model declares it. -/
abbrev states : Nat := evolution.states.length

/-- The energy the observation circuit computes from a state. -/
noncomputable def energy (state : Point states) : ℝ :=
  model.outputs.circuit.run state energyIndex

/-- Inputs: no drivers, and initial wires starting at the declared state. -/
def admitted : SignalPredicate (0 + states) :=
  Initialized evolution.time (fun _ => True) (· = model.initial)

/-- The loop reads an admitted input as the model's own initial state. -/
theorem feedback_reads (input : Signal (0 + states)) (admit : admitted input)
    (state : Signal states) :
    model.feedback.Rel evolution.time input state ↔ model.Realizes state := by
  have noDrivers : signalLeft input = Model.noDrivers := by
    funext t i; exact Fin.elim0 i
  unfold Model.ContinuousModel.Realizes Model.ContinuousModel.feedback
  rw [close_rel_reads_start, noDrivers, admit.2]

/-- The time domain is `t ≥ 2`. -/
theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 2 ≤ t := by
  simp [TimeDomain.domain, Model.Evolution.time, evolution]

/-- The loop alone: unique solutions whose energy stays in `[0, 6]`. -/
theorem loop_contract :
    Contract model.feedback evolution.time admitted
      (Always evolution.time fun state => 0 ≤ energy state ∧ energy state ≤ 6) where
  realizable input admit := by
    obtain ⟨state, realized⟩ := compiled_exists
    exact ⟨state, (feedback_reads input admit state).mpr realized⟩
  unique input admit a b ha hb :=
    compiled_unique ((feedback_reads input admit a).mp ha)
      ((feedback_reads input admit b).mp hb)
  holds input admit state related t within :=
    compiled_energy_bound state ((feedback_reads input admit state).mp related) t
      ((domain_iff t).mp within)

/-- **The observed energy never leaves `[0, 6]`.** For every admitted input the
compiled system has an output, all outputs agree for `t ≥ 2`, and every one of
them has `0 ≤ V ≤ 6` at every `t ≥ 2`. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 6) :=
  Contract.compose loop_contract
    (Contract.lift model.outputs.circuit evolution.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

/-- The declared input is admitted, so the contract is not vacuous. -/
theorem declared_input_admitted :
    admitted (signalAppend Model.noDrivers fun _ => model.initial) := by
  refine ⟨trivial, ?_⟩
  simp

/-- **Five is not a bound.** Some output of the admitted declared input has
`V = 6` at the start. The refutation comes from the admitted initial state, not
from a proof attempt that failed. -/
theorem five_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 5) := by
  intro claim
  obtain ⟨state, realized⟩ := compiled_exists
  have start : state evolution.time.start = model.initial := by
    unfold Model.ContinuousModel.Realizes Model.ContinuousModel.feedback at realized
    exact ((close_rel _ _ _ _ _ _).mp realized).2.1
  have bounded := claim _ declared_input_admitted _
    ⟨state, (feedback_reads _ declared_input_admitted state).mpr realized, rfl⟩
    evolution.time.start (by simp [TimeDomain.domain])
  simp only at bounded
  rw [start] at bounded
  exact initial_not_bounded_by_five bounded

#print axioms energy_contract
#print axioms five_refuted

end Gimle.Forseti.Examples.ThreeStateContract
