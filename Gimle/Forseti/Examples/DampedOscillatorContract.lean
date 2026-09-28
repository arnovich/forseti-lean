import Gimle.Forseti.Trajectory
import Gimle.Forseti.Examples.DampedOscillator

/-! The damped oscillator as one well-posed trajectory contract.

`Examples/DampedOscillator.lean` proves the pieces separately: a solution
exists, it is unique from the start, and the energy `E = 2x² + v²` stays in
`[0, 2]`. Here they become one `Contract` about the original compiled circuit —
the feedback loop asgard-lean compiled from the source equations, followed by
the observation circuit that computes `[x, v, E]` — for every input whose
initial wires start at the declared state `(1, 0)`, at every time `t ≥ 0`.

The contract is assembled with the general rules, exactly as for the
three-state model: a contract for the loop, `Contract.lift` for the observation
circuit, and `Contract.compose` with `DomainRespecting.lift`, since the loop's
output is unique only from `t = 0` on.

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
def observed :=
  Dynamics.Circuit.compose compiled.feedback (.lift compiled.outputs.circuit)

/-- The state dimension, as the model declares it. -/
abbrev states : Nat := evolution.states.length

/-- The energy the observation circuit computes from a state. -/
noncomputable def energy (state : Point states) : ℝ :=
  compiled.outputs.circuit.run state energyIndex

/-- Inputs: no drivers, and initial wires starting at the declared state. -/
def admitted : SignalPredicate (0 + states) :=
  Initialized evolution.time (fun _ => True) (· = compiled.initial)

/-- The loop reads an admitted input as the model's own initial state. -/
theorem feedback_reads (input : Signal (0 + states)) (admit : admitted input)
    (state : Signal states) :
    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state := by
  have noDrivers : signalLeft input = Model.noDrivers := by
    funext t i; exact Fin.elim0 i
  unfold Model.ContinuousModel.Realizes Model.ContinuousModel.feedback
  rw [close_rel_reads_start, noDrivers, admit.2]

/-- The time domain is `t ≥ 0`. -/
theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t :=
  DampedOscillator.domain_iff t

/-- The loop alone: unique solutions whose energy stays in `[0, 2]`. -/
theorem loop_contract :
    Contract compiled.feedback evolution.time admitted
      (Always evolution.time fun state => 0 ≤ energy state ∧ energy state ≤ 2) where
  realizable input admit := by
    obtain ⟨state, realized⟩ := compiled_exists
    exact ⟨state, (feedback_reads input admit state).mpr realized⟩
  unique input admit a b ha hb :=
    compiled_unique ((feedback_reads input admit a).mp ha)
      ((feedback_reads input admit b).mp hb)
  holds input admit state related t within :=
    compiled_energy_bound state ((feedback_reads input admit state).mp related) t
      ((domain_iff t).mp within)

/-- **The observed energy never leaves `[0, 2]`.** For every admitted input the
compiled system has an output, all outputs agree for `t ≥ 0`, and every one of
them has `0 ≤ E ≤ 2` at every `t ≥ 0`. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 2) :=
  Contract.compose loop_contract
    (Contract.lift compiled.outputs.circuit evolution.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

/-- The declared input is admitted, so the contract is not vacuous. -/
theorem declared_input_admitted :
    admitted (signalAppend Model.noDrivers fun _ => compiled.initial) := by
  refine ⟨trivial, ?_⟩
  simp

/-- **One is not a bound.** Some output of the admitted declared input has
`E = 2` at the start. The refutation comes from the admitted initial state, not
from a proof attempt that failed. -/
theorem one_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 1) := by
  intro claim
  obtain ⟨state, realized⟩ := compiled_exists
  have start : state evolution.time.start = compiled.initial := by
    unfold Model.ContinuousModel.Realizes Model.ContinuousModel.feedback at realized
    exact ((close_rel _ _ _ _ _ _).mp realized).2.1
  have bounded := claim _ declared_input_admitted _
    ⟨state, (feedback_reads _ declared_input_admitted state).mpr realized, rfl⟩
    evolution.time.start (by simp [TimeDomain.domain])
  simp only at bounded
  rw [start] at bounded
  exact initial_not_bounded_by_one bounded

end Gimle.Forseti.Examples.DampedOscillatorContract
