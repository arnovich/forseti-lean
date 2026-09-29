import Gimle.Forseti.Examples.ThreeStateContract

/-! Coverage for the three-state model's trajectory contract.

gimle-forseti's trajectory registry and its rendered replay roots cite these
constants by name. Each `example` restates one of them with its exact statement,
fully qualified, so a change to a name or a statement fails the build here
rather than in a downstream replay. The axiom policy is asserted with
`#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.ThreeState

open Gimle.Forseti.Trajectory
open Gimle.Asgard

/-! ### Asgard's constants the registry cites -/

example : ℚ → ℚ → ℚ → Model.Body := Gimle.Asgard.Examples.ThreeState.body
example : Model.Evolution := Gimle.Asgard.Examples.ThreeState.evolution
example : Model.ContinuousModel (Gimle.Asgard.Examples.ThreeState.body (1 / 3) (1 / 2) 2)
    Gimle.Asgard.Examples.ThreeState.evolution :=
  Gimle.Asgard.Examples.ThreeState.model
example : Fin (Gimle.Asgard.Examples.ThreeState.body (1 / 3) (1 / 2) 2).observations.length :=
  Gimle.Asgard.Examples.ThreeState.energyIndex
example : Gimle.Asgard.Examples.ThreeState.model.initial = ![1, 2, -1] :=
  Gimle.Asgard.Examples.ThreeState.initial_eq
example : Gimle.Asgard.Examples.ThreeState.model.outputs.circuit.run
    Gimle.Asgard.Examples.ThreeState.model.initial
    Gimle.Asgard.Examples.ThreeState.energyIndex = 6 :=
  Gimle.Asgard.Examples.ThreeState.energy_at_initial

/-! ### Forseti's constants the registry cites -/

example : ∃ state, Gimle.Asgard.Examples.ThreeState.model.Realizes state :=
  Gimle.Forseti.Examples.ThreeState.compiled_exists

example : Dynamics.Circuit (0 + Gimle.Asgard.Examples.ThreeState.evolution.states.length)
    (Gimle.Asgard.Examples.ThreeState.body (1 / 3) (1 / 2) 2).observations.length :=
  Gimle.Forseti.Examples.ThreeStateContract.observed

example : Gimle.Forseti.Examples.ThreeStateContract.states =
    Gimle.Asgard.Examples.ThreeState.evolution.states.length := rfl

example (state : Point Gimle.Forseti.Examples.ThreeStateContract.states) :
    Gimle.Forseti.Examples.ThreeStateContract.energy state =
      Gimle.Asgard.Examples.ThreeState.model.outputs.circuit.run state
        Gimle.Asgard.Examples.ThreeState.energyIndex := rfl

example : SignalPredicate (0 + Gimle.Forseti.Examples.ThreeStateContract.states) :=
  Gimle.Forseti.Examples.ThreeStateContract.admitted

example : Gimle.Forseti.Examples.ThreeStateContract.admitted =
    Initialized Gimle.Asgard.Examples.ThreeState.evolution.time (fun _ => True)
      (· = Gimle.Asgard.Examples.ThreeState.model.initial) := rfl

example (input : Dynamics.Signal (0 + Gimle.Forseti.Examples.ThreeStateContract.states))
    (admit : Gimle.Forseti.Examples.ThreeStateContract.admitted input)
    (state : Dynamics.Signal Gimle.Forseti.Examples.ThreeStateContract.states) :
    Gimle.Asgard.Examples.ThreeState.model.feedback.Rel
        Gimle.Asgard.Examples.ThreeState.evolution.time input state ↔
      Gimle.Asgard.Examples.ThreeState.model.Realizes state :=
  Gimle.Forseti.Examples.ThreeStateContract.feedback_reads input admit state

example (t : ℝ) : t ∈ Gimle.Asgard.Examples.ThreeState.evolution.time.domain ↔ 2 ≤ t :=
  Gimle.Forseti.Examples.ThreeStateContract.domain_iff t

example : Contract Gimle.Asgard.Examples.ThreeState.model.feedback
    Gimle.Asgard.Examples.ThreeState.evolution.time
    Gimle.Forseti.Examples.ThreeStateContract.admitted
    (Always Gimle.Asgard.Examples.ThreeState.evolution.time fun state =>
      0 ≤ Gimle.Forseti.Examples.ThreeStateContract.energy state ∧
        Gimle.Forseti.Examples.ThreeStateContract.energy state ≤ 6) :=
  Gimle.Forseti.Examples.ThreeStateContract.loop_contract

example : Contract Gimle.Forseti.Examples.ThreeStateContract.observed
    Gimle.Asgard.Examples.ThreeState.evolution.time
    Gimle.Forseti.Examples.ThreeStateContract.admitted
    (Always Gimle.Asgard.Examples.ThreeState.evolution.time fun observation =>
      0 ≤ observation Gimle.Asgard.Examples.ThreeState.energyIndex ∧
        observation Gimle.Asgard.Examples.ThreeState.energyIndex ≤ 6) :=
  Gimle.Forseti.Examples.ThreeStateContract.energy_contract

example : Gimle.Forseti.Examples.ThreeStateContract.admitted
    (Dynamics.signalAppend Model.noDrivers fun _ =>
      Gimle.Asgard.Examples.ThreeState.model.initial) :=
  Gimle.Forseti.Examples.ThreeStateContract.declared_input_admitted

example : ¬ Holds Gimle.Forseti.Examples.ThreeStateContract.observed
    Gimle.Asgard.Examples.ThreeState.evolution.time
    Gimle.Forseti.Examples.ThreeStateContract.admitted
    (Always Gimle.Asgard.Examples.ThreeState.evolution.time fun observation =>
      observation Gimle.Asgard.Examples.ThreeState.energyIndex ≤ 5) :=
  Gimle.Forseti.Examples.ThreeStateContract.five_refuted

/-- The rendered refutation's step: the declared input's realization, read
through `feedback_reads`, is an output of `observed` by the anonymous
constructor, so `observed` still unfolds to the loop and its observations. -/
example : ∃ output, Gimle.Forseti.Examples.ThreeStateContract.observed.Rel
    Gimle.Asgard.Examples.ThreeState.evolution.time
    (Dynamics.signalAppend Model.noDrivers fun _ =>
      Gimle.Asgard.Examples.ThreeState.model.initial) output := by
  obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.ThreeState.compiled_exists
  exact ⟨_, state, (Gimle.Forseti.Examples.ThreeStateContract.feedback_reads _
    Gimle.Forseti.Examples.ThreeStateContract.declared_input_admitted state).mpr realized, rfl⟩

/-! ### The spec the contracts come from -/

example : Gimle.Forseti.Examples.ThreeState.spec.energy =
    Gimle.Asgard.Examples.ThreeState.energyIndex := rfl
example : Gimle.Forseti.Examples.ThreeState.spec.matrix =
    Gimle.Forseti.Examples.ThreeState.identity := rfl
example : Gimle.Forseti.Examples.ThreeState.spec.view =
    Gimle.Asgard.Examples.ThreeState.linear := rfl

/-- A certificate for other damping does not validate the compiled field: the
check recomputes the dissipation rather than trusting the data. -/
example : ¬ (Gimle.Forseti.Examples.ThreeState.certificate 1 (1 / 2) 2).Valid
    (Gimle.Forseti.Examples.ThreeState.expectedMatrix (1 / 3) (1 / 2) 2)
    Gimle.Forseti.Examples.ThreeState.identity := by
  intro valid
  have entry := valid.2.2 ⟨0, by decide⟩ ⟨0, by decide⟩
  rw [Gimle.Forseti.Examples.ThreeState.dissipation_eq] at entry
  norm_num [Gimle.Forseti.Examples.ThreeState.certificate,
    Gimle.Forseti.Examples.ThreeState.diagonal, Gimle.Forseti.Examples.ThreeState.unit,
    Fin.sum_univ_three] at entry

/-! ### The compiled bound and the generic lemmas, unchanged -/

example (state : Dynamics.Signal 3)
    (realized : Gimle.Asgard.Examples.ThreeState.model.Realizes state) (t : ℝ) (forward : 2 ≤ t) :
    0 ≤ Gimle.Asgard.Examples.ThreeState.model.outputs.circuit.run (state t)
        Gimle.Asgard.Examples.ThreeState.energyIndex ∧
      Gimle.Asgard.Examples.ThreeState.model.outputs.circuit.run (state t)
        Gimle.Asgard.Examples.ThreeState.energyIndex ≤ 6 :=
  Gimle.Forseti.Examples.ThreeState.compiled_energy_bound state realized t forward

example (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (problem : Dynamics.Linear.Problem 3)
    (matrix_eq : problem.matrix = Gimle.Forseti.Examples.ThreeState.expectedMatrix a b c)
    (initial_eq : problem.initial = (![1, 2, -1] : Point 3))
    (start_eq : problem.time.start = 2)
    (state : Dynamics.Signal 3) (solves : problem.Solves state) (t : ℝ) (forward : 2 ≤ t) :
    0 ≤ LinearEnergy.quadratic Gimle.Forseti.Examples.ThreeState.identity (state t) ∧
      LinearEnergy.quadratic Gimle.Forseti.Examples.ThreeState.identity (state t) ≤ 6 :=
  Gimle.Forseti.Examples.ThreeState.energy_bound a b c ha hb hc problem matrix_eq initial_eq
    start_eq state solves t forward

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Examples.ThreeState.certificate_valid'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.ThreeState.certificate_valid

/--
info: 'Gimle.Forseti.Examples.ThreeState.compiled_energy_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.ThreeState.compiled_energy_bound
/--
info: 'Gimle.Forseti.Examples.ThreeState.energy_bound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Gimle.Forseti.Examples.ThreeState.energy_bound
/--
info: 'Gimle.Forseti.Examples.ThreeStateContract.feedback_reads'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.ThreeStateContract.feedback_reads
/--
info: 'Gimle.Forseti.Examples.ThreeStateContract.loop_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.ThreeStateContract.loop_contract
/--
info: 'Gimle.Forseti.Examples.ThreeStateContract.declared_input_admitted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.ThreeStateContract.declared_input_admitted

end Gimle.Forseti.Tests.ThreeState
