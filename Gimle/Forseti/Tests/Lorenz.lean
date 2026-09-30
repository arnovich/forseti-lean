import Gimle.Forseti.Examples.Lorenz

/-! Coverage for the Lorenz model's trajectory contract.

gimle-forseti's trajectory registry and its rendered replay roots cite these
constants by name. Each `example` restates one of them with its exact statement,
fully qualified, so a change to a name or a statement fails the build here
rather than in a downstream replay. The axiom policy is asserted with
`#guard_msgs`. This is the first contract whose existence and uniqueness are
not read off a linear view, so those are pinned as well.
-/

namespace Gimle.Forseti.Tests.Lorenz

open Gimle.Forseti.Trajectory
open Gimle.Asgard

/-! ### The model's constants the registry cites -/

example : Model.Body := Gimle.Forseti.Examples.Lorenz.body
example : Model.Evolution := Gimle.Forseti.Examples.Lorenz.evolution
example : Model.ContinuousModel Gimle.Forseti.Examples.Lorenz.body
    Gimle.Forseti.Examples.Lorenz.evolution :=
  Gimle.Forseti.Examples.Lorenz.compiled
example : Fin Gimle.Forseti.Examples.Lorenz.body.observations.length :=
  Gimle.Forseti.Examples.Lorenz.energyIndex
example : Gimle.Forseti.Examples.Lorenz.compiled.initial = ![1, 1, 1] :=
  Gimle.Forseti.Examples.Lorenz.initial_eq
example : Gimle.Forseti.Examples.Lorenz.compiled.outputs.circuit.run
    Gimle.Forseti.Examples.Lorenz.compiled.initial
    Gimle.Forseti.Examples.Lorenz.energyIndex = 1371 :=
  Gimle.Forseti.Examples.Lorenz.energy_at_initial

/-- The model has no linear view: the contract below is not `LinearEnergyContract`'s. -/
example : Gimle.Forseti.Examples.Lorenz.compiled.linear.isNone = true := by decide +kernel

/-! ### The contract's constants the registry cites -/

example : ∃ state, Gimle.Forseti.Examples.Lorenz.compiled.Realizes state :=
  Gimle.Forseti.Examples.Lorenz.compiled_exists

example {x y : Dynamics.Signal 3} (hx : Gimle.Forseti.Examples.Lorenz.compiled.Realizes x)
    (hy : Gimle.Forseti.Examples.Lorenz.compiled.Realizes y) :
    Set.EqOn x y Gimle.Forseti.Examples.Lorenz.evolution.time.domain :=
  Gimle.Forseti.Examples.Lorenz.compiled_unique hx hy

example : Dynamics.Circuit (0 + Gimle.Forseti.Examples.Lorenz.evolution.states.length)
    Gimle.Forseti.Examples.Lorenz.body.observations.length :=
  Gimle.Forseti.Examples.Lorenz.observed

example : SignalPredicate (0 + Gimle.Forseti.Examples.Lorenz.evolution.states.length) :=
  Gimle.Forseti.Examples.Lorenz.admitted

example : Gimle.Forseti.Examples.Lorenz.admitted =
    Initialized Gimle.Forseti.Examples.Lorenz.evolution.time (fun _ => True)
      (· = Gimle.Forseti.Examples.Lorenz.compiled.initial) := rfl

example (input : Dynamics.Signal (0 + Gimle.Forseti.Examples.Lorenz.evolution.states.length))
    (admit : Gimle.Forseti.Examples.Lorenz.admitted input)
    (state : Dynamics.Signal Gimle.Forseti.Examples.Lorenz.evolution.states.length) :
    Gimle.Forseti.Examples.Lorenz.compiled.feedback.Rel
        Gimle.Forseti.Examples.Lorenz.evolution.time input state ↔
      Gimle.Forseti.Examples.Lorenz.compiled.Realizes state :=
  Gimle.Forseti.Examples.Lorenz.feedback_reads input admit state

example (t : ℝ) : t ∈ Gimle.Forseti.Examples.Lorenz.evolution.time.domain ↔ 0 ≤ t :=
  Gimle.Forseti.Examples.Lorenz.domain_iff t

example : Contract Gimle.Forseti.Examples.Lorenz.observed
    Gimle.Forseti.Examples.Lorenz.evolution.time
    Gimle.Forseti.Examples.Lorenz.admitted
    (Always Gimle.Forseti.Examples.Lorenz.evolution.time fun observation =>
      0 ≤ observation Gimle.Forseti.Examples.Lorenz.energyIndex ∧
        observation Gimle.Forseti.Examples.Lorenz.energyIndex ≤ 1600) :=
  Gimle.Forseti.Examples.Lorenz.energy_contract

example : Gimle.Forseti.Examples.Lorenz.admitted
    (Dynamics.signalAppend Model.noDrivers fun _ =>
      Gimle.Forseti.Examples.Lorenz.compiled.initial) :=
  Gimle.Forseti.Examples.Lorenz.declared_input_admitted

example : ¬ Holds Gimle.Forseti.Examples.Lorenz.observed
    Gimle.Forseti.Examples.Lorenz.evolution.time
    Gimle.Forseti.Examples.Lorenz.admitted
    (Always Gimle.Forseti.Examples.Lorenz.evolution.time fun observation =>
      observation Gimle.Forseti.Examples.Lorenz.energyIndex ≤ 1300) :=
  Gimle.Forseti.Examples.Lorenz.thirteen_hundred_refuted

/-- The rendered refutation's step: the declared input's realization, read
through `feedback_reads`, is an output of `observed` by the anonymous
constructor, so `observed` still unfolds to the loop and its observations. -/
example : ∃ output, Gimle.Forseti.Examples.Lorenz.observed.Rel
    Gimle.Forseti.Examples.Lorenz.evolution.time
    (Dynamics.signalAppend Model.noDrivers fun _ =>
      Gimle.Forseti.Examples.Lorenz.compiled.initial) output := by
  obtain ⟨state, realized⟩ := Gimle.Forseti.Examples.Lorenz.compiled_exists
  exact ⟨_, state, (Gimle.Forseti.Examples.Lorenz.feedback_reads _
    Gimle.Forseti.Examples.Lorenz.declared_input_admitted state).mpr realized, rfl⟩

/-! ### The mathematics, restated -/

/-- The closed-form field is the compiled one. -/
example (x : Point 3) : Gimle.Forseti.Examples.Lorenz.compiled.rates.circuit.run x =
    ![10 * (x 1 - x 0), x 0 * (28 - x 2) - x 1, x 0 * x 1 - 8 / 3 * x 2] :=
  Gimle.Forseti.Examples.Lorenz.rates_formula x

/-- `V' + 2V ≤ 2·1541` everywhere; `1541` is not `1600`, and that margin is what
the fencing step in the existence proof needs. -/
example (x : Point 3) : Gimle.Forseti.Examples.Lorenz.rate x ≤
    2 * 1541 - 2 * Gimle.Forseti.Examples.Lorenz.energy x :=
  Gimle.Forseti.Examples.Lorenz.storage_bound x

/-- The bound is not a consequence of `V` decreasing everywhere: at the origin
`V' = 0`, and just above it `V' > 0`. -/
example : 0 < Gimle.Forseti.Examples.Lorenz.rate ![0, 0, 1] := by
  norm_num [Gimle.Forseti.Examples.Lorenz.rate, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Examples.Lorenz.compiled_exists'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.Lorenz.compiled_exists

/--
info: 'Gimle.Forseti.Examples.Lorenz.compiled_unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.Lorenz.compiled_unique

/--
info: 'Gimle.Forseti.Examples.Lorenz.energy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.Lorenz.energy_contract

/--
info: 'Gimle.Forseti.Examples.Lorenz.thirteen_hundred_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Examples.Lorenz.thirteen_hundred_refuted

end Gimle.Forseti.Tests.Lorenz
