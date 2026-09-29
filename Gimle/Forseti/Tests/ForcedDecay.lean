import Gimle.Forseti.Examples.ForcedDecayContract

/-! Coverage for the forced decay's driven trajectory contract.

Pinned here: the stable IDs and shapes a downstream renderer cites (the
observation's port, the driver and initial-wire IDs, the axis, a reducible start
time, the driver coordinates); the precondition's shape, which binds the drivers
and is not `True`; that an input whose drivers are not admitted is rejected; and
the axiom policy, asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.ForcedDecay

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Model
open Gimle.Forseti.Examples.ForcedDecay
open Gimle.Forseti.Examples.ForcedDecayContract

/-! ### The interface a renderer cites -/

example : (body.observations.get xIndex).port.id = "obs-x" := by decide
example : body.observations.map (·.port.id) = ["obs-x"] := by decide
example : List.ofFn (DriverBinding.ids drivers) = ["driver-u", "driver-du"] := by decide +kernel
example : evolution.states.map (·.initialId) = ["initial-x"] := by decide
example : evolution.axis.id = "time" := by decide
example : evolution.time.start = 0 := origin
example : compiled.initial = ![0] := initial_eq
example : width = 2 := rfl
example : states = 1 := rfl
example : index (DriverBinding.ids drivers) "driver-u" = some uIndex := index_u
example : index (DriverBinding.ids drivers) "driver-du" = some duIndex := index_du

/-- The precondition binds the drivers: admitted, and `|u| ≤ 1`. -/
example : admitted = Initialized evolution.time
    (fun d => evolution.Admitted drivers d ∧
      ∀ t ∈ evolution.time.domain, |d t uIndex| ≤ 1)
    (· = compiled.initial) := rfl

example : Contract observed evolution.time admitted
    (Always evolution.time fun o => -2 ≤ o xIndex ∧ o xIndex ≤ 2) :=
  driven_contract

example : admitted witnessInput := witness_input_admitted

example {d : Dynamics.Signal width} (admit : evolution.Admitted drivers d) :
    ∃ state, compiled.Realizes d state := compiled_exists admit

/-- A driver whose `du` is not the derivative of `u` is not admitted: `u = 0`,
`du = 1`. -/
example : ¬ admitted (withInitial fun _ i => if i.val = 0 then 0 else 1) := by
  intro h
  have deriv := (u_deriv h.1.1 1 (by norm_num)).hasDerivAt (Ici_mem_nhds one_pos)
  simp only [withInitial, Dynamics.signalLeft_append, uIndex, duIndex] at deriv
  have := deriv.unique (hasDerivAt_const (1 : ℝ) (0 : ℝ))
  norm_num at this

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Examples.ForcedDecay.same_source' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms same_source
/--
info: 'Gimle.Forseti.Examples.ForcedDecay.x_at_initial'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms x_at_initial
/--
info: 'Gimle.Forseti.Driven.forwarded_rel'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Driven.forwarded_rel
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.feedback_reads'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms feedback_reads
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.compiled_exists'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms compiled_exists
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.contract_within'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms contract_within
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.driven_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms driven_contract
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.witness_input_admitted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms witness_input_admitted
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.one_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms one_refuted
/--
info: 'Gimle.Forseti.Examples.ForcedDecayContract.bound_needed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms bound_needed

end Gimle.Forseti.Tests.ForcedDecay
