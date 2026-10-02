import Gimle.Forseti.Nonlinear
import Gimle.Forseti.Examples.Lorenz

/-! Coverage for the general trapping theorem.

Each `example` restates one of `Nonlinear`'s exported theorems with its exact
statement, so a change to a name or a statement fails the build here rather
than in an instance. The axiom policy is asserted with `#guard_msgs`, and the
Lorenz instance is shown to be exactly an application: its data, its `decrease`
and its `initial_le` are the only model-specific inputs.
-/

namespace Gimle.Forseti.Tests.Nonlinear

open Gimle.Forseti.Trajectory
open Gimle.Forseti.Nonlinear
open Gimle.Asgard
open Gimle.Asgard.Model
open Gimle.Asgard.Polynomial

/-! ### Every compiled field is smooth -/

example {n : Nat} (e : Expr n) : ContDiff ℝ 1 (fun x : Point n => e.eval x) := contDiff_eval e

example {b : Body} {e : Evolution} (M : ContinuousModel b e) : ContDiff ℝ 1 (field M) :=
  field_contDiff M

example {b : Body} {e : Evolution} (M : ContinuousModel b e) (state : Dynamics.Signal e.states.length) :
    M.Realizes state ↔ Solves (field M) e.time M.initial state := realizes_iff M state

/-! ### The trapping theorem, for a raw field and for a compiled model -/

example {n : Nat} (T : Trapping n) (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (time : Dynamics.TimeDomain) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound) :
    ∃ state, Solves F time x₀ state :=
  T.exists_solution F smooth decrease time x₀ initial

example {n : Nat} (T : Trapping n) (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (time : Dynamics.TimeDomain) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound)
    {x y : Dynamics.Signal n} (hx : Solves F time x₀ x) (hy : Solves F time x₀ y) :
    Set.EqOn x y time.domain :=
  T.unique F smooth decrease time x₀ initial hx hy

example {n : Nat} (T : Trapping n) (F : Point n → Point n)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (time : Dynamics.TimeDomain) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound)
    (state : Dynamics.Signal n) (h : Solves F time x₀ state) :
    ∀ t ∈ time.domain, T.energy (state t) ≤ T.bound :=
  T.invariant F decrease time x₀ initial state h

example {b : Body} {e : Evolution} (M : ContinuousModel b e) (T : Trapping e.states.length)
    (k : Fin b.observations.length)
    (energy_eq : ∀ x, M.outputs.circuit.run x k = T.energy x)
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => 0 ≤ observation k ∧ observation k ≤ T.bound) :=
  energy_contract M T k energy_eq decrease initial

example {b : Body} {e : Evolution} (M : ContinuousModel b e) (T : Trapping e.states.length)
    (k : Fin b.observations.length)
    (energy_eq : ∀ x, M.outputs.circuit.run x k = T.energy x)
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound) (β : ℝ) (above : β < T.energy M.initial) :
    ¬ Holds (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => observation k ≤ β) :=
  refuted M T k energy_eq decrease initial β above

/-! ### The margin is used: without it a contact point could have `V' = 0` -/

/-- A `Trapping` needs `C' < C`; equal levels are refused by the structure. -/
example : ¬ ∃ T : Trapping 1, T.inner = T.bound := fun ⟨T, h⟩ => absurd h T.margin.ne

/-! ### The Lorenz instance is one application -/

example : Gimle.Forseti.Examples.Lorenz.trapping.bound = 1600 := rfl
example : Gimle.Forseti.Examples.Lorenz.trapping.inner = 1541 := rfl
example : Gimle.Forseti.Examples.Lorenz.trapping.alpha = 2 := rfl

example : ∃ state, Gimle.Forseti.Examples.Lorenz.compiled.Realizes state :=
  compiled_exists Gimle.Forseti.Examples.Lorenz.compiled Gimle.Forseti.Examples.Lorenz.trapping
    Gimle.Forseti.Examples.Lorenz.decrease Gimle.Forseti.Examples.Lorenz.initial_le

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Nonlinear.contDiff_eval'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Nonlinear.contDiff_eval

/--
info: 'Gimle.Forseti.Nonlinear.Trapping.exists_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Nonlinear.Trapping.exists_solution

/--
info: 'Gimle.Forseti.Nonlinear.Trapping.unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Nonlinear.Trapping.unique

/--
info: 'Gimle.Forseti.Nonlinear.energy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Nonlinear.energy_contract

/--
info: 'Gimle.Forseti.Nonlinear.bounded_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Nonlinear.bounded_contract

/--
info: 'Gimle.Forseti.Nonlinear.refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Gimle.Forseti.Nonlinear.refuted

end Gimle.Forseti.Tests.Nonlinear
