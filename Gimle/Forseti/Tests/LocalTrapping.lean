import Gimle.Forseti.LocalTrapping
import Gimle.Forseti.Examples.GalerkinNS.T3Below12

/-! Coverage for trapping with a decrease local to the sublevel set.

Each `example` restates one of `LocalTrapping`'s exported theorems with its
exact statement, so a change to the trusted shape fails here rather than in a
consumer; the T3 instance below the laminar level is pinned by its data, and
the axiom policy is asserted with `#guard_msgs`. -/

namespace Gimle.Forseti.Tests.LocalTrapping

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Asgard.Model Gimle.Forseti
open Gimle.Forseti.Nonlinear Gimle.Forseti.Trajectory

/-! ### The theorem, for a raw field -/

example {n : Nat} (L : LocalTrapping n) (F : Point n → Point n) (decrease : L.Decreases F)
    (time : TimeDomain) (x₀ : Point n) (initial : L.energy x₀ ≤ L.bound)
    (state : Signal n) (h : Solves F time x₀ state) :
    ∀ t ∈ time.domain, L.energy (state t) ≤ L.bound :=
  L.invariant F decrease time x₀ initial state h

example {n : Nat} (L : LocalTrapping n) (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : L.Decreases F) (time : TimeDomain) (x₀ : Point n)
    (initial : L.energy x₀ ≤ L.bound) : ∃ state, Solves F time x₀ state :=
  L.exists_solution F smooth decrease time x₀ initial

example {n : Nat} (L : LocalTrapping n) (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : L.Decreases F) (time : TimeDomain) (x₀ : Point n)
    (initial : L.energy x₀ ≤ L.bound) {x y : Signal n}
    (hx : Solves F time x₀ x) (hy : Solves F time x₀ y) : Set.EqOn x y time.domain :=
  L.unique F smooth decrease time x₀ initial hx hy

/-- The decrease hypothesis is asked on the set only. -/
example {n : Nat} (L : LocalTrapping n) (F : Point n → Point n) :
    L.Decreases F ↔ ∀ x, L.energy x ≤ L.bound → L.rate F x ≤ L.alpha * (L.inner - L.energy x) :=
  Iff.rfl

/-- A global decrease is a local one. -/
example {n : Nat} (L : LocalTrapping n) (F : Point n → Point n)
    (global : ∀ x, L.rate F x ≤ L.alpha * (L.inner - L.energy x)) : L.Decreases F :=
  fun x _ => global x

/-- The quadratic dominates its diagonal ball, which is why the box is shared. -/
example {n : Nat} (L : LocalTrapping n) (x : Point n) : L.ball.energy x ≤ L.energy x :=
  L.ball_energy_le x

example {n : Nat} (L : LocalTrapping n) : L.inner < L.bound := L.margin

/-! ### The compiled-model shape -/

example {b : Body} {e : Evolution} (M : ContinuousModel b e) (L : LocalTrapping e.states.length)
    (k : Fin b.observations.length) (lo hi : ℝ) (decrease : L.Decreases (field M))
    (initial : L.energy M.initial ≤ L.bound)
    (bounded : ∀ state, M.Realizes state → ∀ t ∈ e.time.domain,
      lo ≤ M.outputs.circuit.run (state t) k ∧ M.outputs.circuit.run (state t) k ≤ hi) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => lo ≤ observation k ∧ observation k ≤ hi) :=
  local_bounded_contract M L k lo hi decrease initial bounded

example : ∃ state, Examples.GalerkinNS.T3.compiled.Realizes state :=
  local_compiled_exists Examples.GalerkinNS.T3.compiled Examples.GalerkinNS.T3.below12
    Examples.GalerkinNS.T3.decreases_below12 Examples.GalerkinNS.T3.initial_below12

/-! ### The 3-mode member below its laminar level -/

example : Examples.GalerkinNS.T3.below12.bound = 1 := rfl
example : Examples.GalerkinNS.T3.below12.lower = 17 / 200 := rfl
example : Examples.GalerkinNS.T3.below12.radius = 7 / 2 := rfl
example : Examples.GalerkinNS.T3.below12.inner < 1 := Examples.GalerkinNS.T3.below12.margin

/-- The bound `12` is below the laminar energy `25/2` and the family bound `13`. -/
example : (12 : ℝ) < Examples.GalerkinNS.T3.trapping.inner ∧
    Examples.GalerkinNS.T3.trapping.inner < Examples.GalerkinNS.T3.trapping.bound := by
  constructor <;> norm_num [Examples.GalerkinNS.T3.trapping]

/-- The laminar point `(0, 5, 0)` is an equilibrium outside the set, and the
start is inside: no global decrease could give this. -/
example : Examples.GalerkinNS.T3.field ![0, 5, 0] = 0 := Examples.GalerkinNS.T3.laminar_equilibrium
example : 1 < Examples.GalerkinNS.T3.V ![0, 5, 0] := Examples.GalerkinNS.T3.laminar_outside
example : Examples.GalerkinNS.T3.V ![1, 1, 1] < 1 := Examples.GalerkinNS.T3.start_inside

example : Contract Examples.GalerkinNS.T3.observed Examples.GalerkinNS.T3.evolution.time
    Examples.GalerkinNS.T3.admitted
    (Always Examples.GalerkinNS.T3.evolution.time fun observation =>
      0 ≤ observation Examples.GalerkinNS.T3.energyIndex ∧
        observation Examples.GalerkinNS.T3.energyIndex ≤ 12) :=
  Examples.GalerkinNS.T3.below12_contract

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Nonlinear.LocalTrapping.invariant'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalTrapping.invariant

/--
info: 'Gimle.Forseti.Nonlinear.LocalTrapping.exists_solution'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalTrapping.exists_solution

/--
info: 'Gimle.Forseti.Nonlinear.LocalTrapping.unique'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LocalTrapping.unique

/--
info: 'Gimle.Forseti.Nonlinear.local_bounded_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms local_bounded_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.below12_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.below12_contract

/--
info: 'Gimle.Forseti.Examples.GalerkinNS.T3.decreases_below12'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.GalerkinNS.T3.decreases_below12

end Gimle.Forseti.Tests.LocalTrapping
