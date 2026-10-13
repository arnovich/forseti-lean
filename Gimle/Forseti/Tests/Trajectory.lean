import Gimle.Forseti.Examples.ThreeStateContract

/-! Coverage for trajectory contracts.

Pinned here: an endpoint observation is weaker than all-forward safety; times
before the start and initial-wire values after it are not constrained; a
circuit with a safe and an unsafe output fails the contract rather than being
credited with the safe one; a circuit with no behaviour satisfies the partial
contract vacuously but never the total one; and a trace has no well-posedness
for free. The axiom policy is asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.Trajectory

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics

/-- The forward domain from `t = 0`. -/
def fromZero : TimeDomain := ⟨"time", 0⟩
/-- The forward domain from `t = 2`. -/
def fromTwo : TimeDomain := ⟨"time", 2⟩

/-- A ramp `y(t) = t`. -/
noncomputable def ramp : Signal 1 := fun t _ => t

/-! ### Endpoint versus all-forward safety -/

/-- The ramp is below 3 at `t = 3`… -/
example : At 3 (fun x : Point 1 => x 0 ≤ 3) ramp := by simp [At, ramp]
/-- …but not at every `t ≥ 0`: it passes 3 at `t = 4`. -/
example : ¬ Always fromZero (fun x : Point 1 => x 0 ≤ 3) ramp := by
  intro always
  have := always 4 (by simp [fromZero, TimeDomain.domain])
  norm_num [ramp] at this

/-! ### The start time and the initial wires -/

/-- A signal that is large before the start is still safe from the start on:
`Always` constrains the forward domain only. -/
example : Always fromTwo (fun x : Point 1 => x 0 ≤ 1)
    (fun t _ => if t < 2 then 100 else 0) := by
  intro t within
  have : ¬ t < 2 := not_lt.mpr within
  simp [this]

/-- An admitted three-state input may carry anything on its initial wires after
the start; it is still admitted and has an output. -/
example : ∃ output, Examples.ThreeStateContract.observed.Rel
    Examples.ThreeState.evolution.time
    (signalAppend Model.noDrivers fun t =>
      if t = Examples.ThreeState.evolution.time.start then
        Examples.ThreeState.model.initial else fun _ => 100) output := by
  apply Examples.ThreeStateContract.energy_contract.realizable
  refine ⟨trivial, ?_⟩
  simp

/-- The start value does bind: wires equal to the declared state everywhere
except at `t = 2` are not admitted. -/
example : ¬ Examples.ThreeStateContract.admitted
    (signalAppend Model.noDrivers fun t =>
      if t = 2 then (fun _ => 0) else Examples.ThreeState.model.initial) := by
  rintro ⟨-, h⟩
  have := congrFun h ⟨0, by decide⟩
  have start : Examples.ThreeState.evolution.time.start = 2 := rfl
  simp [start, Examples.ThreeState.initial_eq] at this
  change (0 : ℝ) = 1 at this
  norm_num at this

/-! ### Uniqueness is on the forward domain only

An integrator constrains its output from the start on. Two outputs that differ
before the start are both related, and `Unique` rightly says only that they
agree from the start. -/

/-- A resting integrator input: derivative 0, initial value 0. -/
def resting : Signal (1 + 1) := fun _ _ => 0

/-- Zero, or five before the start and zero after. -/
noncomputable def early : Signal 1 := fun t _ => if t < 0 then 5 else 0

theorem integrate_rests (output : Signal 1) (rest : ∀ t, 0 ≤ t → output t 0 = 0) :
    (Dynamics.Circuit.integrate "time" 1).Rel fromZero resting output := by
  refine ⟨rfl, ?_, ?_⟩
  · funext i
    fin_cases i
    simpa [resting, pointRight, fromZero] using rest 0 le_rfl
  · intro t within i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have zero : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0 fromZero.domain t :=
      hasDerivWithinAt_const _ _ _
    have left : pointLeft (resting t) 0 = 0 := by simp [resting, pointLeft]
    rw [left]
    exact zero.congr (fun s hs => rest s hs) (rest t within)

example : (Dynamics.Circuit.integrate "time" 1).Rel fromZero resting fun _ _ => 0 :=
  integrate_rests _ fun _ _ => rfl
example : (Dynamics.Circuit.integrate "time" 1).Rel fromZero resting early :=
  integrate_rests _ fun t nonneg => by simp [early, not_lt.mpr nonneg]
/-- The two outputs differ before the start… -/
example : (fun _ _ => 0 : Signal 1) ≠ early := by
  intro same
  have := congrFun (congrFun same (-1)) 0
  norm_num [early] at this
/-- …and agree on the domain, which is all `Unique` asks. -/
example : Set.EqOn (fun _ _ => 0 : Signal 1) early fromZero.domain := by
  intro t within
  funext i
  simp [early, not_lt.mpr (show (0 : ℝ) ≤ t from within)]

/-! ### A safe output does not excuse an unsafe one

`free` feeds its output back to itself and constrains nothing: every signal is
a related output. Some related output is safe, so "a safe output exists" holds;
the partial contract `Holds` still fails, because it asks about all of them. -/

/-- Route both outputs from the feedback wire. -/
def echo : Gimle.Asgard.Circuit (1 + 1) (1 + 1) :=
  Polynomial.route fun _ => ⟨1, by omega⟩

/-- A loop whose output is unconstrained. -/
def free : Dynamics.Circuit 1 1 := .trace 1 (.lift echo)

theorem free_relates (time : TimeDomain) (input output : Signal 1) :
    free.Rel time input output := by
  refine ⟨output, ?_⟩
  change _ = _
  funext t i
  fin_cases i <;> simp [echo, signalAppend, pointAppend]

example : ∃ output, free.Rel fromZero ramp output ∧
    Always fromZero (fun x : Point 1 => x 0 ≤ 0) output :=
  ⟨fun _ _ => 0, free_relates _ _ _, fun _ _ => le_refl _⟩

example : ¬ Holds free fromZero (fun _ => True) (Always fromZero fun x => x 0 ≤ 0) := by
  intro holds
  have := holds ramp trivial ramp (free_relates _ _ _) 1 (by simp [fromZero, TimeDomain.domain])
  norm_num [ramp] at this

/-- **A trace is not well-posed for free**: `free` has many outputs for one input,
so it has no contract at all, whatever the postcondition. -/
theorem free_not_unique : ¬ Unique free fromZero fun _ => True := by
  intro unique
  have := unique ramp trivial (fun _ _ => 0) (fun _ _ => 1) (free_relates _ _ _)
    (free_relates _ _ _) (by simp [fromZero, TimeDomain.domain] : (0 : ℝ) ∈ fromZero.domain)
  have := congrFun this 0
  norm_num at this

example (post : SignalPredicate 1) : ¬ Contract free fromZero (fun _ => True) post :=
  fun contract => free_not_unique contract.unique

/-! ### An empty behaviour -/

/-- An integrator on another axis relates nothing on this clock. -/
def offAxis : Dynamics.Circuit (1 + 1) 1 := .integrate "space" 1

theorem offAxis_empty (input : Signal (1 + 1)) (output : Signal 1) :
    ¬ offAxis.Rel fromZero input output := by
  rintro ⟨axis, _⟩
  simp [fromZero] at axis

/-- Every partial contract holds of it, even an absurd one… -/
example : Holds offAxis fromZero (fun _ => True) fun _ => False :=
  fun input _ output related => (offAxis_empty input output related).elim

/-- …but for a witnessed admitted input it is not realizable, so it has no
contract. -/
example (post : SignalPredicate 1) : ¬ Contract offAxis fromZero (fun _ => True) post :=
  fun contract => by
    obtain ⟨output, related⟩ := contract.realizable (fun _ _ => 0) trivial
    exact offAxis_empty _ _ related

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Trajectory.Contract.consequence'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Contract.consequence
/--
info: 'Gimle.Forseti.Trajectory.Holds.consequence'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Holds.consequence
/--
info: 'Gimle.Forseti.Trajectory.Contract.transport'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Contract.transport
/--
info: 'Gimle.Forseti.Trajectory.Contract.compose'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Contract.compose
/--
info: 'Gimle.Forseti.Trajectory.Contract.parallel'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Contract.parallel
/--
info: 'Gimle.Forseti.Trajectory.close_rel'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms close_rel
/--
info: 'Gimle.Forseti.Trajectory.Contract.linear'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Contract.linear
/--
info: 'Gimle.Forseti.Trajectory.Contract.energy'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Contract.energy
/--
info: 'Gimle.Forseti.Examples.ThreeStateContract.energy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Examples.ThreeStateContract.energy_contract
/--
info: 'Gimle.Forseti.Examples.ThreeStateContract.five_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Examples.ThreeStateContract.five_refuted

end Gimle.Forseti.Tests.Trajectory
