import Gimle.Forseti.Examples.HedgedSpreadContract

/-! Coverage for the hedged exposure's driven trajectory contract.

Pinned here: the stable IDs and shapes external consumers cite (the
observations' ports, the driver and initial-wire IDs, the axis, a reducible start
time, the coordinates); the precondition's shape, which binds the driver and is
not `True`; that the band is the contract's own assumption and not asgard's;
and the axiom policy, asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.HedgedSpread

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Model
open Gimle.Forseti.Examples.HedgedSpread
open Gimle.Forseti.Examples.HedgedSpreadContract

/-! ### The stable interface -/

example : (body.observations.get sIndex).port.id = "obs-s" := by decide
example : (body.observations.get vIndex).port.id = "obs-v" := by decide
example : body.observations.map (·.port.id) = ["obs-s", "obs-v"] := by decide
example : List.ofFn (DriverBinding.ids drivers) = ["driver-d"] := by decide +kernel
example : evolution.states.map (·.initialId) = ["initial-s", "initial-h"] := by decide
example : evolution.axis.id = "time" := by decide
example : evolution.time.start = 0 := origin
example : compiled.initial = ![0, 0] := initial_eq
example : width = 1 := rfl
example : states = 2 := rfl
example : index (DriverBinding.ids drivers) "driver-d" = some dIndex := index_d
example : sIndex = ⟨0, by decide⟩ := rfl
example : vIndex = ⟨1, by decide⟩ := rfl
example : dIndex = ⟨0, by decide⟩ := rfl

/-- The precondition binds the driver: admitted, and `|d| ≤ 1`. -/
example : admitted = Initialized evolution.time
    (fun d => evolution.Admitted drivers d ∧
      ∀ t ∈ evolution.time.domain, |d t dIndex| ≤ 1)
    (· = compiled.initial) := rfl

example : Contract observed evolution.time admitted
    (Always evolution.time fun o => -1 ≤ o sIndex ∧ o sIndex ≤ 1) :=
  exposure_contract

example : Contract observed evolution.time admitted
    (Always evolution.time fun o => 0 ≤ o vIndex ∧ o vIndex ≤ 1) :=
  energy_contract

example : admitted (withInitial sinDriver) := witness_input_admitted

example : evolution.Admitted drivers (fun _ _ => 0) := zero_admitted

example : admittedWithin 2 (withInitial fun _ _ => 0) := zero_within (by norm_num)

/-- The start-value lemmas in the shape a refutation at the start uses them: the
zero driver with the constant initial wires, and no admission needed. -/
example (output) (related : observed.Rel evolution.time (withInitial fun _ _ => 0) output) :
    output 0 sIndex = 0 :=
  output_at_start_s _ (constant_start _) output related

example (output) (related : observed.Rel evolution.time (withInitial fun _ _ => 0) output) :
    output 0 vIndex = 0 :=
  output_at_start_v _ (constant_start _) output related

example (d : Dynamics.Signal width) :
    Dynamics.signalRight (withInitial d) evolution.time.start = compiled.initial :=
  constant_start _

/-- A smaller band strengthens to the contract's precondition, so the contract
answers for every band below its own. -/
example : Contract observed evolution.time
    (Initialized evolution.time
      (fun d => evolution.Admitted drivers d ∧
        ∀ t ∈ evolution.time.domain, |d t dIndex| ≤ 1 / 2)
      (· = compiled.initial))
    (Always evolution.time fun o => -1 ≤ o sIndex ∧ o sIndex ≤ 1) :=
  exposure_contract.consequence
    (fun _ h => ⟨⟨h.1.1, fun t within => (h.1.2 t within).trans (by norm_num)⟩, h.2⟩)
    (fun _ h => h)

example {d : Dynamics.Signal width} (admit : evolution.Admitted drivers d) :
    ∃ state, compiled.Realizes d state := compiled_exists admit

/-- A driver outside the band is still admitted by asgard: the band is the
contract's assumption, stated in its precondition, not a property of drivers. -/
example : admittedOnly (withInitial (constantDriver 3)) :=
  ⟨by simpa [withInitial] using constant_admitted 3, constant_start _⟩

/-- A driver outside the band is rejected by the precondition. -/
example : ¬ admitted (withInitial (constantDriver 2)) := by
  intro h
  have := h.1.2 0 (by rw [domain_eq]; exact Set.self_mem_Ici)
  norm_num [withInitial, constantDriver] at this

/-- A jump at the start is not admitted at all: continuity on the domain is
asgard's requirement, and a missing derivative port does not waive it. -/
example : ¬ admittedOnly (withInitial fun t _ => if t ≤ 0 then 0 else 1) := by
  intro h
  have cont := d_continuousOn h.1
  simp only [withInitial, Dynamics.signalLeft_append] at cont
  have at0 : Filter.Tendsto (fun t : ℝ => if t ≤ 0 then (0 : ℝ) else 1)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    simpa using (cont 0 Set.self_mem_Ici).tendsto
  have lim := at0.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have one : Filter.Tendsto (fun t : ℝ => if t ≤ 0 then (0 : ℝ) else 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [if_neg (not_le.2 (Set.mem_Ioi.1 ht))]
  exact zero_ne_one (tendsto_nhds_unique lim one)

/-- Inside the band, `1/2` is not a bound; without the band, `1` is not either. -/
example : ¬ Holds observed evolution.time admitted
    (Always evolution.time fun o => -(1 / 2) ≤ o sIndex ∧ o sIndex ≤ 1 / 2) :=
  half_refuted

example : ¬ Holds observed evolution.time admittedOnly
    (Always evolution.time fun o => -1 ≤ o sIndex ∧ o sIndex ≤ 1) :=
  bound_needed

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Examples.HedgedSpread.rates_expressions'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms rates_expressions
/--
info: 'Gimle.Forseti.Examples.HedgedSpread.initial_eq'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms initial_eq
/--
info: 'Gimle.Forseti.Examples.HedgedSpread.s_at'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms s_at
/--
info: 'Gimle.Forseti.Examples.HedgedSpread.v_at'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms v_at
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.feedback_reads'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms feedback_reads
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.compiled_exists'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms compiled_exists
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.exposure_within'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exposure_within
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.energy_within'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms energy_within
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.witness_input_admitted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms witness_input_admitted
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.exposure_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms exposure_contract
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.energy_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms energy_contract
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.zero_admitted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms zero_admitted
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.constant_start'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms constant_start
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.output_at_start_s'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms output_at_start_s
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.output_at_start_v'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms output_at_start_v
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.half_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms half_refuted
/--
info: 'Gimle.Forseti.Examples.HedgedSpreadContract.bound_needed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms bound_needed

end Gimle.Forseti.Tests.HedgedSpread
