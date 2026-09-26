import Gimle.Forseti.Examples.StreamObservation

/-! Hostile cases for the coefficient observation adapter.

Each swap below changes what a name or a coordinate reads, and the checker —
not the test — notices: a name no longer resolves, a slot list no longer equals
the lowering's, or a certificate that checked before no longer checks and a
counterexample appears. A finite observation is never a full stream.

The axiom policy is asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.StreamObservation

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Stream
open Gimle.Forseti.StreamObservation
open Gimle.Forseti.Examples.StreamObservation
open Gimle.Asgard
open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Lowering
open Gimle.Asgard.Examples.FormalHeat (heat boundary two circuit)

/-! ### Basis swap -/

/-- `u[t^0, x^2] = 1 ⊨ u_xx[t^0, x^0] = 2`, over the OGF lowering. -/
def ogfGoal : Goal :=
  leafGoal secondDerivative spaceInput spaceOutput
    (equals (spaceInput.context.var "u[t^0, x^2]" (by decide +kernel)) 1)
    (equals (spaceOutput.context.var "u_xx[t^0, x^0]" (by decide +kernel)) 2)

/-- In OGF, `u_xx[x^0] − 2 = 2 · (u[x^2] − 1)`. -/
def ogfCertificate : EntailmentCertificate spaceInput.context.dimension :=
  ⟨[⟨unused, [weight 2, unused]⟩, ⟨unused, [unused, weight 2]⟩]⟩

example : ogfCertificate.check ogfGoal = true := by decide +kernel

/-- The same circuit and the same slots, in EGF. -/
def egfSecond : Streams.Circuit .egf 2 1 1 :=
  .compose (.unary (.derivative 1)) (.unary (.derivative 1))

def egfOutput : Observation .egf 2 1 :=
  .ofManifest ⟨axes, !["u_xx"], [⟨0, ![0, 0]⟩, ⟨0, ![0, 1]⟩]⟩

def egfInput : Observation .egf 2 1 :=
  .ofManifest (lowered egfSecond !["u"] egfOutput.manifest (by decide +kernel)).inputs

/-- The EGF lowering reads the same halo… -/
example : egfInput.context.names = spaceInput.context.names := by decide +kernel

def egfGoal : Goal :=
  leafGoal egfSecond egfInput egfOutput
    (equals (egfInput.context.var "u[t^0, x^2]" (by decide +kernel)) 1)
    (equals (egfOutput.context.var "u_xx[t^0, x^0]" (by decide +kernel)) 2)

/-- …but the raw EGF coefficients carry no factor: the OGF certificate fails… -/
example : EntailmentCertificate.check egfGoal ogfCertificate = false := by decide +kernel

/-- …and the claim is refuted: `u_xx[x^0] = u[x^2] = 1`. -/
example : refutes egfGoal [("u[t^0, x^2]", 1), ("u[t^0, x^3]", 0)] = true := by decide +kernel
example : refutes ogfGoal [("u[t^0, x^2]", 1), ("u[t^0, x^3]", 0)] = false := by decide +kernel

/-- The refutation reaches the root: `bump` has `u[x^2] = 1` and nothing else. -/
theorem egf_root_refuted :
    ¬ StreamHoare (fun x => x = ![bump]) egfSecond
      (egfOutput.Observes
        (equals (egfOutput.context.var "u_xx[t^0, x^0]" (by decide +kernel)) 2)) := by
  refine refutes_root (lowered_ok _ _ _ (by decide +kernel)) egfInput rfl
    (antecedent := equals (egfInput.context.var "u[t^0, x^2]" (by decide +kernel)) 1)
    (answer := [("u[t^0, x^2]", 1), ("u[t^0, x^3]", 0)]) (by decide +kernel) ![bump] rfl ?_
  intro i
  have values : ∀ i, (Syntax.Context.valueOf [("u[t^0, x^2]", 1), ("u[t^0, x^3]", 0)]
      (egfInput.context.name i)).getD 0 = ![1, 0] (Fin.cast (by decide +kernel) i) := by
    decide +kernel
  rw [values]
  fin_cases i
  · rw [egfInput.point_of_slot (by decide +kernel : egfInput.slot _ = ⟨0, ![0, 2]⟩)]
    simp [bump]
  · rw [egfInput.point_of_slot (by decide +kernel : egfInput.slot _ = ⟨0, ![0, 3]⟩)]
    have different : Degrees.toIndex ![0, 3] ≠ Degrees.toIndex ![0, 2] := fun same => by
      have := congrArg (· 1) same
      simp at this
    simp [bump, different]

/-! ### Axis swaps -/

/-- Differentiating along `t` instead of `x`. -/
def timeSecond : Streams.Circuit .ogf 2 1 1 :=
  .compose (.unary (.derivative 0)) (.unary (.derivative 0))

def timeInput : Observation .ogf 2 1 :=
  .ofManifest (lowered timeSecond !["u"] spaceOutput.manifest (by decide +kernel)).inputs

/-- The halo moves to the other axis, and the old names no longer resolve, so a
leaf written for `∂²/∂x²` cannot even be posed for `∂²/∂t²`. -/
example : timeInput.context.names = ["u[t^2, x^0]", "u[t^2, x^1]"] := by decide +kernel
example : (timeInput.context.position? "u[t^0, x^2]").isSome = false := by decide +kernel

/-- The manifest's axis order is part of every name: listed as `[x, t]`, the
same degree vectors are other coefficients, and the `[t, x]` names are gone. -/
def swappedAxes : Observation .ogf 2 1 :=
  .ofManifest ⟨!["x", "t"], !["u_xx"], [⟨0, ![0, 0]⟩, ⟨0, ![0, 1]⟩]⟩

example : swappedAxes.context.names = ["u_xx[x^0, t^0]", "u_xx[x^0, t^1]"] := by decide +kernel
example : (swappedAxes.context.position? "u_xx[t^0, x^1]").isSome = false := by decide +kernel

/-! ### Manifest swaps -/

/-- The output slots in the other order. -/
def reordered : Observation .ogf 2 1 :=
  .ofManifest ⟨axes, !["u_xx"], [⟨0, ![0, 1]⟩, ⟨0, ![0, 0]⟩]⟩

/-- Written by name, the claim still reads `u_xx[t^0, x^0]` and still checks… -/
example : spaceCertificate.check
    (leafGoal secondDerivative spaceInput reordered spaceAntecedent
      (.atom .ge (reordered.context.var "u_xx[t^0, x^0]" (by decide +kernel)))) = true := by
  decide +kernel

/-- …but a claim written by position now reads `u_xx[t^0, x^1] = 6 · u[t^0, x^3]`,
which the antecedent does not constrain: the certificate fails and a
counterexample appears. -/
def positional : Goal :=
  leafGoal secondDerivative spaceInput reordered spaceAntecedent (.atom .ge (.var ⟨0, by decide⟩))

example : spaceCertificate.check positional = false := by decide +kernel
example : refutes positional [("u[t^0, x^2]", 0), ("u[t^0, x^3]", -1)] = true := by
  decide +kernel

/-- A hand-written input observation with the halo in the other order is not the
lowering's: `leaf_hoare` needs the slots to be equal, and they are not. -/
def reversedHalo : Observation .ogf 2 1 :=
  .ofManifest ⟨axes, !["u"], [⟨0, ![0, 3]⟩, ⟨0, ![0, 2]⟩]⟩

example : reversedHalo.manifest.slots ≠ spaceLowered.inputs.slots := by decide +kernel

/-- Renaming the input port renames every coefficient. -/
def renamedPort : Observation .ogf 2 1 :=
  .ofManifest ⟨axes, !["v"], spaceLowered.inputs.slots⟩

example : (renamedPort.context.position? "u[t^0, x^2]").isSome = false := by decide +kernel

/-- An observation cannot name a slot twice: its context would repeat a name. -/
example : ¬ (slotNames (⟨axes, !["u"], [⟨0, ![0, 2]⟩, ⟨0, ![0, 2]⟩]⟩ :
    Manifest .ogf 1 2)).Nodup := by
  decide +kernel

/-! ### An altered initial profile -/

/-- The certificate for the unaltered profile still checks — it is a leaf fact
about coefficients — but under the altered profile the root claim is refuted
(`altered_profile_refuted`), because the lift needs the leaf antecedent to
follow from the precondition, and `boundary[t^0, x^2] = 1` does not follow from
the altered one. -/
example : heatCertificate.check heatGoal = true := by decide +kernel
example : ¬ StreamHoare alteredAdmitted circuit (heatOutput.Observes (equals outSpace 1)) :=
  altered_profile_refuted

/-! ### A finite observation is not a full stream -/

/-- `x² + 2t` with an extra `t²` coefficient. -/
noncomputable def longerTail : Stream 2 :=
  fun k => heat k + if k = Degrees.toIndex ![2, 0] then 1 else 0

/-- **Observed coefficients never determine the stream.** The output
`[2, x² + 2t + t²]` satisfies the whole observed heat claim, yet it is not the
output `[2, x² + 2t]` that task 018's `heat_contract` gives. -/
theorem observed_is_not_full :
    heatOutput.Observes heatPost ![two, longerTail] ∧ ![two, longerTail] ≠ ![two, heat] := by
  have actual : circuit.value ![heat, boundary, 0] = ![two, heat] :=
    (Examples.FormalHeatContract.heat_contract _ ⟨rfl, fun _ _ => rfl⟩).2.1
  have observed := (heat_observed ![heat, boundary, 0] ⟨rfl, fun _ _ => rfl⟩).2
  rw [actual] at observed
  refine ⟨(heatOutput.observes_congr heatPost ?_).mpr observed, ?_⟩
  · intro s member
    have away : ∀ s ∈ heatOutput.manifest.slots, s.degrees ≠ ![2, 0] := by decide +kernel
    have outside : s.degrees.toIndex ≠ Degrees.toIndex ![2, 0] :=
      fun same => away s member (Degrees.toIndex_injective same)
    refine Fin.cases ?_ (fun j => ?_) s.port
    · rfl
    · fin_cases j
      simp [longerTail, outside]
  · intro same
    have := congrFun (congrFun same 1) (Degrees.toIndex ![2, 0])
    simp [longerTail, heat] at this

/-! ### Axiom policy -/

/--
info: 'Gimle.Forseti.StreamObservation.lower_spec'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lower_spec
/--
info: 'Gimle.Forseti.StreamObservation.lift'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lift
/--
info: 'Gimle.Forseti.StreamObservation.leaf_hoare'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms leaf_hoare
/--
info: 'Gimle.Forseti.StreamObservation.lift_certificate'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms lift_certificate
/--
info: 'Gimle.Forseti.StreamObservation.observes_value'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms observes_value
/--
info: 'Gimle.Forseti.StreamObservation.refutes_root'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms refutes_root
/--
info: 'Gimle.Forseti.Examples.StreamObservation.space_nonneg'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms space_nonneg
/--
info: 'Gimle.Forseti.Examples.StreamObservation.halo_changes_output'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms halo_changes_output
/--
info: 'Gimle.Forseti.Examples.StreamObservation.heat_observed'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms heat_observed
/--
info: 'Gimle.Forseti.Examples.StreamObservation.weak_root_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms weak_root_holds
/--
info: 'Gimle.Forseti.Examples.StreamObservation.altered_profile_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms altered_profile_refuted
/--
info: 'Gimle.Forseti.Tests.StreamObservation.egf_root_refuted'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms egf_root_refuted
/--
info: 'Gimle.Forseti.Tests.StreamObservation.observed_is_not_full'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms observed_is_not_full

end Gimle.Forseti.Tests.StreamObservation
