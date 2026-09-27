import Gimle.Forseti.Examples.DisturbedFeedback
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Regression contract for the bottom-up disturbed-feedback proof. -/

namespace Gimle.Forseti.Tests.DisturbedFeedback

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open Gimle.Forseti.Examples.DisturbedFeedback

/-- The root theorem includes existence, uniqueness and the visible output bound. -/
example (time : TimeDomain) :
    Contract (observed time.axis) time (admitted time)
      (Always time fun y => |y 0| ≤ 1) := output_contract time

/-- A nonzero initial state on the invariant boundary is admitted at any start. -/
def boundaryInput : Signal (1 + 2) := signalAppend (fun _ _ => 0) (fun _ => ![1, 0])

theorem boundary_admitted (time : TimeDomain) : admitted time boundaryInput := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [boundaryInput] using
      (continuous_const : Continuous (fun _ : ℝ => (fun _ : Fin 1 => (0 : ℝ))))
  · intro t _
    norm_num [boundaryInput, signalLeft, pointLeft, signalAppend, pointAppend]
  · norm_num [boundaryInput, signalRight, pointRight, signalAppend, pointAppend, energy]

/-- The nonempty input class has an actual safe output, not just a partial claim. -/
example (time : TimeDomain) : ∃ output, (observed time.axis).Rel time boundaryInput output ∧
    Always time (fun y => |y 0| ≤ 1) output :=
  (output_contract time).exists_safe _ (boundary_admitted time)

/-- A nonzero, time-varying disturbance belongs to the proved input class. -/
example (time : TimeDomain) : ∃ output, (observed time.axis).Rel time
    (signalAppend (fun t _ => Real.sin t) (fun _ => ![1, 0])) output ∧
    Always time (fun y => |y 0| ≤ 1) output := by
  apply (output_contract time).exists_safe
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [signalLeft_append] using
      (continuous_pi fun _ : Fin 1 => Real.continuous_sin)
  · intro t _
    simpa only [signalLeft_append] using Real.abs_sin_le_one t
  · norm_num [signalRight, pointRight, signalAppend, pointAppend, energy]

/-- The tempting unweighted circle has an outward-pointing state under d = 1.
This refutes that candidate certificate, not the root safety claim. -/
example : (3 / 5 : ℝ)^2 + (4 / 5 : ℝ)^2 = 1 ∧
    0 < 2 * (3 / 5 : ℝ) * componentA.run ![3 / 5, 4 / 5, 1] 0 +
      2 * (4 / 5 : ℝ) * componentB.run ![4 / 5, 3 / 5] 0 := by
  norm_num

/-- A continuous input of size two is outside the disturbance contract. -/
example (time : TimeDomain) :
    ¬ admitted time (signalAppend (fun _ _ => 2) (fun _ => ![0, 0])) := by
  intro h
  have := h.1.2 time.start (show time.start ∈ time.domain by simp [TimeDomain.domain])
  norm_num [signalLeft, pointLeft, signalAppend, pointAppend] at this

/-- An unsafe initial state cannot be admitted even with a zero disturbance. -/
example (time : TimeDomain) :
    ¬ admitted time (signalAppend (fun _ _ => 0) (fun _ => ![2, 0])) := by
  intro h
  have := h.2
  norm_num [signalRight, pointRight, signalAppend, pointAppend, energy] at this

/-- Initial wires can vary after the start: the actual loop only reads their start value. -/
example (time : TimeDomain) : ∃ state, (loop time.axis).Rel time
    (signalAppend (fun _ _ => 0)
      (fun t => if t = time.start then ![1, 0] else ![100, 100])) state := by
  apply (loop_contract time).realizable
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using
      (continuous_const : Continuous (fun _ : ℝ => (fun _ : Fin 1 => (0 : ℝ))))
  · intro t _
    norm_num [signalLeft, pointLeft, signalAppend, pointAppend]
  · simp [signalRight, pointRight, signalAppend, pointAppend, energy]

/-- The bound one cannot be replaced by one half for this admitted input class. -/
theorem half_refuted (time : TimeDomain) :
    ¬ Holds (observed time.axis) time (admitted time)
      (Always time fun y => |y 0| ≤ (1 / 2 : ℝ)) := by
  intro claim
  obtain ⟨state, realized⟩ := (loop_contract time).realizable _ (boundary_admitted time)
  have initial := ((loop_rel time boundaryInput state).mp realized).1
  have bounded := claim _ (boundary_admitted time)
    (fun t => projection.run (state t)) ⟨state, realized, rfl⟩
    time.start (show time.start ∈ time.domain by simp [TimeDomain.domain])
  change |projection.run (state time.start) 0| ≤ (1 / 2 : ℝ) at bounded
  rw [initial] at bounded
  norm_num [projection, boundaryInput, signalRight, pointRight, signalAppend, pointAppend] at bounded

/-- info: 'Gimle.Forseti.Examples.DisturbedFeedback.output_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms output_contract

/-- info: 'Gimle.Forseti.ForcedLinear.exists_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gimle.Forseti.ForcedLinear.exists_solution

/-- info: 'Gimle.Forseti.ForcedLinear.unique_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gimle.Forseti.ForcedLinear.unique_on

end Gimle.Forseti.Tests.DisturbedFeedback
