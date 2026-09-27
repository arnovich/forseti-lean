import Gimle.Forseti.Examples.ActiveSuspension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Root regression: independently specified initial and output regions,
with two interchangeable actuator dynamics. -/

namespace Gimle.Forseti.Tests.ActiveSuspension

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open Gimle.Forseti.Examples.ActiveSuspension

example (time : TimeDomain) :
    Contract (observed (actuator 2) time.axis) time (admitted time)
      (Always time safeOutputs) := standard_contract time

example (time : TimeDomain) :
    Contract (observed (actuator (5 / 2)) time.axis) time (admitted time)
      (Always time safeOutputs) := replacement_contract time

/-- A nonzero point on the independently specified initial ball. -/
noncomputable def boundaryInput : Signal 6 :=
  signalAppend (fun _ _ => 0) (fun _ => ![1 / 10, 0, 0, 0, 0])

theorem boundary_admitted (time : TimeDomain) : admitted time boundaryInput := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [boundaryInput] using
      (continuous_const : Continuous (fun _ : ℝ => (fun _ : Fin 1 => (0 : ℝ))))
  · intro t _
    norm_num [boundaryInput, signalLeft, pointLeft, signalAppend, pointAppend]
  · norm_num [boundaryInput, signalRight, pointRight, signalAppend, pointAppend,
      initialSize, Fin.sum_univ_succ]

/-- The admitted class is nonempty and has an actual safe output. -/
example (time : TimeDomain) : ∃ output,
    (observed (actuator 2) time.axis).Rel time boundaryInput output ∧
      Always time safeOutputs output :=
  (standard_contract time).exists_safe _ (boundary_admitted time)

/-- A time-varying road at the full admitted amplitude has a safe trajectory. -/
example (time : TimeDomain) : ∃ output, (observed (actuator (5 / 2)) time.axis).Rel time
    (signalAppend (fun t _ => Real.sin t / 1000) (fun _ => ![1 / 10, 0, 0, 0, 0])) output ∧
    Always time safeOutputs output := by
  apply (replacement_contract time).exists_safe
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [signalLeft_append] using
      (continuous_pi fun _ : Fin 1 => Real.continuous_sin.div_const 1000)
  · intro t _
    simp only [signalLeft_append, abs_div, show |(1000 : ℝ)| = 1000 by norm_num]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one t) (by norm_num)
  · norm_num [signalRight, pointRight, signalAppend, pointAppend, initialSize,
      Fin.sum_univ_succ]

/-- A road outside the fixed amplitude budget is not admitted. -/
example (time : TimeDomain) :
    ¬ admitted time (signalAppend (n := 1) (m := 5) (fun _ _ => 1 / 500) (fun _ _ => 0)) := by
  intro h
  have := h.1.2 time.start (show time.start ∈ time.domain by simp [TimeDomain.domain])
  norm_num [signalLeft, pointLeft, signalAppend, pointAppend] at this

/-- The initial ball cannot silently expand with a discovered certificate. -/
example (time : TimeDomain) :
    ¬ admitted time (signalAppend (fun _ _ => 0) (fun _ => ![1 / 5, 0, 0, 0, 0])) := by
  intro h
  have := h.2
  norm_num [signalRight, pointRight, signalAppend, pointAppend, initialSize,
    Fin.sum_univ_succ] at this

/-- Only the start value of the initial wires matters, even if they jump later. -/
example (time : TimeDomain) : ∃ state, (system (actuator 2) time.axis).Rel time
    (signalAppend (fun _ _ => 0)
      (fun t => if t = time.start then ![1 / 10, 0, 0, 0, 0] else fun _ => 100)) state := by
  apply (system_contract _ 2 (actuator_law 2) (Or.inl rfl) time).realizable
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using
      (continuous_const : Continuous (fun _ : ℝ => (fun _ : Fin 1 => (0 : ℝ))))
  · intro t _
    norm_num [signalLeft, pointLeft, signalAppend, pointAppend]
  · norm_num [signalRight, pointRight, signalAppend, pointAppend, initialSize,
      Fin.sum_univ_succ]

/-- These are distinct actuator dynamics, not two names for the same circuit. -/
example : (actuatorField 2).run ![1, 0] 0 ≠ (actuatorField (5 / 2)).run ![1, 0] 0 := by
  norm_num [actuatorField, Polynomial.Expr.eval]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A valid certificate for one rate cannot be replayed against the other rate.
The replacement has its own checked supply decomposition for the same storage. -/
example : ¬ CertificateData.slowSupply.Represents
    (supplyMatrix CertificateData.storage CertificateData.alpha CertificateData.beta (5 / 2)) := by
  unfold Gimle.Forseti.LinearEnergy.WeightedSquares.Represents
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Corrupting one square weight is rejected by the actual Lean validity predicate. -/
example : ¬ ({ CertificateData.positive with weight := fun _ => -1 } :
    Gimle.Forseti.LinearEnergy.WeightedSquares 5).Represents CertificateData.storage := by
  unfold Gimle.Forseti.LinearEnergy.WeightedSquares.Represents
  decide +kernel

/-- Actuator dynamics on a different named axis cannot realize this time domain. -/
example (input : Signal 2) (force : Signal 1) :
    ¬ (actuator 2 "other").Rel ⟨"time", 0⟩ input force := by
  unfold actuator
  rw [← signalAppend_parts (n := 1) (m := 1) input, close_rel]
  simp

/-- A deliberately discontinuous pre-start state, resting on the forward domain. -/
noncomputable def early : Signal 5 := fun t => if t < 0 then ![5, 0, 0, 0, 0] else fun _ => 0

/-- The hidden command really has a jump at the start, rather than cancelling. -/
example (t : ℝ) : command (plantState (early t)) = if t < 0 then -5 else 0 := by
  by_cases h : t < 0 <;> simp [early, h, command, plantState]

/-- The nested circuit permits arbitrary pre-start behavior; its hidden actuator
command is therefore not required to be globally continuous. -/
example : (system (actuator 2) "time").Rel ⟨"time", 0⟩ (fun _ _ => 0) early := by
  apply (system_law _ 2 (actuator_law 2) ⟨"time", 0⟩ _ _).mpr
  constructor
  · funext i
    simp [early, signalRight, pointRight]
  · intro t ht i
    have rest (s : ℝ) (hs : s ∈ (TimeDomain.mk "time" 0).domain) : early s i = 0 := by
      simp [early, not_lt.mpr (show 0 ≤ s from hs)]
    have zero : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) 0
        (TimeDomain.mk "time" 0).domain t := hasDerivWithinAt_const _ _ _
    have atTime : early t = fun _ => 0 := by
      funext j
      simp [early, not_lt.mpr (show 0 ≤ t from ht)]
    have velocity : rhs 2 0 (early t) i = 0 := by
      rw [atTime]
      fin_cases i <;> norm_num [rhs]
    rw [velocity]
    exact zero.congr rest (rest t ht)

/-- info: 'Gimle.Forseti.Examples.ActiveSuspension.output_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms output_contract

/-- info: 'Gimle.Forseti.Examples.ActiveSuspension.replacement_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms replacement_contract

/-- info: 'Gimle.Forseti.Dissipative.sublevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gimle.Forseti.Dissipative.sublevel

end Gimle.Forseti.Tests.ActiveSuspension
