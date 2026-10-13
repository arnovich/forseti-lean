import Gimle.Forseti.Driven
import Gimle.Forseti.Trajectory
import Gimle.Forseti.Examples.ForcedDecay
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The driven model of `Examples/ForcedDecay.lean` as one well-posed contract.

The compiled field is `dx := (du + u) − x` over `[u, du, x]`, with `x(0) = 0`.
For a driver signal that asgard admits — `u` continuous on `t ≥ 0`, `du` its
actual derivative there (`Evolution.Admitted`) — `y = x − u` has `y' = −y`, so
the unique solution is `x(t) = u(t) − u(0)·e^(−t)`. If `u` stays in `[−B, B]`
then `|x| ≤ 2B` at every `t ≥ 0` (`contract_within`); `driven_contract` is
`B = 1`.

The contract is about the original compiled circuit: the driven feedback, with
the driver wires forwarded beside it to the compiled observation circuit, which
reads `[u, du, x]` (`observed`, built by `Driven.forwarded`). Its precondition
binds the drivers — admitted, and bounded — and the initial wire; it is never
`fun _ => True`. `feedback_reads` ties the relation to asgard's own
`DrivenModel.Realizes`.

`witness_input_admitted` shows the precondition is satisfiable; `one_refuted`
that `1` is not a bound (under `u = cos` the output reaches `−1 − e^(−π)` at
`t = π`); and `bound_needed` that the driver bound cannot be dropped: an
admitted `u = 3` takes the output past `2`. -/
namespace Gimle.Forseti.Examples.ForcedDecayContract

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Model
open Gimle.Forseti.Examples.ForcedDecay

/-! ### The analytic core -/

/-- **`x' = a(t) − x` has at most one solution from a given start on `t ≥ 0`.**
The difference `z = f − g` has `z' = −z`, so `z·eᵗ` has zero derivative and
keeps its value `0` at the start. -/
theorem forced_unique {a f g : ℝ → ℝ} (start : f 0 = g 0)
    (hf : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt f (a t - f t) (Set.Ici 0) t)
    (hg : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt g (a t - g t) (Set.Ici 0) t) :
    Set.EqOn f g (Set.Ici 0) := by
  set w : ℝ → ℝ := fun t => (f t - g t) * Real.exp t with hw_def
  have hw : ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt w 0 (Set.Ici 0) t := by
    intro t ht
    have := ((hf t ht).sub (hg t ht)).mul (Real.hasDerivAt_exp t).hasDerivWithinAt
    exact this.congr_deriv (by simp only [Pi.sub_apply]; ring)
  intro T hT
  have hcont : ContinuousOn w (Set.Icc 0 T) := fun t ht =>
    ((hw t ht.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
  have hderiv : ∀ x ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt w 0 (Set.Ici x) x := fun x hx =>
    (hw x hx.1).mono (Set.Ici_subset_Ici.2 hx.1)
  have hconst := constant_of_has_deriv_right_zero hcont hderiv T ⟨hT, le_refl T⟩
  simp only [hw_def, start, sub_self, zero_mul] at hconst
  have hexp : Real.exp T ≠ 0 := (Real.exp_pos T).ne'
  have : f T - g T = 0 := by
    rcases mul_eq_zero.mp hconst with h | h
    · exact h
    · exact absurd h hexp
  linarith

/-! ### The observed circuit -/

/-- The driven feedback, with the drivers forwarded beside it to the compiled
observation circuit, which reads `[u, du, x]`. -/
def observed := Driven.forwarded compiled.feedback compiled.outputs.circuit

theorem observed_rel (input : Signal (width + states)) (output) :
    observed.Rel evolution.time input output ↔
      ∃ state, compiled.feedback.Rel evolution.time input state ∧
        output = fun t => compiled.outputs.circuit.run
          (pointAppend (signalLeft input t) (state t)) :=
  Driven.forwarded_rel _ _ _ input output

/-! ### The precondition -/

/-- The driver `u` stays in `[−B, B]` on the domain. -/
def uBand (B : ℝ) (d : Signal width) : Prop :=
  ∀ t ∈ evolution.time.domain, |d t uIndex| ≤ B

/-- Admitted by asgard, and bounded by `B`. -/
def bounded (B : ℝ) (d : Signal width) : Prop :=
  evolution.Admitted drivers d ∧ uBand B d

/-- Inputs: admitted drivers bounded by `B`, and the initial wire starting at
`x(0)`. -/
def admittedWithin (B : ℝ) : SignalPredicate (width + states) :=
  Initialized evolution.time (bounded B) (· = compiled.initial)

/-- The contract's precondition: `|u| ≤ 1`. -/
def admitted : SignalPredicate (width + states) := admittedWithin 1

/-- Inputs with admitted drivers and no bound on them. -/
def admittedOnly : SignalPredicate (width + states) :=
  Initialized evolution.time (evolution.Admitted drivers) (· = compiled.initial)

/-! ### The feedback, read as an equation -/

/-- The compiled rate at `[u, du, x]` is `(du + u) − x`. -/
theorem field_rate (d : Point width) (x : Point states) :
    (compiled.rates.expressions xState).eval (pointAppend d x) =
      (d duIndex + d uIndex) - x xState := by
  rw [rates_expressions, sub_eq_add_neg]
  rfl

theorem origin : evolution.time.start = 0 := by simp [Evolution.time, evolution]

/-- For an input whose initial wire starts at `x(0)`, the driven feedback
relates exactly the solutions of `x(0) = 0`, `x' = (du + u) − x` on `t ≥ 0`,
read off the compiled field. -/
theorem feedback_iff (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (state : Signal states) :
    compiled.feedback.Rel evolution.time input state ↔
      state 0 xState = 0 ∧ ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt (fun t => state t xState)
          ((signalLeft input t duIndex + signalLeft input t uIndex) - state t xState)
          (Set.Ici 0) t := by
  unfold DrivenModel.feedback
  rw [close_rel_reads_start, start, close_correct]
  rw [domain_eq, origin, initial_eq]
  simp only [DrivenModel.field_correct]
  constructor
  · rintro ⟨-, hstart, hderiv⟩
    refine ⟨by rw [hstart]; rfl, fun t ht => ?_⟩
    simpa only [field_rate] using hderiv t ht xState
  · rintro ⟨hstart, hderiv⟩
    refine ⟨by simp [Evolution.time], ?_, fun t ht i => ?_⟩
    · funext i
      rw [state_index i]
      simpa [xState] using hstart
    · rw [state_index i, field_rate]
      exact hderiv t ht

/-- The constant initial wire starts at `x(0)`. -/
theorem constant_start (d : Signal width) :
    signalRight (signalAppend d fun _ => compiled.initial) evolution.time.start =
      compiled.initial := by
  rw [signalRight_append]

/-- **The contract's relation is asgard's.** For admitted drivers and an initial
wire starting at `x(0)`, the feedback relates exactly the states asgard's
`DrivenModel.Realizes` accepts for those drivers. -/
theorem feedback_reads (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (admit : evolution.Admitted drivers (signalLeft input)) (state : Signal states) :
    compiled.feedback.Rel evolution.time input state ↔
      compiled.Realizes (signalLeft input) state := by
  rw [DrivenModel.Realizes, and_iff_right admit, feedback_iff input start,
    feedback_iff _ (constant_start _), signalLeft_append]

/-! ### The unique solution -/

/-- An admitted driver `u` has its derivative port `du` as its derivative. -/
theorem u_deriv {d : Signal width} (admit : evolution.Admitted drivers d) :
    ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt (fun t => d t uIndex) (d t duIndex) (Set.Ici 0) t := by
  obtain ⟨i, hi, -, hder⟩ := admit ⟨"driver-u", some "driver-du"⟩ (by simp [drivers])
  rw [index_u, Option.some.injEq] at hi
  subst hi
  obtain ⟨j, hj, hjd⟩ := hder "driver-du" rfl
  rw [index_du, Option.some.injEq] at hj
  subst hj
  intro t ht
  rw [← domain_eq] at ht ⊢
  exact hjd t ht

/-- The witness: `x(t) = u(t) − u(0)·e^(−t)`. -/
noncomputable def solution (d : Signal width) : Signal states :=
  fun t _ => d t uIndex - d 0 uIndex * Real.exp (-t)

theorem solution_deriv {d : Signal width} (admit : evolution.Admitted drivers d) :
    ∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt (fun t => solution d t xState)
      ((d t duIndex + d t uIndex) - solution d t xState) (Set.Ici 0) t := by
  intro t ht
  have decay := ((hasDerivAt_neg t).exp.const_mul (d 0 uIndex)).hasDerivWithinAt
    (s := Set.Ici 0)
  have := (u_deriv admit t ht).sub decay
  refine this.congr_deriv ?_
  simp only [solution]
  ring

/-- **Admitted drivers are realized**: asgard's `Realizes` holds of the
closed-form solution, so no admitted driver is left without a state. -/
theorem compiled_exists {d : Signal width} (admit : evolution.Admitted drivers d) :
    ∃ state, compiled.Realizes d state := by
  refine ⟨solution d, admit, ?_⟩
  rw [feedback_iff _ (constant_start d), signalLeft_append]
  exact ⟨by simp [solution], solution_deriv admit⟩

/-- An input with admitted drivers and the declared start has an output. -/
theorem realized (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (admit : evolution.Admitted drivers (signalLeft input)) :
    ∃ output, observed.Rel evolution.time input output :=
  ⟨_, (observed_rel input _).2 ⟨solution (signalLeft input),
    (feedback_iff input start _).2 ⟨by simp [solution], solution_deriv admit⟩, rfl⟩⟩

/-- **Every related output is `u(t) − u(0)·e^(−t)` on `t ≥ 0`.** -/
theorem output_value (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (admit : evolution.Admitted drivers (signalLeft input)) (output)
    (related : observed.Rel evolution.time input output) :
    ∀ t ∈ Set.Ici (0 : ℝ), output t xIndex =
      signalLeft input t uIndex - signalLeft input 0 uIndex * Real.exp (-t) := by
  obtain ⟨state, hstate, rfl⟩ := (observed_rel input output).1 related
  obtain ⟨hstart, hderiv⟩ := (feedback_iff input start state).1 hstate
  have same := forced_unique (a := fun t => signalLeft input t duIndex + signalLeft input t uIndex)
    (f := fun t => state t xState) (g := fun t => solution (signalLeft input) t xState)
    (by simp [hstart, solution]) hderiv (solution_deriv admit)
  intro t ht
  show compiled.outputs.circuit.run (pointAppend (signalLeft input t) (state t)) xIndex = _
  rw [x_at]
  change state t xState = _
  exact same ht

/-- The output starts at the declared `x(0) = 0`. -/
theorem output_at_start (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (admit : evolution.Admitted drivers (signalLeft input)) (output)
    (related : observed.Rel evolution.time input output) : output 0 xIndex = 0 := by
  rw [output_value input start admit output related 0 Set.self_mem_Ici]
  simp

/-! ### The contract -/

/-- **The driven feedback with its observation is a well-posed contract**: under
admitted drivers with `|u| ≤ B`, the output stays in `[−2B, 2B]`. -/
theorem contract_within (B : ℝ) :
    Contract observed evolution.time (admittedWithin B)
      (Always evolution.time fun observation =>
        -(2 * B) ≤ observation xIndex ∧ observation xIndex ≤ 2 * B) where
  realizable input admit := realized input admit.2 admit.1.1
  unique input admit first second hfirst hsecond := by
    intro t ht
    obtain ⟨s1, h1, rfl⟩ := (observed_rel input first).1 hfirst
    obtain ⟨s2, h2, rfl⟩ := (observed_rel input second).1 hsecond
    obtain ⟨start1, deriv1⟩ := (feedback_iff input admit.2 s1).1 h1
    obtain ⟨start2, deriv2⟩ := (feedback_iff input admit.2 s2).1 h2
    rw [domain_eq] at ht
    have same := forced_unique (f := fun t => s1 t xState) (g := fun t => s2 t xState)
      (by rw [start1, start2]) deriv1 deriv2 ht
    have states_eq : s1 t = s2 t := by
      funext i
      rw [state_index i]
      exact same
    simp only [states_eq]
  holds input admit output related := by
    intro t ht
    rw [domain_eq] at ht
    have value := output_value input admit.2 admit.1.1 output related t ht
    have hu : |signalLeft input t uIndex| ≤ B := admit.1.2 t (by rw [domain_eq]; exact ht)
    have hu0 : |signalLeft input 0 uIndex| ≤ B :=
      admit.1.2 0 (by rw [domain_eq]; exact Set.self_mem_Ici)
    have e0 : 0 < Real.exp (-t) := Real.exp_pos _
    have e1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [Set.mem_Ici.1 ht])
    rw [value]
    obtain ⟨lo, hi⟩ := abs_le.1 hu
    obtain ⟨lo0, hi0⟩ := abs_le.1 hu0
    have p1 := mul_nonneg (by linarith : 0 ≤ signalLeft input 0 uIndex + B) e0.le
    have p2 := mul_nonneg (by linarith : 0 ≤ B - signalLeft input 0 uIndex) e0.le
    have p3 := mul_nonneg (by linarith : 0 ≤ B) (by linarith : 0 ≤ 1 - Real.exp (-t))
    constructor <;> nlinarith

/-- The contract at `B = 1`: `|u| ≤ 1` keeps `|x| ≤ 2`. -/
theorem driven_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        -2 ≤ observation xIndex ∧ observation xIndex ≤ 2) := by
  have within := contract_within 1
  rw [show (2 : ℝ) * 1 = 2 by norm_num] at within
  exact within

/-! ### The precondition is satisfiable, and neither part of it is idle -/

/-- A driver with `du` the derivative of a continuous `u` is admitted. -/
theorem admitted_of {d : Signal width} (hcont : Continuous fun t => d t uIndex)
    (hderiv : ∀ t, HasDerivAt (fun t => d t uIndex) (d t duIndex) t) :
    evolution.Admitted drivers d := by
  intro b hb
  simp only [drivers, List.mem_singleton] at hb
  subst hb
  refine ⟨uIndex, index_u, hcont.continuousOn, fun port hp => ?_⟩
  simp only [Option.some.injEq] at hp
  subst hp
  exact ⟨duIndex, index_du, fun t _ => (hderiv t).hasDerivWithinAt⟩

/-- `u = sin`, `du = cos`. -/
noncomputable def sinDrivers : Signal width :=
  fun t i => if i.val = 0 then Real.sin t else Real.cos t

/-- `u = cos`, `du = −sin`. -/
noncomputable def cosDrivers : Signal width :=
  fun t i => if i.val = 0 then Real.cos t else -Real.sin t

/-- `u = 3`, `du = 0`. -/
noncomputable def threeDrivers : Signal width :=
  fun _ i => if i.val = 0 then 3 else 0

/-- The drivers `d` with the constant initial wire. -/
noncomputable def withInitial (d : Signal width) : Signal (width + states) :=
  signalAppend d fun _ => compiled.initial

/-- The satisfying input: `u = sin`. -/
noncomputable def witnessInput : Signal (width + states) := withInitial sinDrivers

theorem sin_admitted : evolution.Admitted drivers sinDrivers :=
  admitted_of (by simpa [sinDrivers, uIndex] using Real.continuous_sin)
    (fun t => by simpa [sinDrivers, uIndex, duIndex] using Real.hasDerivAt_sin t)

theorem cos_admitted : evolution.Admitted drivers cosDrivers :=
  admitted_of (by simpa [cosDrivers, uIndex] using Real.continuous_cos)
    (fun t => by simpa [cosDrivers, uIndex, duIndex] using Real.hasDerivAt_cos t)

theorem three_admitted : evolution.Admitted drivers threeDrivers :=
  admitted_of (by simpa [threeDrivers, uIndex] using continuous_const)
    (fun t => by simpa [threeDrivers, uIndex, duIndex] using hasDerivAt_const t (3 : ℝ))

/-- **The precondition is satisfiable**, so the contract is not vacuous. -/
theorem witness_input_admitted : admitted witnessInput := by
  refine ⟨⟨?_, fun t _ => ?_⟩, constant_start _⟩
  · simpa [witnessInput, withInitial] using sin_admitted
  · simpa [witnessInput, withInitial, sinDrivers, uIndex] using Real.abs_sin_le_one t

theorem cos_input_admitted : admitted (withInitial cosDrivers) := by
  refine ⟨⟨?_, fun t _ => ?_⟩, constant_start _⟩
  · simpa [withInitial] using cos_admitted
  · simpa [withInitial, cosDrivers, uIndex] using Real.abs_cos_le_one t

/-- **One is not a bound.** Under `u = cos`, the output reaches
`cos π − e^(−π) = −1 − e^(−π)` at `t = π`. -/
theorem one_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation =>
        -1 ≤ observation xIndex ∧ observation xIndex ≤ 1) := by
  intro holds
  have admit := cos_input_admitted
  obtain ⟨output, related⟩ := driven_contract.realizable _ admit
  have inDomain : Real.pi ∈ evolution.time.domain := by
    rw [domain_eq]; exact Set.mem_Ici.2 Real.pi_pos.le
  have low := (holds _ admit output related Real.pi inDomain).1
  rw [output_value _ admit.2 admit.1.1 output related Real.pi (Set.mem_Ici.2 Real.pi_pos.le)]
    at low
  simp [withInitial, cosDrivers, uIndex] at low
  linarith [Real.exp_pos (-Real.pi)]

/-- **The driver bound is needed.** Without it the band fails: the admitted
`u = 3` gives `x(2) = 3 − 3·e^(−2) > 2`, since `e² > 3`. -/
theorem bound_needed :
    ¬ Holds observed evolution.time admittedOnly
      (Always evolution.time fun observation =>
        -2 ≤ observation xIndex ∧ observation xIndex ≤ 2) := by
  intro holds
  have admit : admittedOnly (withInitial threeDrivers) :=
    ⟨by simpa [withInitial] using three_admitted, constant_start _⟩
  obtain ⟨output, related⟩ := realized _ admit.2 admit.1
  have two : (2 : ℝ) ∈ Set.Ici 0 := Set.mem_Ici.2 (by norm_num)
  have high := (holds _ admit output related 2 (by rw [domain_eq]; exact two)).2
  rw [output_value _ admit.2 admit.1 output related 2 two] at high
  simp [withInitial, threeDrivers, uIndex] at high
  have grow : (2 : ℝ) + 1 < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
  have prod : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-2)]

#print axioms forced_unique
#print axioms observed_rel
#print axioms feedback_iff
#print axioms feedback_reads
#print axioms compiled_exists
#print axioms contract_within
#print axioms driven_contract
#print axioms witness_input_admitted
#print axioms one_refuted
#print axioms bound_needed

end Gimle.Forseti.Examples.ForcedDecayContract
