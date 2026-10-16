import Gimle.Forseti.Dissipative
import Gimle.Forseti.Driven
import Gimle.Forseti.ForcedLinear
import Gimle.Forseti.Trajectory
import Gimle.Forseti.Examples.HedgedSpread
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The hedged exposure of `Examples/HedgedSpread.lean` as one well-posed contract
for every disturbance in a band.

The compiled field is `ds := (-s + -h) + d`, `dh := s + -h` over `[d, s, h]`,
from `s(0) = h(0) = 0`. For a driver `d` that asgard admits — continuous on
`t ≥ 0` (`Evolution.Admitted`; `d` has no derivative port) — and bounded by `B`
there, the quadratic `V = s² + h²` (`energy` below) satisfies `V' = -2V + 2sd`
along every solution, because the coupling between `s` and `h` is
skew-symmetric (`−h` in `s'`, `+s` in `h'`), so the cross terms cancel in `V'`.
Together with `|d| ≤ B` this gives `V' ≤ B² − V`, and `Dissipative.sublevel`
transports that inequality along every solution: `V ≤ B²` for all `t ≥ 0` from
`V(0) = 0`; hence `|s| ≤ B`
(`exposure_within`, `energy_within`). The contracts at `B = 1` are
`exposure_contract` and `energy_contract`. For `B < 0` the precondition is
unsatisfiable and the contracts hold vacuously; `zero_within` shows it is
satisfied for every `B ≥ 0`.

The statement is about every path, not a sample of them: any disturbance
continuous on `t ≥ 0` and inside the band, however it is chosen, keeps the
exposure inside the same bound. Existence comes from variation of constants on
the half-line (`ForcedLinear.exists_solution_on`); uniqueness from
`ForcedLinear.unique_on`. The bound is the
storage bound, not a sharp one: `half_refuted` shows only that halving it
fails, and at `B = 1` nothing between `1/2 + e^(−π/2)/2` and `1` is decided
here.

The contract is about the original compiled circuit: the driven feedback, with
the driver wire forwarded beside it to the compiled observation circuit, which
reads `[d, s, h]` (`observed`, built by `Driven.forwarded`). Its precondition
binds the driver — admitted, and bounded — and the initial wires; it is never
`fun _ => True`. `feedback_reads` ties the relation to asgard's own
`DrivenModel.Realizes`.

`witness_input_admitted` shows the precondition is satisfiable; `half_refuted`
that `1/2` is not a bound inside the band (under `d = 1` the exposure is
`1/2 + e^(−π/2)/2` at `t = π/2`, its first peak); and `bound_needed` that the
band cannot be dropped: the admitted `d = 3` gives `3/2 + 3e^(−π/2)/2 > 1`
there. -/
namespace Gimle.Forseti.Examples.HedgedSpreadContract

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Model
open Gimle.Forseti.Examples.HedgedSpread

/-! ### The observed circuit -/

/-- The driven feedback, with the driver forwarded beside it to the compiled
observation circuit, which reads `[d, s, h]`. -/
def observed := Driven.forwarded compiled.feedback compiled.outputs.circuit

/-- An output of `observed` is the observation of the input's driver and of a
state the feedback relates to the same input. -/
theorem observed_rel (input : Signal (width + states)) (output) :
    observed.Rel evolution.time input output ↔
      ∃ state, compiled.feedback.Rel evolution.time input state ∧
        output = fun t => compiled.outputs.circuit.run
          (pointAppend (signalLeft input t) (state t)) :=
  Driven.forwarded_rel _ _ _ input output

/-! ### The precondition -/

/-- The driver `d` stays in `[−B, B]` on the domain. -/
def dBand (B : ℝ) (d : Signal width) : Prop :=
  ∀ t ∈ evolution.time.domain, |d t dIndex| ≤ B

/-- Admitted by asgard, and bounded by `B`. -/
def bounded (B : ℝ) (d : Signal width) : Prop :=
  evolution.Admitted drivers d ∧ dBand B d

/-- Inputs: an admitted driver bounded by `B`, and the initial wires starting at
`(s(0), h(0)) = (0, 0)`. -/
def admittedWithin (B : ℝ) : SignalPredicate (width + states) :=
  Initialized evolution.time (bounded B) (· = compiled.initial)

/-- The precondition of both contracts at `B = 1`: an admitted driver with
`|d| ≤ 1`, from the declared start. -/
def admitted : SignalPredicate (width + states) := admittedWithin 1

/-- Inputs with an admitted driver and no bound on it. -/
def admittedOnly : SignalPredicate (width + states) :=
  Initialized evolution.time (evolution.Admitted drivers) (· = compiled.initial)

/-! ### The feedback, read as a forced linear system -/

/-- The homogeneous part of the field, `[[-1, -1], [1, -1]]` on `[s, h]`. -/
noncomputable def operator : Point 2 →L[ℝ] Point 2 :=
  LinearAnalysis.rationalOperator ![![-1, -1], ![1, -1]]

/-- The disturbance acts on `s` only. -/
def forcing (d : Signal width) : Signal 2 := fun t => ![d t dIndex, 0]

/-- The operator's first row at `[s, h]`, plus a forcing `v` on `s`. -/
theorem rate_zero (x : Point 2) (v : ℝ) : (operator x + ![v, 0]) 0 = -x 0 - x 1 + v := by
  simp [operator, LinearAnalysis.rationalOperator_apply, Fin.sum_univ_two]
  ring

/-- The operator's second row at `[s, h]`; the forcing does not reach `h`. -/
theorem rate_one (x : Point 2) (v : ℝ) : (operator x + ![v, 0]) 1 = x 0 - x 1 := by
  simp [operator, LinearAnalysis.rationalOperator_apply, Fin.sum_univ_two]
  ring

/-- The compiled rates at `[d, s, h]` are the operator applied to `[s, h]` plus
the disturbance on the first coordinate. -/
theorem field_forced (d : Point width) (x : Point states) (i : Fin 2) :
    (compiled.rates.expressions i).eval (pointAppend d x) =
      (operator x + ![d dIndex, 0]) i := by
  fin_cases i
  · dsimp only
    rw [Fin.zero_eta, rates_s, rate_zero]
    ring
  · dsimp only
    rw [Fin.mk_one, rates_h, rate_one]
    ring

/-- For an input whose initial wires start at `(0, 0)`, the driven feedback
relates exactly the solutions of the forced linear system on `t ≥ 0`, read off
the compiled field. -/
theorem feedback_iff (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (state : Signal states) :
    compiled.feedback.Rel evolution.time input state ↔
      state 0 = ![0, 0] ∧ ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
        HasDerivWithinAt (fun t => state t i)
          ((operator (state t) + forcing (signalLeft input) t) i) (Set.Ici 0) t := by
  unfold DrivenModel.feedback
  rw [close_rel_reads_start, start, close_correct]
  rw [domain_eq, origin, initial_eq]
  simp only [DrivenModel.field_correct]
  constructor
  · rintro ⟨-, hstart, hderiv⟩
    exact ⟨hstart, fun t ht i => (hderiv t ht i).congr_deriv (field_forced _ _ i)⟩
  · rintro ⟨hstart, hderiv⟩
    exact ⟨by simp [Evolution.time], hstart,
      fun t ht i => (hderiv t ht i).congr_deriv (field_forced _ _ i).symm⟩

/-- The constant initial wires start at `(0, 0)`. -/
theorem constant_start (d : Signal width) :
    signalRight (signalAppend d fun _ => compiled.initial) evolution.time.start =
      compiled.initial := by
  rw [signalRight_append]

/-- **The contract's relation is asgard's.** For an admitted driver and initial
wires starting at `(0, 0)`, the feedback relates exactly the states asgard's
`DrivenModel.Realizes` accepts for that driver. -/
theorem feedback_reads (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (admit : evolution.Admitted drivers (signalLeft input)) (state : Signal states) :
    compiled.feedback.Rel evolution.time input state ↔
      compiled.Realizes (signalLeft input) state := by
  rw [DrivenModel.Realizes, and_iff_right admit, feedback_iff input start,
    feedback_iff _ (constant_start _), signalLeft_append]

/-! ### Existence and uniqueness -/

/-- An admitted driver is continuous on the domain. -/
theorem d_continuousOn {d : Signal width} (admit : evolution.Admitted drivers d) :
    ContinuousOn (fun t => d t dIndex) (Set.Ici 0) := by
  obtain ⟨i, hi, hcont, -⟩ := admit ⟨"driver-d", none⟩ (by simp [drivers])
  rw [index_d, Option.some.injEq] at hi
  subst hi
  rwa [← domain_eq]

/-- The forcing of an admitted driver is continuous on the domain. -/
theorem forcing_continuousOn {d : Signal width} (admit : evolution.Admitted drivers d) :
    ContinuousOn (forcing d) (Set.Ici 0) := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · simpa [forcing] using d_continuousOn admit
  · simpa [forcing] using continuousOn_const (c := (0 : ℝ))

/-- A solution of the forced linear system exists on `t ≥ 0` from `(0, 0)`, for
every admitted driver. -/
theorem solution_exists {d : Signal width} (admit : evolution.Admitted drivers d) :
    ∃ state : Signal 2, state 0 = ![0, 0] ∧ ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
      HasDerivWithinAt (fun t => state t i) ((operator (state t) + forcing d t) i)
        (Set.Ici 0) t :=
  ForcedLinear.exists_solution_on operator (forcing d) 0 (forcing_continuousOn admit) ![0, 0]

/-- **Admitted drivers are realized**: asgard's `Realizes` holds of a solution,
so no admitted driver is left without a state. -/
theorem compiled_exists {d : Signal width} (admit : evolution.Admitted drivers d) :
    ∃ state, compiled.Realizes d state := by
  obtain ⟨state, hstate⟩ := solution_exists admit
  refine ⟨state, admit, ?_⟩
  rw [feedback_iff _ (constant_start d), signalLeft_append]
  exact hstate

/-- An input with an admitted driver and the declared start has an output. -/
theorem realized (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (admit : evolution.Admitted drivers (signalLeft input)) :
    ∃ output, observed.Rel evolution.time input output := by
  obtain ⟨state, hstate⟩ := solution_exists admit
  exact ⟨_, (observed_rel input _).2 ⟨state, (feedback_iff input start state).2 hstate, rfl⟩⟩

/-- Two states the feedback relates to the same input agree on `t ≥ 0`. -/
theorem unique_state (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial)
    (first second : Signal states)
    (hfirst : compiled.feedback.Rel evolution.time input first)
    (hsecond : compiled.feedback.Rel evolution.time input second) :
    Set.EqOn first second (Set.Ici 0) := by
  obtain ⟨i1, d1⟩ := (feedback_iff input start first).1 hfirst
  obtain ⟨i2, d2⟩ := (feedback_iff input start second).1 hsecond
  exact ForcedLinear.unique_on operator (forcing (signalLeft input)) 0 first second
    (i1.trans i2.symm) d1 d2

/-! ### The invariant -/

/-- The quadratic the second observation computes. -/
noncomputable def energy (x : Point 2) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- `0 ≤ V`. -/
theorem energy_nonneg (x : Point 2) : 0 ≤ energy x := by
  unfold energy
  positivity

/-- Along any solution `V' = -2V + 2sd`: the coupling terms cancel. -/
theorem energy_derivative (d : Signal width) (state : Signal 2)
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
      HasDerivWithinAt (fun t => state t i) ((operator (state t) + forcing d t) i)
        (Set.Ici 0) t)
    (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
    HasDerivWithinAt (fun t => energy (state t))
      (-2 * energy (state t) + 2 * state t 0 * d t dIndex) (Set.Ici 0) t := by
  refine (((hderiv t ht 0).pow 2).add ((hderiv t ht 1).pow 2)).congr_deriv ?_
  simp only [forcing]
  rw [rate_zero, rate_one]
  simp only [energy, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

/-- The algebraic leaf: `-2V + 2sd ≤ B² − V` whenever `|d| ≤ B`, because
`(s − d)² + h² + (B² − d²) ≥ 0`. -/
theorem storage_bound (s h d B : ℝ) (hd : |d| ≤ B) :
    -2 * (s ^ 2 + h ^ 2) + 2 * s * d ≤ B ^ 2 - (s ^ 2 + h ^ 2) := by
  obtain ⟨lo, hi⟩ := abs_le.mp hd
  nlinarith [sq_nonneg (s - d), sq_nonneg h,
    mul_nonneg (sub_nonneg.2 hi) (by linarith : 0 ≤ B + d)]

/-- The differential inequality transports through the integrators and the
trace (`Dissipative.sublevel`): `V ≤ B²` for all `t ≥ 0` from `V(0) = 0`. -/
theorem invariant (B : ℝ) (d : Signal width) (band : dBand B d) (state : Signal 2)
    (initial : state 0 = ![0, 0])
    (hderiv : ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
      HasDerivWithinAt (fun t => state t i) ((operator (state t) + forcing d t) i)
        (Set.Ici 0) t) :
    ∀ t ∈ Set.Ici (0 : ℝ), energy (state t) ≤ B ^ 2 := by
  have h := Dissipative.sublevel evolution.time (fun t => energy (state t))
    (fun t => -2 * energy (state t) + 2 * state t 0 * d t dIndex) 1 (B ^ 2)
    (by rw [domain_eq]; exact energy_derivative d state hderiv)
    (fun t ht => by rw [one_mul]; exact storage_bound _ _ _ _ (band t ht))
    (by rw [origin, initial]; simp [energy]; positivity)
  rwa [domain_eq] at h

/-! ### The outputs -/

/-- Every output reads `s` and `V` off a state the feedback relates to the input. -/
theorem output_value (input : Signal (width + states)) (output)
    (related : observed.Rel evolution.time input output) :
    ∃ state : Signal 2, compiled.feedback.Rel evolution.time input state ∧
      ∀ t, output t sIndex = state t 0 ∧ output t vIndex = energy (state t) := by
  obtain ⟨state, hstate, rfl⟩ := (observed_rel input output).1 related
  refine ⟨state, hstate, fun t => ⟨?_, ?_⟩⟩
  · dsimp only
    rw [s_at, append_s]
  · dsimp only
    rw [v_at, append_s, append_h, energy]

/-- The exposure starts at the declared `s(0) = 0`: no admission is needed for
the start value. -/
theorem output_at_start_s (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial) (output)
    (related : observed.Rel evolution.time input output) : output 0 sIndex = 0 := by
  obtain ⟨state, hstate, values⟩ := output_value input output related
  rw [(values 0).1, ((feedback_iff input start state).1 hstate).1]
  rfl

/-- The quadratic starts at the declared `V(0) = 0`. -/
theorem output_at_start_v (input : Signal (width + states))
    (start : signalRight input evolution.time.start = compiled.initial) (output)
    (related : observed.Rel evolution.time input output) : output 0 vIndex = 0 := by
  obtain ⟨state, hstate, values⟩ := output_value input output related
  rw [(values 0).2, ((feedback_iff input start state).1 hstate).1]
  simp [energy]

/-! ### The contracts -/

/-- Every input with an admitted driver bounded by `B` has an output. -/
theorem realizable_within (B : ℝ) : Realizable observed evolution.time (admittedWithin B) :=
  fun input admit => realized input admit.2 admit.1.1

/-- Two outputs of the same input agree on the domain. -/
theorem unique_within (B : ℝ) : Unique observed evolution.time (admittedWithin B) := by
  intro input admit first second hfirst hsecond t ht
  obtain ⟨s1, h1, rfl⟩ := (observed_rel input first).1 hfirst
  obtain ⟨s2, h2, rfl⟩ := (observed_rel input second).1 hsecond
  rw [domain_eq] at ht
  have same := unique_state input admit.2 s1 s2 h1 h2 ht
  simp only [same]

/-- **The exposure stays inside the band**: under an admitted driver with
`|d| ≤ B`, the output `s` stays in `[−B, B]`, for every such driver. -/
theorem exposure_within (B : ℝ) :
    Contract observed evolution.time (admittedWithin B)
      (Always evolution.time fun observation =>
        -B ≤ observation sIndex ∧ observation sIndex ≤ B) where
  realizable := realizable_within B
  unique := unique_within B
  holds input admit output related := by
    intro t ht
    rw [domain_eq] at ht
    obtain ⟨state, hstate, values⟩ := output_value input output related
    obtain ⟨initial, hderiv⟩ := (feedback_iff input admit.2 state).1 hstate
    have energy_le := invariant B (signalLeft input) admit.1.2 state initial hderiv t ht
    have hB : 0 ≤ B := (abs_nonneg _).trans
      (admit.1.2 0 (by rw [domain_eq]; exact Set.self_mem_Ici))
    simp only [energy] at energy_le
    rw [(values t).1]
    exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (state t 1)]) hB

/-- **The quadratic stays below the band's square**: `0 ≤ V ≤ B²`. -/
theorem energy_within (B : ℝ) :
    Contract observed evolution.time (admittedWithin B)
      (Always evolution.time fun observation =>
        0 ≤ observation vIndex ∧ observation vIndex ≤ B ^ 2) where
  realizable := realizable_within B
  unique := unique_within B
  holds input admit output related := by
    intro t ht
    rw [domain_eq] at ht
    obtain ⟨state, hstate, values⟩ := output_value input output related
    obtain ⟨initial, hderiv⟩ := (feedback_iff input admit.2 state).1 hstate
    rw [(values t).2]
    exact ⟨energy_nonneg _, invariant B (signalLeft input) admit.1.2 state initial hderiv t ht⟩

/-- The exposure contract at `B = 1`: `|d| ≤ 1` keeps `|s| ≤ 1`. -/
theorem exposure_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        -1 ≤ observation sIndex ∧ observation sIndex ≤ 1) :=
  exposure_within 1

/-- The quadratic contract at `B = 1`: `|d| ≤ 1` keeps `0 ≤ V ≤ 1`. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation vIndex ∧ observation vIndex ≤ 1) := by
  have within := energy_within 1
  rw [one_pow] at within
  exact within

/-! ### The precondition is satisfiable, and neither part of it is idle -/

/-- A driver continuous on `t ≥ 0` is admitted: `d` declares no derivative
port, so this is the whole of `Evolution.Admitted` here (`d_continuousOn` is
the converse). -/
theorem admitted_of {d : Signal width}
    (hcont : ContinuousOn (fun t => d t dIndex) (Set.Ici 0)) :
    evolution.Admitted drivers d := by
  intro b hb
  simp only [drivers, List.mem_singleton] at hb
  subst hb
  exact ⟨dIndex, index_d, by rwa [domain_eq], fun _ hp => nomatch hp⟩

/-- The zero driver is admitted. -/
theorem zero_admitted : evolution.Admitted drivers (fun _ _ => 0) :=
  admitted_of continuousOn_const

/-- The driver `d` with the constant initial wires. -/
noncomputable def withInitial (d : Signal width) : Signal (width + states) :=
  signalAppend d fun _ => compiled.initial

/-- `d = sin`. -/
noncomputable def sinDriver : Signal width := fun t _ => Real.sin t

/-- The constant driver `d = c`. -/
def constantDriver (c : ℝ) : Signal width := fun _ _ => c

/-- `sin` is admitted. -/
theorem sin_admitted : evolution.Admitted drivers sinDriver :=
  admitted_of (by simpa [sinDriver] using Real.continuous_sin.continuousOn)

/-- Every constant driver is admitted, whatever its size. -/
theorem constant_admitted (c : ℝ) : evolution.Admitted drivers (constantDriver c) :=
  admitted_of continuousOn_const

/-- For every `B ≥ 0` the zero driver satisfies the banded precondition, so no
contract above is vacuous there. -/
theorem zero_within {B : ℝ} (hB : 0 ≤ B) : admittedWithin B (withInitial fun _ _ => 0) :=
  ⟨⟨by simpa [withInitial] using zero_admitted, fun t _ => by simp [withInitial, hB]⟩,
    constant_start _⟩

/-- **The precondition is satisfiable**, so the contract is not vacuous. -/
theorem witness_input_admitted : admitted (withInitial sinDriver) := by
  refine ⟨⟨?_, fun t _ => ?_⟩, constant_start _⟩
  · simpa [withInitial] using sin_admitted
  · simpa [withInitial, sinDriver] using Real.abs_sin_le_one t

/-- The solution under the constant disturbance `c`:
`s = c/2 − (c/2)e^(−t)(cos t − sin t)`, `h = c/2 − (c/2)e^(−t)(cos t + sin t)`. -/
noncomputable def constantSolution (c : ℝ) : Signal 2 := fun t =>
  ![c / 2 - c / 2 * (Real.exp (-t) * (Real.cos t - Real.sin t)),
    c / 2 - c / 2 * (Real.exp (-t) * (Real.cos t + Real.sin t))]

/-- The closed form starts at `(0, 0)`. -/
theorem constantSolution_start (c : ℝ) : constantSolution c 0 = ![0, 0] := by
  funext i
  fin_cases i <;> simp [constantSolution]

/-- The closed form solves the system under the constant driver `c`. -/
theorem constantSolution_deriv (c t : ℝ) (i : Fin 2) :
    HasDerivAt (fun t => constantSolution c t i)
      ((operator (constantSolution c t) + forcing (constantDriver c) t) i) t := by
  have e : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  fin_cases i
  · refine ((hasDerivAt_const t (c / 2)).sub
      ((e.mul ((Real.hasDerivAt_cos t).sub (Real.hasDerivAt_sin t))).const_mul (c / 2))).congr_deriv ?_
    simp [operator, forcing, constantSolution, constantDriver,
      LinearAnalysis.rationalOperator_apply, Fin.sum_univ_two]
    ring
  · refine ((hasDerivAt_const t (c / 2)).sub
      ((e.mul ((Real.hasDerivAt_cos t).add (Real.hasDerivAt_sin t))).const_mul (c / 2))).congr_deriv ?_
    simp [operator, forcing, constantSolution, constantDriver,
      LinearAnalysis.rationalOperator_apply, Fin.sum_univ_two]
    ring

/-- Under the constant driver `c` every output's exposure is the closed form. -/
theorem constant_output (c : ℝ) (output)
    (related : observed.Rel evolution.time (withInitial (constantDriver c)) output)
    (t : ℝ) (ht : 0 ≤ t) :
    output t sIndex = c / 2 - c / 2 * (Real.exp (-t) * (Real.cos t - Real.sin t)) := by
  obtain ⟨state, hstate, values⟩ := output_value _ output related
  obtain ⟨initial, hderiv⟩ := (feedback_iff _ (constant_start _) state).1 hstate
  simp only [signalLeft_append] at hderiv
  have same := ForcedLinear.unique_on operator (forcing (constantDriver c)) 0 state
    (constantSolution c) (by rw [initial, constantSolution_start]) hderiv
    (fun t _ i => (constantSolution_deriv c t i).hasDerivWithinAt)
  rw [(values t).1, same (Set.mem_Ici.2 ht)]
  rfl

/-- **One half is not a bound inside the band.** Under `d = 1` the exposure is
`1/2 + e^(−π/2)/2` at `t = π/2`. -/
theorem half_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation =>
        -(1 / 2) ≤ observation sIndex ∧ observation sIndex ≤ 1 / 2) := by
  intro holds
  have admit : admitted (withInitial (constantDriver 1)) :=
    ⟨⟨by simpa [withInitial] using constant_admitted 1,
      fun t _ => by simp [withInitial, constantDriver]⟩, constant_start _⟩
  obtain ⟨output, related⟩ := realized _ admit.2 admit.1.1
  have inDomain : Real.pi / 2 ∈ evolution.time.domain := by
    rw [domain_eq]
    exact Set.mem_Ici.2 Real.pi_div_two_pos.le
  have high := (holds _ admit output related (Real.pi / 2) inDomain).2
  rw [constant_output 1 output related (Real.pi / 2) Real.pi_div_two_pos.le] at high
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two] at high
  linarith [Real.exp_pos (-(Real.pi / 2))]

/-- **The driver bound is needed.** Without it the bound on `s` fails: the
admitted `d = 3` gives `s(π/2) = 3/2 + 3e^(−π/2)/2 > 1`. -/
theorem bound_needed :
    ¬ Holds observed evolution.time admittedOnly
      (Always evolution.time fun observation =>
        -1 ≤ observation sIndex ∧ observation sIndex ≤ 1) := by
  intro holds
  have admit : admittedOnly (withInitial (constantDriver 3)) :=
    ⟨by simpa [withInitial] using constant_admitted 3, constant_start _⟩
  obtain ⟨output, related⟩ := realized _ admit.2 admit.1
  have inDomain : Real.pi / 2 ∈ evolution.time.domain := by
    rw [domain_eq]
    exact Set.mem_Ici.2 Real.pi_div_two_pos.le
  have high := (holds _ admit output related (Real.pi / 2) inDomain).2
  rw [constant_output 3 output related (Real.pi / 2) Real.pi_div_two_pos.le] at high
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two] at high
  linarith [Real.exp_pos (-(Real.pi / 2))]

#print axioms observed_rel
#print axioms feedback_iff
#print axioms feedback_reads
#print axioms solution_exists
#print axioms compiled_exists
#print axioms invariant
#print axioms exposure_within
#print axioms energy_within
#print axioms exposure_contract
#print axioms energy_contract
#print axioms witness_input_admitted
#print axioms half_refuted
#print axioms bound_needed

end Gimle.Forseti.Examples.HedgedSpreadContract
