import Gimle.Forseti.ForcedLinear
import Gimle.Forseti.Trajectory

/-! Bottom-up safety through an actual continuous trace.

Two component fields x' = -x + 2u + d and z' = -z - v are wired with
u = z and v = x. Their storage identities combine with weights 1 and 2.
The resulting invariant x² + 2z² ≤ 1 proves |x| ≤ 1 for every continuous
disturbance bounded by one on the forward domain. Existence and uniqueness
are proved independently of the invariant; the root is a total Contract.
-/

namespace Gimle.Forseti.Examples.DisturbedFeedback

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory

/-- Component A, with ports [x, u, d]. -/
def componentA : Gimle.Asgard.Circuit 3 1 :=
  (Polynomial.Expr.add (.add (.neg (.var 0)) (.mul (.constant 2) (.var 1)))
    (.var 2)).compile

/-- Component B, with ports [z, v]. -/
def componentB : Gimle.Asgard.Circuit 2 1 :=
  (Polynomial.Expr.add (.neg (.var 0)) (.neg (.var 1))).compile

/-- Route [d, x, z] to the parallel components' ports [x, z, d, z, x]. -/
def wiring : Gimle.Asgard.Circuit 3 (3 + 2) := Polynomial.route ![1, 2, 0, 2, 1]

/-- The feedback field is composition and parallel composition of the components. -/
def field : Gimle.Asgard.Circuit (1 + 2) 2 :=
  .compose wiring (.parallel componentA componentB)

@[simp] theorem componentA_run (x u d : ℝ) :
    componentA.run ![x, u, d] 0 = -x + 2 * u + d := by
  simp [componentA, Polynomial.Expr.eval]

@[simp] theorem componentB_run (z v : ℝ) :
    componentB.run ![z, v] 0 = -z - v := by
  simp [componentB, Polynomial.Expr.eval, sub_eq_add_neg]

@[simp] theorem field_run (d : Point 1) (s : Point 2) :
    field.run (pointAppend d s) = ![-s 0 + 2 * s 1 + d 0, -s 1 - s 0] := by
  funext i
  fin_cases i <;>
    simp [field, wiring, Gimle.Asgard.Circuit.run, componentA, componentB,
      Polynomial.Expr.eval, pointLeft, pointRight, pointAppend, sub_eq_add_neg]

/-- The local storage contract of A, before any feedback identification. -/
theorem componentA_storage (x u d : ℝ) :
    2 * x * (componentA.run ![x, u, d] 0) = -2 * x^2 + 4 * x * u + 2 * x * d := by
  rw [componentA_run]
  ring

/-- The local storage contract of B, before any feedback identification. -/
theorem componentB_storage (z v : ℝ) :
    2 * z * (componentB.run ![z, v] 0) = -2 * z^2 - 2 * z * v := by
  rw [componentB_run]
  ring

/-- The candidate invariant's storage function on both feedback wires. -/
noncomputable def energy (s : Point 2) : ℝ := s 0 ^ 2 + 2 * s 1 ^ 2

/-- Weight B's storage by two: internal exchange cancels at the wiring boundary. -/
theorem storage_cancellation (x z d : ℝ) :
    2 * x * (componentA.run ![x, z, d] 0) +
      2 * (2 * z * (componentB.run ![z, x] 0)) =
      -2 * (x^2 + 2 * z^2) + 2 * x * d := by
  rw [componentA_storage, componentB_storage]
  ring

/-- The algebraic leaf checked for the chosen invariant and disturbance set. -/
theorem storage_bound (x z d : ℝ) (bounded : |d| ≤ 1) :
    -2 * (x^2 + 2 * z^2) + 2 * x * d ≤ 1 - (x^2 + 2 * z^2) := by
  have hd := abs_le.mp bounded
  nlinarith [sq_nonneg (x - d), sq_nonneg z, mul_nonneg (by linarith : 0 ≤ 1 - d)
    (by linarith : 0 ≤ 1 + d)]

/-- The actual trace feeds the integrated states back through `field`. -/
def loop (axis : String) : Dynamics.Circuit (1 + 2) 2 := close axis field

/-- Expose only x; the invariant also needs the hidden state z. -/
def projection : Gimle.Asgard.Circuit 2 1 := Polynomial.route ![0]

/-- A second contract will be composed above the trace for the visible output. -/
def observed (axis : String) : Dynamics.Circuit (1 + 2) 1 :=
  .compose (loop axis) (.lift projection)

/-- Disturbances are continuous on the real line, bounded only from the start;
initialization wires are read only at that start. -/
def admitted (time : TimeDomain) : SignalPredicate (1 + 2) :=
  Initialized time (fun d => Continuous d ∧ ∀ t ∈ time.domain, |d t 0| ≤ 1)
    (fun s => energy s ≤ 1)

/-- Read arbitrary initialization wires through the existing trace theorem. -/
theorem loop_rel (time : TimeDomain) (input : Signal (1 + 2)) (state : Signal 2) :
    (loop time.axis).Rel time input state ↔
      state time.start = signalRight input time.start ∧
      ∀ t ∈ time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        (field.run (pointAppend (signalLeft input t) (state t)) i) time.domain t := by
  unfold loop
  conv_lhs => rw [← signalAppend_parts input]
  rw [close_rel]
  simp

/-- The homogeneous part of the field, used only for analytic well-posedness. -/
noncomputable def operator : Point 2 →L[ℝ] Point 2 :=
  LinearAnalysis.rationalOperator ![![-1, 2], ![-1, -1]]

/-- The disturbance acts on the first component only. -/
def forcing (d : Signal 1) : Signal 2 := fun t => ![d t 0, 0]

theorem field_forced (d : Point 1) (s : Point 2) :
    field.run (pointAppend d s) = operator s + ![d 0, 0] := by
  rw [field_run]
  funext i
  fin_cases i <;> simp [operator, LinearAnalysis.rationalOperator_apply, Fin.sum_univ_two]
  ring

/-- Prove existence without assuming a safe or even an existing trajectory. -/
theorem loop_exists (time : TimeDomain) (input : Signal (1 + 2))
    (continuous : Continuous (signalLeft input : Signal 1)) :
    ∃ state, (loop time.axis).Rel time input state := by
  have cf : Continuous (forcing (signalLeft input)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · convert! (continuous_apply 0).comp continuous using 1
    · simpa [forcing] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  obtain ⟨state, initial, derivative⟩ := ForcedLinear.exists_solution operator
    (forcing (signalLeft input)) cf time.start (signalRight input time.start)
  refine ⟨state, (loop_rel time input state).mpr ⟨initial, ?_⟩⟩
  intro t _ i
  rw [field_forced]
  exact ((hasDerivAt_pi.mp (derivative t)) i).hasDerivWithinAt

/-- Uniqueness needs the fixed disturbance, but no continuity or safety premise. -/
theorem loop_unique (time : TimeDomain) (input : Signal (1 + 2))
    (x y : Signal 2) (hx : (loop time.axis).Rel time input x)
    (hy : (loop time.axis).Rel time input y) : Set.EqOn x y time.domain := by
  obtain ⟨ix, dx⟩ := (loop_rel time input x).mp hx
  obtain ⟨iy, dy⟩ := (loop_rel time input y).mp hy
  apply ForcedLinear.unique_on operator (forcing (signalLeft input)) time.start x y (ix.trans iy.symm)
  · intro t ht i
    simpa only [field_forced, forcing, TimeDomain.domain] using dx t ht i
  · intro t ht i
    simpa only [field_forced, forcing, TimeDomain.domain] using dy t ht i

/-- Differentiation consumes the two component storage contracts through the wiring. -/
theorem energy_derivative (time : TimeDomain) (input : Signal (1 + 2))
    (state : Signal 2) (realized : (loop time.axis).Rel time input state)
    (t : ℝ) (within : t ∈ time.domain) :
    HasDerivWithinAt (fun t => energy (state t))
      (-2 * energy (state t) + 2 * state t 0 * signalLeft input t 0) time.domain t := by
  have dx := ((loop_rel time input state).mp realized).2 t within 0
  have dz := ((loop_rel time input state).mp realized).2 t within 1
  rw [field_run] at dx dz
  have h := (dx.pow 2).add ((dz.pow 2).const_mul 2)
  convert! h using 1
  have cancel := storage_cancellation (state t 0) (state t 1) (signalLeft input t 0)
  simpa [energy] using cancel.symm

/-- An integrating factor transports the local inequality through the integrators
and trace. It does not assume the invariant on the feedback signal. -/
theorem invariant (time : TimeDomain) (input : Signal (1 + 2))
    (admit : admitted time input) (state : Signal 2)
    (realized : (loop time.axis).Rel time input state) :
    Always time (fun s => energy s ≤ 1) state := by
  let V : ℝ → ℝ := fun t => energy (state t)
  let rate : ℝ → ℝ := fun t => -2 * V t + 2 * state t 0 * signalLeft input t 0
  have derivative (t : ℝ) (ht : t ∈ time.domain) :
      HasDerivWithinAt V (rate t) time.domain t := energy_derivative time input state realized t ht
  have bound (t : ℝ) (ht : t ∈ time.domain) : rate t ≤ 1 - V t :=
    storage_bound _ _ _ (admit.1.2 t ht)
  have factor (t : ℝ) (ht : t ∈ time.domain) :
      HasDerivWithinAt (fun t => Real.exp t * (V t - 1))
        (Real.exp t * (V t - 1 + rate t)) time.domain t := by
    convert! (Real.hasDerivAt_exp t).hasDerivWithinAt.mul
      ((derivative t ht).sub_const 1) using 1
    ring
  have anti : AntitoneOn (fun t => Real.exp t * (V t - 1)) time.domain := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun t => Real.exp t * (V t - 1 + rate t)) (convex_Ici time.start)
    · intro t ht
      exact (factor t ht).continuousWithinAt
    · intro t ht
      exact (factor t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos t).le (by
        have := bound t (interior_subset ht)
        linarith)
  have initial : V time.start ≤ 1 := by
    dsimp [V]
    rw [((loop_rel time input state).mp realized).1]
    exact admit.2
  intro t ht
  have h := anti (show time.start ∈ time.domain by simp [TimeDomain.domain]) ht ht
  have atStart : Real.exp time.start * (V time.start - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have nonpos : V t - 1 ≤ 0 := by
    have := h.trans atStart
    nlinarith [Real.exp_pos t]
  change V t ≤ 1
  linarith

/-- The feedback theorem: a trajectory exists, is unique forward, and is invariant. -/
theorem loop_contract (time : TimeDomain) :
    Contract (loop time.axis) time (admitted time)
      (Always time fun s => energy s ≤ 1) where
  realizable input admit := loop_exists time input admit.1.1
  unique input _ x y hx hy := loop_unique time input x y hx hy
  holds input admit state realized := invariant time input admit state realized

/-- The hidden-state invariant entails the requested visible output bound. -/
theorem projection_safe (s : Point 2) (safe : energy s ≤ 1) :
    |projection.run s 0| ≤ 1 := by
  simp only [projection, Polynomial.route_correct, Matrix.cons_val_zero]
  dsimp [energy] at safe
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (s 1), sq_nonneg (s 0 + 1), sq_nonneg (s 0 - 1)]

/-- Root system theorem, built by composing the trace contract with the observer. -/
theorem output_contract (time : TimeDomain) :
    Contract (observed time.axis) time (admitted time)
      (Always time fun y => |y 0| ≤ 1) :=
  Contract.compose (loop_contract time)
    (Contract.lift projection time projection_safe)
    (DomainRespecting.lift _ _ _)

#print axioms storage_cancellation
#print axioms invariant
#print axioms output_contract

end Gimle.Forseti.Examples.DisturbedFeedback
