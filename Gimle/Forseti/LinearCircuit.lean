import Gimle.Asgard.Dynamics.LinearSyntax
import Gimle.Forseti.Discrete
import Gimle.Forseti.FiniteLinearEquivalence

/-! Accepted homogeneous-linear source expressions, their original compilation,
and initialized autonomous execution. All circuit states have exact real semantics. -/
namespace Gimle.Forseti.LinearCircuit

open Gimle.Asgard
open Gimle.Asgard.Polynomial
open Gimle.Asgard.Dynamics
open FiniteLinearEquivalence

/-- Original source expressions together with checked rational coefficients. -/
structure Program (d : Nat) where
  updates : Fin d → Polynomial.Expr d
  readout : Polynomial.Expr d
  matrix : Matrix (Fin d) (Fin d) ℚ
  weights : Fin d → ℚ
  updates_ok : ∀ i, LinearSyntax.coefficients (updates i) = some (matrix i)
  readout_ok : LinearSyntax.coefficients readout = some weights

/-- The unique empty port vector. -/
def empty : Point 0 := Fin.elim0

/-- Compile the supplied update expressions in their original order. -/
def Program.update {d : Nat} (P : Program d) : Circuit d d :=
  compileOutputs P.updates

/-- Compile the supplied readout expression. -/
def Program.output {d : Nat} (P : Program d) : Circuit d 1 := P.readout.compile

/-- Initialized synchronous execution with no input or parameter ports. -/
noncomputable def Program.state {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    Point d := Discrete.run (u := 0) (p := 0) P.update empty x (fun _ => empty) n

/-- Observe the initialized state at time `n`, including the initial time zero. -/
noncomputable def Program.observe {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    ℝ := P.output.run (P.state x n) 0

/-- Empty autonomous ports do not change the state supplied to the circuit. -/
theorem autonomous_step {d : Nat} (U : Circuit d d) (parameter : Point 0)
    (x : Point d) (input : Point 0) :
    Discrete.step (u := 0) (p := 0) U parameter x input = U.run x := by
  unfold Discrete.step
  congr 1
  funext i
  simp [pointAppend]

/-- Original compiled updates act by their accepted rational matrix. -/
theorem Program.update_run {d : Nat} (P : Program d) (x : Point d) :
    P.update.run x = fun i => ∑ j, (P.matrix i j : ℝ) * x j := by
  funext i
  rw [Program.update, compileOutputs_correct]
  exact LinearSyntax.coefficients_correct _ _ (P.updates_ok i) x

/-- Original compiled readout acts by its accepted coefficient row. -/
theorem Program.output_run {d : Nat} (P : Program d) (x : Point d) :
    P.output.run x 0 = ∑ j, (P.weights j : ℝ) * x j :=
  LinearSyntax.compiled_correct _ _ P.readout_ok x

@[simp] theorem Program.state_zero {d : Nat} (P : Program d) (x : Point d) :
    P.state x 0 = x := rfl

theorem Program.state_succ {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    P.state x (n + 1) = P.update.run (P.state x n) :=
  autonomous_step P.update empty (P.state x n) empty

/-- Moving the initial state forward shifts every later initialized state. -/
theorem Program.state_shift {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    P.state (P.update.run x) n = P.state x (n + 1) := by
  induction n with
  | zero => simp [state_succ]
  | succ n ih =>
      rw [state_succ P (P.update.run x) n, ih, state_succ P x (n + 1)]

theorem Program.observe_shift {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    P.observe (P.update.run x) n = P.observe x (n + 1) := by
  unfold Program.observe
  rw [Program.state_shift]

/-- The accepted matrix interpreted as an endomorphism of real states. -/
noncomputable def Program.realMap {d : Nat} (P : Program d) :
    Module.End ℝ (Point d) := Matrix.mulVecLin (fun i j => (P.matrix i j : ℝ))

/-- Initialized circuit execution agrees with powers of the real endomorphism. -/
theorem Program.state_eq_pow {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    P.state x n = (P.realMap ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Program.state_succ, ih, pow_succ', Module.End.mul_apply]
      exact P.update_run _

/-- Casts commute with one rational matrix-vector action. -/
theorem ratCast_mulVec {d : Nat} (A : Matrix (Fin d) (Fin d) ℚ) (x : Fin d → ℚ) :
    Matrix.mulVec (fun i j => (A i j : ℝ)) (fun i => (x i : ℝ)) =
      fun i => ((A.mulVec x) i : ℝ) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- Initialized execution at rational states is the exact embedded rational orbit. -/
theorem Program.state_ratCast {d : Nat} (P : Program d) (x : Fin d → ℚ) (n : Nat) :
    P.state (fun i => (x i : ℝ)) n =
      fun i => (((P.matrix ^ n).mulVec x) i : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Program.state_succ, ih, Program.update_run, pow_succ']
      have h := ratCast_mulVec P.matrix ((P.matrix ^ n).mulVec x)
      rw [Matrix.mulVec_mulVec] at h
      exact h

/-- Original compiled observations embed the previous rational matrix outputs. -/
theorem Program.observe_ratCast {d : Nat} (P : Program d) (x : Fin d → ℚ) (n : Nat) :
    P.observe (fun i => (x i : ℝ)) n =
      (matrix_output P.matrix x P.weights n : ℝ) := by
  rw [Program.observe, Program.output_run, Program.state_ratCast]
  simp [matrix_output, dotProduct]

/-- The actual pair of original compiled update circuits. -/
def pairedUpdate {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    Circuit (d₁ + d₂) (d₁ + d₂) := .parallel P.update Q.update

/-- Running the paired circuit preserves the declared left-then-right state order. -/
theorem paired_state {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (x : Point d₁) (y : Point d₂) (n : Nat) :
    Discrete.run (s := d₁ + d₂) (u := 0) (p := 0) (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q)
      empty (pointAppend x y) (fun _ => empty) n =
      pointAppend (P.state x n) (Q.state y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Discrete.step (s := d₁ + d₂) (u := 0) (p := 0) (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q) empty
        (Discrete.run (s := d₁ + d₂) (u := 0) (p := 0) (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q)
          empty (pointAppend x y) (fun _ => empty) n) empty = _
      rw [autonomous_step, ih, Program.state_succ, Program.state_succ]
      simp [pairedUpdate]

/-- Algebraic completeness for arbitrary real initialized compiled observations.
This is the engine for the separate predicate/Hoare safety proof. -/
theorem compiled_prefix_iff_all_real {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (x : Point d₁) (y : Point d₂) :
    (∀ n < d₁ + d₂, P.observe x n = Q.observe y n) ↔
      ∀ n, P.observe x n = Q.observe y n := by
  constructor
  · intro h
    let T := P.realMap.prodMap Q.realMap
    let ell : (Point d₁ × Point d₂) →ₗ[ℝ] ℝ :=
      (dotProductBilin ℝ ℝ (fun i => (P.weights i : ℝ))).comp (LinearMap.fst ℝ _ _) -
        (dotProductBilin ℝ ℝ (fun i => (Q.weights i : ℝ))).comp (LinearMap.snd ℝ _ _)
    have ho (n : Nat) : ell ((T ^ n) (x, y)) = P.observe x n - Q.observe y n := by
      simp [T, ell, product_power_action, Program.observe, Program.output_run,
        Program.state_eq_pow, dotProduct]
    have hz := observation_zero_of_prefix T (x, y) ell (by
      intro n hn
      rw [ho, sub_eq_zero]
      apply h n
      simpa [Point] using hn)
    intro n
    exact sub_eq_zero.mp ((ho n).symm.trans (hz n))
  · intro h n _
    exact h n

#print axioms Program.update_run
#print axioms Program.state_eq_pow
#print axioms Program.state_ratCast
#print axioms Program.observe_ratCast
#print axioms paired_state
#print axioms compiled_prefix_iff_all_real

end Gimle.Forseti.LinearCircuit
