import Gimle.Forseti.LinearEnergy
import Gimle.Asgard.Examples.ThreeState

/-! Exact properties of the accepted three-state Asgard model.

The generic half (`energy_derivative`, `energy_bound`) is stated for any
recognized three-state linear field with nonnegative rational coefficients; only
the `compiled_*` half binds to Asgard's compiled model. Nothing here restates
the equations or the circuit — `energy_at` reads V off the compiled observation
circuit at its own index, so the bound is about what the compiler produced. -/
namespace Gimle.Forseti.Examples.ThreeState
open Gimle.Asgard Gimle.Asgard.Model
open Gimle.Asgard.Examples.ThreeState
open Gimle.Forseti.LinearEnergy

/-- A specification for the matrix recognized from any accepted parameter
specialization. Concrete Asgard compilation checks this equality. -/
def expectedMatrix (a b c : ℚ) : Dynamics.Linear.Matrix 3 :=
  ![![-a, 1, -1], ![-1, -b, 1], ![1, -1, -c]]

def identity : QMatrix 3 := fun i j => if i = j then 1 else 0

theorem quadratic_identity (x : Point 3) :
    quadratic identity x = x 0^2 + x 1^2 + x 2^2 := by
  simp [identity, quadratic, realMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, pow_two]

def diagonal (a b c : ℚ) : QMatrix 3 :=
  fun i j => if i = j then ![2*a, 2*b, 2*c] i else 0

theorem dissipation_eq (a b c : ℚ) :
    dissipation (expectedMatrix a b c) identity = diagonal a b c := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [dissipation, expectedMatrix, identity, diagonal] <;>
    ring

theorem quadratic_diagonal (a b c : ℚ) (x : Point 3) :
    quadratic (diagonal a b c) x =
      (2*a : ℚ) * x 0^2 + (2*b : ℚ) * x 1^2 + (2*c : ℚ) * x 2^2 := by
  simp [quadratic, diagonal, realMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, pow_two]
  ring

/-- Every solution of a recognized three-state linear field has the stated
energy derivative on the forward time domain. -/
theorem energy_derivative (a b c : ℚ) (problem : Dynamics.Linear.Problem 3)
    (matrix_eq : problem.matrix = expectedMatrix a b c)
    (state : Dynamics.Signal 3) (solves : problem.Solves state)
    (t : ℝ) (forward : t ∈ problem.time.domain) :
    HasDerivWithinAt (fun s => quadratic identity (state s))
      (-(2*(a : ℝ)*(state t 0)^2) - 2*(b : ℝ)*(state t 1)^2 -
        2*(c : ℝ)*(state t 2)^2) problem.time.domain t := by
  have h := quadratic_derivative problem identity state solves t forward
  rw [matrix_eq, dissipation_eq, quadratic_diagonal] at h
  convert h using 1
  push_cast
  ring

theorem dissipation_nonnegative (a b c : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (x : Point 3) :
    0 ≤ quadratic (dissipation (expectedMatrix a b c) identity) x := by
  rw [dissipation_eq, quadratic_diagonal]
  have ha' : (0 : ℝ) ≤ (2*a : ℚ) := by exact_mod_cast (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) ha)
  have hb' : (0 : ℝ) ≤ (2*b : ℚ) := by exact_mod_cast (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) hb)
  have hc' : (0 : ℝ) ≤ (2*c : ℚ) := by exact_mod_cast (mul_nonneg (by norm_num : (0:ℚ) ≤ 2) hc)
  exact add_nonneg (add_nonneg (mul_nonneg ha' (sq_nonneg _))
    (mul_nonneg hb' (sq_nonneg _))) (mul_nonneg hc' (sq_nonneg _))

/-- The bound is for every continuous solution, not for Euler samples. -/
theorem energy_bound (a b c : ℚ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (problem : Dynamics.Linear.Problem 3)
    (matrix_eq : problem.matrix = expectedMatrix a b c)
    (initial_eq : problem.initial = (![1, 2, -1] : Point 3))
    (start_eq : problem.time.start = 2)
    (state : Dynamics.Signal 3) (solves : problem.Solves state)
    (t : ℝ) (forward : 2 ≤ t) :
    0 ≤ quadratic identity (state t) ∧ quadratic identity (state t) ≤ 6 := by
  have nonnegative (x : Point 3) : 0 ≤ quadratic identity x := by
    rw [quadratic_identity]
    positivity
  have decreases (x : Point 3) :
      0 ≤ quadratic (dissipation problem.matrix identity) x := by
    rw [matrix_eq]
    exact dissipation_nonnegative a b c ha hb hc x
  have anti := quadratic_antitone problem identity state solves decreases
  have start_mem : problem.time.start ∈ problem.time.domain := by
    simp [Dynamics.TimeDomain.domain]
  have t_mem : t ∈ problem.time.domain := by
    simpa [Dynamics.TimeDomain.domain, start_eq] using forward
  have start_le : problem.time.start ≤ t := by simpa [start_eq] using forward
  have upper := anti start_mem t_mem start_le
  change quadratic identity (state t) ≤ quadratic identity (state problem.time.start) at upper
  rw [solves.1, initial_eq] at upper
  simp only [quadratic_identity] at upper
  have initial_energy :
      (![1, 2, -1] : Point 3) 0 ^ 2 + (![1, 2, -1] : Point 3) 1 ^ 2 +
      (![1, 2, -1] : Point 3) 2 ^ 2 = (6 : ℝ) := by
    norm_num [show (![1, 2, -1] : Point 3) 2 = -1 from rfl]
  rw [initial_energy] at upper
  exact ⟨nonnegative _, by simpa only [quadratic_identity] using upper⟩

theorem compiled_matrix : linear.matrix = expectedMatrix (1/3) (1/2) 2 := by
  rw [linear_matrix]
  rfl

noncomputable def compiledProblem : Dynamics.Linear.Problem 3 := linear.problem

theorem compiled_problem_matrix : compiledProblem.matrix = expectedMatrix (1/3) (1/2) 2 :=
  compiled_matrix

theorem compiled_problem_initial : compiledProblem.initial = (![1, 2, -1] : Point 3) :=
  initial_eq

theorem compiled_problem_start : compiledProblem.time.start = 2 := by rfl

/-- Translation, global existence, and uniqueness are separate from safety. -/
theorem compiled_exists : ∃ state, model.Realizes state :=
  linear.exists_realization

theorem compiled_unique {x y : Dynamics.Signal 3}
    (hx : model.Realizes x) (hy : model.Realizes y) :
    Set.EqOn x y evolution.time.domain := linear.unique_realization hx hy

theorem compiled_solves (state : Dynamics.Signal 3)
    (realized : model.Realizes state) : compiledProblem.Solves state := by
  have source := (model.solves_iff_realizes state).mpr realized
  exact (linear.source_iff state).mp source

/-- The source-compiled feedback and extracted linear system have exactly the
same forward realizations, with no replacement circuit in the feedback path. -/
theorem compiled_realizes_iff_problem (state : Dynamics.Signal 3) :
    model.Realizes state ↔ compiledProblem.Realizes state := by
  constructor
  · intro realized
    exact (compiledProblem.solves_iff_realizes state).mp (compiled_solves state realized)
  · intro realized
    have solves := (compiledProblem.solves_iff_realizes state).mpr realized
    exact (model.solves_iff_realizes state).mp
      ((linear.source_iff state).mpr solves)

/-- The derivative is for the fourth circuit observation, not a retyped energy. -/
theorem compiled_energy_derivative (state : Dynamics.Signal 3)
    (realized : model.Realizes state) (t : ℝ)
    (forward : t ∈ evolution.time.domain) :
    HasDerivWithinAt
      (fun s => model.outputs.circuit.run (state s) energyIndex)
      (-(2*(1/3 : ℝ)*(state t 0)^2) - 2*(1/2 : ℝ)*(state t 1)^2 -
        2*(2 : ℝ)*(state t 2)^2) evolution.time.domain t := by
  have h := energy_derivative (1/3) (1/2) 2 compiledProblem compiled_problem_matrix
    state (compiled_solves state realized) t forward
  simpa [compiledProblem, LinearView.problem, energy_at,
    quadratic_identity] using h

/-- At the declared initial state, the exact continuous derivative is -26/3. -/
theorem compiled_initial_derivative (state : Dynamics.Signal 3)
    (realized : model.Realizes state) :
    HasDerivWithinAt
      (fun s => model.outputs.circuit.run (state s) energyIndex)
      (-(26/3 : ℝ)) evolution.time.domain 2 := by
  have initial := (compiled_solves state realized).1
  rw [compiled_problem_start, compiled_problem_initial] at initial
  have forward : (2 : ℝ) ∈ evolution.time.domain := by
    simp [Dynamics.TimeDomain.domain, Evolution.time, evolution]
  have h := compiled_energy_derivative state realized 2 forward
  rw [initial] at h
  convert h using 1
  norm_num [show (![1, 2, -1] : Point 3) 2 = -1 from rfl]

/-- Every exact continuous realization remains in the initial energy sublevel. -/
theorem compiled_energy_bound (state : Dynamics.Signal 3)
    (realized : model.Realizes state) (t : ℝ) (forward : 2 ≤ t) :
    0 ≤ model.outputs.circuit.run (state t) energyIndex ∧
    model.outputs.circuit.run (state t) energyIndex ≤ 6 := by
  have h := energy_bound (1/3) (1/2) 2 (by norm_num) (by norm_num) (by norm_num)
    compiledProblem compiled_problem_matrix compiled_problem_initial compiled_problem_start
    state (compiled_solves state realized) t forward
  simpa only [energy_at, quadratic_identity] using h

/-- Five is already false at the exact initial state. -/
theorem initial_not_bounded_by_five :
    ¬ model.outputs.circuit.run model.initial energyIndex ≤ 5 := by
  rw [energy_at, initial_eq]
  norm_num [show (![1, 2, -1] : Point 3) 2 = -1 from rfl]

/-! ## How the claim depends on its hypotheses

Outcome 3 asks to show what changing parameters, bindings, initial conditions or
assumptions does to the bound. `energy_bound` takes each of them as an explicit
hypothesis, so the honest demonstration is that dropping one breaks a step the
proof actually uses, rather than that the theorem stops applying. -/

/-- Nonnegativity is what makes the dissipation term nonnegative, and hence the
energy antitone. With a negative coefficient the form takes negative values, so
the antitonicity step is unavailable — at `a = -1` the dissipation quadratic is
strictly negative off the `x = 0` plane. -/
theorem dissipation_negative_of_negative_coefficient :
    quadratic (dissipation (expectedMatrix (-1) 0 0) identity) ![1, 0, 0] < 0 := by
  rw [dissipation_eq, quadratic_diagonal]
  norm_num

/-- The bound is the initial energy, not a constant of the model: a different
admissible initial state gives a different sublevel. `(2,0,0)` starts at 4. -/
theorem initial_energy_is_the_bound :
    quadratic identity ![2, 0, 0] = 4 := by
  rw [quadratic_identity]
  norm_num [show (![2, 0, 0] : Point 3) 2 = 0 from rfl]

/-- Changing a coefficient changes the recognized matrix, so `matrix_eq` is a
real constraint and not a formality. -/
theorem matrix_depends_on_coefficients :
    expectedMatrix (1/3) (1/2) 2 ≠ expectedMatrix 1 (1/2) 2 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [expectedMatrix] at this

/-- The start time enters only through `start_eq`; the compiled model declares
2, and the bound is stated from there. -/
theorem compiled_start_is_two : compiledProblem.time.start = 2 := compiled_problem_start

#print axioms dissipation_negative_of_negative_coefficient
#print axioms matrix_depends_on_coefficients
#print axioms energy_derivative
#print axioms energy_bound
#print axioms compiled_exists
#print axioms compiled_unique
#print axioms compiled_realizes_iff_problem
#print axioms compiled_energy_derivative
#print axioms compiled_initial_derivative
#print axioms compiled_energy_bound
#print axioms initial_not_bounded_by_five

end Gimle.Forseti.Examples.ThreeState
