import Gimle.Forseti.LinearEnergy
import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax

/-! Exact properties of the damped oscillator compiled from its source equations.

The source is asgard-lean's `Examples/DampedOscillator.lean`:
`D_t(D_t(x)) + c*D_t(x) + k*x = 0` with `c = 3`, `k = 2` and the declared
velocity `dx : D_t(x) = v`. That body declares no observation, so this module
declares its own copy of the same equations with three observations — `x`, `v`
and the energy `E := 2*x^2 + v^2`, a source assignment — and compiles it with
`compileSourceContinuous`. Nothing downstream restates the equations or the
circuit: `energy_at` reads `E` off the compiled observation circuit at its own
index, so the bound is about what the compiler produced.

Along every solution `dE/dt = 4xv + 2v(−3v − 2x) = −6v² ≤ 0`, so
`0 ≤ E ≤ E(0) = 2` for `t ≥ 0`. `compiled_energy_bound` proves this with
`LinearEnergy.certificate_energy_bound` and an exact weighted-square certificate
for `P = diag(2, 1)` and its dissipation `diag(0, 6)`. -/
namespace Gimle.Forseti.Examples.DampedOscillator
open Gimle.Asgard Gimle.Asgard.Model Polynomial
open Gimle.Forseti.LinearEnergy

/-- The oscillator with the declared velocity, plus observations `[x, v, E]`
with stable port IDs. `E` is a source assignment, not a retyped formula. -/
def body : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"state-v", "v", .state⟩,
    ⟨"param-c", "c", .parameter⟩, ⟨"param-k", "k", .parameter⟩]
  assignments := assignments% { E := 2 * x ^ 2 + v ^ 2; }
  differentials := differentials% { dv : diff(diff(x, t), t) + c * diff(x, t) + k * x = 0; }
  velocities := velocities% { dx : diff(x, t) = v; }
  parameters := [⟨"param-c", 3⟩, ⟨"param-k", 2⟩]
  observations := [⟨⟨"obs-x", "x", .output⟩, "state-x"⟩,
    ⟨⟨"obs-v", "v", .output⟩, "state-v"⟩,
    ⟨⟨"obs-e", "E", .output⟩, "E"⟩]
}

/-- State order [x, v], starting at `t = 0` from `x(0) = 1`, `v(0) = 0`. -/
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-v", "dv", "initial-v"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-v", "v0", .initial⟩]
  initialValues := [⟨"initial-x", 1⟩, ⟨"initial-v", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- The source compiled by asgard-lean's verified source compiler. -/
def model : SourceContinuousModel body evolution :=
  (compileSourceContinuous body evolution).toOption.get (by decide +kernel)

/-- The compiled continuous model: its field, feedback and observations. An
`abbrev` so downstream proofs need no unfolding step. -/
abbrev compiled : ContinuousModel model.lowered.body evolution := model.model

/-- The compiled field over state order [x, v]: `dx := v`,
`dv := 0 - (3*v + 2*x)`. -/
theorem rates_expressions : compiled.rates.expressions =
    (![.var 1, .add (.constant 0) (.neg (.add (.mul (.constant 3) (.var 1))
      (.mul (.constant 2) (.var 0))))] : Fin 2 → Expr 2) := by
  decide +kernel

/-- Both initial values, read from the unchanged evolution. -/
theorem initial_eq : compiled.initial = (![1, 0] : Point 2) := by
  change (fun i : Fin 2 => (compiled.initials i : ℝ)) = _
  have values : compiled.initials = ![1, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

/-- The third observation is `E`. -/
def energyIndex : Fin body.observations.length := ⟨2, by decide⟩

/-- `E` read off the compiled observation circuit at its own index. -/
theorem energy_at (x : Point 2) :
    compiled.outputs.circuit.run x energyIndex = 2 * x 0 ^ 2 + x 1 ^ 2 := by
  rw [Selected.circuit, compileOutputs_correct]
  change (compiled.outputs.expressions energyIndex).eval x = _
  have expression : compiled.outputs.expressions energyIndex =
      (.add (.mul (.constant 2) (.mul (.mul (.constant 1) (.var 0)) (.var 0)))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)) : Expr 2) := by decide +kernel
  rw [expression]
  simp [Expr.eval, pow_two]

theorem energy_at_initial : compiled.outputs.circuit.run compiled.initial energyIndex = 2 := by
  rw [energy_at, initial_eq]
  norm_num

/-! ## Linear analysis, for existence and forward uniqueness -/

/-- The accepted linear view of the compiled field. -/
noncomputable def linear : LinearView compiled := compiled.linear.get (by decide +kernel)

theorem linear_matrix : linear.matrix = ![![0, 1], ![-2, -3]] := by decide +kernel

/-- Translation, global existence, and uniqueness are separate from safety. -/
theorem compiled_exists : ∃ state, compiled.Realizes state :=
  linear.exists_realization

theorem compiled_unique {x y : Dynamics.Signal 2}
    (hx : compiled.Realizes x) (hy : compiled.Realizes y) :
    Set.EqOn x y evolution.time.domain := linear.unique_realization hx hy

noncomputable def compiledProblem : Dynamics.Linear.Problem 2 := linear.problem

theorem compiled_solves (state : Dynamics.Signal 2)
    (realized : compiled.Realizes state) : compiledProblem.Solves state := by
  have source := (compiled.solves_iff_realizes state).mpr realized
  exact (linear.source_iff state).mp source

/-! ## The energy certificate -/

/-- `P = diag(2, 1)`, so `xᵀ P x = 2x² + v²`. -/
def energyMatrix : QMatrix 2 := ![![2, 0], ![0, 1]]

/-- `P` as `2·e₀² + 1·e₁²`, and its dissipation `−(AᵀP + PA) = diag(0, 6)` as
`6·e₁²`. Untrusted data; `certificate_valid` checks it. -/
def certificate : Certificate 2 where
  positive := ⟨2, ![2, 1], ![![1, 0], ![0, 1]]⟩
  decrease := ⟨1, ![6], ![![0, 1]]⟩

theorem certificate_valid : certificate.Valid compiledProblem.matrix energyMatrix := by
  change certificate.Valid linear.matrix energyMatrix
  rw [linear_matrix]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro r; fin_cases r <;> simp [certificate]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [certificate, energyMatrix, WeightedSquares.matrix_entry, Fin.sum_univ_two]
  · intro r; fin_cases r; simp [certificate]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [certificate, energyMatrix, dissipation, WeightedSquares.matrix_entry,
        Fin.sum_univ_two]

theorem quadratic_energyMatrix (x : Point 2) :
    quadratic energyMatrix x = 2 * x 0 ^ 2 + x 1 ^ 2 := by
  simp [energyMatrix, quadratic, realMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, pow_two]
  ring

/-- The time domain is `t ≥ 0`. -/
theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t := by
  simp [Dynamics.TimeDomain.domain, Evolution.time, evolution]

/-- Every exact continuous realization keeps `E` in `[0, 2]` for `t ≥ 0`. -/
theorem compiled_energy_bound (state : Dynamics.Signal 2)
    (realized : compiled.Realizes state) (t : ℝ) (forward : 0 ≤ t) :
    0 ≤ compiled.outputs.circuit.run (state t) energyIndex ∧
    compiled.outputs.circuit.run (state t) energyIndex ≤ 2 := by
  have initial : quadratic energyMatrix compiledProblem.initial ≤ 2 := by
    change quadratic energyMatrix compiled.initial ≤ 2
    rw [initial_eq, quadratic_energyMatrix]
    norm_num
  have h := certificate_energy_bound compiledProblem energyMatrix certificate
    certificate_valid state (compiled_solves state realized) 2 initial t
    ((domain_iff t).mpr forward)
  simpa only [energy_at, quadratic_energyMatrix] using h

/-- One is already false at the exact initial state. -/
theorem initial_not_bounded_by_one :
    ¬ compiled.outputs.circuit.run compiled.initial energyIndex ≤ 1 := by
  rw [energy_at_initial]
  norm_num

end Gimle.Forseti.Examples.DampedOscillator
