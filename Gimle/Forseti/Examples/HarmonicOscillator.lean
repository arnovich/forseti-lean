import Gimle.Forseti.LinearEnergyContract
import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Model.SourceSyntax

/-! The undamped oscillator `4x'' + x = 0`, given its contract only through
`LinearEnergyContract`.

The source is the second-order equation with a declared velocity
(asgard-lean 027): `dv : 4 * D_t(D_t(x)) + x = 0` and `dx : D_t(x) = v`,
from `x(0) = 1`, `v(0) = 0`, with the energy `E := x^2 + 4*v^2` observed. The
energy is conserved: `dE/dt = 2xv + 8v·(−x/4) = 0`, so the certificate's
decrease is the empty sum, and `E` stays in `[0, 1]`.

Everything model-specific is data: the source, the matrix `P = diag(1, 4)`, and
its certificate. The contract is `LinearEnergyContract` applied to `spec`,
which is the task-029 measure of how much a new model costs. -/

namespace Gimle.Forseti.Examples.HarmonicOscillator

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Forseti.LinearEnergy
open Gimle.Asgard Gimle.Asgard.Model Polynomial

/-- The source, with observations `[x, v, E]`. -/
def body : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"state-v", "v", .state⟩]
  assignments := assignments% { E := x ^ 2 + 4 * v ^ 2; }
  differentials := differentials% { dv : 4 * diff(diff(x, t), t) + x = 0; }
  velocities := velocities% { dx : diff(x, t) = v; }
  observations := [⟨⟨"obs-x", "x", .output⟩, "state-x"⟩,
    ⟨⟨"obs-v", "v", .output⟩, "state-v"⟩,
    ⟨⟨"obs-e", "E", .output⟩, "E"⟩]
}

/-- State order [x, v], from `x(0) = 1`, `v(0) = 0` at `t = 0`. -/
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-v", "dv", "initial-v"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-v", "v0", .initial⟩]
  initialValues := [⟨"initial-x", 1⟩, ⟨"initial-v", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def model : SourceContinuousModel body evolution :=
  (compileSourceContinuous body evolution).toOption.get (by decide +kernel)

abbrev compiled : ContinuousModel model.lowered.body evolution := model.model

theorem initial_eq : compiled.initial = (![1, 0] : Point 2) := by
  change (fun i : Fin 2 => (compiled.initials i : ℝ)) = _
  have values : compiled.initials = ![1, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

def energyIndex : Fin body.observations.length := ⟨2, by decide⟩

theorem energy_at (x : Point 2) :
    compiled.outputs.circuit.run x energyIndex = x 0 ^ 2 + 4 * x 1 ^ 2 := by
  rw [Selected.circuit, compileOutputs_correct]
  change (compiled.outputs.expressions energyIndex).eval x = _
  have expression : compiled.outputs.expressions energyIndex =
      (.add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.constant 4) (.mul (.mul (.constant 1) (.var 1)) (.var 1))) : Expr 2) := by
    decide +kernel
  rw [expression]
  simp [Expr.eval, pow_two]

theorem energy_at_initial : compiled.outputs.circuit.run compiled.initial energyIndex = 1 := by
  rw [energy_at, initial_eq]
  norm_num

noncomputable def linear : LinearView compiled := compiled.linear.get (by decide +kernel)

theorem linear_matrix : linear.matrix = ![![0, 1], ![-1 / 4, 0]] := by decide +kernel

/-- `P = diag(1, 4)`. -/
def energyMatrix : QMatrix 2 := ![![1, 0], ![0, 4]]

/-- `P = 1·e₀² + 4·e₁²`; the dissipation `−(AᵀP + PA)` is zero, the empty sum. -/
def certificate : Certificate 2 where
  positive := ⟨2, ![1, 4], ![![1, 0], ![0, 1]]⟩
  decrease := ⟨0, ![], ![]⟩

theorem certificate_valid : certificate.Valid linear.matrix energyMatrix := by
  rw [linear_matrix]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro r; fin_cases r <;> simp [certificate]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [certificate, energyMatrix, WeightedSquares.matrix_entry, Fin.sum_univ_two]
  · intro r; exact Fin.elim0 r
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [certificate, energyMatrix, dissipation, WeightedSquares.matrix_entry,
        Fin.sum_univ_two]

theorem quadratic_energyMatrix (x : Point 2) :
    quadratic energyMatrix x = x 0 ^ 2 + 4 * x 1 ^ 2 := by
  simp [energyMatrix, quadratic, realMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, pow_two]
  ring

noncomputable def spec : LinearEnergyContract.Spec compiled where
  view := linear
  energy := energyIndex
  matrix := energyMatrix
  energy_eq x := (energy_at x).trans (quadratic_energyMatrix x).symm
  certificate := certificate
  valid := certificate_valid

/-! ## The contract, from the construction alone -/

def observed := LinearEnergyContract.observed compiled

def admitted := LinearEnergyContract.admitted compiled

/-- **The conserved energy stays in `[0, 1]`** for every admitted input. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 1) :=
  spec.energy_contract 1 (le_of_eq energy_at_initial)

/-- A half is not a bound: `E = 1` at the start. -/
theorem half_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 1 / 2) :=
  spec.refuted (1 / 2) (by
    show (1 / 2 : ℝ) < compiled.outputs.circuit.run compiled.initial energyIndex
    rw [energy_at_initial]; norm_num)

end Gimle.Forseti.Examples.HarmonicOscillator
