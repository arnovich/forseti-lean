import Gimle.Forseti.Examples.LinearCircuitFibonacci
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! Regression checks for compiled linear programs: initialization, port order,
empty states, exact casts, and unsupported syntax. Worked proofs are imported
from Examples; the reusable property modules remain independent of both. -/

namespace Gimle.Forseti.Tests.LinearCircuit

open Gimle.Asgard Gimle.Forseti Gimle.Forseti.LinearCircuit
open Gimle.Forseti.Examples.LinearCircuitFibonacci
open scoped Matrix

/-- Empty state spaces must remain admissible, including their zero readout. -/
def emptyProgram : Program 0 where
  updates := Fin.elim0
  readout := .constant 0
  matrix := fun i => Fin.elim0 i
  weights := Fin.elim0
  updates_ok := fun i => Fin.elim0 i
  readout_ok := by decide +kernel

/-- Changing one coefficient changes the visible recurrence. -/
def changedUpdate : Program 3 where
  updates := ![.var 1, .add (.var 0) (.mul (.constant 2) (.var 1)),
    .mul (.constant 2) (.var 2)]
  readout := .var 1
  matrix := ![![0, 1, 0], ![1, 2, 0], ![0, 0, 2]]
  weights := ![0, 1, 0]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- Swapping next-state ports alone is not a coordinate conjugacy. -/
def swappedUpdates : Program 2 where
  updates := ![.var 0, .add (.var 0) (.var 1)]
  readout := .var 0
  matrix := ![![1, 0], ![1, 1]]
  weights := ![1, 0]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- Exact scalar recurrence with an independently specified readout coefficient. -/
def scalarProgram (a c : ℚ) : Program 1 where
  updates := ![.mul (.constant a) (.var 0)]
  readout := .mul (.constant c) (.var 0)
  matrix := ![![a]]
  weights := ![c]
  updates_ok := by
    intro i
    fin_cases i
    simp [Dynamics.LinearSyntax.coefficients]
    ext j
    fin_cases j
    simp
  readout_ok := by
    simp [Dynamics.LinearSyntax.coefficients]
    ext j
    fin_cases j
    simp

example : fibonacci.observe ![0, 1] 0 = 0 ∧ fibonacci.observe ![0, 1] 1 = 1 := by
  norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
    Program.update, fibonacci, Polynomial.Expr.eval]

example : extendedFibonacci.observe ![1, 0, 1] 0 = 0 ∧
    extendedFibonacci.observe ![1, 0, 1] 1 = 1 := by
  norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
    Program.update, extendedFibonacci, Polynomial.Expr.eval]

theorem empty_prefix :
    (prefixFormula emptyProgram emptyProgram).holds (pointAppend empty empty) := by
  rw [prefixFormula_holds_iff]
  intro n hn
  omega

theorem empty_equivalent : ∀ n, emptyProgram.observe empty n = emptyProgram.observe empty n :=
  observations_eq_of_prefixFormula emptyProgram emptyProgram _ _ empty_prefix

theorem one_empty_prefix :
    (prefixFormula (scalarProgram 2 1) emptyProgram).holds (pointAppend ![0] empty) := by
  rw [prefixFormula_holds_iff]
  simp only [pointLeft_pointAppend, pointRight_pointAppend]
  intro n hn
  interval_cases n
  norm_num [Program.observe, Program.output, Program.state_zero, scalarProgram,
    emptyProgram, Polynomial.Expr.eval]

theorem one_empty_equivalent :
    ∀ n, (scalarProgram 2 1).observe ![0] n = emptyProgram.observe empty n :=
  observations_eq_of_prefixFormula (scalarProgram 2 1) emptyProgram _ _ one_empty_prefix

example : (scalarProgram 1 1).observe ![1] 0 ≠ emptyProgram.observe empty 0 := by
  norm_num [Program.observe, Program.output, Program.state_zero, scalarProgram,
    emptyProgram, Polynomial.Expr.eval]

example : (scalarProgram (1 / 3) (-2 / 7)).observe ![2 / 5] 0 = -4 / 35 ∧
    (scalarProgram (1 / 3) (-2 / 7)).observe ![2 / 5] 1 = -4 / 105 := by
  norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
    Program.update, scalarProgram, Polynomial.Expr.eval]

/-- The rational-cast bridge agrees with the independent real execution checks. -/
theorem fractional_cast_control :
    (scalarProgram (1 / 3) (-2 / 7)).observe
        (fun i => ((![2 / 5] : Fin 1 → ℚ) i : ℝ)) 0 = -4 / 35 ∧
    (scalarProgram (1 / 3) (-2 / 7)).observe
        (fun i => ((![2 / 5] : Fin 1 → ℚ) i : ℝ)) 1 = -4 / 105 := by
  constructor <;> rw [Program.observe_ratCast] <;>
    norm_num [FiniteLinearEquivalence.matrix_output, scalarProgram, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

-- Independent witnesses against four plausible wiring/initialization errors.
example : fibonacci.observe ![1, 1] 0 ≠ extendedFibonacci.observe ![1, 0, 1] 0 := by
  norm_num [Program.observe, Program.output, Program.state_zero, fibonacci,
    extendedFibonacci, Polynomial.Expr.eval]

example : fibonacci.observe ![0, 1] 0 ≠
    (Polynomial.Expr.var (n := 3) 0).compile.run
      (extendedFibonacci.state ![1, 0, 1] 0) 0 := by
  norm_num [Program.observe, Program.output, Program.state_zero, fibonacci,
    Polynomial.Expr.eval]

example : fibonacci.observe ![0, 1] 2 ≠ changedUpdate.observe ![1, 0, 1] 2 := by
  norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
    Program.update, fibonacci, changedUpdate, Polynomial.Expr.eval]

example : swappedUpdates.observe ![0, 1] 1 ≠ extendedFibonacci.observe ![1, 0, 1] 1 := by
  norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
    Program.update, swappedUpdates, extendedFibonacci, Polynomial.Expr.eval]

-- Recognizer rejection is syntactic; cancellation is semantically zero.
example : Dynamics.LinearSyntax.coefficients
    (Polynomial.Expr.mul (n := 1) (.var 0) (.var 0)) = none := rfl
example : Dynamics.LinearSyntax.coefficients
    (Polynomial.Expr.add (n := 1) (.var 0) (.constant 1)) = none := by decide +kernel
example : Dynamics.LinearSyntax.coefficients
    (Polynomial.Expr.add (n := 1) (.mul (.var 0) (.var 0))
      (.neg (.mul (.var 0) (.var 0)))) = none := rfl

/-- The nonlinear readout from the earlier matrix control is rejected. -/
example : Dynamics.LinearSyntax.coefficients
    (Polynomial.Expr.mul (n := 1) (.add (.var 0) (.constant (-1)))
      (.add (.var 0) (.constant (-2)))) = none := rfl

/-- Raw compilation remains available outside the recognized linear fragment. -/
def affineUpdate : Circuit 1 1 :=
  Polynomial.compileOutputs ![.add (.var 0) (.constant 1)]

def doublingUpdate : Circuit 1 1 :=
  Polynomial.compileOutputs ![.mul (.constant 2) (.var 0)]

noncomputable def rawObservation (update : Circuit 1 1) (n : Nat) : ℝ :=
  (Polynomial.Expr.var (n := 1) 0).compile.run
    (Discrete.run (u := 0) (p := 0) update empty ![1] (fun _ => empty) n) 0

theorem affine_compiled_control :
    rawObservation affineUpdate 0 = 1 ∧ rawObservation doublingUpdate 0 = 1 ∧
    rawObservation affineUpdate 1 = 2 ∧ rawObservation doublingUpdate 1 = 2 ∧
    rawObservation affineUpdate 2 = 3 ∧ rawObservation doublingUpdate 2 = 4 := by
  norm_num [rawObservation, Discrete.run, autonomous_step, affineUpdate,
    doublingUpdate, Polynomial.Expr.eval]

#print axioms empty_equivalent
#print axioms one_empty_equivalent
#print axioms affine_compiled_control
#print axioms fractional_cast_control

end Gimle.Forseti.Tests.LinearCircuit
