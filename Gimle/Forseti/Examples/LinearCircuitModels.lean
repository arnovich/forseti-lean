import Gimle.Forseti.LinearCircuitHoare
import Mathlib.Tactic.FinCases

/-! Compiled program definitions shared by the Fibonacci regression tests and notebook. -/

namespace Gimle.Forseti.Examples.LinearCircuitModels

open Gimle.Asgard Gimle.Forseti Gimle.Forseti.LinearCircuit
open scoped Matrix

/-- Every source coordinate is retained in the original compiled expression. -/
def fibonacci : Program 2 where
  updates := ![.add (.var 0) (.var 1), .var 0]
  readout := .var 0
  matrix := ![![1, 1], ![1, 0]]
  weights := ![1, 0]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- Swapped visible coordinates and an unobserved growing coordinate. -/
def extendedFibonacci : Program 3 where
  updates := ![.var 1, .add (.var 0) (.var 1), .mul (.constant 2) (.var 2)]
  readout := .var 1
  matrix := ![![0, 1, 0], ![1, 1, 0], ![0, 0, 2]]
  weights := ![0, 1, 0]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- A consistently conjugated coordinate permutation. -/
def permutedFibonacci : Program 2 where
  updates := ![.var 1, .add (.var 0) (.var 1)]
  readout := .var 1
  matrix := ![![0, 1], ![1, 1]]
  weights := ![0, 1]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

end Gimle.Forseti.Examples.LinearCircuitModels
