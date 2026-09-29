import Gimle.Forseti.LinearCircuitHoare
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two programs producing the Fibonacci stream

This Lean module is also a native Forseti notebook: the prose explains the
same declarations that `lake build` checks, and the adjacent `.forseti.json`
records per-claim checks. There is one authored proof source.

Consider the simultaneous recurrences

$$ (x_0,x_1)^+ = (x_0+x_1,x_0), \qquad o_x=x_0, $$
$$ (y_0,y_1,y_2)^+ = (y_1,y_0+y_1,2y_2), \qquad o_y=y_1. $$

At starts `(0,1)` and `(1,0,1)`, respectively, both output prefixes are
`0, 1, 1, 2, 3`. Observation zero reads the initial state, before any update.
The extra coordinate doubles at each step and is unobserved. Output agreement
does not imply bounded states or identical state representations.

The sum of the state dimensions is five. The reusable finite-dimensional
criterion proves that equality of these five observations implies equality at
every natural-number step. Below we first establish that prefix for the larger
family `(0,r)` and `(r,0,r)`, for every real `r`, then specialize to `r = 1`.
All semantics are exact over the reals with rational coefficients.
-/

namespace Gimle.Forseti.Examples.LinearCircuitFibonacci

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

/-!
## A finite formula at initialization

`prefixFormula` is an existing Forseti `Syntax.Formula`, built from conjunctions
of equality atoms. Each atom substitutes the original polynomial updates into
the readout. `prefixFormula_holds_iff` identifies its denotation with the five
compiled-output comparisons. The following proof checks those comparisons
symbolically; it does not assume the desired infinite conclusion.
-/

/-- Symbolic real scaling exercises all real states of this family. -/
theorem fibonacci_scaled_prefix (r : ℝ) :
    (prefixFormula fibonacci extendedFibonacci).holds
      (pointAppend ![0, r] ![r, 0, r]) := by
  rw [prefixFormula_holds_iff]
  simp only [pointLeft_pointAppend, pointRight_pointAppend]
  intro n hn
  interval_cases n <;>
    norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
      Program.update, fibonacci, extendedFibonacci, Polynomial.Expr.eval]
  ring

/-!
## From predicates and Hoare triples to executions

The library theorem `prefix_hoare` proves `{K} pairedUpdate {K}`, where `K` is
the prefix formula. Cayley–Hamilton on the combined state space supplies the
finite-dimensional step. `prefix_entails_output` gives the predicate entailment
from `K` to equality of the current readouts. `prefix_safety` combines these
premises with the existing `Discrete.certificate_sound` rule.

`observations_eq_of_prefixFormula` consumes that all-step safety contract and
the proved initialization. It identifies the paired run with the two original
`Discrete.run` executions and obtains equality of their selected outputs.
Thus the endpoint below really uses the existing predicate and Hoare calculus.
-/

theorem fibonacci_scaled_equivalent (r : ℝ) :
    ∀ n, fibonacci.observe ![0, r] n = extendedFibonacci.observe ![r, 0, r] n := by
  exact observations_eq_of_prefixFormula fibonacci extendedFibonacci _ _
    (fibonacci_scaled_prefix r)

theorem fibonacci_prefix :
    (prefixFormula fibonacci extendedFibonacci).holds
      (pointAppend ![0, 1] ![1, 0, 1]) := by
  exact fibonacci_scaled_prefix 1

theorem fibonacci_equivalent :
    ∀ n, fibonacci.output.run
        (Discrete.run (u := 0) (p := 0) fibonacci.update
          empty ![0, 1] (fun (_step : Nat) => empty) n) 0 =
      extendedFibonacci.output.run
        (Discrete.run (u := 0) (p := 0) extendedFibonacci.update
          empty ![1, 0, 1] (fun (_step : Nat) => empty) n) 0 := by
  exact observations_eq_of_prefixFormula fibonacci extendedFibonacci _ _ fibonacci_prefix

/-!
## The explicit Hoare judgment

This specialization exposes the reusable preservation result as the existing
`ExactHoare` judgment over the compiled paired circuit. The earlier infinite
conclusions use this same generic preservation theorem through `prefix_safety`;
they do not depend on this later specialized alias.
-/

theorem fibonacci_hoare :
    ExactHoare (prefixFormula fibonacci extendedFibonacci).toPredicate
      (pairedUpdate fibonacci extendedFibonacci)
      (prefixFormula fibonacci extendedFibonacci).toPredicate := by
  exact prefix_hoare fibonacci extendedFibonacci

/-!
## A second realization: permuting the coordinates

Swapping the two visible coordinates, while also swapping the update and
readout consistently, gives a two-state realization. Now the total dimension
is four, so the finite initialization proof has four comparisons. The same
safety endpoint establishes the infinite conclusion without changing the
reusable library.
-/

theorem permutation_prefix :
    (prefixFormula fibonacci permutedFibonacci).holds
      (pointAppend ![0, 1] ![1, 0]) := by
  rw [prefixFormula_holds_iff]
  simp only [pointLeft_pointAppend, pointRight_pointAppend]
  intro n hn
  interval_cases n <;>
    norm_num [Program.observe, Program.output, Program.state_succ, Program.state_zero,
      Program.update, fibonacci, permutedFibonacci, Polynomial.Expr.eval]

theorem permutation_equivalent :
    ∀ n, fibonacci.observe ![0, 1] n = permutedFibonacci.observe ![1, 0] n := by
  exact observations_eq_of_prefixFormula fibonacci permutedFibonacci _ _ permutation_prefix

#print axioms fibonacci_scaled_prefix
#print axioms fibonacci_scaled_equivalent
#print axioms fibonacci_equivalent
#print axioms fibonacci_hoare
#print axioms permutation_equivalent

end Gimle.Forseti.Examples.LinearCircuitFibonacci
