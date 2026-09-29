import Gimle.Forseti.LinearCircuitHoare
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Equivalent damped Jordan chains

This Lean module is also the native Forseti notebook for the worked examples.
The prose and proofs share one source; the adjacent `.forseti.json` records
per-claim checking observations, which can be regenerated with Forseti.

Let `S` be the nilpotent shift sending `(x₀,x₁,x₂)` to `(0,x₀,x₁)` in dimension
three. Compare updates `A = (I + S)/2` and `B = I/2 + S`. Both start at the
first basis vector. Read the last coordinate of the first system and one
quarter of the last coordinate of the second. Although the middle coordinates
after one step are `1/2` and `1`, their selected output streams agree.

The three-dimensional outputs start `0, 0, 1/4, 3/8, 3/8, 5/16`. Six
comparisons suffice because the sum of the dimensions is six. We also check
the one- and two-dimensional versions, with output scalings `1` and `1/2`.
These are exact rational calculations embedded into real circuit semantics.
The proved property is output equality; a decay-rate or stability estimate
would require a separate theorem.
-/
namespace Gimle.Forseti.Examples.LinearCircuitJordan

open Gimle.Asgard Gimle.Forseti Gimle.Forseti.LinearCircuit
open FiniteLinearEquivalence
open scoped Matrix

/-- A one-coordinate damped chain; both selected realizations coincide here. -/
def jordanLeft1 : Program 1 where
  updates := ![.mul (.constant (1 / 2)) (.var 0)]
  readout := .var 0
  matrix := ![![1 / 2]]
  weights := ![1]
  updates_ok := by intro i; fin_cases i; decide +kernel
  readout_ok := by decide +kernel

/-- In dimension one the scaled and unscaled shift are both zero. -/
def jordanRight1 : Program 1 := jordanLeft1

/-- Two coordinates with update `(I + S)/2`, reading the last coordinate. -/
def jordanLeft2 : Program 2 where
  updates := ![.mul (.constant (1 / 2)) (.var 0),
    .add (.mul (.constant (1 / 2)) (.var 0)) (.mul (.constant (1 / 2)) (.var 1))]
  readout := .var 1
  matrix := ![![1 / 2, 0], ![1 / 2, 1 / 2]]
  weights := ![0, 1]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- Two coordinates with update `I/2 + S`, reading half the last coordinate. -/
def jordanRight2 : Program 2 where
  updates := ![.mul (.constant (1 / 2)) (.var 0),
    .add (.var 0) (.mul (.constant (1 / 2)) (.var 1))]
  readout := .mul (.constant (1 / 2)) (.var 1)
  matrix := ![![1 / 2, 0], ![1, 1 / 2]]
  weights := ![0, 1 / 2]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- Three coordinates with update `(I + S)/2`, reading the last coordinate. -/
def jordanLeft3 : Program 3 where
  updates := ![.mul (.constant (1 / 2)) (.var 0),
    .add (.mul (.constant (1 / 2)) (.var 0)) (.mul (.constant (1 / 2)) (.var 1)),
    .add (.mul (.constant (1 / 2)) (.var 1)) (.mul (.constant (1 / 2)) (.var 2))]
  readout := .var 2
  matrix := ![![1 / 2, 0, 0], ![1 / 2, 1 / 2, 0], ![0, 1 / 2, 1 / 2]]
  weights := ![0, 0, 1]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-- Three coordinates with update `I/2 + S`, reading one quarter of the last. -/
def jordanRight3 : Program 3 where
  updates := ![.mul (.constant (1 / 2)) (.var 0),
    .add (.var 0) (.mul (.constant (1 / 2)) (.var 1)),
    .add (.var 1) (.mul (.constant (1 / 2)) (.var 2))]
  readout := .mul (.constant (1 / 4)) (.var 2)
  matrix := ![![1 / 2, 0, 0], ![1, 1 / 2, 0], ![0, 1, 1 / 2]]
  weights := ![0, 0, 1 / 4]
  updates_ok := by intro i; fin_cases i <;> decide +kernel
  readout_ok := by decide +kernel

/-!
## Initial states and the finite predicate

Every example starts at the first basis vector. `embed` casts rational
coordinates exactly into the real state space. The helper below transports a
finite rational matrix calculation to `prefixFormula`, an existing Forseti
formula about the original compiled programs. The transport is justified by
`Program.observe_ratCast`, rather than by an independently translated program.
-/

/-- Explicit rational initial vectors, with the first coordinate equal to one. -/
def initial1 : Fin 1 → ℚ := ![1]
def initial2 : Fin 2 → ℚ := ![1, 0]
def initial3 : Fin 3 → ℚ := ![1, 0, 0]

/-- The exact real initialization associated to a rational vector. -/
def embed {d : Nat} (x : Fin d → ℚ) : Point d := fun i => (x i : ℝ)

/-- Finite rational evidence constructs the existing formula, without changing core APIs. -/
private theorem prefix_of_rational_prefix {d₁ d₂ : Nat}
    (P : Program d₁) (Q : Program d₂) (x : Fin d₁ → ℚ) (y : Fin d₂ → ℚ)
    (h : ∀ n : Fin (d₁ + d₂),
      matrix_output P.matrix x P.weights n = matrix_output Q.matrix y Q.weights n) :
    (prefixFormula P Q).holds (pointAppend (embed x) (embed y)) := by
  rw [prefixFormula_holds_iff]
  simp only [pointLeft_pointAppend, pointRight_pointAppend]
  intro n hn
  calc
    P.observe (embed x) n = (matrix_output P.matrix x P.weights n : ℝ) :=
      P.observe_ratCast x n
    _ = (matrix_output Q.matrix y Q.weights n : ℝ) :=
      congrArg (fun q : ℚ => (q : ℝ)) (h ⟨n, hn⟩)
    _ = Q.observe (embed y) n := (Q.observe_ratCast y n).symm

/-!
## Three concrete applications of the same interface

For each dimension, `decide +kernel` checks the finite rational calculation.
The resulting initialization claim supplies `observations_eq_of_prefixFormula`.
That library endpoint consumes `prefix_safety`: the existing
`Discrete.certificate_sound` rule instantiated with the preservation Hoare
triple `prefix_hoare` and the predicate entailment `prefix_entails_output`.
Consequently each infinite conclusion is about the original compiled circuits
and their initialized executions, not only about their matrix representations.

Dimension one is a boundary check where the two realizations coincide. The
following two dimensions exercise genuinely different transition circuits.
-/

/-- Dimension-one initialization satisfies the actual finite observation formula. -/
theorem jordan1_prefix :
    (prefixFormula jordanLeft1 jordanRight1).holds
      (pointAppend (embed initial1) (embed initial1)) := by
  apply prefix_of_rational_prefix
  decide +kernel

/-- Dimension-one output equality uses the existing Hoare/safety endpoint. -/
theorem jordan1_equivalent : ∀ n,
    jordanLeft1.observe (embed initial1) n = jordanRight1.observe (embed initial1) n := by
  exact observations_eq_of_prefixFormula jordanLeft1 jordanRight1 _ _ jordan1_prefix

/-- Dimension-two initialization satisfies the actual finite observation formula. -/
theorem jordan2_prefix :
    (prefixFormula jordanLeft2 jordanRight2).holds
      (pointAppend (embed initial2) (embed initial2)) := by
  apply prefix_of_rational_prefix
  decide +kernel

/-- Distinct dimension-two realizations agree through the existing Hoare/safety endpoint. -/
theorem jordan2_equivalent : ∀ n,
    jordanLeft2.observe (embed initial2) n = jordanRight2.observe (embed initial2) n := by
  exact observations_eq_of_prefixFormula jordanLeft2 jordanRight2 _ _ jordan2_prefix

/-- Dimension-three initialization satisfies the actual finite observation formula. -/
theorem jordan3_prefix :
    (prefixFormula jordanLeft3 jordanRight3).holds
      (pointAppend (embed initial3) (embed initial3)) := by
  apply prefix_of_rational_prefix
  decide +kernel

/-- Distinct dimension-three realizations agree through the existing Hoare/safety endpoint. -/
theorem jordan3_equivalent : ∀ n,
    jordanLeft3.observe (embed initial3) n = jordanRight3.observe (embed initial3) n := by
  exact observations_eq_of_prefixFormula jordanLeft3 jordanRight3 _ _ jordan3_prefix

/-!
## Independent numerical controls

Agreement between two implementations alone would not rule out the same
mistake in both. The next claims compare the selected left outputs with
prescribed exact values, independently of the equality proof. Observation zero
is included. Finally, explicit unequal next-state coordinates confirm that the
two nontrivial examples really have different transitions.
-/

/-- Independent expected outputs prevent a merely coincident wrong-prefix check. -/
theorem jordan2_expected (n : Fin 4) :
    jordanLeft2.observe (embed initial2) n = (![0, 1 / 2, 1 / 2, 3 / 8] : Fin 4 → ℝ) n := by
  have h : ∀ k : Fin 4, matrix_output jordanLeft2.matrix initial2 jordanLeft2.weights k =
      (![0, 1 / 2, 1 / 2, 3 / 8] : Fin 4 → ℚ) k := by decide +kernel
  calc
    jordanLeft2.observe (embed initial2) n =
        (matrix_output jordanLeft2.matrix initial2 jordanLeft2.weights n : ℝ) :=
      jordanLeft2.observe_ratCast initial2 n
    _ = ((![0, 1 / 2, 1 / 2, 3 / 8] : Fin 4 → ℚ) n : ℝ) :=
      congrArg (fun q : ℚ => (q : ℝ)) (h n)
    _ = _ := by fin_cases n <;> norm_num

/-- The six-observation dimension-three prefix has the prescribed binomial values. -/
theorem jordan3_expected (n : Fin 6) :
    jordanLeft3.observe (embed initial3) n =
      (![0, 0, 1 / 4, 3 / 8, 3 / 8, 5 / 16] : Fin 6 → ℝ) n := by
  have h : ∀ k : Fin 6, matrix_output jordanLeft3.matrix initial3 jordanLeft3.weights k =
      (![0, 0, 1 / 4, 3 / 8, 3 / 8, 5 / 16] : Fin 6 → ℚ) k := by decide +kernel
  calc
    jordanLeft3.observe (embed initial3) n =
        (matrix_output jordanLeft3.matrix initial3 jordanLeft3.weights n : ℝ) :=
      jordanLeft3.observe_ratCast initial3 n
    _ = ((![0, 0, 1 / 4, 3 / 8, 3 / 8, 5 / 16] : Fin 6 → ℚ) n : ℝ) :=
      congrArg (fun q : ℚ => (q : ℝ)) (h n)
    _ = _ := by fin_cases n <;> norm_num

/-- The two nontrivial trials really use different next-state circuits. -/
theorem jordan2_different_updates :
    jordanLeft2.update.run (embed initial2) 1 ≠ jordanRight2.update.run (embed initial2) 1 := by
  norm_num [Program.update_run, jordanLeft2, jordanRight2, embed, initial2, Fin.sum_univ_succ]

theorem jordan3_different_updates :
    jordanLeft3.update.run (embed initial3) 1 ≠ jordanRight3.update.run (embed initial3) 1 := by
  norm_num [Program.update_run, jordanLeft3, jordanRight3, embed, initial3, Fin.sum_univ_succ]

#print axioms jordan1_prefix
#print axioms jordan1_equivalent
#print axioms jordan2_prefix
#print axioms jordan2_equivalent
#print axioms jordan3_prefix
#print axioms jordan3_equivalent
#print axioms jordan2_expected
#print axioms jordan3_expected
#print axioms jordan2_different_updates
#print axioms jordan3_different_updates

end Gimle.Forseti.Examples.LinearCircuitJordan
