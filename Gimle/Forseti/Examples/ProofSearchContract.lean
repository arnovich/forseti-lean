import Gimle.Forseti.Examples.ThreeState

/-! The checked interface for bounded proof-search certificates.

The ThreeState example supplies one known proof of the three-state energy bound.
This module states the *contract* around it: what a searcher may propose, what makes a
proposal valid, and which reusable lemma turns a valid proposal into the
property. Nothing here searches; the certificate below is written by hand and
stands in for what a searcher would emit.

The separation that matters: `certificate` is searched evidence, while
`energy_bound` in `Examples/ThreeState.lean` is the baseline result. A searcher
must not be handed the baseline theorem as its answer. -/
namespace Gimle.Forseti.Examples.ProofSearchContract
open Gimle.Asgard Gimle.Asgard.Model
open Gimle.Forseti.LinearEnergy
open Gimle.Forseti.Examples.ThreeState

/-! ## The search space

A proposal is a `Certificate`: two `WeightedSquares` decompositions, one
certifying that the energy form is nonnegative and one certifying that its
dissipation is. Both carry exact rational weights and vectors, so validity is
decidable arithmetic rather than a tactic search. -/

/-- The unit vectors, the only directions this bounded family uses. -/
def unit (r : Fin 3) : Fin 3 → ℚ := fun i => if i = r then 1 else 0

/-- Identity weights: V = x² + y² + z², the energy the model already observes. -/
def positiveSquares : WeightedSquares 3 where
  count := 3
  weight := fun _ => 1
  vector := unit

/-- Dissipation weights `2a, 2b, 2c`, which is what the skew-symmetric coupling
leaves behind. A searcher proposes these; it does not get told them. -/
def decreaseSquares (a b c : ℚ) : WeightedSquares 3 where
  count := 3
  weight := fun r => ![2 * a, 2 * b, 2 * c] r
  vector := unit

def candidate (a b c : ℚ) : Certificate 3 :=
  { positive := positiveSquares, decrease := decreaseSquares a b c }

/-! ## What makes a proposal valid

`Certificate.Valid` recomputes the dissipation from the field matrix and checks
every exact entry against the proposed decomposition. This is the whole check —
no tactic, no trust in the proposer. -/

/-- The energy form is a sum of unit squares with weight one. -/
theorem positive_represents : positiveSquares.Represents identity := by
  refine ⟨fun _ => by show (0 : ℚ) ≤ 1; norm_num, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveSquares, identity, unit, Fin.sum_univ_three]

/-- The dissipation is a sum of unit squares with weights `2a, 2b, 2c`, which is
nonnegative exactly when the damping coefficients are. ThreeState's
`dissipation_eq` supplies the entry identity, so this reuses the recomputation
rather than repeating it. -/
theorem decrease_represents {a b c : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (decreaseSquares a b c).Represents (dissipation (expectedMatrix a b c) identity) := by
  refine ⟨?_, ?_⟩
  · intro r
    fin_cases r
    · show (0 : ℚ) ≤ 2 * a
      linarith
    · show (0 : ℚ) ≤ 2 * b
      linarith
    · show (0 : ℚ) ≤ 2 * c
      linarith
  · intro i j
    rw [dissipation_eq]
    fin_cases i <;> fin_cases j <;>
      norm_num [decreaseSquares, diagonal, unit, Fin.sum_univ_three]

/-- A searcher's proposal is valid for any nonnegative damping triple. Assembled
as a term so the certificate's projections need no unfolding. -/
theorem candidate_valid {a b c : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (candidate a b c).Valid (expectedMatrix a b c) identity :=
  ⟨positive_represents, decrease_represents ha hb hc⟩

/-! ## The reusable lemma the contract turns on

`certificate_energy_bound` converts any valid certificate plus a sublevel
initial condition into the bound, for every solution on the forward domain. A
searcher that produces a valid certificate has produced a proof. -/

theorem searched_energy_bound (state : Dynamics.Signal 3)
    (solves : compiledProblem.Solves state) (t : ℝ)
    (forward : t ∈ compiledProblem.time.domain) :
    0 ≤ quadratic identity (state t) ∧ quadratic identity (state t) ≤ 6 := by
  refine certificate_energy_bound compiledProblem identity (candidate (1 / 3) (1 / 2) 2)
    ?_ state solves 6 ?_ t forward
  · rw [compiled_problem_matrix]
    exact candidate_valid (by norm_num) (by norm_num) (by norm_num)
  · rw [compiled_problem_initial, quadratic_identity]
    norm_num [show (![1, 2, -1] : Point 3) 2 = -1 from rfl]

/-! ## Hostile cases

A contract is only as good as what it refuses. -/

/-- Nonnegativity is what a searcher cannot fake. `decrease_represents` requires
`0 ≤ a`, and ThreeState's `dissipation_negative_of_negative_coefficient` shows why:
with a negative coefficient the dissipation form takes negative values, so no
weighted-squares decomposition of it exists and `Certificate.Valid` is
unavailable. The bound is therefore not reachable by proposing negative damping. -/
theorem negative_damping_blocks_the_family :
    quadratic (dissipation (expectedMatrix (-1) 0 0) identity) ![1, 0, 0] < 0 :=
  dissipation_negative_of_negative_coefficient

/-- A certificate for different coefficients does not validate this field: the
check recomputes the dissipation rather than trusting the proposal. -/
theorem stale_coefficients_rejected :
    ¬ (candidate 1 (1 / 2) 2).Valid (expectedMatrix (1 / 3) (1 / 2) 2) identity := by
  intro valid
  have entry := valid.2.2 ⟨0, by decide⟩ ⟨0, by decide⟩
  rw [dissipation_eq] at entry
  norm_num [candidate, diagonal, decreaseSquares, unit, Fin.sum_univ_three] at entry

/-- The bound is not free: five fails at the declared initial state, so a
searcher claiming it is refuted by the same sublevel check the contract uses. -/
theorem five_is_not_a_sublevel_bound :
    ¬ quadratic identity compiledProblem.initial ≤ 5 := by
  rw [compiled_problem_initial, quadratic_identity]
  norm_num [show (![1, 2, -1] : Point 3) 2 = -1 from rfl]

#print axioms candidate_valid
#print axioms searched_energy_bound
#print axioms negative_damping_blocks_the_family
#print axioms stale_coefficients_rejected
#print axioms five_is_not_a_sublevel_bound

end Gimle.Forseti.Examples.ProofSearchContract
