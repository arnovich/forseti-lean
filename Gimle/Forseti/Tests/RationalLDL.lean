module

public import Gimle.Forseti.RationalLDL

/-! The proposal is untrusted: acceptance still checks every weight and entry. -/

@[expose] public section

namespace Gimle.Forseti.Tests.RationalLDL
open Gimle.Forseti.LinearEnergy Gimle.Forseti.RationalLDL

def positive : QMatrix 3 := ![![4, 2, 0], ![2, 3, 1], ![0, 1, 2]]

example : (propose positive).Represents positive := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- Empty and zero matrices are harmless semidefinite cases. -/
example : (propose (0 : QMatrix 0)).Represents 0 := by
  unfold WeightedSquares.Represents
  decide +kernel
example : (propose (0 : QMatrix 2)).Represents 0 := by
  unfold WeightedSquares.Represents
  decide +kernel
example : (propose (![![1, 0, 0], ![0, 0, 0], ![0, 0, 2]] : QMatrix 3)).Represents
    ![![1, 0, 0], ![0, 0, 0], ![0, 0, 2]] := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- Positive diagonal entries alone do not certify a matrix. -/
example : ¬ (propose (![![1, 2], ![2, 1]] : QMatrix 2)).Represents
    ![![1, 2], ![2, 1]] := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- Asymmetry cannot disappear into the proposal's triangular factor. -/
example : ¬ (propose (![![2, 1], ![0, 2]] : QMatrix 2)).Represents
    ![![2, 1], ![0, 2]] := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- A zero pivot with a nonzero row does not gain validity through division by zero. -/
example : ¬ (propose (![![0, 1], ![1, 2]] : QMatrix 2)).Represents
    ![![0, 1], ![1, 2]] := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- A certificate is tied to all target entries, not just its pivots. -/
example : ¬ (propose positive).Represents
    (![![4, 2, 0], ![2, 3, 2], ![0, 2, 2]] : QMatrix 3) := by
  unfold WeightedSquares.Represents
  decide +kernel

theorem positive_nonnegative (x : Fin 3 → ℝ) : 0 ≤ quadratic positive x :=
  (propose positive).nonnegative positive (by
    unfold WeightedSquares.Represents
    decide +kernel) x

/-- info: 'Gimle.Forseti.Tests.RationalLDL.positive_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive_nonnegative

end Gimle.Forseti.Tests.RationalLDL
