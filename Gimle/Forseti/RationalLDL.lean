module

public import Gimle.Forseti.LinearEnergy

/-! Compact rational LDL proposals for the existing weighted-square checker.

The recursion is a producer, not a new validity rule. Division by zero and
negative pivots are allowed in proposals; `WeightedSquares.Represents` must
still check every weight and every matrix entry in the ordinary kernel.
No soundness claim relies on the algorithm finding a valid decomposition.
-/

@[expose] public section

namespace Gimle.Forseti.RationalLDL
open Gimle.Forseti.LinearEnergy

/-- Rational pivots and rows of the transposed unit lower triangular factor. -/
def factors : (n : Nat) → QMatrix n → (Fin n → ℚ) × QMatrix n
  | 0, _ => (Fin.elim0, fun i => Fin.elim0 i)
  | n + 1, a =>
    let pivot := a 0 0
    let row : Fin n → ℚ := fun j => a 0 j.succ / pivot
    let remainder : QMatrix n := fun i j => a i.succ j.succ - pivot * row i * row j
    let tail := factors n remainder
    (Fin.cons pivot tail.1,
      Fin.cons (Fin.cons 1 row) (fun i => Fin.cons 0 (tail.2 i)))

/-- Recompute proposed square data from a target, avoiding repeated large literals. -/
def propose {n : Nat} (a : QMatrix n) : WeightedSquares n where
  count := n
  weight := (factors n a).1
  vector := (factors n a).2

end Gimle.Forseti.RationalLDL
