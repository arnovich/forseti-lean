import Gimle.Forseti.BernsteinMatrix

namespace Gimle.Forseti.Tests.BernsteinMatrix
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix

-- Both closed endpoints matter: startup and segment handoff occur there.
example : basis 3 0 (0 : ℝ) = 1 := by norm_num [basis]
example : basis 3 3 (1 : ℝ) = 1 := by norm_num [basis]
example : basis 0 0 (0 : ℝ) = 1 := by norm_num [basis]

-- A mixed-sign basis outside the box cannot support a global positivity claim.
example : basis 1 0 (2 : ℝ) < 0 := by norm_num [basis]

def square : WeightedSquares 2 where
  count := 1
  weight := ![1]
  vector := ![![1, 1]]

example : square.Represents ![![1, 1], ![1, 1]] := by
  unfold WeightedSquares.Represents
  decide +kernel

-- Check every entry: retaining diagonals but changing a cross term is invalid.
example : ¬ square.Represents ![![1, 0], ![1, 1]] := by
  unfold WeightedSquares.Represents
  decide +kernel

-- Negative weights cannot be silently admitted, even for a zero vector.
def negative : WeightedSquares 1 where
  count := 1
  weight := ![-1]
  vector := ![![0]]
example : ¬ negative.Represents 0 := by
  unfold WeightedSquares.Represents
  decide +kernel

example (s u : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 2 → ℝ) :
    0 ≤ tensorQuadratic (fun (_ : Fin 3) (_ : Fin 2) => square.matrix) s u x := by
  apply tensor_nonnegative (certificates := fun _ _ => square) _ hs hu
  intro i j
  unfold WeightedSquares.Represents
  decide +kernel

-- Vary both tensor axes, so accidentally dropping either sum changes the value.
def varying (i j : Fin 2) : QMatrix 1 := ![![(1 + i.val + 2*j.val : ℚ)]]
def varyingSquares (i j : Fin 2) : WeightedSquares 1 where
  count := 1
  weight := ![(1 + i.val + 2*j.val : ℚ)]
  vector := ![![1]]
theorem varying_valid : ∀ i j, (varyingSquares i j).Represents (varying i j) := by
  unfold WeightedSquares.Represents
  decide +kernel
example : tensorQuadratic varying (1/2) (1/4) ![1] = 2 := by
  norm_num [tensorQuadratic, basis, varying, quadratic, realMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
example (s u : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 1 → ℝ) :
    0 ≤ tensorQuadratic varying s u x :=
  tensor_nonnegative varyingSquares varying_valid hs hu x

end Gimle.Forseti.Tests.BernsteinMatrix
