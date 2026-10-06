import Gimle.Forseti.Tests.BernsteinMatrix

namespace Gimle.Forseti.Tests.BernsteinBinding
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix

-- A target identity is an independent obligation, even with valid square data.
example (s u : ℝ) :
    tensorMatrix (fun (_ : Fin 1) (_ : Fin 1) => (![![1]] : QMatrix 1)) s u 0 0 = 1 := by
  norm_num [tensorMatrix, basis, Fin.sum_univ_succ]

example : (0 : Fin 1 → Fin 1 → ℝ) ≠
    tensorMatrix (fun (_ : Fin 1) (_ : Fin 1) => (![![1]] : QMatrix 1)) 0 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num [tensorMatrix, basis, Fin.sum_univ_succ] at this

-- Vary both axes and bind a separately stated affine target.
open Gimle.Forseti.Tests.BernsteinMatrix

theorem varying_binding (s u : ℝ) :
    (![![1+s+2*u]] : Fin 1 → Fin 1 → ℝ) = tensorMatrix varying s u := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [tensorMatrix, basis, varying, Fin.sum_univ_succ]
  ring

example (s u : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 1 → ℝ) :
    0 ≤ matrixForm (![![1+s+2*u]]) x :=
  target_nonnegative varyingSquares varying_valid (varying_binding s u) hs hu x

-- Omitting the parameter contribution cannot satisfy the same binding.
example : (![![3/2]] : Fin 1 → Fin 1 → ℝ) ≠ tensorMatrix varying (1/2) (1/4) := by
  rw [← varying_binding]
  intro h
  have := congrFun (congrFun h 0) 0
  norm_num at this

-- A nonsymmetric matrix retains both cross terms.
example (x y : ℝ) : matrixForm (![![1, 2], ![3, 4]]) ![x,y] =
    x^2 + 5*x*y + 4*y^2 := by
  simp [matrixForm, Fin.sum_univ_succ]
  ring

end Gimle.Forseti.Tests.BernsteinBinding
