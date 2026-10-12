import Gimle.Forseti.RationalPolynomial

namespace Gimle.Forseti.Tests.RationalPolynomial
open Gimle.Forseti.RationalPolynomial

-- Equal polynomials may have different term order and cancellation histories.
def left := mul (add time parameter) (add time (neg parameter))
def right := add (power time 2) (neg (power parameter 2))

example : equivalent left right = true := by decide +kernel

example (s u : ℝ) : eval left s u = eval right s u :=
  eval_eq_of_equivalent (by decide +kernel) s u

-- Reject an altered sign, coefficient, axis, or degree.
example : equivalent left (add (power time 2) (power parameter 2)) = false := by
  decide +kernel
example : equivalent (constant (1/3)) (constant (1/4)) = false := by decide +kernel
example : equivalent time parameter = false := by decide +kernel
example : equivalent time (power time 2) = false := by decide +kernel

-- Cancellation, an empty polynomial, and exponent zero remain exact.
example : equivalent (add time (neg time)) [] = true := by decide +kernel
example : equivalent (power [] 0) (constant 1) = true := by decide +kernel
example : equivalent (mul [] parameter) [] = true := by decide +kernel

-- Arbitrary raw lists need not be collected. The test is sound but incomplete.
private def repeated : Poly := [⟨0, 0, 1⟩, ⟨0, 0, 1⟩]
example : equivalent repeated (constant 2) = true := by decide +kernel
example : equivalent repeated repeated = false := by decide +kernel
example (s u : ℝ) : eval repeated s u = 2 := by
  norm_num [repeated, termEval]

#print axioms eval_eq_of_equivalent
end Gimle.Forseti.Tests.RationalPolynomial
