import Gimle.Forseti.Examples.AIFPolynomialBinding

namespace Gimle.Forseti.Tests.AIFPolynomialBinding
open Gimle.Forseti.RationalPolynomial
open Gimle.Forseti.Examples

-- A non-unit step is essential: this is a physical-time derivative.
example : equivalent (AIFPolynomialBinding.hermiteRate 2 0 2 1 1)
    (constant 1) = true := by decide +kernel
example : equivalent (AIFPolynomialBinding.hermiteRate 2 0 2 1 1)
    (constant 2) = false := by decide +kernel

-- Both Bernstein axes, their endpoint degrees, and mixed terms are retained.
private def table : Fin 3 → Fin 2 → LinearEnergy.QMatrix 1 :=
  ![![![![0]], ![![0]]], ![![![0]], ![![1/2]]], ![![![0]], ![![1]]]]

example : equivalent (AIFPolynomialBinding.tensor table 0 0)
    (mul time parameter) = true := by decide +kernel
example : equivalent (AIFPolynomialBinding.tensor table 0 0)
    (power time 2) = false := by decide +kernel

#print axioms AIFPolynomialBinding.binding
end Gimle.Forseti.Tests.AIFPolynomialBinding
