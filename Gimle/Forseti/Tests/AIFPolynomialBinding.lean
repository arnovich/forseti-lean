module

public import Gimle.Forseti.Examples.AIFPolynomialBinding

/-! Exact polynomial equivalence on Hermite rates and tensor tables, including
altered sign, coefficient, axis and degree. -/

@[expose] public section

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

-- Unequal degrees, signed coefficients, and asymmetric matrix entries.
private def signedTable : Fin 2 → Fin 3 → LinearEnergy.QMatrix 2 := fun a b =>
  let v := (![![1, -1, 2], ![-2, 0, 3]] : Fin 2 → Fin 3 → ℚ) a b
  ![![v, 2*v], ![-3*v, 0]]

private def signedPolynomial : Poly :=
  [⟨0, 0, 1⟩, ⟨0, 1, -4⟩, ⟨0, 2, 5⟩,
    ⟨1, 0, -3⟩, ⟨1, 1, 8⟩, ⟨1, 2, -4⟩]

example : equivalent (AIFPolynomialBinding.tensor signedTable 0 0)
    signedPolynomial = true := by decide +kernel
example : equivalent (AIFPolynomialBinding.tensor signedTable 0 1)
    (mul (constant 2) signedPolynomial) = true := by decide +kernel
example : equivalent (AIFPolynomialBinding.tensor signedTable 1 0)
    (mul (constant (-3)) signedPolynomial) = true := by decide +kernel
example : equivalent (AIFPolynomialBinding.tensor signedTable 1 1)
    [] = true := by decide +kernel
example : equivalent (AIFPolynomialBinding.tensor signedTable 0 0)
    (neg signedPolynomial) = false := by decide +kernel

-- Both degree-zero axes reduce to the single supplied rational coefficient.
private def constantTable : Fin 1 → Fin 1 → LinearEnergy.QMatrix 1 :=
  fun _ _ => ![![(-7/11)]]
example : equivalent (AIFPolynomialBinding.tensor constantTable 0 0)
    (constant (-7/11)) = true := by decide +kernel

/-- info: 'Gimle.Forseti.Examples.AIFPolynomialBinding.binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AIFPolynomialBinding.binding
end Gimle.Forseti.Tests.AIFPolynomialBinding
