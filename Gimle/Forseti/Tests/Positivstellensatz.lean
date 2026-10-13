import Gimle.Forseti.Examples.PositivstellensatzCertificates

/-! Hostile Positivstellensatz certificates, each rejected by the checker, and
the axiom policy of the new theorems. -/

namespace Gimle.Forseti.Tests.Positivstellensatz

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Examples.PredicateCertificates
open Gimle.Forseti.Examples.PositivstellensatzCertificates

/-- Dropping the product leaves no identity: the quadratic module cannot
reach `x·y`. -/
example : PsatzCertificate.check productNonneg
    ⟨[], [⟨unused, [unused, square 1]⟩]⟩ = false := by decide +kernel

/-- A pair out of range reads `0`, so its constraint is `0 ≤ 0` and proves
nothing. -/
example : PsatzCertificate.check productNonneg
    ⟨[(0, 7)], [⟨unused, [unused, unused, square 1]⟩]⟩ = false := by decide +kernel

/-- A negative weight on a product multiplier is refused. -/
example : PsatzCertificate.check productNonneg
    ⟨[(0, 1)], [⟨unused, [unused, unused, ⟨[(-1, 1)]⟩]⟩]⟩ = false := by decide +kernel

/-- A wrong identity: `2 · x·y ≠ x·y`. -/
example : PsatzCertificate.check productNonneg
    ⟨[(0, 1)], [⟨unused, [unused, unused, ⟨[(2, 1)]⟩]⟩]⟩ = false := by decide +kernel

/-- A multiplier list of the wrong length (the products not counted). -/
example : PsatzCertificate.check productNonneg
    ⟨[(0, 1)], [⟨unused, [unused, square 1]⟩]⟩ = false := by decide +kernel

/-- A false goal is not proved by a product: `x ≥ 0 ⊨ x·y ≥ 0` fails at
`(1, −1)`, and the only product, `x²`, gives no identity. -/
def halfProduct : Goal where
  context := plane
  antecedent := .atom .ge (plane.var "x")
  consequent := .atom .ge (plane.var "x" * plane.var "y")

example : PsatzCertificate.check halfProduct
    ⟨[(0, 0)], [⟨unused, [unused, square 1]⟩]⟩ = false := by decide +kernel

example : ¬ halfProduct.Entailment :=
  refutes_sound halfProduct [("x", 1), ("y", -1)] (by decide +kernel)

/-- Strict and disequality goals are outside the positive fragment. -/
def strict : Goal where
  context := plane
  antecedent := (Formula.atom .gt (plane.var "x")).and (.atom .gt (plane.var "y"))
  consequent := .atom .gt (plane.var "x" * plane.var "y")

example : PsatzCertificate.check strict
    ⟨[(0, 1)], [⟨unused, [unused, unused, square 1]⟩]⟩ = false := by decide +kernel

/--
info: 'Gimle.Forseti.Syntax.PsatzCertificate.sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms PsatzCertificate.sound

/--
info: 'Gimle.Forseti.Syntax.PsatzCertificate.check_ofCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms PsatzCertificate.check_ofCertificate

/--
info: 'Gimle.Forseti.Syntax.augment_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms augment_nonpositive

/--
info: 'Gimle.Forseti.Examples.PositivstellensatzCertificates.productNonneg_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms productNonneg_holds

end Gimle.Forseti.Tests.Positivstellensatz
