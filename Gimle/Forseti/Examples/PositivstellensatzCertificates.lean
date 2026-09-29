import Gimle.Forseti.Syntax.Positivstellensatz
import Gimle.Forseti.Examples.PredicateCertificates

/-! Goals beyond 017's quadratic-module certificates, checked by
`PsatzCertificate`.

* `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0` is the product of the two constraints itself.
* `x ≥ 1 ∧ y ≥ 1 ⊨ x·y ≥ 1` is `x·y − 1 = (x − 1)(y − 1) + (x − 1) + (y − 1)`.
* `x² ≤ 1 ∧ y² ≤ 1 ⊨ x·y ≤ 1` needs no product, only the off-diagonal square
  `(x − y)²`, which 017's format already admits.
* 017's disk certificate is reused unchanged through `ofCertificate`.

The evidence is written by hand as fixtures, as in `PredicateCertificates`.
Finding it is the producer's job (gimle-forseti 145).
-/

namespace Gimle.Forseti.Examples.PositivstellensatzCertificates

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Examples.PredicateCertificates

/-! ### `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0` -/

def productNonneg : Goal where
  context := plane
  antecedent := (Formula.atom .ge (plane.var "x")).and (.atom .ge (plane.var "y"))
  consequent := .atom .ge (plane.var "x" * plane.var "y")

/-- The antecedent reads `−x ≤ 0, −y ≤ 0`; the pair `(0, 1)` adds
`−((−x)(−y)) ≤ 0`, and `x·y = 1 · (−x)(−y)` is the whole identity. -/
def productNonnegCertificate : PsatzCertificate plane.dimension where
  pairs := [(0, 1)]
  rows := [⟨unused, [unused, unused, square 1]⟩]

theorem productNonneg_holds : productNonneg.Entailment :=
  PsatzCertificate.sound productNonneg productNonnegCertificate (by decide +kernel)

/-! ### `x ≥ 1 ∧ y ≥ 1 ⊨ x·y ≥ 1` -/

def boxProduct : Goal where
  context := plane
  antecedent := (Formula.atom .ge (plane.var "x" - 1)).and (.atom .ge (plane.var "y" - 1))
  consequent := .atom .ge (plane.var "x" * plane.var "y" - 1)

def boxProductCertificate : PsatzCertificate plane.dimension where
  pairs := [(0, 1)]
  rows := [⟨unused, [square 1, square 1, square 1]⟩]

theorem boxProduct_holds : boxProduct.Entailment :=
  PsatzCertificate.sound boxProduct boxProductCertificate (by decide +kernel)

/-! ### `x² ≤ 1 ∧ y² ≤ 1 ⊨ x·y ≤ 1` -/

def unitProduct : Goal where
  context := plane
  antecedent :=
    (Formula.atom .le (plane.var "x" * plane.var "x" - 1)).and
      (.atom .le (plane.var "y" * plane.var "y" - 1))
  consequent := .atom .le (plane.var "x" * plane.var "y" - 1)

/-- `1 − x·y = ½(x − y)² + ½(1 − x²) + ½(1 − y²)`. -/
def unitProductCertificate : PsatzCertificate plane.dimension where
  pairs := []
  rows := [⟨⟨[(1 / 2, plane.var "x" - plane.var "y")]⟩, [⟨[(1 / 2, 1)]⟩, ⟨[(1 / 2, 1)]⟩]⟩]

theorem unitProduct_holds : unitProduct.Entailment :=
  PsatzCertificate.sound unitProduct unitProductCertificate (by decide +kernel)

/-! ### 017's disk, unchanged -/

theorem disk_holds_again : disk.Entailment :=
  PsatzCertificate.sound disk (PsatzCertificate.ofCertificate diskCertificate)
    (by rw [PsatzCertificate.check_ofCertificate]; decide +kernel)

end Gimle.Forseti.Examples.PositivstellensatzCertificates
