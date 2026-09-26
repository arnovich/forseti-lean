import Gimle.Forseti.Syntax.Certificate

/-! The shared predicate-certificate corpus, checked in Lean.

Five goals, each over an explicit ordered context. The three true ones are
proved from supplied exact certificates, and the two false ones are refuted by
supplied rational points, named coordinate by coordinate. The evidence here is
written by hand, as fixtures for the checker: finding it is an external
producer's job (gimle-forseti task 111), and nothing here would change if a
solver had produced it instead.

The unit-disk entailment is then used as a Hoare postcondition weakening, so a
certificate-checked fact ends up in a theorem about a named circuit.
-/

namespace Gimle.Forseti.Examples.PredicateCertificates

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Asgard

/-- `[x, y]`. -/
def plane : Context := ⟨["x", "y"], by decide, by decide, by decide⟩
/-- `[x]`. -/
def line : Context := ⟨["x"], by decide, by decide, by decide⟩

/-- A square with weight one. -/
def square {n : Nat} (g : Polynomial.Expr n) : SquareSum n := ⟨[(1, g)]⟩

/-- The empty sum, for a multiplier slot the certificate does not use. -/
def unused {n : Nat} : SquareSum n := ⟨[]⟩

/-! ### `x² + y² ≤ 1 ⊨ x² ≤ 1 ∧ y² ≤ 1` -/

def disk : Goal where
  context := plane
  antecedent := .atom .le (plane.var "x" * plane.var "x" + plane.var "y" * plane.var "y" - 1)
  consequent :=
    (Formula.atom .le (plane.var "x" * plane.var "x" - 1)).and
      (.atom .le (plane.var "y" * plane.var "y" - 1))

/-- `1 − x² = y² + (1 − x² − y²)` and `1 − y² = x² + (1 − x² − y²)`. -/
def diskCertificate : EntailmentCertificate plane.dimension where
  rows := [⟨square (plane.var "y"), [square 1]⟩, ⟨square (plane.var "x"), [square 1]⟩]

theorem disk_holds : disk.Entailment :=
  EntailmentCertificate.sound disk diskCertificate (by decide +kernel)

/-! ### `x² ≤ 1 ⊨ x⁴ ≤ x²` -/

def quartic : Goal where
  context := line
  antecedent := .atom .le (line.var "x" * line.var "x" - 1)
  consequent := .atom .le (line.var "x" * line.var "x" * line.var "x" * line.var "x" -
    line.var "x" * line.var "x")

/-- `x² − x⁴ = x² · (1 − x²)`: a nonconstant multiplier. -/
def quarticCertificate : EntailmentCertificate line.dimension where
  rows := [⟨unused, [square (line.var "x")]⟩]

theorem quartic_holds : quartic.Entailment :=
  EntailmentCertificate.sound quartic quarticCertificate (by decide +kernel)

/-! ### `−1 ≤ x ∧ x ≤ 1 ⊨ x ≤ 2` -/

def box : Goal where
  context := line
  antecedent := (Formula.atom .ge (line.var "x" + 1)).and (.atom .le (line.var "x" - 1))
  consequent := .atom .le (line.var "x" - 2)

/-- `2 − x = 1 + (1 − x)`, with an explicit empty slot for the lower bound. -/
def boxCertificate : EntailmentCertificate line.dimension where
  rows := [⟨square 1, [unused, square 1]⟩]

theorem box_holds : box.Entailment :=
  EntailmentCertificate.sound box boxCertificate (by decide +kernel)

/-! ### `x² + y² ≤ 1 ⊨ x² + y² ≤ 1/2` is false -/

def halfDisk : Goal where
  context := plane
  antecedent := disk.antecedent
  consequent := .atom .le (plane.var "x" * plane.var "x" + plane.var "y" * plane.var "y" -
    rational (1/2))

theorem halfDisk_fails : ¬ halfDisk.Entailment :=
  refutes_sound halfDisk [("x", 1), ("y", 0)] (by decide +kernel)

/-! ### `x ≤ 0 ⊨ y ≤ 0` over `[x, y]` is false -/

def unrelated : Goal where
  context := plane
  antecedent := .atom .le (plane.var "x")
  consequent := .atom .le (plane.var "y")

theorem unrelated_fails : ¬ unrelated.Entailment :=
  refutes_sound unrelated [("x", 0), ("y", 1)] (by decide +kernel)

/-- `(1, 0)` is no counterexample: the antecedent `x ≤ 0` fails there. -/
example : refutes unrelated [("x", 1), ("y", 0)] = false := by decide +kernel

/-! ### From a checked entailment to a Hoare triple

The identity circuit on the plane keeps the unit disk; the certificate-checked
entailment then weakens its postcondition to the unit square. The theorem is
about `planeIdentity` itself, not about a claimed statement. -/

/-- The identity on two wires. -/
def planeIdentity : Circuit 2 2 := .parallel .id .id

theorem planeIdentity_run (point : Point 2) : planeIdentity.run point = point := by
  funext i
  fin_cases i <;> simp [planeIdentity, Circuit.run, pointAppend, pointLeft, pointRight]

theorem planeIdentity_keeps_disk :
    ExactHoare disk.antecedent.toPredicate planeIdentity disk.antecedent.toPredicate := by
  intro point holds
  exact (planeIdentity_run point).symm ▸ holds

/-- **The identity sends the unit disk into the unit square**, with the
postcondition weakened by the checked certificate. -/
theorem planeIdentity_into_square :
    ExactHoare disk.antecedent.toPredicate planeIdentity disk.consequent.toPredicate :=
  hoareConsequence planeIdentity_keeps_disk (fun _ holds => holds) disk_holds

end Gimle.Forseti.Examples.PredicateCertificates
