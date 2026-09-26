import Gimle.Forseti.Examples.PredicateCertificates

/-! Hostile and edge-case evidence for the predicate certificate checker.

Every rejection below is a `false` from the checker itself, decided in the
kernel: the checker, not the test, is what refuses the evidence. A rejection
proves nothing about the goal; only the accepting cases carry theorems.

The axiom policy is asserted with `#guard_msgs`, so a proof that picked up any
axiom beyond `propext`, `Classical.choice` and `Quot.sound` fails the build
rather than printing a report no one reads.
-/

namespace Gimle.Forseti.Tests.Certificate

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Syntax.ExprNotation
open Gimle.Forseti.Examples.PredicateCertificates
open Gimle.Asgard

/-- `x` on the plane. -/
abbrev x : Polynomial.Expr plane.dimension := plane.var "x"
/-- `y` on the plane. -/
abbrev y : Polynomial.Expr plane.dimension := plane.var "y"
/-- `x` on the line. -/
abbrev t : Polynomial.Expr line.dimension := line.var "x"

/-! ### Hostile certificates are rejected -/

/-- A negative weight, even one whose identity would hold. -/
example : diskCertificate.check disk = true := by decide +kernel
example : EntailmentCertificate.check disk
    ⟨[⟨⟨[(-1, x), (2, x)]⟩ , [square 1]⟩, ⟨square x, [square 1]⟩]⟩ = false := by
  decide +kernel

/-- One coefficient perturbed. -/
example : EntailmentCertificate.check disk
    ⟨[⟨⟨[(2, y)]⟩, [square 1]⟩, ⟨square x, [square 1]⟩]⟩ = false := by decide +kernel

/-- A missing identity, and an extra one. -/
example : EntailmentCertificate.check disk ⟨[⟨square y, [square 1]⟩]⟩ = false := by
  decide +kernel
example : EntailmentCertificate.check disk
    ⟨diskCertificate.rows ++ [⟨square x, [square 1]⟩]⟩ = false := by decide +kernel

/-- A missing multiplier slot, and an extra one. -/
example : EntailmentCertificate.check box ⟨[⟨square 1, [square 1]⟩]⟩ = false := by
  decide +kernel
example : EntailmentCertificate.check box ⟨[⟨square 1, [unused, square 1, unused]⟩]⟩ =
    false := by decide +kernel

/-- Evidence reused against a changed goal: the disk certificate does not prove
the half-square. -/
def halfSquare : Goal where
  context := plane
  antecedent := disk.antecedent
  consequent := (Formula.atom .le (x * x - rational (1/2))).and
    (.atom .le (y * y - rational (1/2)))

example : diskCertificate.check halfSquare = false := by decide +kernel

/-- A goal outside the positive fragment has no certificate at all. -/
example : diskCertificate.check ⟨plane, .atom .lt x, .atom .le x⟩ = false := by
  decide +kernel

-- Evidence of the wrong dimension cannot even be posed: a certificate is
-- indexed by its goal's context, so the line's certificate does not typecheck
-- against a goal on the plane.
#check_failure (EntailmentCertificate.check disk quarticCertificate)

/-! ### Valid evidence in another form still checks -/

/-- The same squares written differently: `(x + 0)·1` for `x`. -/
def rewritten : EntailmentCertificate plane.dimension :=
  ⟨[⟨square (y * 1 + 0), [square 1]⟩, ⟨square ((x + 0) * 1), [square 1]⟩]⟩

example : rewritten.check disk = true := by decide +kernel

/-- Redundant zero-weight terms change nothing. -/
example : EntailmentCertificate.check disk
    ⟨[⟨⟨[(1, y), (0, x * x)]⟩, [⟨[(1, 1), (0, y)]⟩]⟩, ⟨square x, [square 1]⟩]⟩ = true := by
  decide +kernel

/-- A redundant antecedent constraint with an empty multiplier. -/
def boxWithSpare : Goal where
  context := line
  antecedent := box.antecedent.and (.atom .le (t * t - 4 : Polynomial.Expr line.dimension))
  consequent := box.consequent

def spareCertificate : EntailmentCertificate line.dimension :=
  ⟨[⟨square 1, [unused, square 1, unused]⟩]⟩

example : spareCertificate.check boxWithSpare = true := by decide +kernel

/-! ### Edge cases -/

/-- An empty antecedent: `tru ⊨ −x² ≤ 0`, from `x² = x²`. -/
def squareNonnegative : Goal := ⟨line, .tru, .atom .le (-(t * t))⟩
theorem squareNonnegative_holds : squareNonnegative.Entailment :=
  EntailmentCertificate.sound _ ⟨[⟨square t, []⟩]⟩ (by decide +kernel)

/-- A zero polynomial: `tru ⊨ 0 ≤ 0`, with an empty certificate row. -/
theorem zero_holds : (⟨line, .tru, .atom .le 0⟩ : Goal).Entailment :=
  EntailmentCertificate.sound _ ⟨[⟨unused, []⟩]⟩ (by decide +kernel)

/-- An empty consequent needs no rows. -/
theorem tru_holds : (⟨line, .atom .le t, .tru⟩ : Goal).Entailment :=
  EntailmentCertificate.sound _ ⟨[]⟩ (by decide +kernel)

/-- An empty domain entails anything: `1 ≤ 0 ⊨ x ≤ 0`, from
`−x = ((x−1)/2)² − ((x+1)/2)²`. -/
theorem emptyDomain_holds : (⟨line, .atom .le 1, .atom .le t⟩ : Goal).Entailment :=
  EntailmentCertificate.sound _
    ⟨[⟨⟨[(1/4, t - 1)]⟩, [⟨[(1/4, t + 1)]⟩]⟩]⟩ (by decide +kernel)

/-! ### Counterexamples -/

/-- A point that satisfies both sides is no counterexample. -/
example : refutes halfDisk [("x", 0), ("y", 0)] = false := by decide +kernel
/-- A true goal has none: the disk inside the square. -/
example : refutes disk [("x", 1), ("y", 0)] = false := by decide +kernel
/-- The right values under the wrong names do not count: `(0, 1)` refutes it,
but the same numbers with the names swapped are the point `(1, 0)`. -/
example : refutes unrelated [("y", 0), ("x", 1)] = false := by decide +kernel
/-- The answer's order does not matter, only its names. -/
example : refutes unrelated [("y", 1), ("x", 0)] = true := by decide +kernel
/-- A coordinate given twice is rejected, even with a matching value. -/
example : refutes unrelated [("x", 0), ("x", 0), ("y", 1)] = false := by decide +kernel
/-- An answer with a coordinate missing, or an extra one, is rejected. -/
example : refutes unrelated [("y", 1)] = false := by decide +kernel
example : refutes unrelated [("x", 0), ("y", 1), ("z", 0)] = false := by decide +kernel

/-- Every constructor in the rational lane: `x = 0 ∨ x > 1 ⊨ ¬ (x < 2)` fails at
`x = 0`, which exercises `eq`, `gt`, `or`, `not` and `lt`. -/
def strict : Goal :=
  ⟨line, (Formula.atom .eq t).or (.atom .gt (t - 1)), .not (.atom .lt (t - 2))⟩

theorem strict_fails : ¬ strict.Entailment :=
  refutes_sound strict [("x", 0)] (by decide +kernel)
example : refutes strict [("x", 3)] = false := by decide +kernel

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Syntax.EntailmentCertificate.sound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms EntailmentCertificate.sound
/--
info: 'Gimle.Forseti.Syntax.refutes_sound'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms refutes_sound
/--
info: 'Gimle.Forseti.Examples.PredicateCertificates.disk_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms disk_holds
/--
info: 'Gimle.Forseti.Examples.PredicateCertificates.halfDisk_fails'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms halfDisk_fails
/--
info: 'Gimle.Forseti.Examples.PredicateCertificates.planeIdentity_into_square'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms planeIdentity_into_square

/--
info: 'Gimle.Forseti.Examples.PredicateCertificates.quartic_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms quartic_holds
/--
info: 'Gimle.Forseti.Examples.PredicateCertificates.box_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms box_holds
/--
info: 'Gimle.Forseti.Examples.PredicateCertificates.unrelated_fails'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms unrelated_fails
/--
info: 'Gimle.Forseti.Tests.Certificate.emptyDomain_holds'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms emptyDomain_holds
/--
info: 'Gimle.Forseti.Tests.Certificate.strict_fails'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms strict_fails

end Gimle.Forseti.Tests.Certificate
