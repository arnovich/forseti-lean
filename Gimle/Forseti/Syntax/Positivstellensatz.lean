import Gimle.Forseti.Syntax.Certificate

/-! # Degree-2 Positivstellensatz certificates

`EntailmentCertificate` (017) proves `P ⊨ Q` from `−q = σ₀ + Σᵢ σᵢ · (−pᵢ)`:
every antecedent constraint is used alone, so the identity lives in the
*quadratic module* of the antecedent. `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0` has no such
identity at any degree, because `x·y` is the *product* of two constraints.

A `PsatzCertificate` also names pairs `(i, j)` of antecedent constraints, and
gives ordinary rows against the antecedent *augmented* with `−(pᵢ · pⱼ) ≤ 0`.
That constraint holds wherever `pᵢ ≤ 0` and `pⱼ ≤ 0` do, because
`(−pᵢ)(−pⱼ) ≥ 0`, so soundness is 017's `Row.check_sound` over the augmented
list. The only new mathematics is that a product of two nonpositive reals is
nonnegative. An index out of range reads the constant `0`, whose product is the
trivial constraint `0 ≤ 0`, so it only weakens a certificate.

Every 017 certificate is a Psatz certificate with no pairs, and the two checks
agree on it (`PsatzCertificate.check_ofCertificate`).

The format was selected in gimle-forseti 034, which compared solver proof logs,
exact quantifier elimination and widened certificates; see that repository's
`benchmarks/nonlinear-certificates/`.
-/

namespace Gimle.Forseti.Syntax

open Gimle.Forseti
open Gimle.Asgard

variable {n : Nat}

/-- The derived constraint `−(pᵢ · pⱼ) ≤ 0`, read by index. -/
def product (constraints : List (Polynomial.Expr n)) (pair : ℕ × ℕ) : Polynomial.Expr n :=
  .neg (.mul (constraints.getD pair.1 (.constant 0)) (constraints.getD pair.2 (.constant 0)))

/-- The antecedent's constraints, then the named products, in order. -/
def augment (constraints : List (Polynomial.Expr n)) (pairs : List (ℕ × ℕ)) :
    List (Polynomial.Expr n) :=
  constraints ++ pairs.map (product constraints)

theorem getD_nonpositive (constraints : List (Polynomial.Expr n)) (point : Point n)
    (below : ∀ p ∈ constraints, p.eval point ≤ 0) (i : ℕ) :
    (constraints.getD i (.constant 0)).eval point ≤ 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : constraints[i]? with
  | none => simp [Polynomial.Expr.eval]
  | some p => exact below p (List.mem_of_getElem? h)

/-- **The one new fact.** Where the antecedent's constraints hold, so does every
derived product constraint. -/
theorem augment_nonpositive (constraints : List (Polynomial.Expr n)) (pairs : List (ℕ × ℕ))
    (point : Point n) (below : ∀ p ∈ constraints, p.eval point ≤ 0) :
    ∀ p ∈ augment constraints pairs, p.eval point ≤ 0 := by
  intro p member
  rcases List.mem_append.mp member with original | derived
  · exact below p original
  · obtain ⟨pair, -, rfl⟩ := List.mem_map.mp derived
    have hi := getD_nonpositive constraints point below pair.1
    have hj := getD_nonpositive constraints point below pair.2
    simp only [product, Polynomial.Expr.eval]
    nlinarith

@[simp] theorem augment_nil (constraints : List (Polynomial.Expr n)) :
    augment constraints [] = constraints := by
  simp [augment]

/-- Positive evidence with pairwise products of antecedent constraints. -/
structure PsatzCertificate (n : Nat) where
  /-- Pairs `(i, j)` of antecedent constraint indices. -/
  pairs : List (ℕ × ℕ)
  /-- One row per consequent constraint, against the augmented antecedent. -/
  rows : List (Row n)

namespace PsatzCertificate

/-- Check a certificate against a goal as posed: both sides in the positive
fragment, one row per consequent constraint, each against the augmented
antecedent. -/
def check (goal : Goal) (certificate : PsatzCertificate goal.context.dimension) : Bool :=
  match goal.antecedent.nonstrict?, goal.consequent.nonstrict? with
  | some constraints, some consequents =>
      certificate.rows.length == consequents.length &&
        (certificate.rows.zip consequents).all fun pair =>
          pair.1.check (augment constraints certificate.pairs) pair.2
  | _, _ => false

/-- **A Positivstellensatz certificate that checks proves the goal.** -/
theorem sound (goal : Goal) (certificate : PsatzCertificate goal.context.dimension)
    (valid : certificate.check goal = true) : goal.Entailment := by
  unfold check at valid
  split at valid
  · rename_i constraints consequents antecedentRead consequentRead
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at valid
    obtain ⟨lengths, rows⟩ := valid
    intro point holds
    rw [Formula.holds_of_nonstrict antecedentRead] at holds
    rw [Formula.holds_of_nonstrict consequentRead]
    intro q member
    obtain ⟨index, bound, rfl⟩ := List.getElem_of_mem member
    have paired : (certificate.rows[index]'(by omega), consequents[index]) ∈
        certificate.rows.zip consequents := by
      rw [List.mem_iff_getElem]
      exact ⟨index, by simp [bound, lengths], by simp⟩
    exact Row.check_sound (rows _ paired) point
      (augment_nonpositive constraints certificate.pairs point holds)
  · cases valid

/-- A 017 certificate, as a Psatz certificate with no products. -/
def ofCertificate (certificate : EntailmentCertificate n) : PsatzCertificate n :=
  ⟨[], certificate.rows⟩

/-- **017 certificates keep their meaning.** With no pairs the two checks are
the same function of the goal. -/
theorem check_ofCertificate (goal : Goal)
    (certificate : EntailmentCertificate goal.context.dimension) :
    (ofCertificate certificate).check goal = certificate.check goal := by
  unfold check EntailmentCertificate.check
  simp only [ofCertificate, augment_nil]
  split <;> simp_all

end PsatzCertificate

end Gimle.Forseti.Syntax
