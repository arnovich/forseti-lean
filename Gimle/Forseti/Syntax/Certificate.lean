import Gimle.Forseti.Syntax.Context

/-! Checked polynomial entailment certificates and rational counterexamples.

An external producer — a solver, a search, a person — proposes finite exact
evidence about a `Goal` `P ⊨ Q`. Nothing here trusts the producer. The checks
are computable functions of the goal as posed and of the evidence, and each
has a soundness theorem; a failed check rejects the evidence and establishes
nothing about the goal.

**Positive evidence** (`EntailmentCertificate`), for goals whose sides are
conjunctions of non-strict polynomial inequalities. Each side is read as an
ordered list of constraints `p ≤ 0` (`Formula.nonstrict?`), and for every
consequent constraint `q_j ≤ 0` the certificate gives an identity

    −q_j = σ_j0 + Σ_i σ_ji · (−p_i),  σ = Σ_k w_k · g_k²,  w_k ≥ 0,

with one multiplier slot per antecedent constraint. The identity is checked by
normalizing the difference of the two sides exactly (`Sparse`), never by
sampling and never against a supplied target. The family is sound and
incomplete: a missing certificate says nothing.

**Negative evidence** (`refutes`), for any quantifier-free goal: a rational
point, named coordinate by coordinate, where `P` holds and `Q` does not,
evaluated exactly over ℚ (`Formula.holdsQ`) and proved to agree with the real
semantics.
-/

namespace Gimle.Forseti.Syntax

open Gimle.Forseti
open Gimle.Asgard

/-! ### Writing polynomials

`open Gimle.Forseti.Syntax.ExprNotation` lets `+`, `-`, `*` and numerals build
Asgard expressions, so a goal reads as written on paper. The instances are
scoped: nothing changes for code that does not open the namespace. -/

namespace ExprNotation

scoped instance {n : Nat} : Add (Polynomial.Expr n) := ⟨.add⟩
scoped instance {n : Nat} : Mul (Polynomial.Expr n) := ⟨.mul⟩
scoped instance {n : Nat} : Neg (Polynomial.Expr n) := ⟨.neg⟩
scoped instance {n : Nat} : Sub (Polynomial.Expr n) := ⟨fun a b => .add a (.neg b)⟩
scoped instance {n k : Nat} : OfNat (Polynomial.Expr n) k := ⟨.constant k⟩

/-- An exact rational constant, such as `rational (1/2)`. -/
def rational {n : Nat} (value : ℚ) : Polynomial.Expr n := .constant value

end ExprNotation

/-! ### Exact sparse polynomials -/

/-- A monomial: the coordinates it multiplies, with repetition. -/
abbrev Monomial (n : Nat) := List (Fin n)

/-- A sparse polynomial: monomials with exact rational coefficients. -/
abbrev Sparse (n : Nat) := List (Monomial n × ℚ)

namespace Sparse

variable {n : Nat}

/-- The value of a monomial at a point. -/
noncomputable def monomialValue (monomial : Monomial n) (point : Point n) : ℝ :=
  (monomial.map point).prod

/-- The value of a sparse polynomial at a point. -/
noncomputable def eval (polynomial : Sparse n) (point : Point n) : ℝ :=
  (polynomial.map fun term => (term.2 : ℝ) * monomialValue term.1 point).sum

@[simp] theorem eval_nil (point : Point n) : eval ([] : Sparse n) point = 0 := rfl

@[simp] theorem eval_cons (term : Monomial n × ℚ) (rest : Sparse n)
    (point : Point n) :
    eval (term :: rest) point =
      (term.2 : ℝ) * monomialValue term.1 point + eval rest point := by
  simp [eval]

theorem eval_append (first second : Sparse n) (point : Point n) :
    eval (first ++ second) point = eval first point + eval second point := by
  simp [eval]

/-- Add one term, merging it into an equal monomial and dropping a zero. -/
def insert (term : Monomial n × ℚ) : Sparse n → Sparse n
  | [] => if term.2 = 0 then [] else [term]
  | head :: rest =>
      if head.1 = term.1 then
        if head.2 + term.2 = 0 then rest else (head.1, head.2 + term.2) :: rest
      else head :: insert term rest

theorem eval_insert (term : Monomial n × ℚ) (polynomial : Sparse n)
    (point : Point n) :
    eval (insert term polynomial) point =
      (term.2 : ℝ) * monomialValue term.1 point + eval polynomial point := by
  induction polynomial with
  | nil =>
      unfold insert
      split
      · rename_i zero
        simp [zero]
      · simp
  | cons head rest ih =>
      unfold insert
      split
      · rename_i same
        split
        · rename_i cancels
          have : (head.2 : ℝ) + term.2 = 0 := by exact_mod_cast cancels
          simp only [eval_cons, same] at *
          linear_combination -monomialValue term.1 point * this
        · simp only [eval_cons, same, Rat.cast_add]
          ring
      · simp only [eval_cons, ih]
        ring

/-- Insert every term of a list, in order. -/
def collect (terms : List (Monomial n × ℚ)) : Sparse n := terms.foldr insert []

theorem eval_collect (terms : List (Monomial n × ℚ)) (point : Point n) :
    eval (collect terms) point = eval terms point := by
  induction terms with
  | nil => rfl
  | cons head rest ih =>
      simp only [collect, List.foldr_cons] at *
      rw [eval_insert, ih, eval_cons]

/-- Sum of two polynomials. -/
def add (left right : Sparse n) : Sparse n := right.foldr insert left

theorem eval_add (left right : Sparse n) (point : Point n) :
    eval (add left right) point = eval left point + eval right point := by
  induction right with
  | nil => simp [add]
  | cons head rest ih =>
      simp only [add, List.foldr_cons] at *
      rw [eval_insert, ih, eval_cons]
      ring

/-- Negation. -/
def neg (polynomial : Sparse n) : Sparse n :=
  polynomial.map fun term => (term.1, -term.2)

theorem eval_neg (polynomial : Sparse n) (point : Point n) :
    eval (neg polynomial) point = -eval polynomial point := by
  induction polynomial with
  | nil => simp [neg]
  | cons head rest ih =>
      simp only [neg, List.map_cons, eval_cons, Rat.cast_neg] at *
      rw [ih]
      ring

/-- Put a monomial's coordinates in order, so equal monomials are equal lists. -/
def normalizeMonomial (monomial : Monomial n) : Monomial n :=
  monomial.insertionSort (· ≤ ·)

theorem monomialValue_normalize (monomial : Monomial n) (point : Point n) :
    monomialValue (normalizeMonomial monomial) point = monomialValue monomial point :=
  ((List.perm_insertionSort _ monomial).map point).prod_eq

theorem monomialValue_append (left right : Monomial n) (point : Point n) :
    monomialValue (left ++ right) point =
      monomialValue left point * monomialValue right point := by
  simp [monomialValue]

/-- Multiply every term of a polynomial by one term. -/
theorem eval_scale (factor : Monomial n × ℚ) (polynomial : Sparse n) (point : Point n) :
    eval (polynomial.map fun t => (normalizeMonomial (factor.1 ++ t.1), factor.2 * t.2))
        point =
      (factor.2 : ℝ) * monomialValue factor.1 point * eval polynomial point := by
  induction polynomial with
  | nil => simp
  | cons term others ih =>
      simp only [List.map_cons, eval_cons, monomialValue_normalize,
        monomialValue_append, Rat.cast_mul, ih]
      ring

/-- Product of two polynomials. -/
def mul (left right : Sparse n) : Sparse n :=
  collect (left.flatMap fun s =>
    right.map fun t => (normalizeMonomial (s.1 ++ t.1), s.2 * t.2))

theorem eval_mul (left right : Sparse n) (point : Point n) :
    eval (mul left right) point = eval left point * eval right point := by
  rw [mul, eval_collect]
  induction left with
  | nil => simp
  | cons head rest ih =>
      rw [List.flatMap_cons, eval_append, ih, eval_scale, eval_cons]
      ring

/-- The sparse form of an Asgard polynomial expression. -/
def ofExpr : Polynomial.Expr n → Sparse n
  | .var coordinate => [([coordinate], 1)]
  | .constant value => insert ([], value) []
  | .add left right => add (ofExpr left) (ofExpr right)
  | .mul left right => mul (ofExpr left) (ofExpr right)
  | .neg argument => neg (ofExpr argument)

/-- Normalizing never changes a polynomial's value. -/
theorem eval_ofExpr (expression : Polynomial.Expr n) (point : Point n) :
    eval (ofExpr expression) point = expression.eval point := by
  induction expression with
  | var coordinate => simp [ofExpr, monomialValue, Polynomial.Expr.eval]
  | constant value => simp [ofExpr, eval_insert, monomialValue, Polynomial.Expr.eval]
  | add left right leftIH rightIH =>
      simp [ofExpr, eval_add, leftIH, rightIH, Polynomial.Expr.eval]
  | mul left right leftIH rightIH =>
      simp [ofExpr, eval_mul, leftIH, rightIH, Polynomial.Expr.eval]
  | neg argument argumentIH =>
      simp [ofExpr, eval_neg, argumentIH, Polynomial.Expr.eval]

end Sparse

/-- Whether two expressions are the same polynomial, decided by normalizing
their difference. A `true` answer is proved sound (`identical_sound`); `false`
only means the normal form did not cancel. -/
def identical {n : Nat} (left right : Polynomial.Expr n) : Bool :=
  (Sparse.ofExpr (.add left (.neg right))).isEmpty

theorem identical_sound {n : Nat} {left right : Polynomial.Expr n}
    (same : identical left right = true) (point : Point n) :
    left.eval point = right.eval point := by
  have vanish := Sparse.eval_ofExpr (.add left (.neg right)) point
  rw [List.isEmpty_iff.mp same] at vanish
  simp [Polynomial.Expr.eval] at vanish
  linarith

/-! ### Positive evidence -/

/-- Read a formula as an ordered conjunction of constraints `p ≤ 0`, if it is
one: `tru`, `le`, `ge` (negated exactly) and `and`. Every other shape is
outside the positive fragment. Positions are kept; nothing is dropped. -/
def Formula.nonstrict? {n : Nat} : Formula n → Option (List (Polynomial.Expr n))
  | .tru => some []
  | .atom .le polynomial => some [polynomial]
  | .atom .ge polynomial => some [.neg polynomial]
  | .and left right =>
      match left.nonstrict?, right.nonstrict? with
      | some first, some second => some (first ++ second)
      | _, _ => none
  | _ => none

theorem Formula.holds_of_nonstrict {n : Nat} {formula : Formula n}
    {constraints : List (Polynomial.Expr n)} (read : formula.nonstrict? = some constraints)
    (point : Point n) :
    formula.holds point ↔ ∀ constraint ∈ constraints, constraint.eval point ≤ 0 := by
  induction formula generalizing constraints with
  | tru =>
      simp only [Formula.nonstrict?, Option.some.injEq] at read
      subst read
      simp [Formula.holds]
  | fls => simp [Formula.nonstrict?] at read
  | atom relation polynomial =>
      cases relation <;> simp only [Formula.nonstrict?, Option.some.injEq,
        reduceCtorEq] at read <;> subst read <;>
        simp [Formula.holds, Relation.holds, Polynomial.Expr.eval]
  | and left right leftIH rightIH =>
      simp only [Formula.nonstrict?] at read
      split at read
      · rename_i first second leftRead rightRead
        simp only [Option.some.injEq] at read
        subst read
        simp only [Formula.holds, leftIH leftRead, rightIH rightRead, List.mem_append]
        constructor
        · rintro ⟨l, r⟩ c (hc | hc)
          exacts [l c hc, r c hc]
        · intro h
          exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
      · cases read
  | or => simp [Formula.nonstrict?] at read
  | not => simp [Formula.nonstrict?] at read

/-- A weighted sum of squares `Σ w_k · g_k²`, as untrusted exact data. -/
structure SquareSum (n : Nat) where
  /-- Each term's weight `w_k` and polynomial `g_k`. -/
  terms : List (ℚ × Polynomial.Expr n)

namespace SquareSum

variable {n : Nat}

/-- The polynomial the sum denotes. -/
def expr (sum : SquareSum n) : Polynomial.Expr n :=
  sum.terms.foldr (fun term rest => .add (.mul (.constant term.1) (.mul term.2 term.2)) rest)
    (.constant 0)

/-- Whether every weight is nonnegative. -/
def weightsNonnegative (sum : SquareSum n) : Bool :=
  sum.terms.all fun term => decide (0 ≤ term.1)

theorem eval_nonnegative (sum : SquareSum n) (valid : sum.weightsNonnegative = true)
    (point : Point n) : 0 ≤ sum.expr.eval point := by
  obtain ⟨terms⟩ := sum
  induction terms with
  | nil => simp [expr, Polynomial.Expr.eval]
  | cons head rest ih =>
      simp only [weightsNonnegative, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at valid
      simp only [expr, List.foldr_cons, Polynomial.Expr.eval] at ih ⊢
      have weight : (0 : ℝ) ≤ head.1 := by exact_mod_cast valid.1
      exact add_nonneg (mul_nonneg weight (mul_self_nonneg _))
        (ih (by simpa [weightsNonnegative] using valid.2))

end SquareSum

/-- The evidence for one consequent constraint: `σ_j0` and one multiplier per
antecedent constraint, in order. -/
structure Row (n : Nat) where
  /-- `σ_j0`. -/
  base : SquareSum n
  /-- `σ_ji`, one per antecedent constraint, in the antecedent's order. -/
  multipliers : List (SquareSum n)

namespace Row

variable {n : Nat}

/-- `Σ_i σ_i · (−p_i)`, pairing multipliers with constraints in order. -/
def weighted : List (SquareSum n) → List (Polynomial.Expr n) → Polynomial.Expr n
  | σ :: σs, p :: ps => .add (.mul σ.expr (.neg p)) (weighted σs ps)
  | _, _ => .constant 0

theorem weighted_nonnegative (σs : List (SquareSum n)) (ps : List (Polynomial.Expr n))
    (valid : σs.all SquareSum.weightsNonnegative = true) (point : Point n)
    (below : ∀ p ∈ ps, p.eval point ≤ 0) :
    0 ≤ (weighted σs ps).eval point := by
  induction σs generalizing ps with
  | nil => cases ps <;> simp [weighted, Polynomial.Expr.eval]
  | cons σ rest ih =>
      cases ps with
      | nil => simp [weighted, Polynomial.Expr.eval]
      | cons p others =>
          simp only [List.all_cons, Bool.and_eq_true] at valid
          simp only [weighted, Polynomial.Expr.eval]
          have head := σ.eval_nonnegative valid.1 point
          have tail := ih others valid.2 fun q hq => below q (List.mem_cons_of_mem _ hq)
          have negative := below p List.mem_cons_self
          nlinarith

/-- `σ_j0 + Σ_i σ_ji · (−p_i)`. -/
def expr (row : Row n) (constraints : List (Polynomial.Expr n)) : Polynomial.Expr n :=
  .add row.base.expr (weighted row.multipliers constraints)

/-- Check one row against the antecedent's constraints and one consequent
constraint: a multiplier per constraint, nonnegative weights, and the exact
identity `−q = σ_0 + Σ σ_i · (−p_i)`. -/
def check (row : Row n) (constraints : List (Polynomial.Expr n))
    (consequent : Polynomial.Expr n) : Bool :=
  row.multipliers.length == constraints.length &&
    row.base.weightsNonnegative &&
    row.multipliers.all SquareSum.weightsNonnegative &&
    identical (.neg consequent) (row.expr constraints)

theorem check_sound {row : Row n} {constraints : List (Polynomial.Expr n)}
    {consequent : Polynomial.Expr n} (valid : row.check constraints consequent = true)
    (point : Point n) (below : ∀ p ∈ constraints, p.eval point ≤ 0) :
    consequent.eval point ≤ 0 := by
  simp only [check, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨_, base⟩, multipliers⟩, same⟩ := valid
  have identity := identical_sound same point
  have base_nonneg := row.base.eval_nonnegative base point
  have rest := weighted_nonnegative row.multipliers constraints multipliers point below
  simp only [expr, Polynomial.Expr.eval] at identity
  linarith

end Row

/-- Positive evidence for a goal: one row per consequent constraint, in order. -/
structure EntailmentCertificate (n : Nat) where
  /-- The rows, one per consequent constraint. -/
  rows : List (Row n)

/-- Check a certificate against a goal as posed. Both sides must be in the
positive fragment, and every consequent constraint needs its own valid row. -/
def EntailmentCertificate.check (goal : Goal)
    (certificate : EntailmentCertificate goal.context.dimension) : Bool :=
  match goal.antecedent.nonstrict?, goal.consequent.nonstrict? with
  | some constraints, some consequents =>
      certificate.rows.length == consequents.length &&
        (certificate.rows.zip consequents).all fun pair =>
          pair.1.check constraints pair.2
  | _, _ => false

/-- **A certificate that checks proves the goal.** -/
theorem EntailmentCertificate.sound (goal : Goal)
    (certificate : EntailmentCertificate goal.context.dimension)
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
    exact Row.check_sound (rows _ paired) point holds
  · cases valid

/-! ### Negative evidence -/

/-- An expression evaluated exactly at a rational point. -/
def evalRational {n : Nat} (point : Fin n → ℚ) : Polynomial.Expr n → ℚ
  | .var coordinate => point coordinate
  | .constant value => value
  | .add left right => evalRational point left + evalRational point right
  | .mul left right => evalRational point left * evalRational point right
  | .neg argument => -evalRational point argument

/-- Rational evaluation agrees with the real semantics at the cast point. -/
theorem evalRational_cast {n : Nat} (point : Fin n → ℚ)
    (expression : Polynomial.Expr n) :
    ((evalRational point expression : ℚ) : ℝ) =
      expression.eval fun i => (point i : ℝ) := by
  induction expression with
  | var coordinate => rfl
  | constant value => rfl
  | add left right leftIH rightIH =>
      simp [evalRational, Polynomial.Expr.eval, leftIH, rightIH]
  | mul left right leftIH rightIH =>
      simp [evalRational, Polynomial.Expr.eval, leftIH, rightIH]
  | neg argument argumentIH =>
      simp [evalRational, Polynomial.Expr.eval, argumentIH]

/-- One comparison, decided over ℚ. -/
def Relation.holdsQ : Relation → ℚ → Bool
  | .eq, value => value == 0
  | .le, value => decide (value ≤ 0)
  | .lt, value => decide (value < 0)
  | .ge, value => decide (0 ≤ value)
  | .gt, value => decide (0 < value)

theorem Relation.holdsQ_iff (relation : Relation) (value : ℚ) :
    relation.holdsQ value = true ↔ relation.holds (value : ℝ) := by
  cases relation <;> simp [Relation.holdsQ, Relation.holds]

/-- A formula, decided exactly at a rational point. Every constructor of the
quantifier-free fragment is covered. -/
def Formula.holdsQ {n : Nat} (point : Fin n → ℚ) : Formula n → Bool
  | .tru => true
  | .fls => false
  | .atom relation polynomial => relation.holdsQ (evalRational point polynomial)
  | .and left right => left.holdsQ point && right.holdsQ point
  | .or left right => left.holdsQ point || right.holdsQ point
  | .not argument => !argument.holdsQ point

theorem Formula.holdsQ_iff {n : Nat} (point : Fin n → ℚ) (formula : Formula n) :
    formula.holdsQ point = true ↔ formula.holds fun i => (point i : ℝ) := by
  induction formula with
  | tru => simp [Formula.holdsQ, Formula.holds]
  | fls => simp [Formula.holdsQ, Formula.holds]
  | atom relation polynomial =>
      simp [Formula.holdsQ, Formula.holds, Relation.holdsQ_iff, evalRational_cast]
  | and left right leftIH rightIH =>
      simp [Formula.holdsQ, Formula.holds, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [Formula.holdsQ, Formula.holds, leftIH, rightIH]
  | not argument argumentIH =>
      simp [Formula.holdsQ, Formula.holds, ← argumentIH]

/-- Whether a named answer is a counterexample to a goal as posed: it names
every coordinate of the goal's context exactly once, the antecedent holds there
and the consequent does not. -/
def refutes (goal : Goal) (answer : Context.Assignment) : Bool :=
  match goal.context.read answer with
  | .ok point => goal.antecedent.holdsQ point && !goal.consequent.holdsQ point
  | .error _ => false

/-- **A counterexample that checks refutes the goal.** -/
theorem refutes_sound (goal : Goal) (answer : Context.Assignment)
    (valid : refutes goal answer = true) : ¬ goal.Entailment := by
  unfold refutes at valid
  split at valid
  · rename_i point _
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at valid
    obtain ⟨antecedent, consequent⟩ := valid
    intro entails
    have holds := entails _ ((Formula.holdsQ_iff point _).mp antecedent)
    rw [← Formula.holdsQ_iff] at holds
    rw [holds] at consequent
    cases consequent
  · cases valid

#print axioms Sparse.eval_ofExpr
#print axioms identical_sound
#print axioms EntailmentCertificate.sound
#print axioms refutes_sound

end Gimle.Forseti.Syntax
