import Gimle.Forseti.Syntax.Certificate
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-! Checked real-algebraic counterexamples to formula entailments.

Some false entailments fail at no rational point: `x² = 2 ⊨ x < 0` fails only
at `±√2`. `refutes` (task 017) cannot refute them. Here a counterexample is a
real point described exactly, without being computed:

- a **box** of closed rational intervals, one per coordinate, and
- for each coordinate a univariate rational polynomial whose value changes sign
  across its interval, so (by the intermediate value theorem) it has a root
  there, and whose derivative's interval enclosure excludes zero, so that root
  is the only one (`root_unique`).

The point is that tuple of roots. A rational coordinate `q` is the polynomial
`x - q` on `[q, q]`.

Every atom of the goal is then decided at the point from the box alone, for
every point of the box: by an interval **enclosure** of its polynomial that
excludes zero (a strict sign), or, for a zero, by a checked polynomial
**identity** `q = Σᵢ sᵢ · pᵢ(xᵢ)`, which vanishes wherever each `pᵢ` does. The
producer's claims about roots and signs are never used: `algebraicRefutes`
recomputes everything, and `algebraicRefutes_sound` proves `¬ goal.Entailment`.
-/

namespace Gimle.Forseti.Syntax

open Gimle.Forseti
open Gimle.Asgard

/-! ### Interval arithmetic -/

/-- A closed rational interval `[lo, hi]`. -/
structure Bounds where
  /-- The lower end. -/
  lo : ℚ
  /-- The upper end. -/
  hi : ℚ

namespace Bounds

/-- The real value lies in the interval. -/
def Contains (b : Bounds) (v : ℝ) : Prop := (b.lo : ℝ) ≤ v ∧ v ≤ b.hi

/-- Interval sum. -/
def add (a b : Bounds) : Bounds := ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Interval negation. -/
def neg (a : Bounds) : Bounds := ⟨-a.hi, -a.lo⟩

/-- Interval product: the extremes of the four corner products. -/
def mul (a b : Bounds) : Bounds :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

theorem add_contains {a b : Bounds} {u v : ℝ} (hu : a.Contains u) (hv : b.Contains v) :
    (a.add b).Contains (u + v) := by
  simp only [Contains, add, Rat.cast_add] at *
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

theorem neg_contains {a : Bounds} {u : ℝ} (hu : a.Contains u) : a.neg.Contains (-u) := by
  simp only [Contains, neg, Rat.cast_neg] at *
  constructor <;> linarith [hu.1, hu.2]

/-- A product of two bounded reals lies between the least and greatest corner
products. -/
theorem mul_between {u v a₁ a₂ b₁ b₂ : ℝ} (hu : a₁ ≤ u ∧ u ≤ a₂) (hv : b₁ ≤ v ∧ v ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ u * v ∧
      u * v ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have along (c : ℝ) : min (c * b₁) (c * b₂) ≤ c * v ∧ c * v ≤ max (c * b₁) (c * b₂) := by
    rcases le_total 0 c with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have across : min (a₁ * v) (a₂ * v) ≤ u * v ∧ u * v ≤ max (a₁ * v) (a₂ * v) := by
    rcases le_total 0 v with h | h
    · exact ⟨min_le_of_left_le (by nlinarith), le_max_of_le_right (by nlinarith)⟩
    · exact ⟨min_le_of_right_le (by nlinarith), le_max_of_le_left (by nlinarith)⟩
  have first := along a₁
  have second := along a₂
  exact ⟨le_trans (min_le_min first.1 second.1) across.1,
    le_trans across.2 (max_le_max first.2 second.2)⟩

theorem mul_contains {a b : Bounds} {u v : ℝ} (hu : a.Contains u) (hv : b.Contains v) :
    (a.mul b).Contains (u * v) := by
  have := mul_between hu hv
  simp only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  exact this

end Bounds

/-- An interval enclosure of a polynomial's values over a box. -/
def enclose {n : Nat} (box : Fin n → Bounds) : Polynomial.Expr n → Bounds
  | .var i => box i
  | .constant q => ⟨q, q⟩
  | .add a b => (enclose box a).add (enclose box b)
  | .mul a b => (enclose box a).mul (enclose box b)
  | .neg a => (enclose box a).neg

/-- **The enclosure is sound**: at every point of the box, the polynomial's value
lies in it. -/
theorem enclose_sound {n : Nat} (box : Fin n → Bounds) (x : Point n)
    (inside : ∀ i, (box i).Contains (x i)) (e : Polynomial.Expr n) :
    (enclose box e).Contains (e.eval x) := by
  induction e with
  | var i => exact inside i
  | constant q => exact ⟨le_refl _, le_refl _⟩
  | add a b ha hb => exact Bounds.add_contains ha hb
  | mul a b ha hb => exact Bounds.mul_contains ha hb
  | neg a ha => exact Bounds.neg_contains ha

/-! ### Univariate roots -/

/-- The derivative of a univariate polynomial expression. -/
def derivative : Polynomial.Expr 1 → Polynomial.Expr 1
  | .var _ => .constant 1
  | .constant _ => .constant 0
  | .add a b => .add (derivative a) (derivative b)
  | .mul a b => .add (.mul (derivative a) b) (.mul a (derivative b))
  | .neg a => .neg (derivative a)

/-- A univariate expression as a real function. -/
noncomputable def univariate (e : Polynomial.Expr 1) (t : ℝ) : ℝ := e.eval fun _ => t

theorem hasDerivAt_univariate (e : Polynomial.Expr 1) (t : ℝ) :
    HasDerivAt (univariate e) (univariate (derivative e) t) t := by
  induction e with
  | var i =>
      have slope : univariate (derivative (.var i)) t = 1 := by
        simp [univariate, derivative, Polynomial.Expr.eval]
      rw [slope]
      exact hasDerivAt_id t
  | constant q =>
      have slope : univariate (derivative (.constant q)) t = 0 := by
        simp [univariate, derivative, Polynomial.Expr.eval]
      rw [slope]
      exact hasDerivAt_const t (q : ℝ)
  | add a b ha hb => exact ha.add hb
  | mul a b ha hb => exact ha.mul hb
  | neg a ha => exact ha.neg

theorem continuous_univariate (e : Polynomial.Expr 1) : Continuous (univariate e) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_univariate e t).continuousAt

/-- A coordinate of an algebraic point: a polynomial and an interval that is
meant to isolate one of its roots. -/
structure Root where
  /-- The defining polynomial, in one variable. -/
  polynomial : Polynomial.Expr 1
  /-- The isolating interval. -/
  bounds : Bounds

namespace Root

/-- The polynomial's exact value at a rational argument. -/
def valueAt (root : Root) (q : ℚ) : ℚ := evalRational (fun _ => q) root.polynomial

/-- The checks that make `root` describe exactly one real number: an ordered
interval, a sign change across it, and a derivative enclosure over it that
excludes zero. -/
def check (root : Root) : Bool :=
  let slope := enclose (fun _ => root.bounds) (derivative root.polynomial)
  decide (root.bounds.lo ≤ root.bounds.hi) &&
    decide (root.valueAt root.bounds.lo * root.valueAt root.bounds.hi ≤ 0) &&
    (decide (0 < slope.lo) || decide (slope.hi < 0))

theorem valueAt_cast (root : Root) (q : ℚ) :
    ((root.valueAt q : ℚ) : ℝ) = univariate root.polynomial q := by
  simp [valueAt, univariate, evalRational_cast]

/-- **A checked root exists**: the polynomial vanishes somewhere in the interval. -/
theorem exists_zero {root : Root} (valid : root.check = true) :
    ∃ t : ℝ, root.bounds.Contains t ∧ univariate root.polynomial t = 0 := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at valid
  obtain ⟨⟨ordered, change⟩, _⟩ := valid
  have ordered' : (root.bounds.lo : ℝ) ≤ root.bounds.hi := by exact_mod_cast ordered
  have change' : univariate root.polynomial root.bounds.lo *
      univariate root.polynomial root.bounds.hi ≤ 0 := by
    rw [← valueAt_cast, ← valueAt_cast]; exact_mod_cast change
  have continuous := (continuous_univariate root.polynomial).continuousOn
    (s := Set.Icc (root.bounds.lo : ℝ) root.bounds.hi)
  rcases mul_nonpos_iff.mp change' with ⟨high, low⟩ | ⟨low, high⟩
  · obtain ⟨t, within, value⟩ := intermediate_value_Icc' ordered' continuous ⟨low, high⟩
    exact ⟨t, within, value⟩
  · obtain ⟨t, within, value⟩ := intermediate_value_Icc ordered' continuous ⟨low, high⟩
    exact ⟨t, within, value⟩

/-- **The checked root is the only one in its interval**: the derivative has a
fixed sign there, so the polynomial is strictly monotone on it. -/
theorem root_unique {root : Root} (valid : root.check = true) {s t : ℝ}
    (hs : root.bounds.Contains s) (ht : root.bounds.Contains t)
    (zs : univariate root.polynomial s = 0) (zt : univariate root.polynomial t = 0) :
    s = t := by
  simp only [check, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at valid
  obtain ⟨_, slope⟩ := valid
  set I := Set.Icc (root.bounds.lo : ℝ) root.bounds.hi
  have within : ∀ r ∈ I, (enclose (fun _ => root.bounds) (derivative root.polynomial)).Contains
      (univariate (derivative root.polynomial) r) := fun r hr =>
    enclose_sound _ (fun _ => r) (fun _ => hr) _
  have derivs : ∀ r, deriv (univariate root.polynomial) r =
      univariate (derivative root.polynomial) r := fun r =>
    (hasDerivAt_univariate _ r).deriv
  have continuous := (continuous_univariate root.polynomial).continuousOn (s := I)
  have injective : Set.InjOn (univariate root.polynomial) I := by
    rcases slope with positive | negative
    · refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous fun r hr => ?_).injOn
      rw [derivs]
      have := (within r (interior_subset hr)).1
      exact lt_of_lt_of_le (by exact_mod_cast positive) this
    · refine (strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous fun r hr => ?_).injOn
      rw [derivs]
      have := (within r (interior_subset hr)).2
      exact lt_of_le_of_lt this (by exact_mod_cast negative)
  exact injective hs ht (zs.trans zt.symm)

end Root

/-! ### Deciding atoms at an algebraic point -/

/-- How one atom's sign is established at the point. -/
inductive AtomEvidence (n : Nat) where
  /-- By the polynomial's enclosure over the box, which must exclude zero. -/
  | enclosure
  /-- As zero, by the identity `q = Σᵢ sᵢ · pᵢ(xᵢ)` with these `sᵢ`, one per
  coordinate, in order. -/
  | zero (multipliers : List (Polynomial.Expr n))

/-- An algebraic counterexample: one root per coordinate, in context order, and
the evidence for each atom of the antecedent and the consequent, in the order
the formulas are read left to right. -/
structure AlgebraicWitness (n : Nat) where
  /-- The point's coordinates. -/
  coordinates : List Root
  /-- One piece of evidence per antecedent atom. -/
  antecedent : List (AtomEvidence n)
  /-- One piece of evidence per consequent atom. -/
  consequent : List (AtomEvidence n)

/-- The default coordinate, used only where the length check has already
failed. -/
def Root.default : Root := ⟨.var 0, ⟨0, 0⟩⟩

namespace AlgebraicWitness

variable {n : Nat}

/-- The box of the witness's intervals. -/
def box (w : AlgebraicWitness n) (i : Fin n) : Bounds :=
  (w.coordinates[(i : Nat)]?.getD Root.default).bounds

/-- Coordinate `i`'s polynomial, read at coordinate `i` of an `n`-point. -/
def lifted (w : AlgebraicWitness n) (i : Fin n) : Polynomial.Expr n :=
  rename (fun _ => i) (w.coordinates[(i : Nat)]?.getD Root.default).polynomial

/-- `Σᵢ sᵢ · pᵢ(xᵢ)`, pairing multipliers with coordinates in order. -/
def combination (w : AlgebraicWitness n) : List (Polynomial.Expr n) → Nat → Polynomial.Expr n
  | [], _ => .constant 0
  | s :: rest, k =>
      if h : k < n then .add (.mul s (w.lifted ⟨k, h⟩)) (w.combination rest (k + 1))
      else .constant 0

/-- The truth value an atom's evidence establishes, if it establishes one. -/
def atomTruth (w : AlgebraicWitness n) (relation : Relation) (q : Polynomial.Expr n) :
    AtomEvidence n → Option Bool
  | .enclosure =>
      let b := enclose w.box q
      if 0 < b.lo then some (relation.holdsQ 1)
      else if b.hi < 0 then some (relation.holdsQ (-1))
      else none
  | .zero multipliers =>
      if identical q (w.combination multipliers 0) then some (relation.holdsQ 0) else none

/-- Decide a formula at the point, consuming one piece of evidence per atom. -/
def decideAt (w : AlgebraicWitness n) :
    Formula n → List (AtomEvidence n) → Option (Bool × List (AtomEvidence n))
  | .tru, evidence => some (true, evidence)
  | .fls, evidence => some (false, evidence)
  | .atom _ _, [] => none
  | .atom relation q, e :: rest => (w.atomTruth relation q e).map fun b => (b, rest)
  | .and left right, evidence =>
      match w.decideAt left evidence with
      | none => none
      | some (a, rest) =>
          match w.decideAt right rest with
          | none => none
          | some (b, rest') => some (a && b, rest')
  | .or left right, evidence =>
      match w.decideAt left evidence with
      | none => none
      | some (a, rest) =>
          match w.decideAt right rest with
          | none => none
          | some (b, rest') => some (a || b, rest')
  | .not argument, evidence =>
      (w.decideAt argument evidence).map fun p => (!p.1, p.2)

/-- A point the witness describes: in the box, and a root of each coordinate's
polynomial. -/
def Describes (w : AlgebraicWitness n) (x : Point n) : Prop :=
  ∀ i, (w.box i).Contains (x i) ∧
    univariate (w.coordinates[(i : Nat)]?.getD Root.default).polynomial (x i) = 0

theorem lifted_eval {w : AlgebraicWitness n} {x : Point n} (at_ : w.Describes x) (i : Fin n) :
    (w.lifted i).eval x = 0 := by
  simp only [lifted, rename_eval]
  exact (at_ i).2

theorem combination_eval {w : AlgebraicWitness n} {x : Point n} (at_ : w.Describes x) :
    ∀ (ms : List (Polynomial.Expr n)) (k : Nat), (w.combination ms k).eval x = 0
  | [], _ => by simp [combination, Polynomial.Expr.eval]
  | s :: rest, k => by
      unfold combination
      split
      · simp only [Polynomial.Expr.eval, lifted_eval at_, mul_zero, zero_add]
        exact combination_eval at_ rest (k + 1)
      · simp [Polynomial.Expr.eval]

/-- A relation holds at a value exactly as it holds at any value of the same
sign. -/
theorem Relation.holds_pos (relation : Relation) {v : ℝ} (pos : 0 < v) :
    relation.holds v ↔ relation.holdsQ 1 = true := by
  rw [Relation.holdsQ_iff]
  cases relation <;> simp only [Relation.holds, Rat.cast_one]
  · exact ⟨fun h => absurd h pos.ne', fun h => absurd h one_ne_zero⟩
  · exact ⟨fun h => absurd h (not_le.mpr pos), fun h => absurd h (by norm_num)⟩
  · exact ⟨fun h => absurd h (not_lt.mpr pos.le), fun h => absurd h (by norm_num)⟩
  · exact ⟨fun _ => zero_le_one, fun _ => pos.le⟩
  · exact ⟨fun _ => zero_lt_one, fun _ => pos⟩

theorem Relation.holds_neg (relation : Relation) {v : ℝ} (neg : v < 0) :
    relation.holds v ↔ relation.holdsQ (-1) = true := by
  rw [Relation.holdsQ_iff]
  cases relation <;> simp only [Relation.holds, Rat.cast_neg, Rat.cast_one]
  · exact ⟨fun h => absurd h neg.ne, fun h => absurd h (by norm_num)⟩
  · exact ⟨fun _ => by norm_num, fun _ => neg.le⟩
  · exact ⟨fun _ => by norm_num, fun _ => neg⟩
  · exact ⟨fun h => absurd h (not_le.mpr neg), fun h => absurd h (by norm_num)⟩
  · exact ⟨fun h => absurd h (not_lt.mpr neg.le), fun h => absurd h (by norm_num)⟩

theorem atomTruth_sound {w : AlgebraicWitness n} {x : Point n} (at_ : w.Describes x)
    {relation : Relation} {q : Polynomial.Expr n} {e : AtomEvidence n} {b : Bool}
    (decided : w.atomTruth relation q e = some b) :
    relation.holds (q.eval x) ↔ b = true := by
  cases e with
  | enclosure =>
      have enclosed := enclose_sound w.box x (fun i => (at_ i).1) q
      simp only [atomTruth] at decided
      split at decided
      · rename_i positive
        cases decided
        exact Relation.holds_pos relation
          (lt_of_lt_of_le (by exact_mod_cast positive) enclosed.1)
      · split at decided
        · rename_i _ negative
          cases decided
          exact Relation.holds_neg relation
            (lt_of_le_of_lt enclosed.2 (by exact_mod_cast negative))
        · cases decided
  | zero multipliers =>
      simp only [atomTruth] at decided
      split at decided
      · rename_i same
        cases decided
        have zero : q.eval x = 0 := by
          rw [identical_sound same x, combination_eval at_]
        rw [zero, ← Rat.cast_zero, ← Relation.holdsQ_iff]
      · cases decided

theorem decideAt_sound {w : AlgebraicWitness n} {x : Point n} (at_ : w.Describes x) :
    ∀ (formula : Formula n) (evidence rest : List (AtomEvidence n)) (b : Bool),
      w.decideAt formula evidence = some (b, rest) → (formula.holds x ↔ b = true)
  | .tru, evidence, rest, b, decided => by
      simp only [decideAt, Option.some.injEq, Prod.mk.injEq] at decided
      simp [Formula.holds, ← decided.1]
  | .fls, evidence, rest, b, decided => by
      simp only [decideAt, Option.some.injEq, Prod.mk.injEq] at decided
      simp [Formula.holds, ← decided.1]
  | .atom relation q, [], rest, b, decided => by simp [decideAt] at decided
  | .atom relation q, e :: more, rest, b, decided => by
      simp only [decideAt, Option.map_eq_some_iff, Prod.mk.injEq] at decided
      obtain ⟨b', truth, same, _⟩ := decided
      subst same
      exact atomTruth_sound at_ truth
  | .and left right, evidence, rest, b, decided => by
      simp only [decideAt] at decided
      split at decided
      · cases decided
      · rename_i a mid first
        split at decided
        · cases decided
        · rename_i c last second
          simp only [Option.some.injEq, Prod.mk.injEq] at decided
          rw [← decided.1]
          simp only [Formula.holds, Bool.and_eq_true,
            decideAt_sound at_ left _ _ _ first, decideAt_sound at_ right _ _ _ second]
  | .or left right, evidence, rest, b, decided => by
      simp only [decideAt] at decided
      split at decided
      · cases decided
      · rename_i a mid first
        split at decided
        · cases decided
        · rename_i c last second
          simp only [Option.some.injEq, Prod.mk.injEq] at decided
          rw [← decided.1]
          simp only [Formula.holds, Bool.or_eq_true,
            decideAt_sound at_ left _ _ _ first, decideAt_sound at_ right _ _ _ second]
  | .not argument, evidence, rest, b, decided => by
      simp only [decideAt, Option.map_eq_some_iff, Prod.mk.injEq] at decided
      obtain ⟨⟨a, mid⟩, inner, flipped, _⟩ := decided
      subst flipped
      simp only [Formula.holds, decideAt_sound at_ argument _ _ _ inner]
      cases a <;> simp

/-- A point exists that the witness describes, once every coordinate checks. -/
theorem exists_point {w : AlgebraicWitness n} (roots : w.coordinates.all Root.check = true) :
    ∃ x, w.Describes x := by
  have each : ∀ i : Fin n, ∃ t : ℝ, (w.box i).Contains t ∧
      univariate (w.coordinates[(i : Nat)]?.getD Root.default).polynomial t = 0 := by
    intro i
    simp only [box]
    by_cases inside : (i : Nat) < w.coordinates.length
    · rw [List.getElem?_eq_getElem inside, Option.getD_some]
      exact Root.exists_zero (List.all_eq_true.mp roots _ (List.getElem_mem inside))
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt inside), Option.getD_none]
      refine ⟨0, ?_, ?_⟩
      · simp [Root.default, Bounds.Contains]
      · simp [Root.default, univariate, Polynomial.Expr.eval]
  choose x hx using each
  exact ⟨x, hx⟩

end AlgebraicWitness

/-- Whether an algebraic witness refutes a goal as posed: one checked root per
coordinate, the antecedent decided true and the consequent decided false at the
point, with every piece of evidence used. -/
def algebraicRefutes (goal : Goal) (w : AlgebraicWitness goal.context.dimension) : Bool :=
  w.coordinates.length == goal.context.dimension &&
    w.coordinates.all Root.check &&
    (match w.decideAt goal.antecedent w.antecedent with
      | some (true, []) => true
      | _ => false) &&
    (match w.decideAt goal.consequent w.consequent with
      | some (false, []) => true
      | _ => false)

/-- **A checked algebraic witness refutes the goal.** -/
theorem algebraicRefutes_sound (goal : Goal) (w : AlgebraicWitness goal.context.dimension)
    (valid : algebraicRefutes goal w = true) : ¬ goal.Entailment := by
  simp only [algebraicRefutes, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨_, roots⟩, antecedent⟩, consequent⟩ := valid
  obtain ⟨x, at_⟩ := AlgebraicWitness.exists_point roots
  intro entails
  split at antecedent
  · rename_i decided
    split at consequent
    · rename_i refuted
      have holds := (AlgebraicWitness.decideAt_sound at_ _ _ _ _ decided).mpr rfl
      have fails := AlgebraicWitness.decideAt_sound at_ _ _ _ _ refuted
      exact absurd ((fails.mp (entails x holds))) (by simp)
    · cases consequent
  · cases antecedent

#print axioms Root.exists_zero
#print axioms Root.root_unique
#print axioms algebraicRefutes_sound

end Gimle.Forseti.Syntax
