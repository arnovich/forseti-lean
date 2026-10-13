import Gimle.Asgard.Dynamics.Linear
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul

/-! Soundness of exact rational weighted-square energy certificates. Circuit
translations, matrix identities, nonnegative weights and trajectory semantics
are explicit assumptions. No norm or convergence result follows here. -/
namespace Gimle.Forseti.LinearEnergy
open Gimle.Asgard Dynamics
open scoped Matrix
abbrev QMatrix (n : Nat) := Linear.Matrix n

/-- Cast every rational entry exactly into the real matrix interpretation. -/
noncomputable def realMatrix {n : Nat} (p : QMatrix n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => p i j

/-- The exact quadratic form xᵀ P x, with both matrix indices retained. -/
noncomputable def quadratic {n : Nat} (p : QMatrix n) (x : Point n) : ℝ :=
  dotProduct x ((realMatrix p).mulVec x)

/-- Recompute minus AᵀP+PA entrywise over rational arithmetic. -/
def dissipation {n : Nat} (a p : QMatrix n) : QMatrix n :=
  fun i j => -((∑ k, a k i * p k j) + ∑ k, p i k * a k j)

@[simp] theorem real_dissipation {n : Nat} (a p : QMatrix n) :
    realMatrix (dissipation a p) =
      -((realMatrix a).transpose * realMatrix p + realMatrix p * realMatrix a) := by
  ext i j
  simp [realMatrix, dissipation, Matrix.mul_apply]

/-- The algebraic derivative identity holds before any positivity assumption. -/
theorem derivative_identity {n : Nat} (a p : QMatrix n) (x : Point n) :
    dotProduct (a.eval x) (p.eval x) + dotProduct x (p.eval (a.eval x)) =
      -quadratic (dissipation a p) x := by
  rw [quadratic, real_dissipation, Matrix.neg_mulVec, dotProduct_neg, neg_neg,
    Matrix.add_mulVec, dotProduct_add]
  change dotProduct ((realMatrix a).mulVec x) ((realMatrix p).mulVec x) +
    dotProduct x ((realMatrix p).mulVec ((realMatrix a).mulVec x)) = _
  apply congrArg₂ (· + ·)
  · rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.dotProduct_mulVec]
  · rw [Matrix.mulVec_mulVec]

theorem dotProduct_derivative {n : Nat} (x y : Signal n) (dx dy : Point n)
    (domain : Set ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun t => x t i) (dx i) domain t)
    (hy : ∀ i, HasDerivWithinAt (fun t => y t i) (dy i) domain t) :
    HasDerivWithinAt (fun t => dotProduct (x t) (y t))
      (dotProduct dx (y t) + dotProduct (x t) dy) domain t := by
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ)
    (fun (i : Fin n) _ => (hx i).mul (hy i))
  convert! h using 1
  simp [dotProduct, Finset.sum_add_distrib]

theorem quadratic_derivative {n : Nat} (problem : Linear.Problem n)
    (p : QMatrix n) (state : Signal n) (solves : problem.Solves state)
    (t : ℝ) (ht : t ∈ problem.time.domain) :
    HasDerivWithinAt (fun t => quadratic p (state t))
      (-quadratic (dissipation problem.matrix p) (state t)) problem.time.domain t := by
  have hs : HasDerivWithinAt state (problem.matrix.eval (state t)) problem.time.domain t :=
    hasDerivWithinAt_pi.mpr (solves.2 t ht)
  have hp := (LinearAnalysis.rationalOperator p).hasFDerivAt.comp_hasDerivWithinAt t hs
  have hp' : ∀ i, HasDerivWithinAt (fun t => p.eval (state t) i)
      (p.eval (problem.matrix.eval (state t)) i) problem.time.domain t := by
    intro i
    have hi := hasDerivWithinAt_pi.mp hp i
    convert! hi using 1 <;> simp [Linear.Matrix.eval]
  have h := dotProduct_derivative state (fun t => p.eval (state t))
    (problem.matrix.eval (state t)) (p.eval (problem.matrix.eval (state t)))
    problem.time.domain t (solves.2 t ht) hp'
  rw [derivative_identity] at h
  exact h

@[simp] theorem quadratic_zero {n : Nat} (x : Point n) :
    quadratic (0 : QMatrix n) x = 0 := by
  simp [quadratic, realMatrix, Matrix.mulVec, dotProduct]

@[simp] theorem quadratic_add {n : Nat} (p q : QMatrix n) (x : Point n) :
    quadratic (p + q) x = quadratic p x + quadratic q x := by
  simp [quadratic, realMatrix, Matrix.mulVec, dotProduct, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem quadratic_sum {n : Nat} {ι : Type} (s : Finset ι) (p : ι → QMatrix n)
    (x : Point n) : quadratic (∑ r ∈ s, p r) x = ∑ r ∈ s, quadratic (p r) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, ih]

def termMatrix {n : Nat} (weight : ℚ) (vector : Fin n → ℚ) : QMatrix n :=
  fun i j => weight * vector i * vector j

theorem quadratic_term {n : Nat} (weight : ℚ) (vector : Fin n → ℚ) (x : Point n) :
    quadratic (termMatrix weight vector) x =
      (weight : ℝ) * (∑ i, (vector i : ℝ) * x i)^2 := by
  simp only [quadratic, realMatrix, termMatrix, Matrix.mulVec, dotProduct,
    Rat.cast_mul, pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Untrusted finite rational data; validity is a separate proposition. -/
structure WeightedSquares (n : Nat) where
  count : Nat
  weight : Fin count → ℚ
  vector : Fin count → Fin n → ℚ

def WeightedSquares.matrix {n : Nat} (s : WeightedSquares n) : QMatrix n :=
  ∑ r, termMatrix (s.weight r) (s.vector r)

@[simp] theorem WeightedSquares.matrix_entry {n : Nat} (s : WeightedSquares n)
    (i j : Fin n) : s.matrix i j = ∑ r, s.weight r * s.vector r i * s.vector r j := by
  simp [matrix, termMatrix]

/-- The same nonnegative weights and exact entry identities are replayed natively. -/
def WeightedSquares.Represents {n : Nat} (s : WeightedSquares n) (p : QMatrix n) : Prop :=
  (∀ r, 0 ≤ s.weight r) ∧ ∀ i j, p i j = s.matrix i j

theorem WeightedSquares.nonnegative {n : Nat} (s : WeightedSquares n) (p : QMatrix n)
    (valid : s.Represents p) (x : Point n) : 0 ≤ quadratic p x := by
  have eq : p = s.matrix := funext (fun i => funext (valid.2 i))
  rw [eq, matrix, quadratic_sum]
  apply Finset.sum_nonneg
  intro r _
  rw [quadratic_term]
  exact mul_nonneg (by exact_mod_cast valid.1 r) (sq_nonneg _)

/-- Separate decompositions certify the energy and its negative derivative. -/
structure Certificate (n : Nat) where
  positive : WeightedSquares n
  decrease : WeightedSquares n

/-- Every coefficient and weight is checked, including the recomputed dissipation. -/
def Certificate.Valid {n : Nat} (certificate : Certificate n) (a p : QMatrix n) : Prop :=
  certificate.positive.Represents p ∧ certificate.decrease.Represents (dissipation a p)

theorem quadratic_antitone {n : Nat} (problem : Linear.Problem n) (p : QMatrix n)
    (state : Signal n) (solves : problem.Solves state)
    (decreases : ∀ x, 0 ≤ quadratic (dissipation problem.matrix p) x) :
    AntitoneOn (fun t => quadratic p (state t)) problem.time.domain := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => -quadratic (dissipation problem.matrix p) (state t))
    (convex_Ici problem.time.start)
  · intro t ht
    exact (quadratic_derivative problem p state solves t ht).continuousWithinAt
  · intro t ht
    exact (quadratic_derivative problem p state solves t (interior_subset ht)).mono interior_subset
  · intro t _
    exact neg_nonpos.mpr (decreases (state t))

theorem certificate_energy_bound {n : Nat} (problem : Linear.Problem n)
    (p : QMatrix n) (certificate : Certificate n) (valid : certificate.Valid problem.matrix p)
    (state : Signal n) (solves : problem.Solves state) (bound : ℝ)
    (initial : quadratic p problem.initial ≤ bound) (t : ℝ) (forward : t ∈ problem.time.domain) :
    0 ≤ quadratic p (state t) ∧ quadratic p (state t) ≤ bound := by
  refine ⟨certificate.positive.nonnegative p valid.1 _, ?_⟩
  have anti := quadratic_antitone problem p state solves
    (certificate.decrease.nonnegative _ valid.2)
  have start_mem : problem.time.start ∈ problem.time.domain := by simp [TimeDomain.domain]
  have start_le : problem.time.start ≤ t := by simpa [TimeDomain.domain] using forward
  have lower := anti start_mem forward start_le
  change quadratic p (state t) ≤ quadratic p (state problem.time.start) at lower
  rw [solves.1] at lower
  exact lower.trans initial

/-- Feed the authoritative RHS circuit through the established no-driver route. -/
def authoritativeField {n : Nat} (rhs : Gimle.Asgard.Circuit n n) :
    Gimle.Asgard.Circuit (0 + n) n :=
  .compose (Polynomial.route (fun i => Fin.natAdd 0 i)) rhs

@[simp] theorem authoritativeField_run {n : Nat} (rhs : Gimle.Asgard.Circuit n n)
    (u : Point 0) (x : Point n) :
    (authoritativeField rhs).run (pointAppend u x) = rhs.run x := by
  simp [authoritativeField, Gimle.Asgard.Circuit.run, pointAppend]

private def noDrivers : Signal 0 := fun _ i => Fin.elim0 i

/-- Actual closed feedback over the supplied typed RHS, with explicit initial wires. -/
def Realizes {n : Nat} (rhs : Gimle.Asgard.Circuit n n) (time : TimeDomain)
    (initial : Point n) (state : Signal n) : Prop :=
  (close time.axis (authoritativeField rhs)).Rel time
    (signalAppend noDrivers (fun _ => initial)) state

/-- The RHS translation assumption binds the original circuit to the matrix
problem. This proof reuses Asgard's trajectory relation and feedback theorem. -/
theorem realizes_iff_problem {n : Nat} (problem : Linear.Problem n)
    (rhs : Gimle.Asgard.Circuit n n) (translated : ∀ x, rhs.run x = problem.matrix.eval x)
    (state : Signal n) : Realizes rhs problem.time problem.initial state ↔ problem.Realizes state := by
  rw [← problem.solves_iff_realizes]
  unfold Realizes
  rw [close_correct]
  simp only [authoritativeField_run, translated, true_and, Linear.Problem.Solves]

/-- Every initial point has a trajectory for the original RHS circuit, from
Asgard's global homogeneous linear existence theorem. -/
theorem exists_realization {n : Nat} (problem : Linear.Problem n)
    (rhs : Gimle.Asgard.Circuit n n) (translated : ∀ x, rhs.run x = problem.matrix.eval x) :
    ∃ state, Realizes rhs problem.time problem.initial state := by
  obtain ⟨state, h⟩ := problem.exists_realization
  exact ⟨state, (realizes_iff_problem problem rhs translated state).mpr h⟩

/-- Uniqueness transfers to the original circuit on the same forward domain. -/
theorem unique_realization {n : Nat} (problem : Linear.Problem n)
    (rhs : Gimle.Asgard.Circuit n n) (translated : ∀ x, rhs.run x = problem.matrix.eval x)
    (x y : Signal n) (hx : Realizes rhs problem.time problem.initial x)
    (hy : Realizes rhs problem.time problem.initial y) : Set.EqOn x y problem.time.domain :=
  problem.unique_realization ((realizes_iff_problem problem rhs translated x).mp hx)
    ((realizes_iff_problem problem rhs translated y).mp hy)

/-- Generic native-rule contract. Both typed circuit translations and both exact
matrix certificates are explicit premises; the conclusion is about the supplied
energy circuit on every actual feedback realization, rather than a detached formula. -/
theorem circuit_energy_bound {n : Nat} (problem : Linear.Problem n)
    (rhs : Gimle.Asgard.Circuit n n) (energy : Gimle.Asgard.Circuit n 1)
    (p : QMatrix n) (certificate : Certificate n)
    (rhs_translated : ∀ x, rhs.run x = problem.matrix.eval x)
    (energy_translated : ∀ x, energy.run x 0 = quadratic p x)
    (valid : certificate.Valid problem.matrix p)
    (state : Signal n) (realized : Realizes rhs problem.time problem.initial state)
    (bound : ℝ) (initial : energy.run problem.initial 0 ≤ bound)
    (t : ℝ) (forward : t ∈ problem.time.domain) :
    0 ≤ energy.run (state t) 0 ∧ energy.run (state t) 0 ≤ bound := by
  have source := (problem.solves_iff_realizes state).mpr
    ((realizes_iff_problem problem rhs rhs_translated state).mp realized)
  rw [energy_translated] at initial ⊢
  exact certificate_energy_bound problem p certificate valid state source bound initial t forward

/-- The native judgment includes global existence, forward-domain uniqueness,
and sublevel safety for the two original typed circuits. -/
def SublevelSafety {n : Nat} (rhs : Gimle.Asgard.Circuit n n)
    (energy : Gimle.Asgard.Circuit n 1) (time : TimeDomain) (bound : ℝ) : Prop :=
  (∀ initial, ∃ state, Realizes rhs time initial state) ∧
  (∀ initial x y, Realizes rhs time initial x → Realizes rhs time initial y →
    Set.EqOn x y time.domain) ∧
  ∀ initial state, energy.run initial 0 ≤ bound → Realizes rhs time initial state →
    ∀ t ∈ time.domain, 0 ≤ energy.run (state t) 0 ∧ energy.run (state t) 0 ≤ bound

/-- The complete native-rule contract: existence and uniqueness for every initial
point, and energy safety for every realization beginning in the sublevel. -/
theorem certificate_sound {n : Nat} (template : Linear.Problem n)
    (rhs : Gimle.Asgard.Circuit n n) (energy : Gimle.Asgard.Circuit n 1)
    (p : QMatrix n) (certificate : Certificate n)
    (rhs_translated : ∀ x, rhs.run x = template.matrix.eval x)
    (energy_translated : ∀ x, energy.run x 0 = quadratic p x)
    (valid : certificate.Valid template.matrix p) (bound : ℝ) :
    SublevelSafety rhs energy template.time bound := by
  refine ⟨?_, ?_, ?_⟩
  · intro initial
    exact exists_realization { template with initial := initial } rhs rhs_translated
  · intro initial x y hx hy
    exact unique_realization { template with initial := initial } rhs rhs_translated x y hx hy
  · intro initial state initial_bound realized t forward
    exact circuit_energy_bound { template with initial := initial } rhs energy p certificate
      rhs_translated energy_translated valid state realized bound initial_bound t forward

/-- A nonnegative homogeneous energy sublevel contains the origin. This is
separate from both the certificate rule and global trajectory existence. -/
theorem sublevel_nonempty {n : Nat} (energy : Gimle.Asgard.Circuit n 1)
    (p : QMatrix n) (translated : ∀ x, energy.run x 0 = quadratic p x)
    (bound : ℝ) (nonnegative : 0 ≤ bound) : ∃ initial, energy.run initial 0 ≤ bound := by
  refine ⟨fun _ => 0, ?_⟩
  rw [translated]
  simpa [quadratic, realMatrix, Matrix.mulVec, dotProduct] using nonnegative

#print axioms derivative_identity
#print axioms quadratic_derivative
#print axioms WeightedSquares.nonnegative
#print axioms circuit_energy_bound
#print axioms certificate_sound
#print axioms sublevel_nonempty
#print axioms exists_realization
#print axioms unique_realization
end Gimle.Forseti.LinearEnergy
