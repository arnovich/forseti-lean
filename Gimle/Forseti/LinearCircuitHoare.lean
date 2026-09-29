import Gimle.Forseti.LinearCircuit
import Gimle.Forseti.Syntax
import Gimle.Asgard.Compile.Normalization

/-! Finite compiled observations as existing Forseti formulas and Hoare invariants.
The initialized observation endpoint consumes the existing discrete safety rule.
No checker admission or automated certificate search is claimed. -/

namespace Gimle.Forseti.LinearCircuit

open Gimle.Asgard
open Gimle.Forseti.Syntax

/-- Substitute the original simultaneous updates into a future readout. -/
def futureExpr {d : Nat} (P : Program d) : Nat → Polynomial.Expr d
  | 0 => P.readout
  | n + 1 => Normalization.substitute P.updates (futureExpr P n)

/-- Future-expression syntax denotes the original initialized compiled observation. -/
theorem futureExpr_eval {d : Nat} (P : Program d) (x : Point d) (n : Nat) :
    (futureExpr P n).eval x = P.observe x n := by
  induction n generalizing x with
  | zero => simp [futureExpr, Program.observe, Program.state, Program.output, Discrete.run]
  | succ n ih =>
    rw [futureExpr, Normalization.substitute_correct, ih]
    have hu : (fun i => (P.updates i).eval x) = P.update.run x := by
      simp [Program.update]
    rw [hu, Program.observe_shift]

/-- An equality atom on the original left and right future-readout expressions. -/
def equalityFormula {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (n : Nat) : Formula (d₁ + d₂) :=
  .atom .eq (.add
    (Syntax.rename (Fin.castAdd d₂) (futureExpr P n))
    (.neg (Syntax.rename (Fin.natAdd d₁) (futureExpr Q n))))

/-- The current-output equality is the zero-step atom. -/
def outputFormula {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    Formula (d₁ + d₂) := equalityFormula P Q 0

private def prefixThrough {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    Nat → Formula (d₁ + d₂)
  | 0 => .tru
  | n + 1 => .and (prefixThrough P Q n) (equalityFormula P Q n)

/-- A finite existing formula; the empty prefix is truth. -/
def prefixFormula {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    Formula (d₁ + d₂) := prefixThrough P Q (d₁ + d₂)

/-- Each equality atom denotes equality of original compiled observations. -/
theorem equalityFormula_holds_iff {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (z : Point (d₁ + d₂)) (n : Nat) :
    (equalityFormula P Q n).holds z ↔
      P.observe (pointLeft z) n = Q.observe (pointRight z) n := by
  simp only [equalityFormula, Formula.holds, Relation.holds, Polynomial.Expr.eval,
    Syntax.rename_eval, futureExpr_eval]
  change P.observe (pointLeft z) n + -(Q.observe (pointRight z) n) = 0 ↔ _
  rw [← sub_eq_add_neg, sub_eq_zero]

/-- The safety postcondition is equality at the current state. -/
theorem outputFormula_holds_iff {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (z : Point (d₁ + d₂)) :
    (outputFormula P Q).holds z ↔
      P.observe (pointLeft z) 0 = Q.observe (pointRight z) 0 :=
  equalityFormula_holds_iff P Q z 0

private theorem prefixThrough_holds_iff {d₁ d₂ : Nat} (P : Program d₁)
    (Q : Program d₂) (z : Point (d₁ + d₂)) (m : Nat) :
    (prefixThrough P Q m).holds z ↔
      ∀ n < m, P.observe (pointLeft z) n = Q.observe (pointRight z) n := by
  induction m with
  | zero => simp [prefixThrough]
  | succ m ih =>
    simp only [prefixThrough, Formula.holds, ih, equalityFormula_holds_iff]
    constructor
    · rintro ⟨hp, hm⟩ n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · exact hp n hn
      · exact hm
    · intro h
      exact ⟨fun n hn => h n (Nat.lt_succ_of_lt hn), h m (Nat.lt_succ_self m)⟩

/-- The actual formula denotes exactly the finite compiled-output criterion. -/
theorem prefixFormula_holds_iff {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (z : Point (d₁ + d₂)) :
    (prefixFormula P Q).holds z ↔
      ∀ n < d₁ + d₂, P.observe (pointLeft z) n = Q.observe (pointRight z) n :=
  prefixThrough_holds_iff P Q z (d₁ + d₂)

/-- Finite-prefix equality is preserved by the original paired compiled update. -/
theorem prefix_hoare {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    ExactHoare (prefixFormula P Q).toPredicate (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q)
      (prefixFormula P Q).toPredicate := by
  intro z hz
  have hall := (compiled_prefix_iff_all_real P Q (pointLeft z) (pointRight z)).mp
    ((prefixFormula_holds_iff P Q z).mp hz)
  apply (prefixFormula_holds_iff P Q _).mpr
  intro n _
  simpa only [pairedUpdate, Circuit.run, pointLeft_pointAppend,
    pointRight_pointAppend, Program.observe_shift] using hall (n + 1)

/-- The invariant entails current output equality, also for an empty prefix. -/
theorem prefix_entails_output {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    PredicateEntailment (prefixFormula P Q).toPredicate (outputFormula P Q).toPredicate := by
  intro z hz
  apply (outputFormula_holds_iff P Q z).mpr
  exact (compiled_prefix_iff_all_real P Q (pointLeft z) (pointRight z)).mp
    ((prefixFormula_holds_iff P Q z).mp hz) 0

/-- Existing discrete safety, discharged by the actual Hoare invariant and entailment. -/
theorem prefix_safety {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂) :
    Discrete.AllStepSafety (s := d₁ + d₂) (u := 0) (p := 0) (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q)
      (prefixFormula P Q).holds (outputFormula P Q).holds
      (fun _ => True) (fun _ => True) := by
  apply Discrete.certificate_sound (s := d₁ + d₂) (u := 0) (p := 0) (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q)
    (prefixFormula P Q).holds (prefixFormula P Q).holds
    (outputFormula P Q).holds (fun _ => True) (fun _ => True)
  · exact ⟨empty, trivial⟩
  · exact fun _ h => h
  · intro x input parameter hx _ _
    rw [autonomous_step]
    exact prefix_hoare P Q x hx
  · exact prefix_entails_output P Q

/-- Initialized component equality obtained through the existing safety certificate. -/
theorem observations_eq_of_prefixFormula {d₁ d₂ : Nat} (P : Program d₁)
    (Q : Program d₂) (x : Point d₁) (y : Point d₂)
    (h : (prefixFormula P Q).holds (pointAppend x y)) :
    ∀ n, P.observe x n = Q.observe y n := by
  intro n
  have hs := (prefix_safety P Q).2.2.2 empty (pointAppend x y) (fun _ => empty)
    (Discrete.run (s := d₁ + d₂) (u := 0) (p := 0) (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q)
      empty (pointAppend x y) (fun _ => empty))
    trivial h (fun _ => trivial)
    (Discrete.run_realizes (s := d₁ + d₂) (u := 0) (p := 0)
      (pairedUpdate (d₁ := d₁) (d₂ := d₂) P Q) empty (pointAppend x y) (fun _ => empty)) n
  rw [paired_state] at hs
  have he := (outputFormula_holds_iff P Q _).mp hs
  simpa [Program.observe, Program.state_zero] using he

/-- The initialized finite criterion, with its forward direction using Hoare safety. -/
theorem compiled_prefix_iff_all {d₁ d₂ : Nat} (P : Program d₁) (Q : Program d₂)
    (x : Point d₁) (y : Point d₂) :
    (∀ n < d₁ + d₂, P.observe x n = Q.observe y n) ↔
      ∀ n, P.observe x n = Q.observe y n := by
  constructor
  · intro h
    apply observations_eq_of_prefixFormula P Q x y
    exact (prefixFormula_holds_iff P Q _).mpr (by simpa using h)
  · exact fun h n _ => h n

#print axioms futureExpr_eval
#print axioms prefixFormula_holds_iff
#print axioms prefix_hoare
#print axioms prefix_entails_output
#print axioms prefix_safety
#print axioms observations_eq_of_prefixFormula
#print axioms compiled_prefix_iff_all

end Gimle.Forseti.LinearCircuit
