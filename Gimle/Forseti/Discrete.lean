import Gimle.Asgard.Semantics.Real

/-! Explicit synchronous unit-delay iteration of total feedforward circuits.
This does not interpret Asgard's continuous trace or raw register syntax. -/

namespace Gimle.Forseti.Discrete
open Gimle.Asgard

/-- Parameters are fixed; state and input use the exact declared port order. -/
def step {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (state : Point s) (input : Point u) : Point s :=
  update.run (pointAppend state (pointAppend input parameter))

/-- The entire next state is computed from the previous state at one clock tick. -/
def run {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (initial : Point s) (input : Nat → Point u) : Nat → Point s
  | 0 => initial
  | k + 1 => step update parameter (run update parameter initial input k) (input k)

/-- The recurrence relation includes explicit initialized registers. -/
def Realizes {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (initial : Point s) (input : Nat → Point u)
    (state : Nat → Point s) : Prop :=
  state 0 = initial ∧ ∀ k, state (k + 1) = step update parameter (state k) (input k)

/-- Every input sequence has an actual infinite recurrence, without deadlock. -/
theorem run_realizes {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (initial : Point s) (input : Nat → Point u) :
    Realizes update parameter initial input (run update parameter initial input) := by
  exact ⟨rfl, fun _ => rfl⟩

/-- Uniqueness is relative to one fixed parameter, initial state and input trace. -/
theorem realizes_unique {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (initial : Point s) (input : Nat → Point u)
    (left right : Nat → Point s)
    (hl : Realizes update parameter initial input left)
    (hr : Realizes update parameter initial input right) : left = right := by
  funext k
  induction k with
  | zero => exact hl.1.trans hr.1.symm
  | succ k ih => rw [hl.2 k, hr.2 k, ih]

/-- A finite realization constrains exactly states 0..N and inputs 0..N-1. -/
def RealizesThrough {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (initial : Point s) (input : Nat → Point u)
    (N : Nat) (state : Nat → Point s) : Prop :=
  state 0 = initial ∧ ∀ k < N, state (k + 1) = step update parameter (state k) (input k)

/-- Finite run uniqueness is equality only on the declared prefix. -/
theorem prefix_unique {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (parameter : Point p) (initial : Point s) (input : Nat → Point u)
    (N : Nat) (left right : Nat → Point s)
    (hl : RealizesThrough update parameter initial input N left)
    (hr : RealizesThrough update parameter initial input N right) :
    ∀ k ≤ N, left k = right k := by
  intro k hk
  induction k with
  | zero => exact hl.1.trans hr.1.symm
  | succ k ih => rw [hl.2 k (by omega), hr.2 k (by omega), ih (by omega)]

/-- Checked initial, preservation and safety inclusions imply finite every-step safety. -/
theorem induction_through {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (I K S : Point s → Prop) (U : Point u → Prop) (P : Point p → Prop)
    (initial_inclusion : ∀ x, I x → K x)
    (preserve : ∀ x input parameter, K x → U input → P parameter →
      K (step update parameter x input))
    (safe : ∀ x, K x → S x)
    (parameter : Point p) (hp : P parameter) (initial : Point s) (hi : I initial)
    (input : Nat → Point u) (N : Nat) (hu : ∀ k < N, U (input k))
    (state : Nat → Point s) (realized : RealizesThrough update parameter initial input N state) :
    ∀ k ≤ N, S (state k) := by
  have invariant : ∀ k ≤ N, K (state k) := by
    intro k hk
    induction k with
    | zero => rw [realized.1]; exact initial_inclusion initial hi
    | succ k ih =>
      rw [realized.2 k (by omega)]
      exact preserve (state k) (input k) parameter (ih (by omega)) (hu k (by omega)) hp
  exact fun k hk => safe (state k) (invariant k hk)

/-- Full native contract: continuing admissible inputs, existence and uniqueness
for every fixed input sequence, and safety for every realization at every step. -/
def AllStepSafety {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (I S : Point s → Prop) (U : Point u → Prop) (P : Point p → Prop) : Prop :=
  (∃ input : Nat → Point u, ∀ k, U (input k)) ∧
  (∀ parameter initial input, P parameter → I initial → (∀ k, U (input k)) →
    ∃ state, Realizes update parameter initial input state) ∧
  (∀ parameter initial input left right,
    Realizes update parameter initial input left →
    Realizes update parameter initial input right → left = right) ∧
  (∀ parameter initial input state, P parameter → I initial → (∀ k, U (input k)) →
    Realizes update parameter initial input state → ∀ k, S (state k))

/-- The versioned induction rule is justified by this theorem over Circuit.run. -/
theorem certificate_sound {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (I K S : Point s → Prop) (U : Point u → Prop) (P : Point p → Prop)
    (inputWitness : ∃ value, U value)
    (initial_inclusion : ∀ x, I x → K x)
    (preserve : ∀ x input parameter, K x → U input → P parameter →
      K (step update parameter x input))
    (safe : ∀ x, K x → S x) : AllStepSafety update I S U P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨value, hv⟩ := inputWitness
    exact ⟨fun _ => value, fun _ => hv⟩
  · intro parameter initial input _ _ _
    exact ⟨run update parameter initial input, run_realizes update parameter initial input⟩
  · intro parameter initial input left right hl hr
    exact realizes_unique update parameter initial input left right hl hr
  · intro parameter initial input state hp hi hu realized k
    exact induction_through update I K S U P initial_inclusion preserve safe parameter hp initial hi
      input k (fun j _ => hu j) state ⟨realized.1, fun j _ => realized.2 j⟩ k (by omega)

/-- Finite endpoint safety is a separate consequence, including N=0. -/
theorem endpoint_sound {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (I K S : Point s → Prop) (U : Point u → Prop) (P : Point p → Prop)
    (initial_inclusion : ∀ x, I x → K x)
    (preserve : ∀ x input parameter, K x → U input → P parameter →
      K (step update parameter x input))
    (safe : ∀ x, K x → S x)
    (parameter : Point p) (hp : P parameter) (initial : Point s) (hi : I initial)
    (input : Nat → Point u) (N : Nat) (hu : ∀ k < N, U (input k))
    (state : Nat → Point s) (realized : RealizesThrough update parameter initial input N state) :
    S (state N) :=
  induction_through update I K S U P initial_inclusion preserve safe parameter hp initial hi input N
    hu state realized N (Nat.le_refl N)

/-- Observation of a finite prefix distinguishes endpoint from every-step safety. -/
inductive Observation where
  | everyStep
  | endpoint

def Observed (mode : Observation) {s : Nat} (S : Point s → Prop)
    (N : Nat) (state : Nat → Point s) : Prop :=
  match mode with
  | .everyStep => ∀ k ≤ N, S (state k)
  | .endpoint => S (state N)

/-- Finite contracts include admissible inputs, existence and prefix uniqueness. -/
def FiniteSafety {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (I S : Point s → Prop) (U : Point u → Prop) (P : Point p → Prop)
    (N : Nat) (mode : Observation) : Prop :=
  (∃ input : Nat → Point u, ∀ k < N, U (input k)) ∧
  (∀ parameter initial input, P parameter → I initial → (∀ k < N, U (input k)) →
    ∃ state, RealizesThrough update parameter initial input N state) ∧
  (∀ parameter initial input left right,
    RealizesThrough update parameter initial input N left →
    RealizesThrough update parameter initial input N right → ∀ k ≤ N, left k = right k) ∧
  (∀ parameter initial input state, P parameter → I initial → (∀ k < N, U (input k)) →
    RealizesThrough update parameter initial input N state → Observed mode S N state)

/-- One induction certificate supports either finite observation, including N=0. -/
theorem finite_certificate_sound {s u p : Nat} (update : Circuit (s + (u + p)) s)
    (I K S : Point s → Prop) (U : Point u → Prop) (P : Point p → Prop)
    (inputWitness : ∃ value, U value)
    (initial_inclusion : ∀ x, I x → K x)
    (preserve : ∀ x input parameter, K x → U input → P parameter →
      K (step update parameter x input))
    (safe : ∀ x, K x → S x) (N : Nat) (mode : Observation) :
    FiniteSafety update I S U P N mode := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨value, hv⟩ := inputWitness
    exact ⟨fun _ => value, fun _ _ => hv⟩
  · intro parameter initial input _ _ _
    exact ⟨run update parameter initial input, rfl, fun _ _ => rfl⟩
  · intro parameter initial input left right hl hr
    exact prefix_unique update parameter initial input N left right hl hr
  · intro parameter initial input state hp hi hu realized
    have h := induction_through update I K S U P initial_inclusion preserve safe parameter hp
      initial hi input N hu state realized
    cases mode with
    | everyStep => exact h
    | endpoint => exact h N (Nat.le_refl N)

/-- The native nonempty box restriction has a constructive rational witness. -/
structure Box (n : Nat) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ
  ordered : ∀ i, lower i ≤ upper i

def Box.Contains {n : Nat} (box : Box n) (x : Point n) : Prop :=
  ∀ i, (box.lower i : ℝ) ≤ x i ∧ x i ≤ (box.upper i : ℝ)

theorem Box.nonempty {n : Nat} (box : Box n) : ∃ x, box.Contains x := by
  refine ⟨fun i => (box.lower i : ℝ), fun i => ⟨le_refl _, ?_⟩⟩
  change (box.lower i : ℝ) ≤ (box.upper i : ℝ)
  exact_mod_cast box.ordered i

#print axioms certificate_sound
#print axioms finite_certificate_sound
#print axioms endpoint_sound
#print axioms prefix_unique

end Gimle.Forseti.Discrete
