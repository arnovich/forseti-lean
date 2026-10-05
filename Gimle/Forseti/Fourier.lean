import Gimle.Asgard.Streams.VorticityCircuit

/-! Hoare contracts for Asgard's Fourier-stream interpretation.
Every admitted boundary has an output, all outputs agree, and every output
satisfies the postcondition. In particular a nonexistent feedback solution
cannot make a system contract vacuously true. Predicates concern whole formal
streams; analytic properties need explicit convergence and realization proofs.
-/
namespace Gimle.Forseti.Fourier

open Gimle.Asgard.Streams

/-- Predicates on banks of Fourier time streams. -/
abbrev Predicate (n : Nat) := Fourier.Point n → Prop

/-- A total, deterministic Hoare contract for a relational Fourier circuit. -/
structure Contract {basis : Basis} {n m : Nat} (circuit : Fourier.Circuit basis n m)
    (pre : Predicate n) (post : Predicate m) : Prop where
  realizable : ∀ x, pre x → ∃ y, circuit.Rel x y
  unique : ∀ x, pre x → ∀ y z, circuit.Rel x y → circuit.Rel x z → y = z
  holds : ∀ x, pre x → ∀ y, circuit.Rel x y → post y

variable {basis : Basis} {n m k : Nat}

/-- Extract an actual safe output, rather than conditional safety alone. -/
theorem Contract.exists_safe {c : Fourier.Circuit basis n m} {pre : Predicate n}
    {post : Predicate m} (h : Contract c pre post) (x : Fourier.Point n) (hx : pre x) :
    ∃ y, c.Rel x y ∧ post y := by
  obtain ⟨y, hy⟩ := h.realizable x hx
  exact ⟨y, hy, h.holds x hx y hy⟩

/-- Strengthen admission and weaken the guaranteed property. -/
theorem Contract.consequence {c : Fourier.Circuit basis n m}
    {pre strong : Predicate n} {post weak : Predicate m} (h : Contract c pre post)
    (hp : ∀ x, strong x → pre x) (hq : ∀ y, post y → weak y) :
    Contract c strong weak where
  realizable x hx := h.realizable x (hp x hx)
  unique x hx := h.unique x (hp x hx)
  holds x hx y hy := hq y (h.holds x (hp x hx) y hy)

/-- Sequentially compose contracts through their shared predicate. -/
theorem Contract.compose {c : Fourier.Circuit basis n m} {d : Fourier.Circuit basis m k}
    {pre : Predicate n} {middle : Predicate m} {post : Predicate k}
    (hc : Contract c pre middle) (hd : Contract d middle post) :
    Contract (.compose c d) pre post where
  realizable x hx := by
    obtain ⟨y, hy, safe⟩ := hc.exists_safe x hx
    obtain ⟨z, hz⟩ := hd.realizable y safe
    exact ⟨z, y, hy, hz⟩
  unique x hx y z hy hz := by
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    have eq := hc.unique x hx a b ha hb
    subst b
    exact hd.unique a (hc.holds x hx a ha) y z hay hbz
  holds x hx y hy := by
    obtain ⟨a, ha, hay⟩ := hy
    exact hd.holds a (hc.holds x hx a ha) y hay

/-- Every feedforward expression has a total contract for any established output property. -/
theorem expression_contract (e : Fourier.Expr n) (pre : Predicate n) (post : Predicate 1)
    (h : ∀ x, pre x → post ![e.value basis x]) : Contract (e.compile basis) pre post where
  realizable x _ := ⟨_, (e.compile_rel basis x _).mpr rfl⟩
  unique x _ y z hy hz := ((e.compile_rel basis x y).mp hy).trans
    ((e.compile_rel basis x z).mp hz).symm
  holds x hx y hy := by
    rw [(e.compile_rel basis x y).mp hy]
    exact h x hx

/-- Initial vorticity alone determines the whole output of the actual feedback circuit.
Higher coefficients of the boundary input remain unconstrained. -/
theorem solution_contract (basis : Basis) (ν : ℚ) (boundary : TrigStream) :
    Contract (NS.vorticityCircuit basis ν) (fun x => x 0 0 = boundary 0)
      (fun y => y = ![NS.stream basis ν boundary]) := by
  have behavior (x : Fourier.Point 1) (hx : x 0 0 = boundary 0) (y : Fourier.Point 1) :
      (NS.vorticityCircuit basis ν).Rel x y ↔ y = ![NS.stream basis ν boundary] := by
    have eta : x = ![x 0] := by funext i; fin_cases i; rfl
    rw [eta, NS.vorticityCircuit_rel_iff]
    rw [NS.stream_congr_slice basis ν (x 0) boundary hx]
  exact {
    realizable := fun x hx => ⟨_, (behavior x hx _).mpr rfl⟩
    unique := fun x hx y z hy hz => ((behavior x hx y).mp hy).trans ((behavior x hx z).mp hz).symm
    holds := fun x hx y hy => (behavior x hx y).mp hy
  }

end Gimle.Forseti.Fourier
