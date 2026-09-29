import Gimle.Forseti.Trajectory

/-! The observed circuit of a driven model.

An undriven model's observations read only its state, so its observed circuit is
the feedback followed by the observation circuit (`LinearEnergyContract.observed`).
A driven model's observations read `[drivers, state]`, the coordinates its
output circuit was compiled against, so the drivers must reach the observation
beside the feedback. `forwarded F obs` copies the input `[drivers, initial]`,
keeps the driver wires on one copy, runs the feedback `F` on the other, and
applies `obs` to the result.

`forwarded_rel` states what that circuit relates without unfolding `F`: an
output is `obs` of the input's drivers and of a state `F` relates to the same
input. Nothing here is specific to a model.
-/

namespace Gimle.Forseti.Driven

open Gimle.Forseti
open Gimle.Asgard
open Gimle.Asgard.Dynamics

/-! ### One layer of the relation at a time -/

/-- A composite relates through some intermediate signal. -/
theorem compose_rel {n k m : Nat} (a : Dynamics.Circuit n k) (b : Dynamics.Circuit k m)
    (time : TimeDomain) (x : Signal n) (y : Signal m) :
    (Dynamics.Circuit.compose a b).Rel time x y ↔ ∃ z, a.Rel time x z ∧ b.Rel time z y :=
  Iff.rfl

/-- A lifted static circuit relates exactly its pointwise run. -/
theorem lift_rel {n m : Nat} (c : Gimle.Asgard.Circuit n m) (time : TimeDomain)
    (x : Signal n) (y : Signal m) :
    (Dynamics.Circuit.lift c).Rel time x y ↔ y = fun t => c.run (x t) :=
  Iff.rfl

/-- A parallel composite relates each half separately. -/
theorem parallel_rel {n m k l : Nat} (a : Dynamics.Circuit n m) (b : Dynamics.Circuit k l)
    (time : TimeDomain) (x : Signal (n + k)) (y : Signal (m + l)) :
    (Dynamics.Circuit.parallel a b).Rel time x y ↔
      a.Rel time (signalLeft x) (signalLeft y) ∧ b.Rel time (signalRight x) (signalRight y) :=
  Iff.rfl

/-! ### Forwarding the drivers -/

/-- The driver wires of an input `[drivers, initial]`. -/
def keepLeft (w n : Nat) : Gimle.Asgard.Circuit (w + n) w :=
  Polynomial.route (fun i => Fin.castAdd n i)

theorem keepLeft_run {w n : Nat} (x : Point (w + n)) : (keepLeft w n).run x = pointLeft x := by
  funext i
  simp only [keepLeft, Polynomial.route_correct, pointLeft]
  rfl

/-- A driven feedback `F`, with the driver wires forwarded beside it to an
observation `obs` of `[drivers, state]`. -/
def forwarded {w n m : Nat} (F : Dynamics.Circuit (w + n) n)
    (obs : Gimle.Asgard.Circuit (w + n) m) : Dynamics.Circuit (w + n) m :=
  .compose (.lift (duplicate (w + n)))
    (.compose (.parallel (.lift (keepLeft w n)) F) (.lift obs))

/-- **An output of `forwarded` is the observation of the input's drivers and of
a state `F` relates to the same input.** -/
theorem forwarded_rel {w n m : Nat} (F : Dynamics.Circuit (w + n) n)
    (obs : Gimle.Asgard.Circuit (w + n) m) (time : TimeDomain) (input : Signal (w + n))
    (output : Signal m) :
    (forwarded F obs).Rel time input output ↔
      ∃ state, F.Rel time input state ∧
        output = fun t => obs.run (pointAppend (signalLeft input t) (state t)) := by
  have copy : (fun t => (duplicate (w + n)).run (input t)) = signalAppend input input := by
    funext t
    exact duplicate_run _
  have keep : (fun t => (keepLeft w n).run (signalLeft (signalAppend input input) t)) =
      signalLeft input := by
    funext t
    rw [signalLeft_append, keepLeft_run]
    rfl
  unfold forwarded
  rw [compose_rel]
  constructor
  · rintro ⟨copied, hcopy, hrest⟩
    rw [lift_rel, copy] at hcopy
    subst hcopy
    rw [compose_rel] at hrest
    obtain ⟨mid, hpar, hout⟩ := hrest
    rw [parallel_rel, lift_rel, keep, signalRight_append] at hpar
    rw [lift_rel] at hout
    refine ⟨signalRight mid, hpar.2, ?_⟩
    rw [hout]
    funext t
    have parts := congrFun (signalAppend_parts mid) t
    rw [hpar.1] at parts
    exact congrArg obs.run parts.symm
  · rintro ⟨state, hstate, rfl⟩
    refine ⟨signalAppend input input, by rw [lift_rel, copy], ?_⟩
    rw [compose_rel]
    refine ⟨signalAppend (signalLeft input) state, ?_, ?_⟩
    · rw [parallel_rel, lift_rel, keep, signalLeft_append, signalRight_append,
        signalRight_append]
      exact ⟨rfl, hstate⟩
    · rw [lift_rel]
      rfl

#print axioms forwarded_rel

end Gimle.Forseti.Driven
