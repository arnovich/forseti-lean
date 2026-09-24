import Gimle.Forseti.Discrete

namespace Gimle.Forseti.Tests.Discrete
open Gimle.Asgard Gimle.Forseti.Discrete

-- Each tick reads x and u, then writes the initialized register once.
def average : Circuit (1 + (1 + 0)) 1 := .compose .add (.scalar (1/2))
def unitInterval : Point 1 → Prop := fun x => -1 ≤ x 0 ∧ x 0 ≤ 1

theorem average_step (parameter : Point 0) (x u : Point 1) :
    step average parameter x u 0 = (x 0 + u 0) / 2 := by
  simp [step, average, pointAppend]
  ring

theorem average_preserves (x u : Point 1) (parameter : Point 0)
    (hx : unitInterval x) (hu : unitInterval u) (_ : True) :
    unitInterval (step average parameter x u) := by
  rw [unitInterval, average_step]
  dsimp [unitInterval] at hx hu
  constructor <;> linarith

theorem average_all_steps :
    AllStepSafety average unitInterval unitInterval unitInterval (fun _ => True) := by
  apply certificate_sound average unitInterval unitInterval unitInterval unitInterval (fun _ => True)
  · exact ⟨![0], by norm_num [unitInterval]⟩
  · exact fun _ h => h
  · exact average_preserves
  · exact fun _ h => h

-- The same premises prove either explicitly selected finite observation.
theorem average_finite (N : Nat) (mode : Observation) :
    FiniteSafety average unitInterval unitInterval unitInterval (fun _ => True) N mode := by
  apply finite_certificate_sound average unitInterval unitInterval unitInterval unitInterval
    (fun _ => True)
  · exact ⟨![0], by norm_num [unitInterval]⟩
  · exact fun _ h => h
  · exact average_preserves
  · exact fun _ h => h

-- Changing the input contract to admit 3 would invalidate the preservation premise.
example (parameter : Point 0) : ¬ unitInterval (step average parameter ![1] ![3]) := by
  norm_num [unitInterval, average_step]

-- Uniqueness never means that different input traces yield the same trajectory.
example : run average (fun i => Fin.elim0 i) ![0] (fun _ => ![1]) 1 0 = 1/2 := by
  norm_num [run, average_step]
example : run average (fun i => Fin.elim0 i) ![0] (fun _ => ![-1]) 1 0 = -1/2 := by
  norm_num [run, average_step]

-- A swap computes both next-state coordinates from the old state simultaneously.
def swapState : Circuit (2 + (0 + 0)) 2 := .swap
example (parameter : Point 0) (input : Nat → Point 0) :
    run swapState parameter ![2, 3] input 1 = ![3, 2] := by
  funext i
  fin_cases i <;> simp [run, step, swapState, pointAppend]

-- Parameters are read through the same final port at every tick.
def fixedParameter : Circuit (1 + (0 + 1)) 1 := .compose .add (.scalar (1/2))
example : run fixedParameter ![1] ![0] (fun _ i => Fin.elim0 i) 2 0 = 3/4 := by
  norm_num [run, step, fixedParameter, pointAppend]

-- The empty box is the unit input/parameter space, not a deadlocked contract.
def noInputs : Box 0 := ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
example : ∃ input, noInputs.Contains input := noInputs.nonempty

-- N=0 observes the initialized value without requiring any input sample.
example (parameter : Point 0) (x : Point 1) (hx : unitInterval x)
    (input : Nat → Point 1) (state : Nat → Point 1)
    (realized : RealizesThrough average parameter x input 0 state) : unitInterval (state 0) := by
  exact endpoint_sound average unitInterval unitInterval unitInterval unitInterval (fun _ => True)
    (fun _ h => h) average_preserves (fun _ h => h) parameter trivial x hx input 0
    (by intro k hk; omega) state realized

#print axioms average_all_steps
#print axioms average_finite

end Gimle.Forseti.Tests.Discrete
