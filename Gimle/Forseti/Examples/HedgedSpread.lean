module

public import Gimle.Asgard.Model.DrivenSource
public import Gimle.Asgard.Model.SourceSyntax

/-! A hedged, mean-reverting exposure under a bounded disturbance, compiled from
its source equations, with two observations.

The equations are `s' = -s - h + d` and `h' = s - h` from `s(0) = h(0) = 0`:
`s` is the exposure to a spread, the difference between two prices, which
decays at unit rate, is pushed by the disturbance `d` and pulled back by the
hedge `h`, which relaxes toward `s` at unit rate (`h' = s - h`); `d` is a
declared driver. The driver has no derivative port, so every disturbance
continuous on `t ≥ 0` is admitted (`Evolution.Admitted`) and nothing else about
`d` is asked. The observations are `obs-s`, the exposure itself, and `obs-v`,
the quadratic `V = s² + h²` the contract's invariant is about. Nothing
downstream restates the equations unverified: `s_at` and `v_at` read the
outputs off the compiled observation circuit at their own indices, and the
contract module ties its analytic operator to the compiled rates.

The runtime coordinates are `[d, s, h]`: the driver port, then the states in
declaration order. -/

@[expose] public section

namespace Gimle.Forseti.Examples.HedgedSpread
open Gimle.Asgard Gimle.Asgard.Model Polynomial

/-- The exposure, the hedge, and the disturbance, with the observations `obs-s`
of `s` and `obs-v` of `V = s² + h²`. -/
def body : SourceBody := {
  inputs := [⟨"state-s", "s", .state⟩, ⟨"state-h", "h", .state⟩,
    ⟨"driver-d", "d", .driver⟩]
  assignments := assignments% { V := s ^ 2 + h ^ 2; }
  differentials := differentials% { ds : diff(s, t) = -s - h + d; dh : diff(h, t) = s - h; }
  observations := [⟨⟨"obs-s", "s", .output⟩, "state-s"⟩, ⟨⟨"obs-v", "V", .output⟩, "V"⟩]
}

/-- Two states `[s, h]`, starting at `t = 0` from `s(0) = h(0) = 0`. -/
abbrev evolution : Evolution := {
  states := [⟨"state-s", "ds", "initial-s"⟩, ⟨"state-h", "dh", "initial-h"⟩]
  initialPorts := [⟨"initial-s", "s0", .initial⟩, ⟨"initial-h", "h0", .initial⟩]
  initialValues := [⟨"initial-s", 0⟩, ⟨"initial-h", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- `d` is a driver without a derivative port: continuity is all that is asked. -/
abbrev drivers : List DriverBinding := [⟨"driver-d", none⟩]

/-- The source compiled by asgard-lean's verified source compiler. -/
def model : SourceDrivenModel body evolution drivers :=
  (compileSourceDriven body evolution drivers).toOption.get (by decide +kernel)

/-- The compiled driven model: its field, feedback and observations. An
`abbrev` so downstream proofs need no unfolding step. -/
abbrev compiled : DrivenModel model.lowered.body evolution drivers := model.model

/-- The compiled field over `[d, s, h]`: `ds := (-s + -h) + d` and `dh := s + -h`. -/
theorem rates_expressions : compiled.rates.expressions =
    (![.add (.add (.neg (.var 1)) (.neg (.var 2))) (.var 0),
      .add (.var 1) (.neg (.var 2))] : Fin 2 → Expr 3) := by
  decide +kernel

/-- The declared initial state is `s(0) = h(0) = 0`. -/
theorem initial_eq : compiled.initial = (![0, 0] : Point 2) := by
  -- Over `Fin 2` rather than `Fin evolution.states.length`, so `fin_cases` yields
  -- the literal indices the vector lemmas rewrite.
  change (fun i : Fin 2 => (compiled.initials i : ℝ)) = _
  have values : compiled.initials = ![0, 0] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

/-- Where `obs-s` sits among the observations. -/
def sIndex : Fin body.observations.length := ⟨0, by decide⟩

/-- Where `obs-v` sits among the observations. -/
def vIndex : Fin body.observations.length := ⟨1, by decide⟩

/-- The observation circuit, as compiled: `obs-s` is the state coordinate `s`. -/
theorem outputs_s : compiled.outputs.expressions sIndex = (.var 1 : Expr 3) := by
  decide +kernel

/-- `obs-v` is `1·s·s + 1·h·h`, as the compiler writes the squares. -/
theorem outputs_v : compiled.outputs.expressions vIndex =
    (.add (.mul (.mul (.constant 1) (.var 1)) (.var 1))
      (.mul (.mul (.constant 1) (.var 2)) (.var 2)) : Expr 3) := by
  decide +kernel

/-- `obs-s` reads the state `s` of `[d, s, h]`. -/
theorem s_at (point : Point 3) : compiled.outputs.circuit.run point sIndex = point 1 := by
  simp only [Selected.circuit, compileOutputs_correct, outputs_s]
  rfl

/-- `obs-v` reads `s² + h²` of `[d, s, h]`. -/
theorem v_at (point : Point 3) :
    compiled.outputs.circuit.run point vIndex = point 1 ^ 2 + point 2 ^ 2 := by
  simp only [Selected.circuit, compileOutputs_correct, outputs_v]
  show @Expr.eval 3 point _ = _
  simp only [Expr.eval, Rat.cast_one, one_mul]
  ring

/-- The time domain is `t ≥ 0`. -/
theorem domain_eq : evolution.time.domain = Set.Ici 0 := by
  simp [Evolution.time, Dynamics.TimeDomain.domain]

/-- Membership in the domain is `0 ≤ t`. -/
theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t := by
  rw [domain_eq, Set.mem_Ici]

/-- The declared start, reducibly `0`. -/
theorem origin : evolution.time.start = 0 := by simp [Evolution.time]

/-! ### Coordinates -/

/-- The number of driver coordinates, `[d]`. -/
abbrev width : Nat := DriverBinding.width drivers

/-- The state dimension, as the model declares it. -/
abbrev states : Nat := evolution.states.length

/-- The driver `d`. -/
def dIndex : Fin width := ⟨0, by decide⟩

/-- The driver `d` is the first and only driver coordinate. -/
theorem index_d : index (DriverBinding.ids drivers) "driver-d" = some dIndex := by
  decide +kernel

/-! ### Reading the runtime point `[d, s, h]`

The three coordinate lemmas evaluate asgard's `pointAppend` once, by
reduction; everything downstream rewrites with them instead of unfolding it. -/

theorem append_d (d : Point width) (x : Point states) :
    pointAppend d x (0 : Fin 3) = d dIndex := rfl

theorem append_s (d : Point width) (x : Point states) :
    pointAppend d x (1 : Fin 3) = x (0 : Fin 2) := rfl

theorem append_h (d : Point width) (x : Point states) :
    pointAppend d x (2 : Fin 3) = x (1 : Fin 2) := rfl

/-- The compiled rate of `s` at `[d, s, h]`. -/
theorem rates_s (d : Point width) (x : Point states) :
    (compiled.rates.expressions (0 : Fin 2)).eval (pointAppend d x) =
      -x (0 : Fin 2) + -x (1 : Fin 2) + d dIndex := by
  rw [rates_expressions]
  rfl

/-- The compiled rate of `h` at `[d, s, h]`. -/
theorem rates_h (d : Point width) (x : Point states) :
    (compiled.rates.expressions (1 : Fin 2)).eval (pointAppend d x) =
      x (0 : Fin 2) + -x (1 : Fin 2) := by
  rw [rates_expressions]
  rfl

/-- At the declared initial state the exposure is `0`, whatever the driver. -/
theorem s_at_initial (d : Point width) :
    compiled.outputs.circuit.run (pointAppend d compiled.initial) sIndex = 0 := by
  rw [s_at, append_s, initial_eq]
  simp

/-- At the declared initial state `V = 0`, whatever the driver. -/
theorem v_at_initial (d : Point width) :
    compiled.outputs.circuit.run (pointAppend d compiled.initial) vIndex = 0 := by
  rw [v_at, append_s, append_h, initial_eq]
  simp

#print axioms rates_expressions
#print axioms initial_eq
#print axioms s_at
#print axioms v_at
#print axioms s_at_initial
#print axioms v_at_initial

end Gimle.Forseti.Examples.HedgedSpread
