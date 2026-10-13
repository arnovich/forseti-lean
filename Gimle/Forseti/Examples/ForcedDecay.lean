import Gimle.Asgard.Model.DrivenSource
import Gimle.Asgard.Model.SourceSyntax
import Gimle.Asgard.Examples.DrivenForcing

/-! A driven model compiled from its source equations, with an observation.

The source is asgard-lean's `Examples/DrivenForcing.lean`:
`D_t(x) + x = D_t(u) + u` with `x(0) = 0`, where `u` is a declared driver whose
derivative port `du` must carry its actual derivative (`Evolution.Admitted`).
That body declares no observation, so this module declares its own copy of the
same equations with one observation, `obs-x`, and compiles it with
`compileSourceDriven`; `same_source` checks the copy against asgard's. Nothing downstream restates the equations or the circuit:
`x_at` reads `x` off the compiled observation circuit at its own index.

The runtime coordinates are `[u, du, x]`: the driver ports in binding order,
then the state. -/
namespace Gimle.Forseti.Examples.ForcedDecay
open Gimle.Asgard Gimle.Asgard.Model Polynomial

/-- The equations of `DrivenForcing`, plus the observation `obs-x` of `x`. -/
def body : SourceBody := {
  inputs := [⟨"state-x", "x", .state⟩, ⟨"driver-u", "u", .driver⟩,
    ⟨"driver-du", "du", .driver⟩]
  assignments := []
  differentials := differentials% { dx : diff(x, t) + x = diff(u, t) + u; }
  observations := [⟨⟨"obs-x", "x", .output⟩, "state-x"⟩]
}

/-- One state `x`, starting at `t = 0` from `x(0) = 0`. -/
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩]
  initialValues := [⟨"initial-x", 0⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

/-- `u` is a driver, differentiable with derivative port `du`. -/
def drivers : List DriverBinding := [⟨"driver-u", some "driver-du"⟩]

/-- The source compiled by asgard-lean's verified source compiler. -/
def model : SourceDrivenModel body evolution drivers :=
  (compileSourceDriven body evolution drivers).toOption.get (by decide +kernel)

/-- The compiled driven model: its field, feedback and observations. An
`abbrev` so downstream proofs need no unfolding step. -/
abbrev compiled : DrivenModel model.lowered.body evolution drivers := model.model

/-- The compiled field over `[u, du, x]`: `dx := (du + u) - x`. -/
theorem rates_expressions : compiled.rates.expressions =
    (![.add (.add (.var 1) (.var 0)) (.neg (.var 2))] : Fin 1 → Expr 3) := by
  decide +kernel

/-- The declared initial state is `x(0) = 0`. -/
theorem initial_eq : compiled.initial = (![0] : Point 1) := by
  have : compiled.initials = ![0] := by decide +kernel
  funext i
  fin_cases i
  simp [DrivenModel.initial, this]

/-- Where `obs-x` sits among the observations. -/
def xIndex : Fin body.observations.length := ⟨0, by decide⟩

/-- The observation circuit, as compiled: `x` is the state coordinate. -/
theorem outputs_expressions : compiled.outputs.expressions =
    (![.var 2] : Fin 1 → Expr 3) := by
  decide +kernel

/-- `obs-x` reads the state `x` of `[u, du, x]`. -/
theorem x_at (point : Point 3) : compiled.outputs.circuit.run point xIndex = point 2 := by
  simp [Selected.circuit, outputs_expressions, xIndex, Expr.eval]

/-- The declared start is `0` from the declared initial state, where `x = 0`. -/
theorem x_at_initial (d : Point (DriverBinding.width drivers)) :
    compiled.outputs.circuit.run (pointAppend d compiled.initial) xIndex = 0 := by
  rw [x_at, initial_eq]
  rfl

/-- The time domain is `t ≥ 0`. -/
theorem domain_eq : evolution.time.domain = Set.Ici 0 := by
  simp [Evolution.time, evolution, Dynamics.TimeDomain.domain]

theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t := by
  rw [domain_eq, Set.mem_Ici]

/-- The equations, evolution and drivers are asgard's `DrivenForcing` ones: only
the observation is added. -/
theorem same_source :
    body.inputs = Gimle.Asgard.Examples.DrivenForcing.body.inputs ∧
      body.assignments = Gimle.Asgard.Examples.DrivenForcing.body.assignments ∧
      body.differentials = Gimle.Asgard.Examples.DrivenForcing.body.differentials ∧
      evolution = Gimle.Asgard.Examples.DrivenForcing.evolution ∧
      drivers = Gimle.Asgard.Examples.DrivenForcing.drivers := by
  decide +kernel

/-! ### Coordinates -/

/-- The number of driver coordinates, `[u, du]`. -/
abbrev width : Nat := DriverBinding.width drivers

/-- The state dimension, as the model declares it. -/
abbrev states : Nat := evolution.states.length

/-- The driver `u`. -/
def uIndex : Fin width := ⟨0, by decide⟩

/-- Its derivative port `du`. -/
def duIndex : Fin width := ⟨1, by decide⟩

/-- The one state, `x`. -/
def xState : Fin states := ⟨0, by decide⟩

theorem index_u : index (DriverBinding.ids drivers) "driver-u" = some uIndex := by
  decide +kernel

theorem index_du : index (DriverBinding.ids drivers) "driver-du" = some duIndex := by
  decide +kernel

/-- The state dimension is one, so every state index is `xState`. -/
theorem state_index (i : Fin states) : i = xState := by
  have one : (states : ℕ) = 1 := rfl
  have := i.isLt
  exact Fin.ext (by show i.val = 0; omega)

#print axioms rates_expressions
#print axioms initial_eq
#print axioms x_at
#print axioms same_source

end Gimle.Forseti.Examples.ForcedDecay
