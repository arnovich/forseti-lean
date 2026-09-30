import Gimle.Forseti.Nonlinear
import Gimle.Asgard.Model.Linear
import Gimle.Asgard.Compile.Syntax

/-! # The Lorenz system stays in a ball: a nonlinear trajectory contract

`x' = σ(y − x)`, `y' = x(ρ − z) − y`, `z' = xy − βz` with `σ = 10`, `ρ = 28`,
`β = 8/3`, from `(1, 1, 1)` at `t = 0`, observing `V = x² + y² + (z − σ − ρ)²`,
`σ + ρ = 38`.

Along every solution `V' = −2σx² − 2y² − 2βz² + 2β(σ+ρ)z`, so
`V' + 2V ≤ 2·1541` at every state (the least constant is `23104/15`), and
`V ≤ 1600` follows for every solution from `V(0) = 1371`. This is the first
trajectory contract here whose field has no linear view; existence for all
`t ≥ 0`, forward uniqueness and the contract come from `Nonlinear`'s general
trapping theorem, of which this is the first instance. -/

namespace Gimle.Forseti.Examples.Lorenz

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard Gimle.Asgard.Model Polynomial

/-- The Lorenz equations with the classical parameters and the observed
storage `V = x² + y² + (z − 38)²`, `38 = σ + ρ`. -/
def body : Body := {
  program := ⟨[⟨"state-x", "x", .state⟩, ⟨"state-y", "y", .state⟩,
      ⟨"state-z", "z", .state⟩, ⟨"param-s", "s", .parameter⟩,
      ⟨"param-r", "r", .parameter⟩, ⟨"param-b", "b", .parameter⟩],
    equations% {
      dx := s * (y - x);
      dy := x * (r - z) - y;
      dz := x * y - b * z;
      V := sqx + sqy + sqw;
      sqx := x ^ 2;
      sqy := y ^ 2;
      sqw := w ^ 2;
      w := z - 38;
    }⟩
  parameters := [⟨"param-s", 10⟩, ⟨"param-r", 28⟩, ⟨"param-b", 8 / 3⟩]
  observations := [⟨⟨"obs-x", "x", .output⟩, "state-x"⟩,
    ⟨⟨"obs-y", "y", .output⟩, "state-y"⟩,
    ⟨⟨"obs-z", "z", .output⟩, "state-z"⟩,
    ⟨⟨"obs-v", "V", .output⟩, "V"⟩]
}

/-- State order `[x, y, z]`, from `(1, 1, 1)` at `t = 0`. -/
def evolution : Evolution := {
  states := [⟨"state-x", "dx", "initial-x"⟩, ⟨"state-y", "dy", "initial-y"⟩,
    ⟨"state-z", "dz", "initial-z"⟩]
  initialPorts := [⟨"initial-x", "x0", .initial⟩, ⟨"initial-y", "y0", .initial⟩,
    ⟨"initial-z", "z0", .initial⟩]
  initialValues := [⟨"initial-x", 1⟩, ⟨"initial-y", 1⟩, ⟨"initial-z", 1⟩]
  axis := ⟨"time", "t"⟩
  evolveAlong := "time"
  start := 0
}

def compiled : ContinuousModel body evolution :=
  (compileContinuous body evolution).toOption.get (by decide +kernel)

/-- The compiled right-hand sides, in state order `[x, y, z]`, as the compiler
normalises them. Private: `rates_formula` is the statement to depend on. -/
private theorem rates_expressions : compiled.rates.expressions =
    (![.mul (.constant 10) (.add (.var 1) (.neg (.var 0))),
      .add (.mul (.var 0) (.add (.constant 28) (.neg (.var 2)))) (.neg (.var 1)),
      .add (.mul (.var 0) (.var 1)) (.neg (.mul (.constant (8 / 3)) (.var 2)))] :
      Fin 3 → Expr 3) := by decide +kernel

theorem initial_eq : compiled.initial = (![1, 1, 1] : Point 3) := by
  change (fun i : Fin 3 => (compiled.initials i : ℝ)) = _
  have values : compiled.initials = ![1, 1, 1] := by decide +kernel
  rw [values]
  ext i
  fin_cases i <;> norm_num

/-- The Lorenz field in closed form. -/
noncomputable def field (x : Point 3) : Point 3 :=
  ![10 * (x 1 - x 0), x 0 * (28 - x 2) - x 1, x 0 * x 1 - 8 / 3 * x 2]

theorem rates_formula (x : Point 3) : compiled.rates.circuit.run x = field x := by
  rw [Selected.circuit, compileOutputs_correct, rates_expressions]
  ext i
  change Fin 3 at i
  fin_cases i <;> norm_num [field, Expr.eval, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

theorem rates_eval (i : Fin evolution.states.length) (x : Point evolution.states.length) :
    (compiled.rates.expressions i).eval x = field x i := by
  have h := congrFun (rates_formula x) i
  rwa [Selected.circuit, compileOutputs_correct] at h

/-- `V` is the fourth observation. -/
def energyIndex : Fin body.observations.length := ⟨3, by decide⟩

/-- The storage `V = x² + y² + (z − 38)²`. -/
noncomputable def energy (x : Point 3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + (x 2 - 38) ^ 2

/-- The observation's normal form. Private: `energy_at` is the statement to depend on. -/
private theorem energy_expression : compiled.outputs.expressions energyIndex =
    (.add (.add (.mul (.mul (.constant 1) (.var 0)) (.var 0))
        (.mul (.mul (.constant 1) (.var 1)) (.var 1)))
      (.mul (.mul (.constant 1) (.add (.var 2) (.neg (.constant 38))))
        (.add (.var 2) (.neg (.constant 38)))) : Expr 3) := by
  decide +kernel

theorem energy_at (x : Point 3) :
    compiled.outputs.circuit.run x energyIndex = energy x := by
  rw [Selected.circuit, compileOutputs_correct]
  change (compiled.outputs.expressions energyIndex).eval x = _
  rw [energy_expression]
  simp [energy, Expr.eval, pow_two, sub_eq_add_neg]

theorem energy_at_initial :
    compiled.outputs.circuit.run compiled.initial energyIndex = 1371 := by
  rw [energy_at, initial_eq]
  norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## Realizations, as solutions of the closed-form field -/

theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t := by
  simp [Dynamics.TimeDomain.domain, Evolution.time, evolution]

theorem domain_eq : evolution.time.domain = Set.Ici 0 := by
  ext t
  rw [Set.mem_Ici]
  exact domain_iff t

/-- A realization is a forward solution of `field` from `(1, 1, 1)`. -/
theorem realizes_iff (state : Dynamics.Signal 3) :
    compiled.Realizes state ↔
      state 0 = (![1, 1, 1] : Point 3) ∧
      ∀ t ∈ evolution.time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        (field (state t) i) evolution.time.domain t := by
  rw [← compiled.solves_iff_realizes, compiled.solves_iff_field, initial_eq]
  have start : evolution.time.start = 0 := by simp [Evolution.time, evolution]
  rw [start]
  apply and_congr_right
  intro _
  constructor
  · intro h t ht i
    have := h t ht i
    rwa [rates_eval] at this
  · intro h t ht i
    have := h t ht i
    rwa [← rates_eval] at this

/-- The rate of `V`: the cubic terms cancel and only the damping and the
`z`-shift remain. -/
noncomputable def rate (x : Point 3) : ℝ :=
  -20 * x 0 ^ 2 - 2 * x 1 ^ 2 - 16 / 3 * x 2 ^ 2 + 608 / 3 * x 2

theorem energy_derivative (state : Dynamics.Signal 3) (realized : compiled.Realizes state)
    (t : ℝ) (within : t ∈ evolution.time.domain) :
    HasDerivWithinAt (fun t => energy (state t)) (rate (state t)) evolution.time.domain t := by
  have dx := ((realizes_iff state).mp realized).2 t within 0
  have dy := ((realizes_iff state).mp realized).2 t within 1
  have dz := ((realizes_iff state).mp realized).2 t within 2
  have h := ((dx.pow 2).add (dy.pow 2)).add ((dz.sub_const 38).pow 2)
  convert! h using 1
  simp only [field, rate, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The algebraic heart: `V' + 2V ≤ 2·1541` at every state. The least constant
for which this holds is `23104/15 ≈ 1540.27`; the margin to `1600` is what makes
the fencing argument below strict. -/
theorem storage_bound (x : Point 3) : rate x ≤ 2 * 1541 - 2 * energy x := by
  unfold rate energy
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2 - 38 / 5)]

/-! ## The trapping data

Everything below the inequality is `Nonlinear`: existence for all `t ≥ 0` by
the clamped, glued and fenced Picard–Lindelöf argument, uniqueness on the
compact box, the invariant, and the contracts. -/

/-- `V` as the weighted sum of squares the general theorem takes: weights `1`,
centre `(0, 0, 38)`, rate `2`, inner level `1541`, trapped level `1600`, and
the sup-norm radius `40` about the centre (`1600 ≤ 1 · 40²`). -/
noncomputable def trapping : Nonlinear.Trapping 3 where
  weights := fun _ => 1
  centre := ![0, 0, 38]
  alpha := 2
  inner := 1541
  bound := 1600
  radius := 40
  weights_pos := fun _ => one_pos
  alpha_pos := by norm_num
  margin := by norm_num
  radius_nonneg := by norm_num
  covers := fun _ => by norm_num

theorem energy_eq_trapping (x : Point 3) : energy x = trapping.energy x := by
  simp [energy, trapping, Nonlinear.Trapping.energy, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.tail_cons]

theorem field_eq : Nonlinear.field compiled = field := by
  funext x i
  exact rates_eval i x

theorem rate_eq_trapping (x : Point 3) :
    rate x = trapping.rate (Nonlinear.field compiled) x := by
  rw [field_eq]
  simp only [rate, trapping, Nonlinear.Trapping.rate, field, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- `storage_bound`, in the general theorem's shape. -/
theorem decrease (x : Point 3) :
    trapping.rate (Nonlinear.field compiled) x ≤
      trapping.alpha * (trapping.inner - trapping.energy x) := by
  rw [← rate_eq_trapping, ← energy_eq_trapping]
  have := storage_bound x
  show rate x ≤ 2 * (1541 - energy x)
  linarith

theorem initial_le : trapping.energy compiled.initial ≤ trapping.bound := by
  rw [← energy_eq_trapping, initial_eq]
  show energy ![1, 1, 1] ≤ 1600
  norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons]

/-- Every realization keeps `V ≤ 1600`. -/
theorem invariant (state : Dynamics.Signal 3) (realized : compiled.Realizes state) :
    Always evolution.time (fun x => energy x ≤ 1600) state := by
  intro t ht
  rw [energy_eq_trapping]
  exact Nonlinear.compiled_invariant compiled trapping decrease initial_le state realized t ht

theorem compiled_exists : ∃ state, compiled.Realizes state :=
  Nonlinear.compiled_exists compiled trapping decrease initial_le

theorem compiled_unique {x y : Dynamics.Signal 3}
    (hx : compiled.Realizes x) (hy : compiled.Realizes y) :
    Set.EqOn x y evolution.time.domain :=
  Nonlinear.compiled_unique compiled trapping decrease initial_le hx hy

/-! ## The contract, in the interface gimle-forseti's trajectory registry cites -/

def observed := LinearEnergyContract.observed compiled

def admitted : Trajectory.SignalPredicate (0 + evolution.states.length) :=
  LinearEnergyContract.admitted compiled

theorem feedback_reads (input : Dynamics.Signal (0 + evolution.states.length))
    (admit : admitted input) (state : Dynamics.Signal evolution.states.length) :
    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state :=
  LinearEnergyContract.feedback_reads compiled input admit state

theorem declared_input_admitted :
    admitted (Dynamics.signalAppend Model.noDrivers fun _ => compiled.initial) :=
  LinearEnergyContract.declared_input_admitted compiled

theorem energy_at_trapping (x : Point 3) :
    compiled.outputs.circuit.run x energyIndex = trapping.energy x := by
  rw [energy_at, energy_eq_trapping]

/-- **The Lorenz trajectory stays in the ball `V ≤ 1600`**, for every admitted input. -/
theorem energy_contract :
    Contract observed evolution.time admitted
      (Always evolution.time fun observation =>
        0 ≤ observation energyIndex ∧ observation energyIndex ≤ 1600) :=
  Nonlinear.energy_contract compiled trapping energyIndex energy_at_trapping decrease initial_le

/-- `1300` is not a bound: `V = 1371` at the start. -/
theorem thirteen_hundred_refuted :
    ¬ Holds observed evolution.time admitted
      (Always evolution.time fun observation => observation energyIndex ≤ 1300) :=
  Nonlinear.refuted compiled trapping energyIndex energy_at_trapping decrease initial_le 1300
    (by
      show (1300 : ℝ) < @Nonlinear.Trapping.energy 3 trapping compiled.initial
      rw [← energy_eq_trapping, initial_eq]
      norm_num [energy, Matrix.cons_val_two, Matrix.tail_cons])

#print axioms invariant
#print axioms compiled_exists
#print axioms compiled_unique
#print axioms energy_contract
#print axioms thirteen_hundred_refuted

end Gimle.Forseti.Examples.Lorenz
