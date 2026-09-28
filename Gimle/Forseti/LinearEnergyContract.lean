import Gimle.Forseti.Trajectory
import Gimle.Forseti.LinearEnergy
import Gimle.Asgard.Model.Linear

/-! # Trajectory contracts for compiled linear models, from an energy certificate

A trajectory contract in the shape gimle-forseti's deciders cite
(`Examples/ThreeStateContract.lean`) needs, for one compiled continuous model:
existence and forward uniqueness, a reading of admitted inputs as the model's
own initial state, an energy bound, the bound lifted through the observation
circuit, and the declared input admitted. For a model whose compiled field is
homogeneous linear, and whose observed energy is a quadratic form `xᵀPx` with a
`LinearEnergy.Certificate`, all of it follows from the same few facts. A
`Spec` bundles them, and the rest is derived here:

* `feedback_reads` — the loop reads an admitted input as the model's own;
* `Spec.energy_bound` — every realization keeps the energy in `[0, β]` on the
  forward domain, for any `β` at least the initial energy;
* `Spec.loop_contract`, `Spec.energy_contract` — the two contracts;
* `declared_input_admitted` — the contract is not vacuous;
* `Spec.refuted` — a bound below the initial energy is refuted by the declared
  input's own realization.

Nothing is trusted beyond `LinearEnergy` and asgard-lean's `LinearView`: the
energy is read off the compiled observation circuit (`Spec.energy_eq`), and the
certificate is checked against the recognized matrix (`Spec.valid`). -/

namespace Gimle.Forseti.LinearEnergyContract

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Forseti.LinearEnergy
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Model

variable {b : Body} {e : Evolution}

/-- The compiled loop followed by the compiled observations. -/
def observed (M : ContinuousModel b e) :=
  Dynamics.Circuit.compose M.feedback (.lift M.outputs.circuit)

/-- Inputs: no drivers, and initial wires starting at the declared state. -/
def admitted (M : ContinuousModel b e) : SignalPredicate (0 + e.states.length) :=
  Initialized e.time (fun _ => True) (· = M.initial)

/-- The loop reads an admitted input as the model's own initial state. -/
theorem feedback_reads (M : ContinuousModel b e) (input : Signal (0 + e.states.length))
    (admit : admitted M input) (state : Signal e.states.length) :
    M.feedback.Rel e.time input state ↔ M.Realizes state := by
  have noDrivers : signalLeft input = Model.noDrivers := by
    funext t i; exact Fin.elim0 i
  unfold ContinuousModel.Realizes ContinuousModel.feedback
  rw [close_rel_reads_start, noDrivers, admit.2]

/-- The declared input is admitted, so a contract over `admitted` is not vacuous. -/
theorem declared_input_admitted (M : ContinuousModel b e) :
    admitted M (signalAppend Model.noDrivers fun _ => M.initial) := by
  refine ⟨trivial, ?_⟩
  simp

/-- What makes a compiled linear model's energy contract: its linear view, the
index of an observation that computes `xᵀPx`, and a certificate valid for the
recognized matrix and `P`. -/
structure Spec (M : ContinuousModel b e) where
  /-- The accepted linear view of the compiled field. -/
  view : LinearView M
  /-- The observed energy's position among the compiled observations. -/
  energy : Fin b.observations.length
  /-- The energy's quadratic form. -/
  matrix : QMatrix e.states.length
  /-- The compiled observation computes that form. -/
  energy_eq : ∀ x, M.outputs.circuit.run x energy = quadratic matrix x
  /-- Untrusted weighted squares for `P` and its dissipation. -/
  certificate : Certificate e.states.length
  /-- The certificate, checked against the recognized matrix. -/
  valid : certificate.Valid view.matrix matrix

namespace Spec

variable {M : ContinuousModel b e} (s : Spec M)

/-- The energy of a state, as the compiled observation circuit computes it. -/
noncomputable def energyOf (state : Point e.states.length) : ℝ :=
  M.outputs.circuit.run state s.energy

/-- **Energy bound.** Every realization keeps the observed energy in `[0, β]` on
the forward domain, for any `β` at least the initial energy. -/
theorem energy_bound (β : ℝ) (initial : s.energyOf M.initial ≤ β)
    (state : Signal e.states.length) (realized : M.Realizes state)
    (t : ℝ) (forward : t ∈ e.time.domain) :
    0 ≤ s.energyOf (state t) ∧ s.energyOf (state t) ≤ β := by
  have solves : s.view.problem.Solves state :=
    (s.view.source_iff state).mp ((M.solves_iff_realizes state).mpr realized)
  have start : quadratic s.matrix s.view.problem.initial ≤ β := by
    rw [← s.energy_eq]; exact initial
  have h := certificate_energy_bound s.view.problem s.matrix s.certificate s.valid
    state solves β start t forward
  simpa only [energyOf, s.energy_eq] using h

/-- The loop alone: unique solutions whose energy stays in `[0, β]`. -/
theorem loop_contract (β : ℝ) (initial : s.energyOf M.initial ≤ β) :
    Contract M.feedback e.time (admitted M)
      (Always e.time fun state => 0 ≤ s.energyOf state ∧ s.energyOf state ≤ β) where
  realizable input admit := by
    obtain ⟨state, realized⟩ := s.view.exists_realization
    exact ⟨state, (feedback_reads M input admit state).mpr realized⟩
  unique input admit x y hx hy :=
    s.view.unique_realization ((feedback_reads M input admit x).mp hx)
      ((feedback_reads M input admit y).mp hy)
  holds input admit state related t within :=
    s.energy_bound β initial state ((feedback_reads M input admit state).mp related) t within

/-- **The observed energy never leaves `[0, β]`.** For every admitted input the
compiled system has an output, all outputs agree on the forward domain, and
every one of them keeps the energy observation in `[0, β]`. -/
theorem energy_contract (β : ℝ) (initial : s.energyOf M.initial ≤ β) :
    Contract (observed M) e.time (admitted M)
      (Always e.time fun observation =>
        0 ≤ observation s.energy ∧ observation s.energy ≤ β) :=
  Contract.compose (s.loop_contract β initial)
    (Contract.lift M.outputs.circuit e.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

/-- **A bound below the initial energy is refuted**, by the declared input's own
realization at the start, not by a failed proof attempt. -/
theorem refuted (β : ℝ) (above : β < s.energyOf M.initial) :
    ¬ Holds (observed M) e.time (admitted M)
      (Always e.time fun observation => observation s.energy ≤ β) := by
  intro claim
  obtain ⟨state, realized⟩ := s.view.exists_realization
  have start : state e.time.start = M.initial := by
    unfold ContinuousModel.Realizes ContinuousModel.feedback at realized
    exact ((close_rel _ _ _ _ _ _).mp realized).2.1
  have bounded := claim _ (declared_input_admitted M) _
    ⟨state, (feedback_reads M _ (declared_input_admitted M) state).mpr realized, rfl⟩
    e.time.start (by simp [TimeDomain.domain])
  simp only at bounded
  rw [start] at bounded
  exact absurd bounded (not_le.mpr above)

end Spec

end Gimle.Forseti.LinearEnergyContract
