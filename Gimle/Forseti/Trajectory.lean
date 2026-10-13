import Gimle.Forseti
import Gimle.Forseti.LinearEnergy

/-! Well-posed contracts over continuous trajectories.

Asgard's continuous circuits have a *relational* semantics,
`Dynamics.Circuit.Rel time input output`: an input signal may be related to no
output, to one, or to many. A useful system theorem must therefore say three
separate things for every admitted input, and this module keeps them separate:

* `Realizable` — some output is related to it;
* `Unique` — all related outputs agree on the forward time domain;
* `Holds` — **every** related output satisfies the postcondition.

`Holds` alone is the *partial* contract. It is true of a circuit with no
behaviour at all, so it is never reported as a system theorem: only `Contract`,
which bundles all three, is. Asking only that some unique *safe* output exists
would leave other, unsafe outputs free; `Holds` quantifies over all of them.

Predicates are ordinary Lean properties of whole signals. `Always` lifts a
state predicate pointwise over the forward domain, `At` observes one time, and
`Initialized` binds driving signals and initial wires, reading an initial wire
only at the start as Asgard does.

No rule here gives a trace an unconditional contract: feedback can have no
solution or many, and only a proof about the particular loop, such as the
linear rules below, supplies one.
-/

namespace Gimle.Forseti.Trajectory

open Gimle.Forseti
open Gimle.Asgard
open Gimle.Asgard.Dynamics

/-- A property of a whole signal. -/
abbrev SignalPredicate (n : Nat) := Signal n → Prop

variable {n m k l : Nat}

/-! ### The three obligations -/

/-- Every admitted input has a related output. -/
def Realizable (circuit : Dynamics.Circuit n m) (time : TimeDomain)
    (pre : SignalPredicate n) : Prop :=
  ∀ input, pre input → ∃ output, circuit.Rel time input output

/-- Related outputs of an admitted input agree on the forward domain. Outside
it they may differ; that is not a uniqueness requirement. -/
def Unique (circuit : Dynamics.Circuit n m) (time : TimeDomain)
    (pre : SignalPredicate n) : Prop :=
  ∀ input, pre input → ∀ first second, circuit.Rel time input first →
    circuit.Rel time input second → Set.EqOn first second time.domain

/-- The partial contract: every related output of an admitted input satisfies
the postcondition. It holds vacuously of a circuit with no behaviour. -/
def Holds (circuit : Dynamics.Circuit n m) (time : TimeDomain)
    (pre : SignalPredicate n) (post : SignalPredicate m) : Prop :=
  ∀ input, pre input → ∀ output, circuit.Rel time input output → post output

/-- A well-posed trajectory contract: existence, uniqueness on the domain, and
the postcondition for every related output. -/
structure Contract (circuit : Dynamics.Circuit n m) (time : TimeDomain)
    (pre : SignalPredicate n) (post : SignalPredicate m) : Prop where
  realizable : Realizable circuit time pre
  unique : Unique circuit time pre
  holds : Holds circuit time pre post

/-- A contract gives each admitted input an output that satisfies the
postcondition. The converse is false: a safe output can coexist with unsafe
ones, which is exactly what `Holds` rules out. -/
theorem Contract.exists_safe {circuit : Dynamics.Circuit n m} {time : TimeDomain}
    {pre : SignalPredicate n} {post : SignalPredicate m}
    (contract : Contract circuit time pre post) (input : Signal n) (admitted : pre input) :
    ∃ output, circuit.Rel time input output ∧ post output := by
  obtain ⟨output, related⟩ := contract.realizable input admitted
  exact ⟨output, related, contract.holds input admitted output related⟩

/-! ### Observations -/

/-- A state predicate at every time of the forward domain: all-forward safety. -/
def Always (time : TimeDomain) (state : Point n → Prop) : SignalPredicate n :=
  fun signal => ∀ t ∈ time.domain, state (signal t)

/-- A state predicate at one time: an endpoint observation. -/
def At (t : ℝ) (state : Point n → Prop) : SignalPredicate n :=
  fun signal => state (signal t)

/-- All-forward safety gives the endpoint at any time of the domain. The
converse is false; `Tests/Trajectory.lean` shows a signal safe at its endpoint
only. -/
theorem Always.at {time : TimeDomain} {state : Point n → Prop} {signal : Signal n}
    (always : Always time state signal) {t : ℝ} (within : t ∈ time.domain) :
    At t state signal :=
  always t within

/-- Inputs made of driving signals and initial wires. The drivers are
constrained as whole signals; an initial wire only by its value at the start,
which is the only value Asgard's integrators read. -/
def Initialized (time : TimeDomain) (drivers : SignalPredicate k)
    (initial : Point n → Prop) : SignalPredicate (k + n) :=
  fun input => drivers (signalLeft input) ∧ initial (signalRight input time.start)

/-! ### Consequence and transport -/

/-- Strengthen the precondition and weaken the postcondition. -/
theorem Contract.consequence {circuit : Dynamics.Circuit n m} {time : TimeDomain}
    {pre strong : SignalPredicate n} {post weak : SignalPredicate m}
    (contract : Contract circuit time pre post)
    (strengthen : ∀ input, strong input → pre input)
    (weaken : ∀ output, post output → weak output) :
    Contract circuit time strong weak where
  realizable input admitted := contract.realizable input (strengthen input admitted)
  unique input admitted := contract.unique input (strengthen input admitted)
  holds input admitted output related :=
    weaken output (contract.holds input (strengthen input admitted) output related)

/-- The same weakening for the partial contract. -/
theorem Holds.consequence {circuit : Dynamics.Circuit n m} {time : TimeDomain}
    {pre strong : SignalPredicate n} {post weak : SignalPredicate m}
    (holds : Holds circuit time pre post)
    (strengthen : ∀ input, strong input → pre input)
    (weaken : ∀ output, post output → weak output) : Holds circuit time strong weak :=
  fun input admitted output related =>
    weaken output (holds input (strengthen input admitted) output related)

/-- Relationally equivalent circuits have the same contracts. -/
theorem Contract.transport {first second : Dynamics.Circuit n m} {time : TimeDomain}
    {pre : SignalPredicate n} {post : SignalPredicate m}
    (equivalent : Equivalent first second) (contract : Contract first time pre post) :
    Contract second time pre post where
  realizable input admitted := by
    obtain ⟨output, related⟩ := contract.realizable input admitted
    exact ⟨output, (equivalent time input output).mp related⟩
  unique input admitted a b ha hb :=
    contract.unique input admitted a b ((equivalent time input a).mpr ha)
      ((equivalent time input b).mpr hb)
  holds input admitted output related :=
    contract.holds input admitted output ((equivalent time input output).mpr related)

/-! ### Feedforward circuits -/

/-- A lifted feedforward circuit relates each input to exactly one output, at
every time; so an exact Hoare triple holds pointwise on the forward domain.
This is a statement about `lift` only, not about integrators or traces. -/
theorem Contract.lift (circuit : Gimle.Asgard.Circuit n m) (time : TimeDomain)
    {pre : Point n → Prop} {post : Point m → Prop} (hoare : ExactHoare ⟨pre⟩ circuit ⟨post⟩) :
    Contract (.lift circuit) time (Always time pre) (Always time post) where
  realizable input _ := ⟨fun t => circuit.run (input t), rfl⟩
  unique input _ a b ha hb := by
    change a = _ at ha
    change b = _ at hb
    rw [ha, hb]
    exact Set.eqOn_refl _ _
  holds input admitted output related t within := by
    change output = _ at related
    rw [related]
    exact hoare (input t) (admitted t within)

/-! ### Composition -/

/-- A circuit that respects its domain: admitted inputs that agree on the
forward domain have outputs that agree there. `Unique` compares outputs of one
input; composing needs it across inputs a first stage produced, which agree on
the domain only. -/
def DomainRespecting (circuit : Dynamics.Circuit n m) (time : TimeDomain)
    (pre : SignalPredicate n) : Prop :=
  ∀ first second, pre first → pre second → Set.EqOn first second time.domain →
    ∀ a b, circuit.Rel time first a → circuit.Rel time second b →
      Set.EqOn a b time.domain

/-- A lifted circuit reads its input pointwise, so it respects any domain. -/
theorem DomainRespecting.lift (circuit : Gimle.Asgard.Circuit n m) (time : TimeDomain)
    (pre : SignalPredicate n) : DomainRespecting (.lift circuit) time pre := by
  intro first second _ _ agree a b ha hb t within
  change a = _ at ha
  change b = _ at hb
  rw [ha, hb]
  simp only
  rw [agree within]

/-- Sequential composition through an intermediate signal contract. The second
stage must respect the domain on the intermediate signals, because the first
stage's outputs are unique only there. -/
theorem Contract.compose {first : Dynamics.Circuit n k} {second : Dynamics.Circuit k m}
    {time : TimeDomain} {pre : SignalPredicate n} {middle : SignalPredicate k}
    {post : SignalPredicate m}
    (head : Contract first time pre middle) (tail : Contract second time middle post)
    (respecting : DomainRespecting second time middle) :
    Contract (.compose first second) time pre post where
  realizable input admitted := by
    obtain ⟨between, related⟩ := head.realizable input admitted
    obtain ⟨output, after⟩ :=
      tail.realizable between (head.holds input admitted between related)
    exact ⟨output, between, related, after⟩
  unique input admitted a b := by
    rintro ⟨between, related, after⟩ ⟨between', related', after'⟩
    exact respecting between between' (head.holds input admitted between related)
      (head.holds input admitted between' related')
      (head.unique input admitted between between' related related') a b after after'
  holds input admitted output := by
    rintro ⟨between, related, after⟩
    exact tail.holds between (head.holds input admitted between related) output after

/-- Two circuits side by side, on the same clock, each owning its own ports. -/
def Both (left : SignalPredicate n) (right : SignalPredicate k) :
    SignalPredicate (n + k) :=
  fun signal => left (signalLeft signal) ∧ right (signalRight signal)

/-- Parallel composition: each factor's contract on its own ports. -/
theorem Contract.parallel {first : Dynamics.Circuit n m} {second : Dynamics.Circuit k l}
    {time : TimeDomain} {pre₁ : SignalPredicate n} {post₁ : SignalPredicate m}
    {pre₂ : SignalPredicate k} {post₂ : SignalPredicate l}
    (left : Contract first time pre₁ post₁) (right : Contract second time pre₂ post₂) :
    Contract (.parallel first second) time (Both pre₁ pre₂) (Both post₁ post₂) where
  realizable input admitted := by
    obtain ⟨a, ha⟩ := left.realizable _ admitted.1
    obtain ⟨b, hb⟩ := right.realizable _ admitted.2
    refine ⟨signalAppend a b, ?_, ?_⟩
    · simpa using ha
    · simpa using hb
  unique input admitted a b ha hb t within := by
    have l := left.unique _ admitted.1 _ _ ha.1 hb.1 within
    have r := right.unique _ admitted.2 _ _ ha.2 hb.2 within
    rw [← signalAppend_parts a, ← signalAppend_parts b]
    simp only [signalAppend] at l r ⊢
    rw [l, r]
  holds input admitted output related :=
    ⟨left.holds _ admitted.1 _ related.1, right.holds _ admitted.2 _ related.2⟩

/-! ### Initialized feedback

`Dynamics.close_correct` characterises a closed loop for a *constant*
initial-wire signal. A contract quantifies over every admitted input, whose
initial wires may carry anything after the start, so the characterisation is
needed for an arbitrary wire signal; `close_rel_reads_start` then says the
loop reads those wires only at the start. -/

/-- A closed feedback loop, for any driver and initial-wire signals. -/
theorem close_rel {d : Nat} (axis : String) (field : Gimle.Asgard.Circuit (d + n) n)
    (time : TimeDomain) (drivers : Signal d) (wires : Signal n) (state : Signal n) :
    (close axis field).Rel time (signalAppend drivers wires) state ↔
      axis = time.axis ∧ state time.start = wires time.start ∧
      ∀ t ∈ time.domain, ∀ i,
        HasDerivWithinAt (fun t => state t i)
          (field.run (pointAppend (drivers t) (state t)) i) time.domain t := by
  simp only [close, feedbackBody, Circuit.Rel]
  constructor
  · rintro ⟨feedback, routed, hr, bank, hb, integrated, hi, hout⟩
    subst routed
    have hr : (fun t => (prepare d n).run
        (signalAppend (signalAppend drivers wires) feedback t)) =
        signalAppend (signalAppend drivers feedback) wires := by
      funext t
      exact prepare_run _ _ _
    rw [hr] at hb
    simp only [signalLeft_append, signalRight_append, Wiring.identity_run] at hb
    have hbank : bank = signalAppend
        (fun t => field.run (signalAppend drivers feedback t)) wires := by
      have right : wires = signalRight bank := funext fun t => (congrFun hb.2 t).symm
      rw [← hb.1, right, signalAppend_parts]
    subst bank
    have hs : state = integrated := by
      funext t
      have h := congrFun hout t
      change pointAppend (state t) (feedback t) = _ at h
      rw [duplicate_run] at h
      simpa only [pointLeft_pointAppend] using congrArg pointLeft h
    have hf : feedback = integrated := by
      funext t
      have h := congrFun hout t
      change pointAppend (state t) (feedback t) = _ at h
      rw [duplicate_run] at h
      simpa only [pointRight_pointAppend] using congrArg pointRight h
    subst feedback
    subst integrated
    simpa only [signalAppend, pointLeft_pointAppend, pointRight_pointAppend] using hi
  · intro h
    refine ⟨state, _, rfl,
      signalAppend (fun t => field.run (pointAppend (drivers t) (state t))) wires, ?_,
      state, ?_, ?_⟩
    · rw [show (fun t => (prepare d n).run
          (signalAppend (signalAppend drivers wires) state t)) =
          signalAppend (signalAppend drivers state) wires by
        funext t; exact prepare_run _ _ _]
      simp only [signalLeft_append, signalRight_append, Wiring.identity_run]
      exact ⟨rfl, trivial⟩
    · simpa only [signalAppend, pointLeft_pointAppend, pointRight_pointAppend] using h
    · funext t
      exact (duplicate_run (state t)).symm

/-- A closed loop reads its initial wires only at the start: replacing them by
their start value changes no trajectory. -/
theorem close_rel_reads_start {d : Nat} (axis : String)
    (field : Gimle.Asgard.Circuit (d + n) n) (time : TimeDomain) (input : Signal (d + n))
    (state : Signal n) :
    (close axis field).Rel time input state ↔
      (close axis field).Rel time
        (signalAppend (signalLeft input) (fun _ => signalRight input time.start)) state := by
  conv_lhs => rw [← signalAppend_parts input]
  rw [close_rel, close_rel]

/-! ### Rules from linear well-posedness -/

/-- **A linear initial-value problem is well-posed.** For every input whose
initial wires start at the problem's initial point, the compiled loop has a
solution, all solutions agree from the start on, and each solves the source
problem. This consumes Asgard's linear existence and uniqueness theorems. -/
theorem Contract.linear (problem : Linear.Problem n) :
    Contract problem.circuit problem.time
      (Initialized problem.time (fun _ => True) (· = problem.initial)) problem.Solves := by
  have reading : ∀ input, Initialized problem.time (fun _ => True) (· = problem.initial) input →
      ∀ state, problem.circuit.Rel problem.time input state ↔ problem.Realizes state := by
    intro input admitted state
    have noDrivers : signalLeft input = fun _ i => Fin.elim0 i := by
      funext t i; exact Fin.elim0 i
    rw [Linear.Problem.circuit, close_rel_reads_start, admitted.2, noDrivers]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro input admitted
    obtain ⟨state, realized⟩ := problem.exists_realization
    exact ⟨state, (reading input admitted state).mpr realized⟩
  · intro input admitted a b ha hb
    exact problem.unique_realization ((reading input admitted a).mp ha)
      ((reading input admitted b).mp hb)
  · intro input admitted state related
    exact (problem.solves_iff_realizes state).mpr ((reading input admitted state).mp related)

/-- **An energy certificate gives a sublevel contract.** For the closed loop
around a supplied field circuit, every input starting in the energy sublevel
has a unique solution, and every solution stays in the sublevel at every time
of the forward domain. The premises are exactly `LinearEnergy.certificate_sound`'s:
both circuit translations and the checked weighted-square certificate.
Derivative inequalities alone would give only `Holds`. -/
theorem Contract.energy (template : Linear.Problem n) (rhs : Gimle.Asgard.Circuit n n)
    (energy : Gimle.Asgard.Circuit n 1) (p : LinearEnergy.QMatrix n)
    (certificate : LinearEnergy.Certificate n)
    (rhs_translated : ∀ x, rhs.run x = template.matrix.eval x)
    (energy_translated : ∀ x, energy.run x 0 = LinearEnergy.quadratic p x)
    (valid : certificate.Valid template.matrix p) (bound : ℝ) :
    Contract (close template.time.axis (LinearEnergy.authoritativeField rhs)) template.time
      (Initialized template.time (fun _ => True) fun x => energy.run x 0 ≤ bound)
      (Always template.time fun x => 0 ≤ energy.run x 0 ∧ energy.run x 0 ≤ bound) := by
  obtain ⟨exists_, unique_, safe⟩ := LinearEnergy.certificate_sound template rhs energy p
    certificate rhs_translated energy_translated valid bound
  have reading : ∀ input : Signal (0 + n), ∀ state,
      (close template.time.axis (LinearEnergy.authoritativeField rhs)).Rel template.time
        input state ↔
      LinearEnergy.Realizes rhs template.time (signalRight input template.time.start) state := by
    intro input state
    have noDrivers : signalLeft input = fun _ i => Fin.elim0 i := by
      funext t i; exact Fin.elim0 i
    rw [close_rel_reads_start, noDrivers]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro input _
    obtain ⟨state, realized⟩ := exists_ (signalRight input template.time.start)
    exact ⟨state, (reading input state).mpr realized⟩
  · intro input _ a b ha hb
    exact unique_ _ a b ((reading input a).mp ha) ((reading input b).mp hb)
  · intro input admitted state related t within
    exact safe _ state admitted.2 ((reading input state).mp related) t within

#print axioms close_rel
#print axioms Contract.compose
#print axioms Contract.parallel
#print axioms Contract.lift
#print axioms Contract.linear
#print axioms Contract.energy

end Gimle.Forseti.Trajectory
