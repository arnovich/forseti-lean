import Gimle.Forseti.Stream
import Gimle.Forseti.Syntax.Certificate
import Gimle.Asgard.Streams.Lowering

/-! Finite coefficient observations of stream circuits, checked by polynomial
certificates.

Task 017 checks entailments between polynomial formulas over finitely many real
coordinates. Task 018 states total contracts over whole infinite coefficient
streams. This module is the bridge between them, and it goes through exactly
one Asgard theorem: `Lowering.lower_correct` (asgard-lean 023), which says that
running the lowered feedforward circuit on the input coefficients a manifest
names gives exactly the output coefficients another manifest names, of the
*original* stream circuit, for every input stream.

An `Observation` is a manifest — ordered axis IDs, port IDs and coefficient
slots, in a basis fixed by its type — together with the `Context` that names
each slot, `u[t^0, x^2]`. The names are computed from the manifest, never
supplied, so a formula written by name reads the slot the name describes.
`Observation.Observes` interprets a 017 formula on the observed exact rational
coefficients, cast into ℝ.

**The transfer rule.** `lift`: a point Hoare triple over the lowered circuit,
together with a proof that every admitted full input stream satisfies the
triple's precondition on its dependency coefficients, gives a total
`StreamHoare` contract over the original stream circuit, with the original
full-stream precondition retained and definedness discharged by the lowering
(`lower_defined`). `leaf_hoare` produces that point triple from a checked 017
entailment (`leafGoal`), and `lift_certificate` chains the two.

**What it does not give.** A postcondition is `Observes`: a statement about
finitely many output coefficients. It never implies equality of whole streams
(`Tests/StreamObservation.lean`), and it says nothing about the real function a
stream represents: that is the evaluated-field adapter of task 021, which needs
asgard-lean 024.

**Refutation.** A leaf counterexample refutes only the leaf. `refutes_root`
turns one into `¬ StreamHoare` only given a full input stream that is admitted
by the original precondition and whose dependency coefficients are the
counterexample's values.
-/

namespace Gimle.Forseti.Syntax

open Gimle.Asgard

/-! ### Substituting polynomials for variables -/

/-- Replace every variable of a polynomial by a polynomial. -/
def substitute {source target : Nat} (values : Fin source → Polynomial.Expr target) :
    Polynomial.Expr source → Polynomial.Expr target
  | .var coordinate => values coordinate
  | .constant value => .constant value
  | .add left right => .add (substitute values left) (substitute values right)
  | .mul left right => .mul (substitute values left) (substitute values right)
  | .neg argument => .neg (substitute values argument)

@[simp] theorem substitute_eval {source target : Nat}
    (values : Fin source → Polynomial.Expr target) (polynomial : Polynomial.Expr source)
    (point : Point target) :
    (substitute values polynomial).eval point =
      polynomial.eval fun i => (values i).eval point := by
  induction polynomial with
  | var coordinate => rfl
  | constant value => rfl
  | add left right leftIH rightIH =>
      simp [substitute, Polynomial.Expr.eval, leftIH, rightIH]
  | mul left right leftIH rightIH =>
      simp [substitute, Polynomial.Expr.eval, leftIH, rightIH]
  | neg argument argumentIH => simp [substitute, Polynomial.Expr.eval, argumentIH]

/-- Replace every variable of a formula by a polynomial. -/
def Formula.substitute {source target : Nat} (values : Fin source → Polynomial.Expr target) :
    Formula source → Formula target
  | .tru => .tru
  | .fls => .fls
  | .atom relation polynomial => .atom relation (Syntax.substitute values polynomial)
  | .and left right => .and (left.substitute values) (right.substitute values)
  | .or left right => .or (left.substitute values) (right.substitute values)
  | .not argument => .not (argument.substitute values)

/-- A substituted formula holds where the original holds at the substituted
values. -/
@[simp] theorem Formula.substitute_holds {source target : Nat}
    (values : Fin source → Polynomial.Expr target) (formula : Formula source)
    (point : Point target) :
    (formula.substitute values).holds point ↔
      formula.holds fun i => (values i).eval point := by
  induction formula with
  | tru => rfl
  | fls => rfl
  | atom relation polynomial => simp [Formula.substitute, Formula.holds]
  | and left right leftIH rightIH =>
      simp [Formula.substitute, Formula.holds, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp [Formula.substitute, Formula.holds, leftIH, rightIH]
  | not argument argumentIH => simp [Formula.substitute, Formula.holds, argumentIH]

/-- The point an answer denotes, when it reads: each coordinate's value by name. -/
theorem Context.read_eq {context : Context} {answer : Syntax.Context.Assignment}
    {point : Fin context.dimension → ℚ} (read_ok : context.read answer = .ok point) :
    point = fun coordinate => (Syntax.Context.valueOf answer (context.name coordinate)).getD 0 := by
  unfold Context.read at read_ok
  split at read_ok
  · cases read_ok
  · split at read_ok
    · cases read_ok
    · cases read_ok
      rfl

end Gimle.Forseti.Syntax

namespace Gimle.Forseti.StreamObservation

open Gimle.Forseti
open Gimle.Forseti.Syntax
open Gimle.Forseti.Stream
open Gimle.Asgard
open Gimle.Asgard.Streams
open Gimle.Asgard.Streams.Lowering

variable {basis : Basis} {d n m : Nat}

/-! ### Naming coefficient slots -/

/-- The name of one coefficient slot: its port ID, then each axis ID with its
degree, in axis order — `u[t^0, x^2]`. -/
def slotName (axes : Fin d → String) (ports : Fin m → String) (slot : Slot m d) : String :=
  ports slot.port ++ "[" ++
    ", ".intercalate (List.ofFn fun i => axes i ++ "^" ++ toString (slot.degrees i)) ++ "]"

/-- The names of a manifest's slots, in its order. -/
def slotNames (manifest : Manifest basis m d) : List String :=
  manifest.slots.map (slotName manifest.axes manifest.ports)

/-- A finite coefficient observation: a manifest, and the context that names its
slots. The names are the manifest's own (`named`), so the context cannot be
reordered or renamed independently of the slots it describes, and a context
exists only when those names are distinct and non-blank. The basis is in the
type, as in the manifest. -/
structure Observation (basis : Basis) (d m : Nat) where
  /-- The ordered axes, ports and slots being observed. -/
  manifest : Manifest basis m d
  /-- The names of the slots, as formula coordinates. -/
  context : Syntax.Context
  /-- Coordinate `i` is named after slot `i`. -/
  named : context.names = slotNames manifest

namespace Observation

/-- Name a manifest's slots. The name checks are discharged when the
observation is built, by default in the kernel. -/
def ofManifest (manifest : Manifest basis m d)
    (nonempty : slotNames manifest ≠ [] := by decide +kernel)
    (distinct : (slotNames manifest).Nodup := by decide +kernel)
    (nonblank : ∀ name ∈ slotNames manifest, name ≠ "" := by decide +kernel) :
    Observation basis d m :=
  ⟨manifest, ⟨slotNames manifest, nonempty, distinct, nonblank⟩, rfl⟩

variable (observation : Observation basis d m)

/-- One coordinate per observed slot. -/
theorem dimension_eq : observation.context.dimension = observation.manifest.slots.length := by
  simp [Context.dimension, observation.named, slotNames]

/-- The slot a coordinate observes. -/
def slot (i : Fin observation.context.dimension) : Slot m d :=
  observation.manifest.slots[Fin.cast observation.dimension_eq i]

/-- A coordinate is named after the slot it observes. -/
theorem name_slot (i : Fin observation.context.dimension) :
    observation.context.name i =
      slotName observation.manifest.axes observation.manifest.ports (observation.slot i) := by
  have names := observation.named
  simp only [Context.name, slot]
  simp only [slotNames] at names
  simp [names]

/-- Reorder a point over the manifest's slots as a point over the context. -/
def slotPoint (z : Point observation.manifest.slots.length) :
    Point observation.context.dimension :=
  fun i => z (Fin.cast observation.dimension_eq i)

/-- The observed coefficients of a stream point, exactly, cast into ℝ. -/
noncomputable def point (y : StreamPoint d m) : Point observation.context.dimension :=
  fun i => ((y (observation.slot i).port (observation.slot i).degrees.toIndex : ℚ) : ℝ)

/-- The observed point is the lowering's dependency point, read by name. -/
theorem point_eq_dependencyPoint (y : StreamPoint d m) :
    observation.point y =
      observation.slotPoint (dependencyPoint observation.manifest.slots y) :=
  rfl

/-- **The coefficient predicate**: a 017 formula over the named slots, read on
their exact coefficients cast into ℝ. It constrains those finitely many
coefficients and nothing else. -/
def Observes (formula : Formula observation.context.dimension) : StreamPredicate d m :=
  fun y => formula.holds (observation.point y)

/-- An observation reads only its own slots: two points that agree there are
observed alike. -/
theorem observes_congr (formula : Formula observation.context.dimension)
    {y y' : StreamPoint d m}
    (agree : ∀ s ∈ observation.manifest.slots, y s.port s.degrees.toIndex =
      y' s.port s.degrees.toIndex) :
    observation.Observes formula y ↔ observation.Observes formula y' := by
  have same : observation.point y = observation.point y' := by
    funext i
    simp only [point, slot]
    congr 1
    exact agree _ (List.getElem_mem _)
  simp only [Observes, same]

/-- A coordinate observes the coefficient of the slot it is bound to. -/
theorem point_of_slot {i : Fin observation.context.dimension} {s : Slot m d}
    (bound : observation.slot i = s) (y : StreamPoint d m) :
    observation.point y i = ((y s.port s.degrees.toIndex : ℚ) : ℝ) := by
  subst bound
  rfl

/-- A variable written by name reads the coefficient of the slot it is bound to. -/
theorem var_eval {name : String} {found} {s : Slot m d}
    (bound : observation.slot (observation.context.coordinate name found) = s)
    (y : StreamPoint d m) :
    (observation.context.var name found).eval (observation.point y) =
      ((y s.port s.degrees.toIndex : ℚ) : ℝ) :=
  observation.point_of_slot bound y

/-- The postcondition of a point triple over the lowered circuit: the formula
read on its outputs, which are the manifest's slots in order. -/
def leaf (formula : Formula observation.context.dimension) :
    Predicate observation.manifest.slots.length :=
  ⟨fun z => formula.holds (observation.slotPoint z)⟩

end Observation

/-! ### What a successful lowering computed -/

private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (ok : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases ok
  | ok a => exact ⟨a, rfl, ok⟩

/-- **What `lower` returns.** A successful lowering reads exactly the deduplicated
slots of the output terms, and its circuit evaluates, at every real point, the
output terms as polynomials over those slots. `lower_correct` is the special
case at points made of stream coefficients. -/
theorem lower_spec {circuit : Streams.Circuit basis d n m} {inputPorts : Fin n → String}
    {output : Manifest basis m d} {limit : Nat} {lowered : Lowered basis n m d output}
    (ok : lower circuit inputPorts output limit = .ok lowered) :
    lowered.inputs.slots =
        ((output.slots.map fun s => lowerRaw circuit s.port s.degrees).flatMap Term.slots).dedup ∧
      ∀ z : Point lowered.inputs.slots.length, lowered.circuit.run z = fun o =>
        (toExpr lowered.inputs.slots
          (lowerRaw circuit output.slots[o].port output.slots[o].degrees)).eval z := by
  have support := (lower_names circuit inputPorts output limit lowered ok).1
  unfold lower at ok
  simp only [support, Bool.not_true, Bool.false_eq_true, ite_false] at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · obtain ⟨_, _, ok⟩ := bind_ok ok
      cases ok
      refine ⟨rfl, fun z => ?_⟩
      rw [Gimle.Asgard.Polynomial.compileOutputs_correct]

/-- Every slot an output term reads is among a successful lowering's inputs. -/
theorem lower_covers {circuit : Streams.Circuit basis d n m} {inputPorts : Fin n → String}
    {output : Manifest basis m d} {limit : Nat} {lowered : Lowered basis n m d output}
    (ok : lower circuit inputPorts output limit = .ok lowered) (s : Slot m d)
    (member : s ∈ output.slots) :
    ∀ t ∈ (lowerRaw circuit s.port s.degrees).slots, t ∈ lowered.inputs.slots := by
  intro t read
  rw [(lower_spec ok).1, List.mem_dedup, List.mem_flatMap]
  exact ⟨_, List.mem_map.mpr ⟨s, member, rfl⟩, read⟩

/-- The value of a computation that succeeded. -/
def okValue {ε α : Type} : (result : Except ε α) → result.toBool = true → α
  | .ok value, _ => value
  | .error _, failed => absurd failed (by simp [Except.toBool])

theorem eq_ok_okValue {ε α : Type} (result : Except ε α) (succeeds : result.toBool = true) :
    result = .ok (okValue result succeeds) := by
  cases result with
  | ok value => rfl
  | error _ => simp [Except.toBool] at succeeds

/-- The lowering of an observation, once the kernel has checked that it
succeeds. -/
def lowered (circuit : Streams.Circuit basis d n m) (inputPorts : Fin n → String)
    (output : Manifest basis m d) (succeeds : (lower circuit inputPorts output).toBool = true) :
    Lowered basis n m d output :=
  okValue _ succeeds

theorem lowered_ok (circuit : Streams.Circuit basis d n m) (inputPorts : Fin n → String)
    (output : Manifest basis m d) (succeeds : (lower circuit inputPorts output).toBool = true) :
    lower circuit inputPorts output = .ok (lowered circuit inputPorts output succeeds) :=
  eq_ok_okValue _ succeeds

/-! ### The transfer rule -/

/-- **A point triple over the lowered circuit is a total stream contract over the
original circuit.** Every input admitted by the full-stream precondition `pre`
is in the circuit's domain (`lower_defined`), and, when its dependency
coefficients satisfy the leaf precondition, the observed output coefficients
satisfy `post` (`lower_correct`). The precondition stays the full-stream one:
the leaf precondition is an obligation on it, not a replacement for it. -/
theorem lift {circuit : Streams.Circuit basis d n m} {inputPorts : Fin n → String}
    {output : Observation basis d m} {limit : Nat}
    {lowered : Lowered basis n m d output.manifest}
    (ok : lower circuit inputPorts output.manifest limit = .ok lowered)
    {pre : StreamPredicate d n} {pointPre : Predicate lowered.inputs.slots.length}
    {post : Formula output.context.dimension}
    (inputs : ∀ x, pre x → pointPre.holds (dependencyPoint lowered.inputs.slots x))
    (leaf : ExactHoare pointPre lowered.circuit (output.leaf post)) :
    StreamHoare pre circuit (output.Observes post) := by
  intro x admitted
  refine ⟨lower_defined circuit inputPorts output.manifest limit lowered ok x, ?_⟩
  have holds := leaf _ (inputs x admitted)
  rw [lower_correct circuit inputPorts output.manifest limit lowered ok x] at holds
  exact holds

/-! ### Leaf goals -/

/-- A term over the input slots, as a polynomial over the input observation's
named coordinates. -/
def observedExpr (input : Observation basis d n) (term : Term n d) :
    Polynomial.Expr input.context.dimension :=
  Syntax.rename (Fin.cast input.dimension_eq.symm) (toExpr input.manifest.slots term)

/-- **The leaf question.** Over the input observation's named coefficients: does
`antecedent` entail `post`, with each output coordinate replaced by the
polynomial the lowering computes for its slot? This is an ordinary 017 `Goal`;
a certificate or counterexample is checked against it as posed. -/
def leafGoal (circuit : Streams.Circuit basis d n m) (input : Observation basis d n)
    (output : Observation basis d m) (antecedent : Formula input.context.dimension)
    (post : Formula output.context.dimension) : Goal where
  context := input.context
  antecedent := antecedent
  consequent := post.substitute fun j =>
    observedExpr input (lowerRaw circuit (output.slot j).port (output.slot j).degrees)

/-- The leaf precondition over the lowered circuit's inputs, read by name. -/
def leafPre (input : Observation basis d n) {k : Nat}
    (same : input.manifest.slots.length = k) (antecedent : Formula input.context.dimension) :
    Predicate k :=
  ⟨fun z => antecedent.holds fun i => z (Fin.cast (input.dimension_eq.trans same) i)⟩

private theorem toExpr_cast {first second : List (Slot n d)} (same : first = second)
    (term : Term n d) (z : Point second.length) :
    (toExpr first term).eval (fun k => z (Fin.cast (congrArg List.length same) k)) =
      (toExpr second term).eval z := by
  subst same
  rfl

/-- An observed term evaluates at the observed point to the lowered one. -/
private theorem observedExpr_eval {input : Observation basis d n}
    {slots : List (Slot n d)} (same : input.manifest.slots = slots)
    (term : Term n d) (z : Point slots.length) :
    (observedExpr input term).eval
        (fun i => z (Fin.cast (input.dimension_eq.trans (congrArg List.length same)) i)) =
      (toExpr slots term).eval z := by
  rw [observedExpr, rename_eval]
  exact toExpr_cast same term z

/-- **A checked leaf entailment is a point triple over the lowered circuit.** The
input observation must name exactly the lowering's input slots (`same`), which
is how the leaf's coordinates are bound to the coefficients the lowered circuit
reads. -/
theorem leaf_hoare {circuit : Streams.Circuit basis d n m} {inputPorts : Fin n → String}
    {output : Observation basis d m} {limit : Nat}
    {lowered : Lowered basis n m d output.manifest}
    (ok : lower circuit inputPorts output.manifest limit = .ok lowered)
    (input : Observation basis d n) (same : input.manifest.slots = lowered.inputs.slots)
    {antecedent : Formula input.context.dimension} {post : Formula output.context.dimension}
    (entails : (leafGoal circuit input output antecedent post).Entailment) :
    ExactHoare (leafPre input (congrArg List.length same) antecedent) lowered.circuit
      (output.leaf post) := by
  intro z admitted
  have holds := entails _ admitted
  simp only [leafGoal, Formula.substitute_holds] at holds
  show post.holds (output.slotPoint (lowered.circuit.run z))
  rw [(lower_spec ok).2 z]
  convert holds using 2 with j
  exact (observedExpr_eval same _ z).symm

/-- **The coefficient transfer rule, end to end.** A 017 certificate that checks
against the leaf goal, and a proof that every admitted full input satisfies the
leaf antecedent on its named coefficients, give the total stream contract. -/
theorem lift_certificate {circuit : Streams.Circuit basis d n m}
    {inputPorts : Fin n → String} {output : Observation basis d m} {limit : Nat}
    {lowered : Lowered basis n m d output.manifest}
    (ok : lower circuit inputPorts output.manifest limit = .ok lowered)
    (input : Observation basis d n) (same : input.manifest.slots = lowered.inputs.slots)
    {pre : StreamPredicate d n} {antecedent : Formula input.context.dimension}
    {post : Formula output.context.dimension}
    (certificate : EntailmentCertificate input.context.dimension)
    (valid : certificate.check (leafGoal circuit input output antecedent post) = true)
    (inputs : ∀ x, pre x → antecedent.holds (input.point x)) :
    StreamHoare pre circuit (output.Observes post) := by
  refine lift ok (fun x admitted => ?_)
    (leaf_hoare ok input same (EntailmentCertificate.sound _ certificate valid))
  have holds := inputs x admitted
  simp only [leafPre]
  convert holds using 2 with i
  simp only [Observation.point, Observation.slot, dependencyPoint]
  congr 3 <;> simp [same]

/-! ### Refutation -/

/-- A contract fails as soon as one admitted input's output fails the
postcondition. -/
theorem not_streamHoare {pre : StreamPredicate d n} {circuit : Streams.Circuit basis d n m}
    {post : StreamPredicate d m} (x : StreamPoint d n) (admitted : pre x)
    (fails : ¬ post (circuit.value x)) : ¬ StreamHoare pre circuit post :=
  fun hoare => fails (hoare x admitted).2

/-- The observed output of a full input is the leaf consequent read at its named
input coefficients, whenever the input observation covers the output terms. -/
theorem observes_value {circuit : Streams.Circuit basis d n m} (supported : supported circuit)
    (input : Observation basis d n) (output : Observation basis d m)
    (covers : ∀ s ∈ output.manifest.slots, ∀ t ∈ (lowerRaw circuit s.port s.degrees).slots,
      t ∈ input.manifest.slots)
    (antecedent : Formula input.context.dimension) (post : Formula output.context.dimension)
    (x : StreamPoint d n) :
    output.Observes post (circuit.value x) ↔
      (leafGoal circuit input output antecedent post).consequent.holds (input.point x) := by
  simp only [leafGoal, Formula.substitute_holds, Observation.Observes]
  apply iff_of_eq
  congr 1
  funext j
  rw [observedExpr, rename_eval]
  have agree := toExpr_eval input.manifest.slots
    (lowerRaw circuit (output.slot j).port (output.slot j).degrees) x
    (covers _ (List.getElem_mem _))
  simp only [Observation.point, lowerRaw_correct circuit supported x]
  rw [← agree]
  rfl

/-- **A leaf counterexample refutes the root only through an admitted full
input.** The answer must refute the leaf goal as posed, and a full input stream
must be admitted by the original precondition and carry the answer's values at
the named input coefficients. Without such an input, nothing is refuted. -/
theorem refutes_root {circuit : Streams.Circuit basis d n m} {inputPorts : Fin n → String}
    {output : Observation basis d m} {limit : Nat}
    {lowered : Lowered basis n m d output.manifest}
    (ok : lower circuit inputPorts output.manifest limit = .ok lowered)
    (input : Observation basis d n) (same : input.manifest.slots = lowered.inputs.slots)
    {pre : StreamPredicate d n} {antecedent : Formula input.context.dimension}
    {post : Formula output.context.dimension} {answer : Syntax.Context.Assignment}
    (valid : refutes (leafGoal circuit input output antecedent post) answer = true)
    (x : StreamPoint d n) (admitted : pre x)
    (agrees : ∀ i, input.point x i =
      (((Syntax.Context.valueOf answer (input.context.name i)).getD 0 : ℚ) : ℝ)) :
    ¬ StreamHoare pre circuit (output.Observes post) := by
  apply not_streamHoare x admitted
  have supported := (lower_names circuit inputPorts output.manifest limit lowered ok).1
  rw [observes_value supported input output
    (fun s member t read => same ▸ lower_covers ok s member t read) antecedent post x]
  unfold refutes at valid
  split at valid
  · rename_i point read
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at valid
    have fails := valid.2
    rw [Syntax.Context.read_eq read] at fails
    intro holds
    have cast : input.point x = fun i =>
        ((((Syntax.Context.valueOf answer (input.context.name i)).getD 0 : ℚ)) : ℝ) :=
      funext agrees
    rw [cast] at holds
    have back := (Formula.holdsQ_iff _ _).mpr holds
    exact absurd (fails.symm.trans back) (by decide)
  · cases valid

#print axioms lower_spec
#print axioms lift
#print axioms leaf_hoare
#print axioms lift_certificate
#print axioms refutes_root

end Gimle.Forseti.StreamObservation
