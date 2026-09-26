import Gimle.Forseti.Examples.FormalHeatContract

/-! Coverage for total stream contracts.

Pinned here: contracts at independent axis and port counts; a boundary slice
moving with the axes under reindexing; the declared basis deciding what a
product means; shared and unused ports; a changed boundary changing the
reconstruction; a finite window that cannot see a tail; and a series
substitution outside its domain that stays undefined — so no total contract
holds — even when its result is discarded or multiplied by zero. The axiom
policy is asserted with `#guard_msgs`.
-/

namespace Gimle.Forseti.Tests.Stream

open Gimle.Asgard
open Gimle.Asgard.Streams
open Gimle.Asgard.Examples.FormalHeat
open Gimle.Forseti.Stream
open Gimle.Forseti.Examples.FormalHeatContract

/-! ### Independent axis and port counts -/

/-- One axis, two input ports, one output port. -/
example (a b : Stream 1) :
    StreamHoare (Equals ![a, b]) (Streams.Circuit.binary (basis := .ogf) .product)
      fun y => decode .ogf (y 0) = decode .ogf a * decode .ogf b :=
  StreamHoare.product a b

/-- Three axes, one port in and out. -/
example (a : Stream 3) :
    StreamHoare (Equals ![a]) (Streams.Circuit.unary (basis := .egf) (.derivative 2))
      (Equals ![derivative .egf 2 a]) :=
  StreamHoare.derivative 2 a

/-! ### Axes `[t, x]` and their permutation -/

/-- Swap `t` and `x`. -/
def swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

/-- The heat output's boundary along `t` is, after swapping the axes, the
swapped boundary along the new position of `t`, which is axis 1. -/
example (unused : Stream 2) :
    Boundary 1 1 (reindex swap boundary)
      (reindexPoint swap (circuit.value ![heat, boundary, unused])) := by
  have kept := (heat_contract _ (⟨rfl, fun _ _ => rfl⟩ : admitted ![heat, boundary, unused])).2.2
  simpa [swap] using (boundary_reindex swap 0 1 boundary _).mp kept

/-- The same slice, with the axis named as the model's stream context names it. -/
example (unused : Stream 2) :
    NamedBoundary context "time" 1 boundary (circuit.value ![heat, boundary, unused]) :=
  ⟨⟨0, by decide⟩, by decide,
    (heat_contract _ (⟨rfl, fun _ _ => rfl⟩ : admitted ![heat, boundary, unused])).2.2⟩

/-! ### The declared basis -/

/-- In EGF the product is the factorial-conjugated one: decoded, it is the
ordinary product. -/
example (a b : Stream 2) :
    StreamHoare (Equals ![a, b]) (Streams.Circuit.binary (basis := .egf) .product)
      fun y => decode .egf (y 0) = decode .egf a * decode .egf b :=
  StreamHoare.product a b

/-- A derivative contract moves across the EGF encoding: differentiating the
encoded stream in the EGF circuit gives the encoding of the ordinary derivative. -/
example (a : Stream 2) :
    StreamHoare (Equals ![encode .egf a])
      (Streams.Circuit.unary (basis := .egf) (.derivative 0))
      (Equals ![encode .egf (derivative .ogf 0 a)]) :=
  (StreamHoare.derivative 0 (encode .egf a)).consequence (fun _ admit => admit)
    (fun y same => by rw [same, derivative_encode]; rfl)

/-- The bases differ in raw coefficients: the same circuit on the same raw
stream `x` differentiates to coefficient `1` in OGF but to the shifted raw
coefficient `0` in EGF at degree 1 of `x²`-like input `[0,0,1]`. -/
def xSquared : Stream 1 := fun index => if index 0 = 2 then 1 else 0

example : derivative .ogf 0 xSquared (Finsupp.single 0 1) = 2 := by
  simp [derivative, xSquared]
  norm_num
example : derivative .egf 0 xSquared (Finsupp.single 0 1) = 1 := by
  simp [derivative, xSquared]

/-! ### Shared and unused ports -/

/-- `pair` reads one input twice: the heat circuit's two branches share `u`. -/
example : StreamHoare admitted (rhs.compile.pair rebuilt.compile)
    fun y => y = ![two, heat] ∧ Boundary 0 1 boundary y :=
  heat_contract

/-- The unused port may hold anything, including a stream that would be invalid
if it were substituted. -/
example : circuit.Defined ![heat, boundary, Streams.constant .ogf 1] :=
  (heat_contract _ ⟨rfl, fun _ _ => rfl⟩).1

/-- The boundary port matters only on its zero slice: `u` itself is an admitted
boundary input, since it agrees with `x²` wherever `t = 0`. -/
example (unused : Stream 2) : circuit.value ![heat, heat, unused] = ![two, heat] :=
  (heat_contract _ ⟨rfl, fun index zero => heat_boundary index zero⟩).2.1

/-- A resolved named axis is just that axis. -/
example (y : StreamPoint 2 2) :
    NamedBoundary context "time" 1 boundary y ↔ Boundary ⟨0, by decide⟩ 1 boundary y :=
  NamedBoundary.iff_boundary (context := context) (name := "time")
    (found := ⟨0, by decide⟩) (by decide) 1 boundary y

/-- `pair`'s output, block by block, is the appended point. -/
example (a b : Stream 2) : Both (Equals ![a]) (Equals ![b]) ![a, b] :=
  both_equals.mpr (append_single a b).symm

/-! ### A changed boundary -/

/-- `x²` at `t = 0`: the coefficient of `t⁰ x²`. -/
noncomputable def tZeroXTwo : Index 2 := Finsupp.single 1 2

/-- With a zero boundary the reconstruction is not the heat solution: it
disagrees at `t⁰ x²`, which the boundary alone decides. -/
example : ¬ StreamHoare (fun x : StreamPoint 2 3 => x 0 = heat ∧ x 1 = 0) circuit
    fun y => y 1 = heat := by
  intro hoare
  have := congrFun (hoare ![heat, 0, 0] ⟨rfl, rfl⟩).2 tZeroXTwo
  simp [circuit, rebuilt, rhs, Expr.value, Binary.value, Unary.value, integral, heat,
    tZeroXTwo] at this
  exact absurd this (by change ¬ (0 : ℚ) = 1; norm_num)

/-! ### A window does not see the tail -/

/-- `x⁵` on one axis. -/
def fifth : Stream 1 := fun index => if index 0 = 5 then 1 else 0

/-- `0` and `x⁵` agree below degree 3… -/
example : Window (fun _ => 3) 0 (0 : Stream 1) ![fifth] := by
  funext index
  by_cases inside : ∀ i, index i < 3
  · have : index 0 ≠ 5 := by have := inside 0; omega
    simp [truncate, inside, fifth, this]
    rfl
  · simp [truncate, inside]

/-- …but are different streams, so window equality is not equality. -/
example : ¬ Equals ![(0 : Stream 1)] ![fifth] := by
  intro same
  have := congrFun (congrFun same 0) (Finsupp.single 0 5)
  simp [fifth] at this
  exact absurd this (by change ¬ (1 : ℚ) = 0; norm_num)

/-! ### An invalid substitution stays undefined -/

/-- A nonzero constant is not a valid inner stream. -/
theorem one_invalid : ¬ CanCompose .ogf (Streams.constant .ogf 1 : Stream 1) := by
  simp [CanCompose, Streams.constant, encode, decode]

/-- Substitute a constant `1` for the axis, then throw the result away. -/
def discarded : Streams.Circuit .ogf 1 1 0 :=
  .compose (Expr.seriesCompose 0 (.input 0) (.constant 1)).compile (.route Fin.elim0)

/-- Substitute it, then multiply by zero. -/
def timesZero : Expr .ogf 1 1 :=
  .binary .product (.constant 0) (Expr.seriesCompose 0 (.input 0) (.constant 1))

example (post : StreamPredicate 1 0) : ¬ StreamHoare (fun _ => True) discarded post := by
  intro hoare
  have := (hoare ![0] trivial).1
  simp [discarded, Streams.Circuit.Defined, Expr.Defined, Expr.seriesCompose,
    Binary.Domain, Expr.value] at this
  exact one_invalid this

example (post : StreamPredicate 1 1) :
    ¬ StreamHoare (fun _ => True) timesZero.compile post := by
  intro hoare
  have := (Expr.compile_defined _ _).mp (hoare ![0] trivial).1
  simp [timesZero, Expr.Defined, Expr.seriesCompose, Binary.Domain, Expr.value] at this
  exact one_invalid this

/-! ### The axiom policy, asserted -/

/--
info: 'Gimle.Forseti.Stream.streamHoare_iff_rel'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms streamHoare_iff_rel
/--
info: 'Gimle.Forseti.Stream.StreamHoare.compose'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.compose
/--
info: 'Gimle.Forseti.Stream.StreamHoare.parallel'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.parallel
/--
info: 'Gimle.Forseti.Stream.StreamHoare.substitute'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.substitute
/--
info: 'Gimle.Forseti.Stream.boundary_reindex'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms boundary_reindex
/--
info: 'Gimle.Forseti.Stream.window_reindex'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms window_reindex
/--
info: 'Gimle.Forseti.Examples.FormalHeatContract.heat_contract'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms heat_contract

/--
info: 'Gimle.Forseti.Stream.StreamHoare.consequence'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.consequence
/--
info: 'Gimle.Forseti.Stream.StreamHoare.route'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.route
/--
info: 'Gimle.Forseti.Stream.StreamHoare.identity'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.identity
/--
info: 'Gimle.Forseti.Stream.StreamHoare.pair'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.pair
/--
info: 'Gimle.Forseti.Stream.StreamHoare.and'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.and
/--
info: 'Gimle.Forseti.Stream.StreamHoare.or'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.or
/--
info: 'Gimle.Forseti.Stream.StreamHoare.congr'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.congr
/--
info: 'Gimle.Forseti.Stream.StreamHoare.expr'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.expr
/--
info: 'Gimle.Forseti.Stream.StreamHoare.derivative'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.derivative
/--
info: 'Gimle.Forseti.Stream.StreamHoare.integral'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.integral
/--
info: 'Gimle.Forseti.Stream.StreamHoare.integralFrom'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.integralFrom
/--
info: 'Gimle.Forseti.Stream.StreamHoare.product'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.product
/--
info: 'Gimle.Forseti.Stream.StreamHoare.seriesCompose'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms StreamHoare.seriesCompose
/--
info: 'Gimle.Forseti.Stream.Equals.boundary'
  depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Equals.boundary
/--
info: 'Gimle.Forseti.Stream.Equals.window'
  depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Equals.window
/--
info: 'Gimle.Forseti.Stream.both_equals'
  depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms both_equals
/--
info: 'Gimle.Forseti.Stream.NamedBoundary.iff_boundary'
  depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms NamedBoundary.iff_boundary
/--
info: 'Gimle.Forseti.Stream.eq_integral_of_boundary'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms eq_integral_of_boundary

end Gimle.Forseti.Tests.Stream
