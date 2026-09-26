import Gimle.Forseti
import Gimle.Asgard.Streams.Laws
import Gimle.Asgard.Streams.Named
import Gimle.Asgard.Streams.Reindex

/-! Total Hoare contracts over Asgard's formal streams.

Asgard's stream circuits (`Streams.Circuit basis d n m`) map `n` ports of exact
formal coefficient streams over `d` ordered axes to `m` ports, in a declared
basis (OGF or EGF). Their semantics is partial and deterministic: an input is
either outside the circuit's domain — a series substitution whose inner stream
has a nonzero constant — or has exactly one output, `Streams.Circuit.rel_iff`.

`StreamHoare P c Q` is the *total* contract: every input satisfying `P` is in
the domain and its output satisfies `Q`. An undefined substitution therefore
never makes a contract vacuously true, even when its result is later discarded
or multiplied by zero. `streamHoare_iff_rel` restates it through the relation:
some output exists, and every related output satisfies `Q`.

Predicates are ordinary Lean properties of whole streams; no decidable language
of stream predicates is claimed. `Equals`, `Boundary` and `Window` are reusable
ones: equality to a full stream point, equality of one port's zero slice along
an axis, and equality on a finite rectangular coefficient window. A window
equality never gives full equality (`Tests/Stream.lean`).

This is exact formal coefficient reasoning. It says nothing about analytic
functions, convergence, norms or numerical accuracy.
-/

namespace Gimle.Forseti.Stream

open Gimle.Asgard
open Gimle.Asgard.Streams

/-- A property of a stream point: `n` ports over `d` axes. -/
abbrev StreamPredicate (d n : Nat) := StreamPoint d n → Prop

variable {basis : Basis} {d n m k o : Nat}

/-- Entailment between stream predicates. -/
def StreamEntailment (antecedent consequent : StreamPredicate d n) : Prop :=
  ∀ x, antecedent x → consequent x

/-- Equality of stream predicates. -/
def StreamEquality (left right : StreamPredicate d n) : Prop :=
  ∀ x, left x ↔ right x

/-- **The total contract**: every admitted input is in the circuit's domain, and
its output satisfies the postcondition. -/
def StreamHoare (pre : StreamPredicate d n) (circuit : Streams.Circuit basis d n m)
    (post : StreamPredicate d m) : Prop :=
  ∀ x, pre x → circuit.Defined x ∧ post (circuit.value x)

/-- The total contract, read through Asgard's relation: an output exists, and
every related output satisfies the postcondition. -/
theorem streamHoare_iff_rel (pre : StreamPredicate d n) (circuit : Streams.Circuit basis d n m)
    (post : StreamPredicate d m) :
    StreamHoare pre circuit post ↔
      ∀ x, pre x → (∃ y, circuit.Rel x y) ∧ ∀ y, circuit.Rel x y → post y := by
  constructor
  · intro hoare x admitted
    obtain ⟨defined, holds⟩ := hoare x admitted
    refine ⟨⟨_, (circuit.rel_iff _ _).mpr ⟨defined, rfl⟩⟩, ?_⟩
    intro y related
    obtain ⟨_, rfl⟩ := (circuit.rel_iff _ _).mp related
    exact holds
  · intro relational x admitted
    obtain ⟨⟨y, related⟩, every⟩ := relational x admitted
    obtain ⟨defined, rfl⟩ := (circuit.rel_iff _ _).mp related
    exact ⟨defined, every _ related⟩

/-! ### Structural rules -/

/-- Strengthen the precondition, weaken the postcondition. -/
theorem StreamHoare.consequence {pre strong : StreamPredicate d n}
    {circuit : Streams.Circuit basis d n m} {post weak : StreamPredicate d m}
    (hoare : StreamHoare pre circuit post) (strengthen : StreamEntailment strong pre)
    (weaken : StreamEntailment post weak) : StreamHoare strong circuit weak :=
  fun x admitted =>
    let ⟨defined, holds⟩ := hoare x (strengthen x admitted)
    ⟨defined, weaken _ holds⟩

/-- A route reads its output ports from its input ports. -/
theorem StreamHoare.route (indices : Fin m → Fin n) (post : StreamPredicate d m) :
    StreamHoare (fun x => post (x ∘ indices))
      (Streams.Circuit.route (basis := basis) indices) post :=
  fun _ admitted => ⟨trivial, admitted⟩

/-- The identity route preserves any predicate. -/
theorem StreamHoare.identity (pre : StreamPredicate d n) :
    StreamHoare pre (Streams.Circuit.route (basis := basis) id) pre :=
  fun _ admitted => ⟨trivial, admitted⟩

/-- Sequential wiring through an explicit intermediate predicate. This composes
circuits, not time intervals. -/
theorem StreamHoare.compose {pre : StreamPredicate d n} {first : Streams.Circuit basis d n m}
    {middle : StreamPredicate d m} {second : Streams.Circuit basis d m o}
    {post : StreamPredicate d o}
    (head : StreamHoare pre first middle) (tail : StreamHoare middle second post) :
    StreamHoare pre (.compose first second) post := by
  intro x admitted
  obtain ⟨defined, between⟩ := head x admitted
  obtain ⟨defined', holds⟩ := tail _ between
  exact ⟨⟨defined, defined'⟩, holds⟩

/-- Both factors, each on its own block of ports. -/
def Both (left : StreamPredicate d n) (right : StreamPredicate d k) :
    StreamPredicate d (n + k) :=
  fun x => left (Gimle.Asgard.Streams.left x) ∧ right (Gimle.Asgard.Streams.right x)

/-- Parallel circuits on the same axes and basis, each owning its ports. -/
theorem StreamHoare.parallel {pre₁ : StreamPredicate d n} {first : Streams.Circuit basis d n m}
    {post₁ : StreamPredicate d m} {pre₂ : StreamPredicate d k}
    {second : Streams.Circuit basis d k o} {post₂ : StreamPredicate d o}
    (left : StreamHoare pre₁ first post₁) (right : StreamHoare pre₂ second post₂) :
    StreamHoare (Both pre₁ pre₂) (.parallel first second) (Both post₁ post₂) := by
  intro x admitted
  obtain ⟨d₁, h₁⟩ := left _ admitted.1
  obtain ⟨d₂, h₂⟩ := right _ admitted.2
  refine ⟨⟨d₁, d₂⟩, ?_⟩
  simp only [Both, Streams.Circuit.value, left_append, right_append]
  exact ⟨h₁, h₂⟩

/-- Two circuits reading the same inputs, outputs side by side. -/
theorem StreamHoare.pair {pre : StreamPredicate d n} {first : Streams.Circuit basis d n m}
    {post₁ : StreamPredicate d m} {second : Streams.Circuit basis d n o}
    {post₂ : StreamPredicate d o}
    (left : StreamHoare pre first post₁) (right : StreamHoare pre second post₂) :
    StreamHoare pre (first.pair second) (Both post₁ post₂) := by
  intro x admitted
  obtain ⟨d₁, h₁⟩ := left x admitted
  obtain ⟨d₂, h₂⟩ := right x admitted
  refine ⟨(Streams.Circuit.pair_defined _ _ _).mpr ⟨d₁, d₂⟩, ?_⟩
  simp only [Both, Streams.Circuit.pair_value, left_append, right_append]
  exact ⟨h₁, h₂⟩

/-- Postconditions conjoin. -/
theorem StreamHoare.and {pre : StreamPredicate d n} {circuit : Streams.Circuit basis d n m}
    {first second : StreamPredicate d m}
    (left : StreamHoare pre circuit first) (right : StreamHoare pre circuit second) :
    StreamHoare pre circuit fun y => first y ∧ second y :=
  fun x admitted => ⟨(left x admitted).1, (left x admitted).2, (right x admitted).2⟩

/-- Preconditions disjoin. -/
theorem StreamHoare.or {first second : StreamPredicate d n} {circuit : Streams.Circuit basis d n m}
    {post : StreamPredicate d m}
    (left : StreamHoare first circuit post) (right : StreamHoare second circuit post) :
    StreamHoare (fun x => first x ∨ second x) circuit post := by
  rintro x (admitted | admitted)
  exacts [left x admitted, right x admitted]

/-- Contracts can be restated along equal predicates. -/
theorem StreamHoare.congr {pre pre' : StreamPredicate d n}
    {circuit : Streams.Circuit basis d n m} {post post' : StreamPredicate d m}
    (same_pre : StreamEquality pre pre') (same_post : StreamEquality post post') :
    StreamHoare pre circuit post ↔ StreamHoare pre' circuit post' :=
  ⟨fun hoare => hoare.consequence (fun x h => (same_pre x).mpr h) (fun y h => (same_post y).mp h),
    fun hoare => hoare.consequence (fun x h => (same_pre x).mp h) (fun y h => (same_post y).mpr h)⟩

/-- Relationally equivalent circuits have the same contracts. -/
theorem StreamHoare.substitute {pre : StreamPredicate d n}
    {first second : Streams.Circuit basis d n m} {post : StreamPredicate d m}
    (equivalent : first.Equivalent second) (hoare : StreamHoare pre first post) :
    StreamHoare pre second post := by
  rw [streamHoare_iff_rel] at hoare ⊢
  intro x admitted
  obtain ⟨⟨y, related⟩, every⟩ := hoare x admitted
  exact ⟨⟨y, (equivalent x y).mp related⟩,
    fun y related => every y ((equivalent x y).mpr related)⟩

/-- A compiled expression: defined where the expression is, with its value. -/
theorem StreamHoare.expr (expression : Expr basis d n) (post : StreamPredicate d 1) :
    StreamHoare (fun x => expression.Defined x ∧ post ![expression.value x])
      expression.compile post := by
  intro x ⟨defined, holds⟩
  exact ⟨(Expr.compile_defined _ _).mpr defined, by rw [Expr.compile_value]; exact holds⟩

/-! ### Reusable predicates -/

/-- The input or output is exactly this stream point. -/
def Equals (point : StreamPoint d n) : StreamPredicate d n := fun x => x = point

/-- Port `port` agrees with `profile` on the whole zero slice along `axis`: the
complete boundary profile, every coefficient with degree zero in that axis. -/
def Boundary (axis : Fin d) (port : Fin n) (profile : Stream d) : StreamPredicate d n :=
  fun x => ∀ index : Index d, index axis = 0 → x port index = profile index

/-- A boundary slice along an axis named in an Asgard stream context. -/
def NamedBoundary (context : Context) (axis : String) (port : Fin n)
    (profile : Stream context.axes.length) : StreamPredicate context.axes.length n :=
  fun x => ∃ found, context.axis axis = some found ∧ Boundary found port profile x

/-- Port `port` agrees with `stream` on the finite window `index < window`,
coordinatewise. Nothing is said outside the window. -/
def Window (window : Fin d → Nat) (port : Fin n) (stream : Stream d) :
    StreamPredicate d n :=
  fun x => truncate window (x port) = truncate window stream

/-- Two blocks, each equal to a point, make the appended point. This is what
`pair` produces, as the operation contracts take it. -/
theorem both_equals {a : StreamPoint d n} {b : StreamPoint d k} {y : StreamPoint d (n + k)} :
    Both (Equals a) (Equals b) y ↔ y = append a b := by
  constructor
  · rintro ⟨first, second⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have := congrFun first j
      simp only [Gimle.Asgard.Streams.left] at this
      simp [append, this]
    · have := congrFun second j
      simp only [Gimle.Asgard.Streams.right] at this
      simp [append, this]
  · rintro rfl
    exact ⟨left_append _ _, right_append _ _⟩

/-- A named boundary is the boundary along the axis the name resolves to. A
name the context does not resolve makes `NamedBoundary` false, so a contract
with it as precondition would be vacuous: discharge the lookup first. -/
theorem NamedBoundary.iff_boundary {context : Context} {name : String}
    {found : Fin context.axes.length} (resolved : context.axis name = some found)
    (port : Fin n) (profile : Stream context.axes.length)
    (x : StreamPoint context.axes.length n) :
    NamedBoundary context name port profile x ↔ Boundary found port profile x := by
  constructor
  · rintro ⟨other, again, holds⟩
    rw [resolved] at again
    cases again
    exact holds
  · exact fun holds => ⟨found, resolved, holds⟩

/-- Full equality gives any boundary slice… -/
theorem Equals.boundary {point : StreamPoint d n} (axis : Fin d) (port : Fin n) :
    StreamEntailment (Equals point) (Boundary axis port (point port)) := by
  rintro x rfl _ _
  rfl

/-- …and any window. The converse is false: see `Tests/Stream.lean`. -/
theorem Equals.window {point : StreamPoint d n} (window : Fin d → Nat) (port : Fin n) :
    StreamEntailment (Equals point) (Window window port (point port)) := by
  rintro x rfl
  rfl

/-! ### Transport through axis reindexing -/

/-- Reindex every port along an axis permutation. -/
noncomputable def reindexPoint {e : Nat} (p : Fin d ≃ Fin e) (x : StreamPoint d n) :
    StreamPoint e n :=
  fun i => reindex p (x i)

/-- A boundary slice along `axis` is the reindexed slice along `p axis`. -/
theorem boundary_reindex {e : Nat} (p : Fin d ≃ Fin e) (axis : Fin d) (port : Fin n)
    (profile : Stream d) (x : StreamPoint d n) :
    Boundary axis port profile x ↔
      Boundary (p axis) port (reindex p profile) (reindexPoint p x) := by
  constructor
  · intro holds index zero
    exact holds _ (by simpa [pullIndex] using zero)
  · intro holds index zero
    have := holds (pullIndex p.symm index) (by simpa [pullIndex] using zero)
    simpa [reindexPoint, reindex, pullIndex, Finsupp.ext_iff] using this

/-- A window moves with the axes, its bounds permuted by the inverse map. -/
theorem window_reindex {e : Nat} (p : Fin d ≃ Fin e) (window : Fin d → Nat)
    (port : Fin n) (stream : Stream d) (x : StreamPoint d n) :
    Window window port stream x ↔
      Window (fun j => window (p.symm j)) port (reindex p stream) (reindexPoint p x) := by
  unfold Window reindexPoint
  rw [← reindex_truncate, ← reindex_truncate]
  constructor
  · intro same; rw [same]
  · intro same
    have := congrArg (reindex p.symm) same
    simpa [reindex_inverse] using this

/-! ### Operation contracts, from Asgard's laws -/

/-- Differentiation along an axis. -/
theorem StreamHoare.derivative (axis : Fin d) (a : Stream d) :
    StreamHoare (Equals ![a]) (Streams.Circuit.unary (basis := basis) (.derivative axis))
      (Equals ![Gimle.Asgard.Streams.derivative basis axis a]) := by
  rintro x rfl
  exact ⟨trivial, rfl⟩

/-- **Integration keeps its whole boundary profile.** The output's zero slice
along the axis is the supplied boundary, and differentiating it gives back the
integrand. -/
theorem StreamHoare.integral (axis : Fin d) (a profile : Stream d) :
    StreamHoare (Equals ![a, profile]) (Streams.Circuit.binary (basis := basis) (.integral axis))
      fun y => Boundary axis 0 profile y ∧
        Gimle.Asgard.Streams.derivative basis axis (y 0) = a := by
  rintro x rfl
  refine ⟨trivial, ?_, ?_⟩
  · intro index zero
    exact integral_boundary basis axis a profile index zero
  · exact derivative_integral basis axis a profile

/-- Integration against any boundary port with the given zero slice: only the
slice is read, and it is kept whole. -/
theorem StreamHoare.integralFrom (axis : Fin d) (a profile : Stream d) :
    StreamHoare (fun x => x 0 = a ∧ Boundary axis 1 profile x)
      (Streams.Circuit.binary (basis := basis) (.integral axis))
      fun y => Boundary axis 0 profile y ∧
        Gimle.Asgard.Streams.derivative basis axis (y 0) = a := by
  rintro x ⟨integrand, slice⟩
  refine ⟨trivial, ?_, ?_⟩
  · intro index zero
    show Gimle.Asgard.Streams.integral basis axis (x 0) (x 1) index = profile index
    rw [integral_boundary basis axis _ _ index zero]
    exact slice index zero
  · show Gimle.Asgard.Streams.derivative basis axis
      (Gimle.Asgard.Streams.integral basis axis (x 0) (x 1)) = a
    rw [derivative_integral]
    exact integrand

/-- **Product in the declared basis.** Decoded, it is the product of the decoded
factors: ordinary power-series product for OGF, factorial-conjugated for EGF. -/
theorem StreamHoare.product (a b : Stream d) :
    StreamHoare (Equals ![a, b]) (Streams.Circuit.binary (basis := basis) .product)
      fun y => decode basis (y 0) = decode basis a * decode basis b := by
  rintro x rfl
  exact ⟨trivial, decode_product basis a b⟩

/-- **An antiderivative is fixed by its boundary.** A stream whose derivative
along an axis is `a`, and whose zero slice along it is `profile`'s, is the
integral of `a` with that boundary. -/
theorem eq_integral_of_boundary (axis : Fin d) (a profile y : Stream d)
    (boundary : ∀ index : Index d, index axis = 0 → y index = profile index)
    (derivative : Gimle.Asgard.Streams.derivative basis axis y = a) :
    y = Gimle.Asgard.Streams.integral basis axis a profile := by
  funext index
  by_cases zero : index axis = 0
  · rw [integral_boundary basis axis a profile index zero, boundary index zero]
  · have pos : 0 < index axis := Nat.pos_of_ne_zero zero
    have back : (index.update axis (index axis - 1)).update axis
        ((index.update axis (index axis - 1)) axis + 1) = index := by
      ext i
      by_cases same : i = axis
      · subst same; simp [Finsupp.update_apply]; omega
      · simp [Finsupp.update_apply, same]
    have at_below := congrFun derivative (index.update axis (index axis - 1))
    have cast : ((index axis - 1 : ℕ) : ℚ) + 1 = index axis := by
      exact_mod_cast Nat.sub_add_cancel pos
    have nonzero : (index axis : ℚ) ≠ 0 := by exact_mod_cast zero
    have below_axis : (index.update axis (index axis - 1)) axis = index axis - 1 := by simp
    cases basis with
    | ogf =>
        simp only [Gimle.Asgard.Streams.derivative] at at_below
        rw [back, below_axis, cast] at at_below
        simp only [Gimle.Asgard.Streams.integral, zero, if_false]
        rw [← at_below]
        field_simp
    | egf =>
        simp only [Gimle.Asgard.Streams.derivative] at at_below
        rw [back] at at_below
        simp only [Gimle.Asgard.Streams.integral, zero, if_false]
        exact at_below

/-- Series substitution is total exactly on inner streams with zero constant. -/
theorem StreamHoare.seriesCompose (axis : Fin d) (outer inner : Stream d)
    (valid : CanCompose basis inner) :
    StreamHoare (Equals ![outer, inner])
      (Streams.Circuit.binary (basis := basis) (.seriesCompose axis))
      (Equals ![Gimle.Asgard.Streams.seriesCompose basis axis outer inner]) := by
  rintro x rfl
  exact ⟨valid, rfl⟩

#print axioms streamHoare_iff_rel
#print axioms StreamHoare.compose
#print axioms StreamHoare.parallel
#print axioms StreamHoare.pair
#print axioms StreamHoare.substitute
#print axioms StreamHoare.integral
#print axioms boundary_reindex
#print axioms window_reindex

end Gimle.Forseti.Stream
