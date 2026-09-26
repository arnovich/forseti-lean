import Gimle.Forseti.Stream
import Gimle.Asgard.Examples.FormalHeat

/-! The formal two-axis heat circuit as a total stream contract.

Asgard's `FormalHeat.circuit_behavior` says the compiled circuit relates the
inputs `[u, boundary, unused]` to `[u_xx, u]` for the formal heat solution
`u = x² + 2t` on axes `[t, x]` (OGF). Here the same compiled circuit gets a
*total* contract: every input whose first two ports are `u` and its boundary
profile, whatever the unused third port holds, is in the domain, and its output
is `[u_xx, u]` with the boundary profile preserved along `t`.

It is derived with the general rules — `StreamHoare.pair` over the two compiled
expressions, `StreamHoare.expr`, `route`, `compose` and `integralFrom` — and
Asgard's own identities `heat_space`, `reconstructed` and `heat_boundary`, not
by re-evaluating the circuit by hand.
-/

namespace Gimle.Forseti.Examples.FormalHeatContract

open Gimle.Asgard
open Gimle.Asgard.Streams
open Gimle.Asgard.Examples.FormalHeat
open Gimle.Forseti.Stream

/-- Inputs: `u`, and a boundary port whose zero slice along `t` is the
declared profile `x²`; the rest of that port and the third port are free. -/
def admitted : StreamPredicate 2 3 := fun x => x 0 = heat ∧ Boundary 0 1 boundary x

/-- **The compiled heat circuit is total on its admitted inputs**, with output
`[u_xx, u] = [2, x² + 2t]` and the boundary profile kept along `t`. The second
output is identified by `eq_integral_of_boundary`: it has the derivative and
the boundary slice of `u`, so it is `u`. -/
theorem heat_contract :
    StreamHoare admitted circuit fun y => y = ![two, heat] ∧ Boundary 0 1 boundary y := by
  have space : StreamHoare admitted rhs.compile (Equals ![two]) :=
    (StreamHoare.expr rhs _).consequence
      (fun x ⟨u, _⟩ => ⟨trivial, by
        simp [Equals, rhs, Expr.value, Unary.value, u, heat_space]⟩)
      (fun _ holds => holds)
  have profile : StreamHoare admitted
      (Expr.input (basis := .ogf) (d := 2) (n := 3) 1).compile (Boundary 0 0 boundary) :=
    (StreamHoare.route _ _).consequence (fun _ admit => admit.2) (fun _ holds => holds)
  have integrand : StreamHoare admitted (rhs.compile.pair (Expr.input 1).compile)
      fun z => z 0 = two ∧ Boundary 0 1 boundary z :=
    (space.pair profile).consequence (fun _ admit => admit)
      (fun _ ⟨first, second⟩ => ⟨congrFun first 0, second⟩)
  have rebuild : StreamHoare admitted rebuilt.compile fun y => y 0 = heat :=
    (integrand.compose (StreamHoare.integralFrom 0 two boundary)).consequence
      (fun _ admit => admit)
      (fun y ⟨kept, derivative⟩ => by
        rw [← reconstructed]
        exact eq_integral_of_boundary 0 two boundary (y 0) kept derivative)
  refine (space.pair rebuild).consequence (fun _ admit => admit) ?_
  rintro y ⟨first, second⟩
  have point : y = ![two, heat] := by
    funext i
    fin_cases i
    · exact congrFun first 0
    · exact second
  exact ⟨point, fun index zero => by rw [point]; exact heat_boundary index zero⟩

/-- The unused port really is arbitrary: any third stream is admitted. -/
example (unused : Stream 2) : circuit.Defined ![heat, boundary, unused] ∧
    circuit.value ![heat, boundary, unused] = ![two, heat] :=
  let ⟨defined, holds, _⟩ := heat_contract _ ⟨rfl, fun _ _ => rfl⟩
  ⟨defined, holds⟩

/-- The relational form, as Asgard states the behaviour. -/
example (unused : Stream 2) : circuit.Rel ![heat, boundary, unused] ![two, heat] := by
  obtain ⟨⟨y, related⟩, every⟩ :=
    (streamHoare_iff_rel _ _ _).mp heat_contract ![heat, boundary, unused]
      ⟨rfl, fun _ _ => rfl⟩
  exact (every y related).1 ▸ related

#print axioms heat_contract

end Gimle.Forseti.Examples.FormalHeatContract
