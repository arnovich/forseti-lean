import Gimle.Forseti.Fourier
import Gimle.Asgard.Examples.EulerBand

/-! Three-mode Euler, certified as a property of a typed Asgard feedback circuit.
The precondition fixes only initial vorticity. The postcondition concerns every
output, and the contract includes formal existence and uniqueness. Classical
uniqueness among arbitrary real fields, a global-in-time solution, and convergence
of the viscous time series are not conclusions of this contract.
-/
namespace Gimle.Forseti.Examples.EulerContract

open Gimle.Asgard.Streams Gimle.Asgard.Streams.TrigStream
open Gimle.Asgard.Examples.EulerThreeMode Gimle.Asgard.Examples.EulerBand
open Gimle.Forseti.Fourier

/-- Euler's Fourier feedback circuit; viscosity is exactly zero. -/
def circuit := NS.vorticityCircuit .ogf 0

/-- Only the time-zero slice is prescribed; the solution is not an input. -/
def admitted : Predicate 1 := fun input => input 0 0 = ω₀

/-- The actual output is the formal solution, with its certified analytic properties. -/
def certified : Predicate 1 := fun output =>
  output 0 = NS.stream .ogf 0 start ∧
  (∀ n, Torus.MeanZero (output 0 n) ∧ Torus.IsEven (output 0 n)) ∧
  TruncationBound (output 0) (1 / 6480) 3 (1 / 100) ∧
  (∀ (t : ℝ) (x : ℝ × ℝ), |t| ≤ 1 / 6480 →
    |analyticField (output 0) t x -
      (Real.cos x.1 + Real.cos (x.1 + x.2) + Real.cos (2 * x.1 + x.2))| ≤ 1 / 50) ∧
  (∀ (t : ℝ) (x : ℝ × ℝ), |t| < 1 / 648 → NS.IsClassicalSolution (output 0) t x)

/-- A complete circuit contract: formal existence, uniqueness, and the certified
band, truncation and local classical Euler property of every output. -/
theorem euler_contract : Contract circuit admitted certified := by
  apply (solution_contract .ogf 0 start).consequence (fun _ h => h)
  intro output h
  subst output
  refine ⟨rfl, fun n => ⟨coeff_meanZero 0 n, coeff_isEven 0 n⟩, truncation, ?_, ?_⟩
  · exact fun _ x ht => band x ht
  · exact fun _ x ht => classical ht x

#print axioms euler_contract

end Gimle.Forseti.Examples.EulerContract
