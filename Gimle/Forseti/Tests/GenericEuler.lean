import Gimle.Forseti.Euler

/-! Generic classical properties belong to the actual Fourier circuit output. -/
namespace Gimle.Forseti.Tests.GenericEuler

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.TrigStream Gimle.Forseti

example (b : TrigStream) (hz : MeanZero (b 0)) (he : IsEven (b 0))
    {K : ℕ} (hs : SizeLE K (b 0)) {M ρ r : ℝ}
    (hg : GeometricBound (NS.stream .ogf 0 b) M ρ)
    (hp : 0 < ρ) (hr : 0 ≤ r) (hq : ρ * r < 1) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = b 0) (Euler.Certified b r) :=
  Euler.contract b hz he hs hg hp hr hq

/-- Zero data have a classical output on every finite closed interval. -/
example (b : TrigStream) (hz : b 0 = 0) (r : ℝ) (hr : 0 ≤ r) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = b 0) (Euler.Certified b r) :=
  Euler.zero_contract b hz hr

/-- Symmetry is checked on aggregate coefficients, including duplicate entries. -/
example : IsEven (Table.toTrig [((1, 0), 1), ((1, 0), -1)]) :=
  Euler.Table.isEven (by decide +kernel)

example : MeanZero (Table.toTrig [((0, 0), 1), ((0, 0), -1)]) :=
  Euler.Table.meanZero (by decide +kernel)

example : ¬ Euler.Table.Symmetric [((1, 0), 1)] := by decide +kernel

example : ¬ Euler.Table.ZeroMean [((0, 0), 1)] := by decide +kernel

/-- The strict certificate condition excludes its convergence boundary. -/
example : ¬ ((144 : ℝ) * (1 / 144) < 1) := by norm_num

/-- Different frequencies and amplitudes from the original three-mode example. -/
def alternateTable : Torus.Table :=
  [((1, 0), 1 / 2), ((-1, 0), 1 / 2), ((0, 2), 1 / 4), ((0, -2), 1 / 4)]

noncomputable def alternateStart : TrigStream := fun _ => Torus.Table.toTrig alternateTable

theorem alternate_contract :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = alternateStart 0)
      (Euler.Certified alternateStart (1 / 2160)) :=
  Euler.Table.contract alternateTable (by decide +kernel) (by decide +kernel)
    (K := 2) (by decide) (by decide) (L := 3 / 2) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

theorem alternate_geometric : GeometricBound (NS.stream .ogf 0 alternateStart) (9 / 2) 216 := by
  have h := NS.euler_geometricBound alternateStart (K := 2) (by decide)
    (Torus.Table.sizeLE_toTrig (by decide)) (L := 3 / 2)
    ((Torus.Table.l1_le_absSum _).trans (le_of_eq (by decide +kernel)))
  norm_num at h
  exact h

/-- The requested truncation and the classical PDE are one circuit postcondition. -/
example : Fourier.Contract (NS.vorticityCircuit .ogf 0)
    (fun input => input 0 0 = alternateStart 0)
    (fun output => Euler.Certified alternateStart (1 / 2160) output ∧
      TruncationBound (output 0) (1 / 2160) 3 (1 / 100)) := by
  apply Euler.contract_with alternateStart alternate_contract
  exact (truncationBound alternate_geometric (by norm_num) (by norm_num) 3).mono (by norm_num)

/-- Both endpoints, not merely the interior, are classical. -/
example (output : Gimle.Asgard.Streams.Fourier.Point 1)
    (h : Euler.Certified alternateStart (1 / 2160) output) (x : ℝ × ℝ) :
    NS.IsClassicalSolution (output 0) (1 / 2160) x ∧
    NS.IsClassicalSolution (output 0) (-1 / 2160) x :=
  ⟨h.classical _ x (by norm_num), h.classical _ x (by norm_num)⟩

/-- Radius zero still certifies the initial point and its actual derivatives. -/
example : Fourier.Contract (NS.vorticityCircuit .ogf 0)
    (fun input => input 0 0 = alternateStart 0) (Euler.Certified alternateStart 0) :=
  Euler.Table.contract alternateTable (by decide +kernel) (by decide +kernel)
    (K := 2) (by decide) (by decide) (L := 3 / 2) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

/-- Higher boundary coefficients remain free, even when they are nonzero. -/
noncomputable def noisyBoundary : TrigStream :=
  fun n => if n = 0 then alternateStart 0 else cosine (3, 4)

example : ∃ output, (NS.vorticityCircuit .ogf 0).Rel ![noisyBoundary] output ∧
    Euler.Certified alternateStart (1 / 2160) output :=
  alternate_contract.exists_safe _ rfl

/-- A false postcondition is impossible; the feedback contract is not vacuous. -/
example : ¬ Fourier.Contract (NS.vorticityCircuit .ogf 0)
    (fun input => input 0 0 = alternateStart 0) (fun _ => False) := by
  intro h
  obtain ⟨_, _, hf⟩ := h.exists_safe ![alternateStart] rfl
  exact hf

/-- A different initial slice cannot masquerade as this certified solution. -/
example : ¬ ∃ output, (NS.vorticityCircuit .ogf 0).Rel ![fun _ => 0] output ∧
    Euler.Certified alternateStart (1 / 2160) output := by
  rintro ⟨output, related, certified⟩
  have same := (NS.vorticityCircuit_rel_iff .ogf 0 (fun _ => 0) output).mp related
  have initial := congrArg (fun s => s 0 (1, 0)) certified.formal_eq
  rw [same] at initial
  norm_num [NS.stream_slice, alternateStart, alternateTable, Torus.Table.toTrig_apply,
    Torus.Table.coeff] at initial

/-- Replacing the feedback circuit by a wire cannot inherit its guarantee. -/
example : ¬ Fourier.Contract
    (Gimle.Asgard.Streams.Fourier.Circuit.route (basis := .ogf) (n := 1) id)
    (fun input => input 0 0 = alternateStart 0)
    (Euler.Certified alternateStart (1 / 2160)) := by
  intro h
  have hc := h.holds ![noisyBoundary] rfl ![noisyBoundary] rfl
  have eq := congrArg (fun s => s 1 (3, 4)) hc.formal_eq
  have absent : NS.stream .ogf 0 alternateStart 1 (3, 4) = 0 := by
    rw [NS.stream_coeff 0 alternateTable alternateStart rfl]
    decide +kernel
  rw [absent] at eq
  norm_num [noisyBoundary, cosine, Finsupp.single_apply] at eq

/-- Cancellation includes the zero mode and works at an arbitrarily large radius. -/
example : Fourier.Contract (NS.vorticityCircuit .ogf 0)
    (fun input => input 0 0 = Torus.Table.toTrig
      [((0, 0), 1), ((0, 0), -1), ((2, 1), 3), ((2, 1), -3)])
    (Euler.Certified (fun _ => Torus.Table.toTrig
      [((0, 0), 1), ((0, 0), -1), ((2, 1), 3), ((2, 1), -3)]) 1000000) :=
  Euler.Table.zero_contract _ (by decide +kernel) (by norm_num)

/--
info: 'Gimle.Forseti.Euler.contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Euler.contract

/--
info: 'Gimle.Forseti.Euler.Table.zero_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms Euler.Table.zero_contract

end Gimle.Forseti.Tests.GenericEuler
