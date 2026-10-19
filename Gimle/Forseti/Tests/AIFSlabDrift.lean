import Gimle.Forseti.Examples.AIFCertifiedCell

/-! The checks behind a certified AIF cell reject a drift table bound to the wrong
error extreme, an altered coefficient and a square certificate for another matrix;
the mesh corollary composes the certified cell; and the assembled theorems use only
the standard axioms. -/
namespace Gimle.Forseti.Tests.AIFSlabDrift
open Gimle.Forseti.LinearEnergy Gimle.Forseti.RationalPolynomial
open Gimle.Forseti.Examples Gimle.Forseti.Examples.AIFCertifiedCellData
open Gimle.Forseti.Examples.AIFMesh

-- Each table is bound to its own extreme. Swapping them is rejected in row and
-- column four, the only entries that depend on the error value.
set_option maxRecDepth 100000 in
example : equivalent (AIFPolynomialBinding.block slab (-3/200) 4 4)
    (AIFPolynomialBinding.tensor Positive.coefficients 4 4) = false := by
  decide +kernel

-- One coefficient changed by one in a single Bernstein matrix.
private def altered : Fin 10 → Fin 4 → QMatrix 5 := fun a b i j =>
  if a = 0 ∧ b = 0 ∧ i = 1 ∧ j = 1 then Negative.coefficients a b i j + 1
  else Negative.coefficients a b i j

set_option maxRecDepth 100000 in
example : equivalent (AIFPolynomialBinding.block slab (-3/200) 1 1)
    (AIFPolynomialBinding.tensor altered 1 1) = false := by
  decide +kernel

-- A checked square certificate does not represent the other table's matrix.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
example : ¬ (Negative.certificates 0 0).Represents (Positive.coefficients 0 0) := by
  unfold WeightedSquares.Represents
  decide +kernel

/-- The certified cell as the single interval of a one-cell mesh. -/
def cellMesh : Mesh 1 1 where
  times := ![0, 1/200]
  edges := ![8, 17/2]
  nodes := fun _ => ![
    ⟨slab.loStart, slab.hiStart, slab.loStartSlope, slab.hiStartSlope,
      slab.startMetric, slab.startMetricSlope⟩,
    ⟨slab.loEnd, slab.hiEnd, slab.loEndSlope, slab.hiEndSlope,
      slab.endMetric, slab.endMetricSlope⟩]

theorem cellMesh_slab : cellMesh.slab 0 0 = slab := by
  simp only [Mesh.slab, cellMesh, slab]
  norm_num

-- The mesh corollary needs no drift hypothesis once each cell is certified.
theorem cell_mesh_invariant (p : ℝ) (hp : p ∈ Set.Icc (8 : ℝ) (17/2))
    (state : ℝ → Fin 4 → ℝ)
    (derivative : ∀ t ∈ Set.Icc (0 : ℝ) (1/200), ∀ j,
      HasDerivWithinAt (fun z => state z j) (AIFDriftModel.field p (state t) j)
        (Set.Icc (0 : ℝ) (1/200)) t)
    (initial : tubeEnergy slab 0 p (state 0) ≤ 1/40000) :
    ∀ t ∈ Set.Icc (0 : ℝ) (1/200), tubeEnergy slab t p (state t) ≤ 1/40000 := by
  have h := AIFSlabDrift.mesh_invariant_of_certificates cellMesh 0
    (by intro i; fin_cases i; norm_num [Mesh.slab, cellMesh])
    (by norm_num [cellMesh]) p (by norm_num [cellMesh]; exact hp) state
    (by intro i; fin_cases i; norm_num [cellMesh]; exact fun t h0 h1 => derivative t ⟨h0, h1⟩)
    (fun i => by rw [Fin.fin_one_eq_zero i, cellMesh_slab]; exact AIFCertifiedCell.certificates)
    (by rw [cellMesh_slab]; norm_num [cellMesh]; exact initial)
  intro t ht
  have := h 0 t (by norm_num [cellMesh]; exact ht)
  rwa [cellMesh_slab] at this

/-- info: 'Gimle.Forseti.Examples.AIFSlabDrift.drift_in_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AIFSlabDrift.drift_in_tube

/--
info: 'Gimle.Forseti.Examples.AIFSlabDrift.BlockCertificate.nonnegative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AIFSlabDrift.BlockCertificate.nonnegative

/--
info: 'Gimle.Forseti.Examples.AIFSlabDrift.mesh_invariant_of_certificates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AIFSlabDrift.mesh_invariant_of_certificates

/-- info: 'Gimle.Forseti.Tests.AIFSlabDrift.cell_mesh_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cell_mesh_invariant

/-- info: 'Gimle.Forseti.Examples.AIFCertifiedCell.solution_in_tube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AIFCertifiedCell.solution_in_tube

/--
info: 'Gimle.Forseti.Examples.AIFCertifiedCell.solution_error_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AIFCertifiedCell.solution_error_bound

end Gimle.Forseti.Tests.AIFSlabDrift
