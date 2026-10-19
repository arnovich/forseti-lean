import Gimle.Forseti.Examples.AIFInvariance

/-! Propagation of a moving-tube energy bound across a time mesh for the antithetic
integral feedback (AIF) drift model, at one fixed parameter in a mesh column.
Each slab carries a moving center and a metric; the tube is the set where the
metric distance from the center is at most `1/40000`. Adjacent slabs share exact
endpoint data, so the bound passes from one slab to the next. Every cell needs a
supplied drift inequality: inside the tube the energy rate is at most
`(1/100)(1/40000 − energy) − 1/16000000`. Those inequalities and the solution's
derivatives are hypotheses here; no certificate for them is included. -/
namespace Gimle.Forseti.Examples.AIFMeshComposition
open Gimle.Forseti.BernsteinMatrix AIFSlabModel AIFMesh

/-- A finite chain of local sublevel rules propagates one initial bound when
adjacent energies agree at their shared endpoint. -/
theorem chain_invariant {n : Nat} (energy : Fin (n + 1) → ℝ → ℝ)
    (times : Fin (n + 2) → ℝ) (bound : ℝ)
    (ordered : ∀ i : Fin (n + 1), times i.castSucc ≤ times i.succ)
    (joins : ∀ i : Fin n,
      energy i.castSucc (times i.succ.castSucc) = energy i.succ (times i.succ.castSucc))
    (local_rule : ∀ i, energy i (times i.castSucc) ≤ bound →
      ∀ t ∈ Set.Icc (times i.castSucc) (times i.succ), energy i t ≤ bound)
    (initial : energy 0 (times 0) ≤ bound) :
    ∀ i, ∀ t ∈ Set.Icc (times i.castSucc) (times i.succ), energy i t ≤ bound := by
  intro i
  induction i using Fin.induction with
  | zero => exact local_rule 0 initial
  | succ i ih =>
    apply local_rule i.succ
    rw [← joins i]
    exact ih _ ⟨ordered i.castSucc, le_rfl⟩

/-- Shared mesh nodes supply the exact endpoint energy equality needed by the
finite propagation rule; one local rule is required for every interval. -/
theorem mesh_invariant_of_local {nt nb : Nat} (m : Mesh (nt + 1) nb) (b : Fin nb)
    (widths : ∀ i, 0 < (m.slab b i).step) (p : ℝ) (state : ℝ → Fin 4 → ℝ)
    (local_rule : ∀ i,
      tubeEnergy (m.slab b i) (m.times i.castSucc) p (state (m.times i.castSucc)) ≤ 1/40000 →
      ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ),
        tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000)
    (initial : tubeEnergy (m.slab b 0) (m.times 0) p (state (m.times 0)) ≤ 1/40000) :
    ∀ i, ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ),
      tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000 := by
  apply chain_invariant (fun i t => tubeEnergy (m.slab b i) t p (state t))
    (fun j => (m.times j : ℝ)) (1/40000) _ _ local_rule initial
  · intro i
    have h := widths i
    change 0 < m.times i.succ - m.times i.castSucc at h
    exact_mod_cast (sub_pos.mp h).le
  · intro i
    exact (m.joins b i.castSucc i.succ rfl).tubeEnergy_eq
      (ne_of_gt (widths i.castSucc)) (ne_of_gt (widths i.succ)) p _

/-- Compose checked in-tube drift on every cell of one fixed parameter bin.
The conclusion is along a supplied trajectory, not an existence statement. -/
theorem mesh_invariant {nt nb : Nat} (m : Mesh (nt + 1) nb) (b : Fin nb)
    (widths : ∀ i, 0 < (m.slab b i).step)
    (eta_ordered : m.edges b.castSucc < m.edges b.succ)
    (p : ℝ) (hp : p ∈ Set.Icc (m.edges b.castSucc : ℝ) (m.edges b.succ : ℝ))
    (state : ℝ → Fin 4 → ℝ)
    (derivative : ∀ i : Fin (nt + 1), ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ), ∀ j,
      HasDerivWithinAt (fun z => state z j) (AIFDriftModel.field p (state t) j)
        (Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ)) t)
    (drift : ∀ (i : Fin (nt + 1)) t q e,
      t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ) →
      q ∈ Set.Icc (m.edges b.castSucc : ℝ) (m.edges b.succ : ℝ) →
      matrixForm (metric (m.slab b i) (timeCoordinate (m.slab b i) t)) e ≤ 1/40000 →
      energyRate (m.slab b i) (timeCoordinate (m.slab b i) t)
        (etaCoordinate (m.slab b i) q) e ≤
        (1/100) * (1/40000 - matrixForm
          (metric (m.slab b i) (timeCoordinate (m.slab b i) t)) e) - 1/16000000)
    (initial : tubeEnergy (m.slab b 0) (m.times 0) p (state (m.times 0)) ≤ 1/40000) :
    ∀ i, ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ),
      tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000 := by
  apply mesh_invariant_of_local m b widths p state _ initial
  intro i hi
  have hs : ((m.slab b i).tStart : ℝ) = (m.times i.castSucc : ℝ) := rfl
  have he : (m.times i.castSucc : ℝ) + (m.slab b i).step = (m.times i.succ : ℝ) := by
    simp [Mesh.slab]
  have hlo : (m.slab b i).etaLo = m.edges b.castSucc := rfl
  have hhi : (m.slab b i).etaHi = m.edges b.succ := rfl
  have h := AIFInvariance.tube_invariant (m.slab b i) (widths i) eta_ordered p hp state
    (by simpa only [hs, he] using derivative i)
    (by simpa only [hs, he, hlo, hhi] using drift i) hi
  simpa only [hs, he] using h

/-- Every time in the mesh span has a cell carrying the propagated energy bound. -/
theorem covered_energy {nt nb : Nat} (m : Mesh (nt + 1) nb) (b : Fin nb)
    (p : ℝ) (state : ℝ → Fin 4 → ℝ)
    (invariant : ∀ i, ∀ t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ),
      tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000)
    (t : ℝ) (ht : t ∈ Set.Icc (m.times 0 : ℝ) (m.times (Fin.last (nt + 1)) : ℝ)) :
    ∃ i, t ∈ Set.Icc (m.times i.castSucc : ℝ) (m.times i.succ : ℝ) ∧
      tubeEnergy (m.slab b i) t p (state t) ≤ 1/40000 := by
  obtain ⟨i, hi⟩ := interval_covered nt (fun j => (m.times j : ℝ)) t ht
  exact ⟨i, hi, invariant i t hi⟩

/-- Coincident endpoint centers give exact zero initial energy for every parameter. -/
theorem initial_energy_of_centers (d : Slab) (x : Fin 4 → ℚ)
    (lo : d.loStart = x) (hi : d.hiStart = x) (p : ℝ) :
    tubeEnergy d d.tStart p (fun i => (x i : ℝ)) = 0 := by
  simp [tubeEnergy, timeCoordinate, center, hermite, lo, hi, matrixForm]

#print axioms chain_invariant
#print axioms mesh_invariant_of_local
#print axioms mesh_invariant
#print axioms covered_energy
#print axioms initial_energy_of_centers
end Gimle.Forseti.Examples.AIFMeshComposition
