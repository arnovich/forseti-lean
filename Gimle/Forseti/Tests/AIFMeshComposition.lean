import Gimle.Forseti.Examples.AIFMeshComposition
import Gimle.Forseti.Tests.AIFMesh

/-! Finite propagation tests: endpoint joins and complete local coverage matter. -/
namespace Gimle.Forseti.Tests.AIFMeshComposition
open Gimle.Forseti.Examples AIFMesh AIFMeshComposition

-- A single interval needs no join; its complete local rule suffices.
theorem one_interval (value : ℝ → ℝ)
    (local_rule : value 0 ≤ 3 → ∀ t ∈ Set.Icc (0 : ℝ) 2, value t ≤ 3)
    (initial : value 0 ≤ 3) : ∀ t ∈ Set.Icc (0 : ℝ) 2, value t ≤ 3 := by
  have h := chain_invariant (n := 0) (fun _ t => value t) (![0,2]) 3
    (by intro i; fin_cases i; norm_num)
    (by intro i; exact Fin.elim0 i)
    (by intro i; fin_cases i; exact local_rule) initial
  exact h 0

-- At a shared endpoint, the same state has the same energy from either side.
example (p : ℝ) (state : ℝ → Fin 4 → ℝ)
    (local_rule : ∀ i : Fin 2,
      tubeEnergy (AIFMesh.mesh.slab 0 i) (AIFMesh.mesh.times i.castSucc) p
        (state (AIFMesh.mesh.times i.castSucc)) ≤ 1/40000 →
      ∀ t ∈ Set.Icc (AIFMesh.mesh.times i.castSucc : ℝ) (AIFMesh.mesh.times i.succ : ℝ),
        tubeEnergy (AIFMesh.mesh.slab 0 i) t p (state t) ≤ 1/40000)
    (initial : tubeEnergy (AIFMesh.mesh.slab 0 0) 0 p (state 0) ≤ 1/40000) :
    ∀ i : Fin 2, ∀ t ∈ Set.Icc (AIFMesh.mesh.times i.castSucc : ℝ)
      (AIFMesh.mesh.times i.succ : ℝ),
      tubeEnergy (AIFMesh.mesh.slab 0 i) t p (state t) ≤ 1/40000 := by
  apply mesh_invariant_of_local AIFMesh.mesh 0
    (by intro i; fin_cases i <;> norm_num [Mesh.slab, AIFMesh.mesh, Matrix.cons_val_two]) p state local_rule
  simpa [AIFMesh.mesh] using initial

-- Without energy compatibility, local rules and initial membership are insufficient.
theorem broken_join_can_escape :
    (∀ i : Fin 2, (i : ℝ) ≤ 0 → ∀ t ∈ Set.Icc (i : ℝ) ((i : ℝ)+1), (i : ℝ) ≤ 0) ∧
    ((0 : Fin 2) : ℝ) ≤ 0 ∧
    ¬ (∀ i : Fin 2, ∀ t ∈ Set.Icc (i : ℝ) ((i : ℝ)+1), (i : ℝ) ≤ 0) := by
  refine ⟨fun _ h _ _ => h, by norm_num, ?_⟩
  intro h
  have := h 1 1 (by norm_num)
  norm_num at this

-- Span coverage retains the last closed endpoint together with its energy bound.
example (p : ℝ) (state : ℝ → Fin 4 → ℝ)
    (invariant : ∀ i : Fin 2, ∀ t ∈ Set.Icc
      (AIFMesh.mesh.times i.castSucc : ℝ) (AIFMesh.mesh.times i.succ : ℝ),
      tubeEnergy (AIFMesh.mesh.slab 0 i) t p (state t) ≤ 1/40000) :
    ∃ i : Fin 2, (1/40 : ℝ) ∈ Set.Icc (AIFMesh.mesh.times i.castSucc : ℝ)
      (AIFMesh.mesh.times i.succ : ℝ) ∧
      tubeEnergy (AIFMesh.mesh.slab 0 i) (1/40) p (state (1/40)) ≤ 1/40000 :=
  covered_energy AIFMesh.mesh 0 p state invariant (1/40)
    (by norm_num [AIFMesh.mesh, Fin.last, Matrix.cons_val_two])

-- The startup state can equal both rational center endpoints for any metric.
example (d : AIFSlabModel.Slab) (x : Fin 4 → ℚ) (p : ℝ) :
    tubeEnergy { d with loStart := x, hiStart := x } d.tStart p
      (fun i => (x i : ℝ)) = 0 :=
  initial_energy_of_centers _ x rfl rfl p

#print axioms one_interval
#print axioms broken_join_can_escape
end Gimle.Forseti.Tests.AIFMeshComposition
