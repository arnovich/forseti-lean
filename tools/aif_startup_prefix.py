#!/usr/bin/env python3
"""Emit conditional startup-prefix invariance for the compiled AIF circuit."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Emit the fixed checked-cell composition; Lean replay supplies proof authority."""
    source = """import Gimle.Forseti.Examples.AIFCircuitTransport
import Gimle.Forseti.Examples.AIFStartupInitial
import Gimle.Forseti.Examples.AIFMeshBindingBin0Slab0
import Gimle.Forseti.Examples.AIFMeshBindingBin7Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin1Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin2Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin3Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin4Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin5Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin6Slab0
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab1
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab2
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab3
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab4
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab5
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab6
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab7
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab8
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab9
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab10
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab11
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab12
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab13
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab14
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab15
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab16
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab17
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab18
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab19
import Gimle.Forseti.Examples.AIFPolynomialMeshBindingBin0Slab20

/-! Conditional invariance of concrete startup prefixes for the compiled circuit.
All included cells have checked drift proofs; no unproved later cell is assumed. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Gimle.Forseti.Examples.AIFStartupPrefix
open AIFMesh AIFSlabModel AIFPhysicalCoordinates Gimle.Forseti.BernsteinMatrix

noncomputable def prefixMesh (n : Nat) (hn : n ≤ 370) : Mesh n 8 where
  times i := AIFCandidateMesh.mesh.times ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hn)⟩
  edges := AIFCandidateMesh.mesh.edges
  nodes b i := AIFCandidateMesh.mesh.nodes b ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hn)⟩

theorem prefix_slab (n : Nat) (hn : n ≤ 370) (b : Fin 8) (i : Fin n) :
    (prefixMesh n hn).slab b i =
      AIFCandidateMesh.mesh.slab b ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ := rfl

theorem times_nonnegative : ∀ i : Fin 371, 0 ≤ AIFMeshGeometry.times i := by
  decide +kernel

/-- A checked drift obligation for one concrete full-mesh cell. -/
def CellDrift (b : Fin 8) (i : Fin 370) : Prop :=
  ∀ t p (e : Fin 4 → ℝ),
    t ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b i).tStart : ℝ)
      (((AIFCandidateMesh.mesh.slab b i).tStart : ℝ) + (AIFCandidateMesh.mesh.slab b i).step) →
    p ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b i).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab b i).etaHi : ℝ) →
    matrixForm (metric (AIFCandidateMesh.mesh.slab b i)
      (timeCoordinate (AIFCandidateMesh.mesh.slab b i) t)) e ≤ 1/40000 →
    energyRate (AIFCandidateMesh.mesh.slab b i)
      (timeCoordinate (AIFCandidateMesh.mesh.slab b i) t)
      (etaCoordinate (AIFCandidateMesh.mesh.slab b i) p) e ≤
      (1/100) * (1/40000 - matrixForm (metric (AIFCandidateMesh.mesh.slab b i)
        (timeCoordinate (AIFCandidateMesh.mesh.slab b i) t)) e) - 1/16000000

/-- Every prefix cell must supply its own checked drift result. -/
theorem prefix_invariant (n : Nat) (hn : n + 1 ≤ 370) (b : Fin 8)
    (eta : ℝ) (hp : eta ∈ Set.Icc ((prefixMesh (n+1) hn).edges b.castSucc : ℝ)
      ((prefixMesh (n+1) hn).edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (drift : ∀ i : Fin (n+1), CellDrift b ⟨i.val, lt_of_lt_of_le i.isLt hn⟩) :
    ∀ i, ∀ t ∈ Set.Icc ((prefixMesh (n+1) hn).times i.castSucc : ℝ)
      ((prefixMesh (n+1) hn).times i.succ : ℝ),
      tubeEnergy ((prefixMesh (n+1) hn).slab b i) t eta (shift eta (state t)) ≤ 1/40000 := by
  apply AIFMeshComposition.mesh_invariant (prefixMesh (n+1) hn) b
  · intro i
    rw [prefix_slab]
    exact AIFMeshGeometry.step_positive AIFCandidateMesh.nodes b _
  · exact AIFMeshGeometry.eta_positive b
  · exact hp
  · intro i t ht j
    apply AIFCircuitTransport.shifted_derivative_on eta state realized _ _ _ t ht j
    exact_mod_cast times_nonnegative ⟨i.val, by omega⟩
  · intro i t p e ht hparam he
    apply drift i t p e
    · change t ∈ Set.Icc
        (AIFCandidateMesh.mesh.times (⟨i.val, lt_of_lt_of_le i.isLt hn⟩ : Fin 370).castSucc : ℝ)
        (AIFCandidateMesh.mesh.times (⟨i.val, lt_of_lt_of_le i.isLt hn⟩ : Fin 370).succ : ℝ) at ht
      simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel] using ht
    · exact hparam
    · exact he
  · have hz : ((prefixMesh (n+1) hn).times 0 : ℝ) = 0 := by
      change (AIFCandidateMesh.mesh.times 0 : ℝ) = 0
      rw [AIFStartupInitial.time_zero]
      norm_num
    rw [hz, AIFCircuitTransport.shifted_initial eta state realized]
    have hi := AIFStartupInitial.initial_energy b eta
    have hs : (fun i => (AIFStartupInitial.shiftedInitial i : ℝ)) = ![-2,-2,-2,-1] := by
      ext i
      fin_cases i <;> norm_num [AIFStartupInitial.shiftedInitial]
    rw [hs] at hi
    change tubeEnergy (AIFCandidateMesh.mesh.slab b 0) 0 eta ![-2,-2,-2,-1] ≤ 1/40000
    rw [hi]
    norm_num

theorem first_drift (b : Fin 8) : CellDrift b 0 := by
  fin_cases b
  · exact AIFMeshBindingBin0Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin1Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin2Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin3Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin4Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin5Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin6Slab0.drift_in_mesh
  · exact AIFMeshBindingBin7Slab0.drift_in_mesh

theorem bin0_drift (i : Fin 21) : CellDrift 0 ⟨i.val, by omega⟩ := by
  fin_cases i
  · exact AIFMeshBindingBin0Slab0.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab1.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab2.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab3.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab4.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab5.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab6.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab7.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab8.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab9.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab10.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab11.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab12.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab13.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab14.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab15.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab16.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab17.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab18.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab19.drift_in_mesh
  · exact AIFPolynomialMeshBindingBin0Slab20.drift_in_mesh

theorem first_endpoint : (prefixMesh 1 (by decide)).times 1 = 1/200 := by decide +kernel

theorem bin0_endpoint : (prefixMesh 21 (by decide)).times 21 = 21/200 := by decide +kernel

/-- All eight parameter bins have an invariant first closed time slab. -/
theorem first_slab_invariant (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (AIFMeshGeometry.edges b.castSucc : ℝ)
      (AIFMeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    tubeEnergy (AIFCandidateMesh.mesh.slab b 0) t eta (shift eta (state t)) ≤ 1/40000 := by
  have h := prefix_invariant 0 (by decide) b eta hp state realized
    (fun i => by fin_cases i; exact first_drift b) 0 t
  apply h
  change t ∈ Set.Icc (AIFCandidateMesh.mesh.times 0 : ℝ) ((prefixMesh 1 (by decide)).times 1 : ℝ)
  rw [AIFStartupInitial.time_zero, first_endpoint]
  norm_num at *
  exact ht

/-- The first closed startup interval is covered for every parameter in [8,12]. -/
theorem all_parameter_startup (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    ∃ b : Fin 8, ∀ t ∈ Set.Icc (0 : ℝ) (1/200),
      tubeEnergy (AIFCandidateMesh.mesh.slab b 0) t eta (shift eta (state t)) ≤ 1/40000 := by
  obtain ⟨b, hb⟩ := AIFMesh.interval_covered 7
    (fun j => (AIFMeshGeometry.edges j : ℝ)) eta
    (by simpa [AIFMeshGeometry.edges] using hp)
  exact ⟨b, fun t ht => first_slab_invariant b eta hb state realized t ht⟩

/-- A fixed parameter in [8,17/2] stays in the moving tube for all 21 startup cells. -/
theorem bin0_prefix_invariant (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    ∃ i : Fin 21,
      t ∈ Set.Icc ((prefixMesh 21 (by decide)).times i.castSucc : ℝ)
        ((prefixMesh 21 (by decide)).times i.succ : ℝ) ∧
      tubeEnergy ((prefixMesh 21 (by decide)).slab 0 i) t eta (shift eta (state t)) ≤ 1/40000 := by
  apply AIFMeshComposition.covered_energy (prefixMesh 21 (by decide)) 0 eta
    (fun s => shift eta (state s))
  · apply prefix_invariant 20 (by decide) 0 eta _ state realized bin0_drift
    simpa [prefixMesh, AIFCandidateMesh.mesh, AIFMeshGeometry.mesh, AIFMeshGeometry.edges] using hp
  · change t ∈ Set.Icc (AIFCandidateMesh.mesh.times 0 : ℝ) ((prefixMesh 21 (by decide)).times 21 : ℝ)
    rw [AIFStartupInitial.time_zero, bin0_endpoint]
    norm_num at *
    exact ht

#print axioms prefix_slab
#print axioms times_nonnegative
#print axioms prefix_invariant
#print axioms first_drift
#print axioms bin0_drift
#print axioms first_endpoint
#print axioms bin0_endpoint
#print axioms first_slab_invariant
#print axioms all_parameter_startup
#print axioms bin0_prefix_invariant
end Gimle.Forseti.Examples.AIFStartupPrefix
"""
    return {"AIFStartupPrefix.lean": source}


def main() -> None:
    """Write the prefix proof source, or compare it without changing any file."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.check:
        args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, source in generate().items():
        path = args.output_directory / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
