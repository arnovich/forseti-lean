#!/usr/bin/env python3
"""Emit physical AIF output bounds on the checked startup prefixes."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Emit proof source; successful Lean replay is required for proof authority."""
    source = """import Gimle.Forseti.Examples.AIFStartupPrefix
import Gimle.Forseti.Examples.AIFOutputBin0Slab0
import Gimle.Forseti.Examples.AIFOutputBin7Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin1Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin2Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin3Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin4Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin5Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin6Slab0
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab1
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab2
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab3
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab4
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab5
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab6
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab7
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab8
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab9
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab10
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab11
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab12
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab13
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab14
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab15
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab16
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab17
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab18
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab19
import Gimle.Forseti.Examples.AIFPolynomialOutputBin0Slab20

/-! Physical compiled-output safety on checked startup prefixes.
Every result remains conditional on an actual circuit realization. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Gimle.Forseti.Examples.AIFStartupOutput
open AIFMesh AIFSlabModel AIFPhysicalCoordinates

/-- Every first-slab bin supplies a checked output enclosure. -/
theorem first_cell_output (b : Fin 8) (t eta : ℝ) (x : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b 0).tStart : ℝ)
      (((AIFCandidateMesh.mesh.slab b 0).tStart : ℝ) + (AIFCandidateMesh.mesh.slab b 0).step))
    (hp : eta ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b 0).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab b 0).etaHi : ℝ))
    (he : tubeEnergy (AIFCandidateMesh.mesh.slab b 0) t eta x ≤ 1/40000) :
    x 1 ≤ 6/5 := by
  fin_cases b
  · exact AIFOutputBin0Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin1Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin2Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin3Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin4Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin5Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin6Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFOutputBin7Slab0.shifted_output_in_mesh t eta x ht hp he

/-- All 21 cells of the first bin supply checked output enclosures. -/
theorem bin0_cell_output (i : Fin 21) (t eta : ℝ) (x : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc
      ((AIFCandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩).tStart : ℝ)
      (((AIFCandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩).tStart : ℝ) +
        (AIFCandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩).step))
    (hp : eta ∈ Set.Icc (AIFMeshGeometry.edges 0 : ℝ) (AIFMeshGeometry.edges 1 : ℝ))
    (he : tubeEnergy (AIFCandidateMesh.mesh.slab 0 ⟨i.val, by omega⟩) t eta x ≤ 1/40000) :
    x 1 ≤ 6/5 := by
  fin_cases i
  · exact AIFOutputBin0Slab0.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab1.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab2.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab3.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab4.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab5.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab6.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab7.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab8.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab9.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab10.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab11.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab12.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab13.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab14.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab15.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab16.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab17.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab18.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab19.shifted_output_in_mesh t eta x ht hp he
  · exact AIFPolynomialOutputBin0Slab20.shifted_output_in_mesh t eta x ht hp he

/-- Physical x2 safety over the first closed slab in any fixed parameter bin. -/
theorem first_slab_output (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (AIFMeshGeometry.edges b.castSucc : ℝ)
      (AIFMeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  apply (AIFCircuitTransport.compiled_output_bound_iff eta (state t)).mpr
  apply first_cell_output b t eta (shift eta (state t)) _ hp
    (AIFStartupPrefix.first_slab_invariant b eta hp state realized t ht)
  have ht1q : AIFCandidateMesh.mesh.times 1 = 1/200 := by decide +kernel
  have ht1 : (AIFCandidateMesh.mesh.times 1 : ℝ) = 1/200 := by
    rw [ht1q]
    norm_num
  have ht' : t ∈ Set.Icc (AIFCandidateMesh.mesh.times 0 : ℝ)
      (AIFCandidateMesh.mesh.times 1 : ℝ) := by
    rw [AIFStartupInitial.time_zero, ht1]
    simpa only [Rat.cast_zero] using ht
  simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel, Fin.castSucc_zero, Fin.succ_zero_eq_one] using ht'

/-- Physical x2 stays at most 16/5 through time 1/200 for every eta in [8,12]. -/
theorem all_parameter_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (1/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨b, hb⟩ := AIFMesh.interval_covered 7
    (fun j => (AIFMeshGeometry.edges j : ℝ)) eta
    (by simpa [AIFMeshGeometry.edges] using hp)
  exact first_slab_output b eta hb state realized t ht

/-- Physical x2 stays at most 16/5 through time 21/200 for eta in [8,17/2]. -/
theorem bin0_prefix_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) (17/2))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨i, hi, he⟩ := AIFStartupPrefix.bin0_prefix_invariant eta hp state realized t ht
  apply (AIFCircuitTransport.compiled_output_bound_iff eta (state t)).mpr
  apply bin0_cell_output i t eta (shift eta (state t)) _ _ he
  · change t ∈ Set.Icc
      (AIFCandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).castSucc : ℝ)
      (AIFCandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).succ : ℝ) at hi
    simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel] using hi
  · simpa [AIFMeshGeometry.edges] using hp

#print axioms first_cell_output
#print axioms bin0_cell_output
#print axioms first_slab_output
#print axioms all_parameter_output
#print axioms bin0_prefix_output
end Gimle.Forseti.Examples.AIFStartupOutput
"""
    return {"AIFStartupOutput.lean": source}


def main() -> None:
    """Write the output proof source, or compare it without changing any file."""
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
