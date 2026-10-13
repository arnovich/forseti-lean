#!/usr/bin/env python3
"""Emit actual-circuit safety on the checked all-bin 21-slab startup prefix."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Emit concrete certificate dispatch and composition for Lean to check."""
    outputs = {}
    for b in range(1, 8):
        name = f"AIFUniformPrefixBin{b}"
        source = "import Gimle.Forseti.Examples.AIFSafetyComposition\n"
        source += "".join(
            f"import Gimle.Forseti.Examples.AIFPolynomialOutputBin{b}Slab{i}\n"
            for i in range(1, 21)
        )
        source += f"""
/-! All 21 drift and output obligations in parameter bin {b}.
Only concrete checked certificates are used; no cell obligation is assumed. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Gimle.Forseti.Examples.{name}

theorem drift (i : Fin 21) :
    AIFStartupPrefix.CellDrift {b} ⟨i.val, by omega⟩ := by
  fin_cases i
  · exact AIFStartupPrefix.first_drift {b}
"""
        source += "".join(
            f"  · exact AIFPolynomialMeshBindingBin{b}Slab{i}.drift_in_mesh\n"
            for i in range(1, 21)
        )
        source += f"""
theorem output (i : Fin 21) :
    AIFSafetyComposition.CellOutput {b} ⟨i.val, by omega⟩ := by
  fin_cases i
  · exact AIFStartupOutput.first_cell_output {b}
"""
        source += "".join(
            f"  · exact AIFPolynomialOutputBin{b}Slab{i}.shifted_output_in_mesh\n"
            for i in range(1, 21)
        )
        source += f"""
#print axioms drift
#print axioms output
end Gimle.Forseti.Examples.{name}
"""
        outputs[name + ".lean"] = source
    source = "import Gimle.Forseti.Examples.AIFSafetyComposition\n"
    source += "".join(
        f"import Gimle.Forseti.Examples.AIFUniformPrefixBin{b}\n" for b in range(1, 8)
    )
    source += """
/-! Nonempty actual compiled-circuit safety on [0,21/200] for all eta in [8,12].
All 168 prefix cells supply checked drift and output certificates. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Gimle.Forseti.Examples.AIFUniformPrefix
open AIFMesh AIFSlabModel AIFPhysicalCoordinates AIFStartupPrefix

theorem drift (b : Fin 8) (i : Fin 21) : CellDrift b ⟨i.val, by omega⟩ := by
  fin_cases b
  · exact bin0_drift i
"""
    source += "".join(
        f"  · exact AIFUniformPrefixBin{b}.drift i\n" for b in range(1, 8)
    )
    source += """
theorem output (b : Fin 8) (i : Fin 21) :
    AIFSafetyComposition.CellOutput b ⟨i.val, by omega⟩ := by
  fin_cases b
  · exact AIFStartupOutput.bin0_cell_output i
"""
    source += "".join(
        f"  · exact AIFUniformPrefixBin{b}.output i\n" for b in range(1, 8)
    )
    source += """
theorem membership (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (AIFMeshGeometry.edges b.castSucc : ℝ)
      (AIFMeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (i : Fin 21) (t : ℝ)
    (ht : t ∈ Set.Icc ((prefixMesh 21 (by decide)).times i.castSucc : ℝ)
      ((prefixMesh 21 (by decide)).times i.succ : ℝ)) :
    tubeEnergy ((prefixMesh 21 (by decide)).slab b i) t eta
      (shift eta (state t)) ≤ 1/40000 :=
  prefix_invariant 20 (by decide) b eta hp state realized (drift b) i t ht

theorem bin_output (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (AIFMeshGeometry.edges b.castSucc : ℝ)
      (AIFMeshGeometry.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  have ht' : t ∈ Set.Icc ((prefixMesh 21 (by decide)).times 0 : ℝ)
      ((prefixMesh 21 (by decide)).times 21 : ℝ) := by
    change t ∈ Set.Icc (AIFCandidateMesh.mesh.times 0 : ℝ)
      ((prefixMesh 21 (by decide)).times 21 : ℝ)
    rw [AIFStartupInitial.time_zero, bin0_endpoint]
    norm_num at *
    exact ht
  obtain ⟨i, hi, he⟩ := AIFMeshComposition.covered_energy
    (prefixMesh 21 (by decide)) b eta (fun s => shift eta (state s))
    (membership b eta hp state realized) t ht'
  apply (AIFCircuitTransport.compiled_output_bound_iff eta (state t)).mpr
  apply output b i t eta (shift eta (state t)) _ hp he
  change t ∈ Set.Icc
    (AIFCandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).castSucc : ℝ)
    (AIFCandidateMesh.mesh.times (⟨i.val, by omega⟩ : Fin 370).succ : ℝ) at hi
  simpa only [Mesh.slab, Rat.cast_sub, add_sub_cancel] using hi

theorem all_parameter_output (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (21/200)) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨b, hb⟩ := AIFMesh.interval_covered 7
    (fun j => (AIFMeshGeometry.edges j : ℝ)) eta
    (by simpa [AIFMeshGeometry.edges] using hp)
  exact bin_output b eta hb state realized t ht

/-- Existence plus universal safety, with no tube or cell-certificate premises. -/
theorem all_parameter_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    ∀ state, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨AIFCircuitSolution.exists_realization eta heta, ?_⟩
  intro state realized t ht
  exact ⟨AIFCircuitSolution.realization_output_nonnegative eta heta state realized t ht.1,
    all_parameter_output eta hp state realized t ht⟩

#print axioms drift
#print axioms output
#print axioms membership
#print axioms bin_output
#print axioms all_parameter_output
#print axioms all_parameter_safety
end Gimle.Forseti.Examples.AIFUniformPrefix
"""
    outputs["AIFUniformPrefix.lean"] = source
    return outputs


def main() -> None:
    """Write proof sources or check their bytes without modifying evidence."""
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
