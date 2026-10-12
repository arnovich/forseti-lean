#!/usr/bin/env python3
"""Generate metric-containment companions for the six checked AIF slab modules."""

from __future__ import annotations

import argparse
from pathlib import Path

from aif_slab_coverage import SELECTIONS


def generate() -> dict[str, str]:
    """Reuse imported slab data and drift proofs; Lean checks every new proposal."""
    outputs = {}
    for b, i in SELECTIONS:
        base = f"AIFCoverageBin{b}Slab{i}"
        name = f"AIFContainmentBin{b}Slab{i}"
        source = f"""import Gimle.Forseti.Examples.AIFSlabContainment
import Gimle.Forseti.Examples.{base}

/-! Companion to {base}: no independent copy of the slab inputs.
Generated source is not proof evidence until the whole module compiles. -/
namespace Gimle.Forseti.Examples.{name}
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFSlabModel AIFSlabContainment {base}

def certificates (i : Fin 4) (_ : Fin 1) : WeightedSquares 4 :=
  Gimle.Forseti.RationalLDL.propose (errorCoefficients slab i 0)

"""
        for k in range(4):
            source += f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem valid_{k} : (certificates {k} 0).Represents (errorCoefficients slab {k} 0) := by
  unfold WeightedSquares.Represents
  decide +kernel

"""
        source += """theorem valid (i : Fin 4) (j : Fin 1) :
    (certificates i j).Represents (errorCoefficients slab i j) := by
  fin_cases i <;> fin_cases j
  · exact valid_0
  · exact valid_1
  · exact valid_2
  · exact valid_3

/-- Closed metric tube membership supplies the nonlinear error bound. -/
theorem error_contained_physical (t : ℝ) (e : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc (slab.tStart : ℝ) ((slab.tStart : ℝ) + slab.step))
    (he : matrixForm (metric slab (timeCoordinate slab t)) e ≤ 1/40000) :
    e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200) :=
  error_contained_of_certificates slab certificates valid _
    (timeCoordinate_mem slab (by norm_num [slab]) t ht) e he

/-- Pointwise drift throughout the metric tube, without an external error bound. -/
theorem drift_bound_in_tube (t p : ℝ) (e : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc (slab.tStart : ℝ) ((slab.tStart : ℝ) + slab.step))
    (hp : p ∈ Set.Icc (slab.etaLo : ℝ) (slab.etaHi : ℝ))
    (he : matrixForm (metric slab (timeCoordinate slab t)) e ≤ 1/40000) :
    energyRate slab (timeCoordinate slab t) (etaCoordinate slab p) e ≤
      (1/100) * (1/40000 - matrixForm (metric slab (timeCoordinate slab t)) e) -
        1/16000000 := by
  exact drift_bound_physical t p e ht hp (error_contained_physical t e ht he)

#print axioms error_contained_physical
#print axioms drift_bound_in_tube
"""
        outputs[name + ".lean"] = source + f"end Gimle.Forseti.Examples.{name}\n"
    return outputs


def main() -> None:
    """Write companion sources, or compare their bytes without modifying files."""
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
