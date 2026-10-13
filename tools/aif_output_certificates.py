#!/usr/bin/env python3
"""Generate exact output-enclosure companions for selected checked AIF cells."""

from __future__ import annotations

import argparse
from pathlib import Path

from aif_slab_coverage import SELECTIONS, parse_cell, validate_selections


def generate(
    *,
    selections: tuple[tuple[int, int], ...] = SELECTIONS,
    polynomial_binding: bool = False,
) -> dict[str, str]:
    """Reuse each imported slab; Lean checks center bounds and every margin."""
    validate_selections(selections)
    outputs = {}
    for b, i in selections:
        base = (
            f"{'AIFPolynomial' if polynomial_binding else 'AIFCoverage'}Bin{b}Slab{i}"
        )
        binding = f"{'AIFPolynomialMeshBinding' if polynomial_binding else 'AIFMeshBinding'}Bin{b}Slab{i}"
        name = f"{'AIFPolynomialOutput' if polynomial_binding else 'AIFOutput'}Bin{b}Slab{i}"
        source = f"""import Gimle.Forseti.Examples.AIFOutputEnclosure
import Gimle.Forseti.Examples.{binding}

/-! Exact center/output-margin certificates for the imported slab {base}.
Generation is a proposal; proof authority requires successful Lean checking. -/
namespace Gimle.Forseti.Examples.{name}
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFSlabModel AIFOutputEnclosure {base}

def loControls : Fin 4 → ℚ := hermiteControls slab.step (slab.loStart 1)
  (slab.loEnd 1) (slab.loStartSlope 1) (slab.loEndSlope 1)
def hiControls : Fin 4 → ℚ := hermiteControls slab.step (slab.hiStart 1)
  (slab.hiEnd 1) (slab.hiStartSlope 1) (slab.hiEndSlope 1)
def centerBound : ℚ := max
  (max (max (loControls 0) (loControls 1)) (max (loControls 2) (loControls 3)))
  (max (max (hiControls 0) (hiControls 1)) (max (hiControls 2) (hiControls 3)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem lo_bound : ∀ i, loControls i ≤ centerBound := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem hi_bound : ∀ i, hiControls i ≤ centerBound := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem gap_positive : 0 < 6/5 - centerBound := by decide +kernel

def certificates (i : Fin 4) (_ : Fin 1) : WeightedSquares 4 :=
  Gimle.Forseti.RationalLDL.propose (outputCoefficients slab (6/5-centerBound) i 0)

"""
        for k in range(4):
            source += f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem valid_{k} : (certificates {k} 0).Represents
    (outputCoefficients slab (6/5-centerBound) {k} 0) := by
  unfold WeightedSquares.Represents
  decide +kernel

"""
        source += """theorem valid (i : Fin 4) (j : Fin 1) :
    (certificates i j).Represents (outputCoefficients slab (6/5-centerBound) i j) := by
  fin_cases i <;> fin_cases j
  · exact valid_0
  · exact valid_1
  · exact valid_2
  · exact valid_3

/-- A cell's tube membership implies its shifted output threshold. -/
theorem shifted_output_bound_physical (t p : ℝ) (x : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc (slab.tStart : ℝ) ((slab.tStart : ℝ) + slab.step))
    (hp : p ∈ Set.Icc (slab.etaLo : ℝ) (slab.etaHi : ℝ))
    (he : AIFMesh.tubeEnergy slab t p x ≤ 1/40000) : x 1 ≤ 6/5 :=
  shifted_output_bound slab centerBound (le_of_lt gap_positive) certificates valid
    lo_bound hi_bound _ _ (timeCoordinate_mem slab (by norm_num [slab]) t ht)
    (etaCoordinate_mem slab (by norm_num [slab]) p hp) x he

"""
        source += f"""/-- The bound uses the exact candidate mesh cell already linked to this slab. -/
theorem shifted_output_in_mesh (t p : ℝ) (x : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc ((AIFCandidateMesh.mesh.slab {b} {i}).tStart : ℝ)
      (((AIFCandidateMesh.mesh.slab {b} {i}).tStart : ℝ) + (AIFCandidateMesh.mesh.slab {b} {i}).step))
    (hp : p ∈ Set.Icc ((AIFCandidateMesh.mesh.slab {b} {i}).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab {b} {i}).etaHi : ℝ))
    (he : AIFMesh.tubeEnergy (AIFCandidateMesh.mesh.slab {b} {i}) t p x ≤ 1/40000) :
    x 1 ≤ 6/5 := by
  rw [{binding}.slab_binding] at *
  exact shifted_output_bound_physical t p x ht hp he

#print axioms shifted_output_bound_physical
#print axioms shifted_output_in_mesh
end Gimle.Forseti.Examples.{name}
"""
        outputs[name + ".lean"] = source
    return outputs


def main() -> None:
    """Write selected companions or verify existing bytes without mutation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--polynomial-binding", action="store_true")
    parser.add_argument(
        "--cell",
        type=parse_cell,
        action="append",
        help="Select BIN:SLAB; repeat for a batch.",
    )
    args = parser.parse_args()
    try:
        outputs = generate(
            selections=tuple(args.cell) if args.cell is not None else SELECTIONS,
            polynomial_binding=args.polynomial_binding,
        )
    except ValueError as error:
        parser.error(str(error))
    if not args.check:
        args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = args.output_directory / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
