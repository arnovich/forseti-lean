"""Isolated proposal checking rational slab side conditions before real lifting."""

from __future__ import annotations

import argparse
from pathlib import Path

import aif_slab_coverage as original

ROOT = Path(__file__).resolve().parents[1]
DRIFT_MARKER = (
    "/-- Algebraic drift inequality on this closed physical-time/eta slab. -/"
)

OLD_SYMMETRY = """theorem metric_symmetric (s : ℝ) (i j : Fin 4) :
    metric slab s i j = metric slab s j i := by
  fin_cases i <;> fin_cases j <;> norm_num [metric, hermite, slab]

"""
NEW_SYMMETRY = """theorem symmetric_data : AIFSlabData.SymmetricData slab := by
  unfold AIFSlabData.SymmetricData
  decide +kernel

theorem metric_symmetric (s : ℝ) (i j : Fin 4) :
    metric slab s i j = metric slab s j i :=
  AIFSlabData.metric_symmetric slab symmetric_data s i j

"""


def generate(
    candidate: Path, *, selections: tuple[tuple[int, int], ...]
) -> dict[str, str]:
    """Preserve every polynomial/certificate declaration and drift statement."""
    sources = original.generate(
        candidate, polynomial_binding=True, selections=selections
    )
    result = {}
    import_line = "import Gimle.Forseti.Examples.AIFPolynomialBinding\n"
    marker = DRIFT_MARKER
    for filename, source in sources.items():
        if (
            source.count(OLD_SYMMETRY) != 1
            or source.count(import_line) != 1
            or source.count(marker) != 1
        ):
            raise ValueError("unrecognized slab generator shape")
        source = source.replace(
            import_line, import_line + "import Gimle.Forseti.Examples.AIFSlabData\n", 1
        )
        source = source.replace(OLD_SYMMETRY, NEW_SYMMETRY, 1)
        prefix, suffix = source.split(marker, 1)
        if suffix.count("(by norm_num [slab])") != 2:
            raise ValueError(
                "expected exactly the two rational interval side conditions"
            )
        result[filename] = (
            prefix
            + marker
            + suffix.replace("(by norm_num [slab])", "(by decide +kernel)")
        )
    return result


def main() -> None:
    """Write isolated proposals, or verify existing bytes without repairing them."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument(
        "--cell", type=original.parse_cell, action="append", required=True
    )
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    destination = args.output_directory.resolve()
    if not destination.is_relative_to((ROOT / ".lake").resolve()):
        parser.error("slab-data proposals must be under the repository .lake directory")
    outputs = generate(args.candidate, selections=tuple(args.cell))
    if not args.check:
        destination.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = destination / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
