"""Emit optional whole-family kernel checks for exact AIF drift certificates."""

from __future__ import annotations

import argparse
from pathlib import Path

import aif_slab_coverage as original
import aif_slab_data as slab_data

ROOT = Path(__file__).resolve().parents[1]


def _individual_proof(a: int, b: int) -> str:
    """Identify one existing per-matrix proof without matching its data."""
    return f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem valid_{a}_{b} : cert_{a}_{b}.Represents (coefficients {a} {b}) := by
  unfold WeightedSquares.Represents
  decide +kernel

"""


def _family_proofs(source: str) -> str:
    """Replace only the two validity and two polynomial proof constructions."""
    before = source
    removed = []
    for a in range(10):
        for b in range(4):
            proof = _individual_proof(a, b)
            if source.count(proof) != 2:
                raise ValueError(f"expected both endpoint proofs for {a},{b}")
            source = source.replace(proof, "")
            removed.append(proof)
    old = (
        "theorem valid : ∀ i j, (certificates i j).Represents (coefficients i j) := by\n"
        "  intro i j\n  fin_cases i <;> fin_cases j\n"
        + "".join(f"  · exact valid_{a}_{b}\n" for a in range(10) for b in range(4))
    )
    new = (
        "set_option maxRecDepth 100000 in\n"
        "set_option maxHeartbeats 16000000 in\n"
        "theorem valid : ∀ i j, (certificates i j).Represents (coefficients i j) := by\n"
        "  unfold WeightedSquares.Represents\n  decide +kernel\n"
    )
    if source.count(old) != 2:
        raise ValueError("expected both finite-family validity dispatch proofs")
    source = source.replace(old, new)
    old_checked = "  intro i j\n  fin_cases i <;> fin_cases j <;> decide +kernel\n"
    if source.count(old_checked) != 2:
        raise ValueError("expected both polynomial-binding dispatch proofs")
    source = source.replace(old_checked, "  decide +kernel\n")
    # Every byte outside the explicitly replaced proof blocks must agree.
    for proof in removed:
        before = before.replace(proof, "")
    before = before.replace(old, "<VALIDITY PROOF>\n").replace(
        old_checked, "<BINDING PROOF>\n"
    )
    after = source.replace(new, "<VALIDITY PROOF>\n").replace(
        " := by\n  decide +kernel\n", " := by\n<BINDING PROOF>\n"
    )
    if before != after:
        raise ValueError("unexpected change outside finite-family proof bodies")
    return source


def generate(
    candidate: Path, *, selections: tuple[tuple[int, int], ...]
) -> dict[str, str]:
    """Preserve all certificate data and quantified obligations for selected cells."""
    return {
        name: _family_proofs(source)
        for name, source in slab_data.generate(candidate, selections=selections).items()
    }


def main() -> None:
    """Write isolated proposals or check existing files without repairing them."""
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
        parser.error(
            "family-check proposals must be under the repository .lake directory"
        )
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
