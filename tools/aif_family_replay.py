"""Replay explicitly selected AIF family-check cells with separate provenance.

This optional runner never changes the original replay producer. Receipts record
build evidence; Lean's kernel and named axiom reports remain proof authority.
"""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path

import aif_family_checks as producer
import aif_replay as replay
import aif_slab_coverage as coverage

ROOT = Path(__file__).resolve().parents[1]
VARIANT = "family-checks-v1"
HELPER = "Gimle.Forseti.Examples.AIFSlabData"
INPUT_MODULES = (
    "aif_family_replay",
    "aif_family_checks",
    "aif_slab_data",
    "aif_replay",
    "aif_slab_coverage",
    "aif_drift_pilot",
    "aif_metric_pilot",
    "search_suspension",
)


def input_hashes(candidate: Path, setups: list[Path]) -> dict[str, str]:
    """Pin the candidate, setup maps and complete local producer source closure."""
    paths = [
        candidate,
        *setups,
        *(ROOT / "tools" / (name + ".py") for name in INPUT_MODULES),
    ]
    return {str(p.resolve()): replay.sha256(p) for p in paths}


def make_setup(paths: list[Path]) -> dict:
    """Require the rational slab helper in the explicitly supplied Lake context."""
    setup = replay.merge_setups(paths)
    if not any(Path(p).suffix == ".olean" for p in setup["importArts"].get(HELPER, [])):
        raise ValueError("family replay requires the AIFSlabData helper setup")
    return setup


def receipt_payload(receipt: dict) -> dict:
    """Ignore only whether matching cell evidence was compiled or reused."""
    if receipt.get("status") not in ("compiled", "reused"):
        raise ValueError("invalid cell receipt status")
    return {k: v for k, v in receipt.items() if k != "status"}


def check_write_paths(directory: Path) -> None:
    """Reject links and nonregular entries before touching resumable evidence."""
    if directory.exists() and any(
        p.is_symlink() or not p.is_file() for p in directory.iterdir()
    ):
        raise ValueError("unsafe entry in family replay output directory")


def check_inventory(directory: Path, names: set[str]) -> None:
    """Require precisely the complete evidence files, with no pending artifacts."""
    expected = {"environment.json", "batch.json"} | {
        name + suffix
        for name in names
        for suffix in (".lean", ".setup.json", ".olean", ".log", ".receipt.json")
    }
    if {p.name for p in directory.iterdir()} != expected or any(
        not p.is_file() or p.is_symlink() for p in directory.iterdir()
    ):
        raise ValueError("cell evidence inventory differs from the exact selection")


def run_batch(
    candidate: Path,
    lean: Path,
    setups: list[Path],
    directory: Path,
    selections: tuple[tuple[int, int], ...],
    *,
    resume: bool = False,
    verify_only: bool = False,
) -> dict:
    """Replay or independently recheck the exact selected family-encoding batch."""
    directory = directory.resolve()
    if not directory.is_relative_to((ROOT / ".lake").resolve()):
        raise ValueError("family replay output must be under .lake")
    if resume and verify_only:
        raise ValueError("resume and verify-only are mutually exclusive")
    if not verify_only:
        check_write_paths(directory)
    coverage.validate_selections(selections)
    inputs = input_hashes(candidate, setups)
    setup = make_setup(setups)
    context = replay.environment_fingerprint(lean, setup)
    sources = producer.generate(candidate, selections=selections)
    expected_names = {f"AIFPolynomialBin{b}Slab{i}" for b, i in selections}
    if set(sources) != {name + ".lean" for name in expected_names}:
        raise ValueError("generated sources differ from the explicit selection")
    identity = {
        "schema": 1,
        "variant": VARIANT,
        "cells": [list(c) for c in selections],
        "candidate_sha256": coverage.CANDIDATE_SHA256,
        "environment_sha256": context["sha256"],
        "inputs": inputs,
    }
    batch_path = directory / "batch.json"
    previous = None
    if verify_only or batch_path.exists():
        previous = json.loads(batch_path.read_text())
        if any(previous.get(k) != v for k, v in identity.items()):
            raise ValueError("batch identity differs from the requested family replay")
        if json.loads((directory / "environment.json").read_text()) != context:
            raise ValueError("recorded environment differs from current context")
        if (
            not isinstance(previous.get("modules"), dict)
            or not set(previous["modules"]) <= expected_names
        ):
            raise ValueError("unexpected batch modules")
        if verify_only and (
            previous.get("status") != "passed"
            or set(previous["modules"]) != expected_names
        ):
            raise ValueError("batch is not complete for the exact selection")
    elif directory.exists() and any(directory.iterdir()):
        raise ValueError("refusing output directory without family batch provenance")
    if verify_only:
        check_inventory(directory, expected_names)
    batch = {
        **identity,
        "status": "running",
        "modules": {},
        "scope": "Only the explicitly selected drift cells; no trajectory theorem.",
    }
    if not verify_only:
        directory.mkdir(parents=True, exist_ok=True)
        check_write_paths(directory)
        replay.write_json(directory / "environment.json", context)
        replay.write_json(batch_path, batch)
    try:
        for filename, source in sources.items():
            if input_hashes(candidate, setups) != inputs:
                raise ValueError("producer inputs changed during replay")
            if not verify_only and shutil.disk_usage(directory).free <= 5 * 1024**3:
                raise ValueError("insufficient space for next family replay cell")
            if not verify_only:
                check_write_paths(directory)
            name = Path(filename).stem
            print(f"Checking {name} ({VARIANT})", flush=True)
            result = replay.replay_cell(
                directory,
                name,
                source,
                lean,
                setup,
                context,
                resume=resume,
                verify_only=verify_only,
            )
            if verify_only and receipt_payload(result) != receipt_payload(
                previous["modules"][name]
            ):
                raise ValueError(f"batch receipt differs for {name}")
            batch["modules"][name] = result
            if not verify_only:
                replay.write_json(batch_path, batch)
            print(f'Passed {name}: {result["status"]}', flush=True)
        check_inventory(directory, expected_names)
        if not verify_only:
            for filename, source in sources.items():
                name = Path(filename).stem
                checked = replay.replay_cell(
                    directory,
                    name,
                    source,
                    lean,
                    setup,
                    context,
                    verify_only=True,
                )
                if receipt_payload(checked) != receipt_payload(batch["modules"][name]):
                    raise ValueError(f"final cell receipt differs for {name}")
        check_inventory(directory, expected_names)
        if replay.environment_fingerprint(lean, setup) != context:
            raise ValueError("checking environment changed during replay")
        if input_hashes(candidate, setups) != inputs:
            raise ValueError("producer inputs changed during replay")
        batch["status"] = "passed"
    except BaseException:
        batch["status"] = "failed"
        raise
    finally:
        if not verify_only:
            replay.write_json(batch_path, batch)
    return batch


def main() -> None:
    """Run selected family checks or audit their existing evidence read-only."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--setup", type=Path, action="append", required=True)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument(
        "--cell", type=coverage.parse_cell, action="append", required=True
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--resume", action="store_true")
    mode.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    result = run_batch(
        args.candidate,
        args.lean,
        args.setup,
        args.output_directory,
        tuple(args.cell),
        resume=args.resume,
        verify_only=args.verify_only,
    )
    print(
        json.dumps(
            {
                "status": result["status"],
                "variant": VARIANT,
                "cells": len(result["cells"]),
                "environment_sha256": result["environment_sha256"],
            }
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
