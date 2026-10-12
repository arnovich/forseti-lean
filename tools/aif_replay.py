#!/usr/bin/env python3
"""Replay explicit AIF cells with checked provenance and resumable local receipts.

Receipts are build bookkeeping, not mathematical certificates. Lean's ordinary
kernel and the exact named axiom reports remain the proof authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

import aif_slab_coverage as coverage

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    """Hash artifacts without loading large files into memory."""
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def json_hash(value: object) -> str:
    """Hash a deterministic JSON representation."""
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def write_json(path: Path, value: object) -> None:
    """Publish a complete receipt atomically."""
    pending = path.with_suffix(path.suffix + ".tmp")
    pending.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    pending.replace(path)


def merge_setups(paths: list[Path]) -> dict:
    """Merge Lake-resolved imports, rejecting ambiguous checking environments."""
    if not paths:
        raise ValueError("at least one Lake setup map is required")
    result = json.loads(paths[0].read_text())
    metadata = {k: v for k, v in result.items() if k not in ("name", "importArts")}
    if result.get("plugins") or result.get("dynlibs"):
        raise ValueError(
            "this runner requires a setup without external plugins or dynlibs"
        )
    for path in paths[1:]:
        other = json.loads(path.read_text())
        if {
            k: v for k, v in other.items() if k not in ("name", "importArts")
        } != metadata:
            raise ValueError("Lake setup metadata differs")
        for name, artifacts in other["importArts"].items():
            if name in result["importArts"] and result["importArts"][name] != artifacts:
                raise ValueError(f"conflicting import artifacts for {name}")
            result["importArts"][name] = artifacts
    return result


def environment_fingerprint(lean: Path, setup: dict) -> dict:
    """Bind receipts to the compiler, runtime libraries and every resolved import."""
    artifacts = {}
    for paths in setup["importArts"].values():
        for value in paths:
            path = (ROOT / value).resolve()
            if path.suffix == ".olean" and not path.is_file():
                raise ValueError(f"missing imported artifact: {path}")
            artifacts[str(path)] = sha256(path) if path.is_file() else None
    # Lake maps omit implicit Init/Lean imports. Bind the full library tree,
    # including private oleans and runtime libraries outside lib/lean.
    libraries = lean.resolve().parent.parent / "lib"
    for path in libraries.rglob("*"):
        if path.is_file():
            artifacts[str(path.resolve())] = sha256(path)
    inputs = {
        "compiler": str(lean.resolve()),
        "compiler_sha256": sha256(lean),
        "toolchain_sha256": sha256(ROOT / "lean-toolchain"),
        "lake_manifest_sha256": sha256(ROOT / "lake-manifest.json"),
        "setup": {k: v for k, v in setup.items() if k != "name"},
        "artifacts": artifacts,
    }
    return {"sha256": json_hash(inputs), "inputs": inputs}


def expected_reports(name: str) -> list[str]:
    """Require the two endpoint results and the full physical drift statement."""
    return [
        f"Gimle.Forseti.Examples.{name}.{suffix}"
        for suffix in (
            "Negative.nonnegative",
            "Positive.nonnegative",
            "drift_bound_physical",
        )
    ]


def audit_log(log: str, name: str) -> list[dict]:
    """Reject partial, duplicate or unrelated reports and every forbidden axiom."""
    if re.search(r"\b(?:error|warning)(?:\(|\[|:)", log):
        raise ValueError(f"compiler errors or warnings in {name}")
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    reports += [
        (n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", log)
    ]
    if len(reports) != 3 or {n for n, _ in reports} != set(expected_reports(name)):
        raise ValueError(f"missing, duplicate or unexpected axiom reports in {name}")
    result = []
    for theorem, values in reports:
        axioms = {v.strip() for v in values.split(",") if v.strip()}
        if not axioms <= ALLOWED_AXIOMS:
            raise ValueError(f"forbidden axioms in {theorem}: {sorted(axioms)}")
        result.append({"theorem": theorem, "axioms": sorted(axioms)})
    return result


def replay_cell(
    directory: Path,
    name: str,
    source: str,
    lean: Path,
    setup: dict,
    context: dict,
    *,
    resume: bool = False,
    verify_only: bool = False,
) -> dict:
    """Compile one cell or reuse only a complete, independently rechecked receipt."""
    match = re.fullmatch(r"AIFPolynomialBin([0-7])Slab([0-9]+)", name)
    if not match:
        raise ValueError("invalid cell module name")
    coverage.validate_selections(((int(match[1]), int(match[2])),))
    directory = directory.resolve()
    local_setup = {**setup, "name": "Gimle.Forseti.Examples." + name}
    setup_text = json.dumps(local_setup, sort_keys=True) + "\n"
    expected = {
        "schema": 1,
        "module": name,
        "candidate_sha256": coverage.CANDIDATE_SHA256,
        "environment_sha256": context["sha256"],
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "setup_sha256": hashlib.sha256(setup_text.encode()).hexdigest(),
    }
    paths = {
        ext: directory / (name + ext)
        for ext in (".lean", ".setup.json", ".olean", ".log")
    }
    receipt_path = directory / (name + ".receipt.json")
    if resume or verify_only:
        try:
            receipt = json.loads(receipt_path.read_text())
            matches = all(receipt.get(k) == v for k, v in expected.items())
            hashes = {ext: sha256(path) for ext, path in paths.items()}
            matches &= hashes == receipt["hashes"]
            matches &= paths[".olean"].stat().st_size == receipt["olean_bytes"] > 0
            matches &= hashes[".lean"] == expected["source_sha256"]
            matches &= hashes[".setup.json"] == expected["setup_sha256"]
            reports = audit_log(paths[".log"].read_text(), name)
            matches &= reports == receipt["reports"] and receipt["exit_code"] == 0
            if matches:
                return {**receipt, "status": "reused"}
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            pass
        if verify_only:
            raise ValueError(f"missing or stale verified receipt for {name}")
    directory.mkdir(parents=True, exist_ok=True)
    receipt_path.unlink(missing_ok=True)
    paths[".lean"].write_bytes(source.encode())
    paths[".setup.json"].write_bytes(setup_text.encode())
    pending = directory / (name + ".pending.olean")
    pending.unlink(missing_ok=True)
    started = time.monotonic()
    try:
        with paths[".log"].open("w") as log:
            result = subprocess.run(
                [
                    str(lean.resolve()),
                    "-j1",
                    "-DElab.async=false",
                    "--setup",
                    str(paths[".setup.json"]),
                    "-o",
                    str(pending),
                    str(paths[".lean"]),
                ],
                stdout=log,
                stderr=subprocess.STDOUT,
                stdin=subprocess.DEVNULL,
                text=True,
                cwd=ROOT,
                check=False,
            )
        if (
            result.returncode != 0
            or not pending.is_file()
            or pending.stat().st_size == 0
        ):
            raise ValueError(f"Lean failed for {name}; see {paths['.log']}")
        reports = audit_log(paths[".log"].read_text(), name)
        pending.replace(paths[".olean"])
        receipt = {
            **expected,
            "exit_code": 0,
            "reports": reports,
            "hashes": {ext: sha256(path) for ext, path in paths.items()},
            "olean_bytes": paths[".olean"].stat().st_size,
            "elapsed_seconds": time.monotonic() - started,
        }
        write_json(receipt_path, receipt)
        return {**receipt, "status": "compiled"}
    finally:
        pending.unlink(missing_ok=True)


def main() -> None:
    """Run one explicit batch sequentially, retaining exact per-cell evidence."""
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
    directory = args.output_directory.resolve()
    if not directory.is_relative_to((ROOT / ".lake").resolve()):
        parser.error("replay output must be under the repository .lake directory")
    selections = tuple(args.cell)
    coverage.validate_selections(selections)
    setup = merge_setups(args.setup)
    print(json.dumps({"phase": "fingerprinting_environment"}), flush=True)
    context = environment_fingerprint(args.lean, setup)
    sources = coverage.generate(
        args.candidate, polynomial_binding=True, selections=selections
    )
    expected = {f"AIFPolynomialBin{b}Slab{i}.lean" for b, i in selections}
    if set(sources) != expected:
        raise ValueError("generated sources differ from the declared batch")
    manifest = {
        "schema": 1,
        "cells": selections,
        "candidate_sha256": coverage.CANDIDATE_SHA256,
        "environment_sha256": context["sha256"],
        "status": "running",
        "modules": {},
        "scope": "Only the explicitly listed drift cells; no trajectory theorem.",
    }
    if not args.verify_only:
        directory.mkdir(parents=True, exist_ok=True)
        write_json(directory / "environment.json", context)
        write_json(directory / "batch.json", manifest)
    try:
        for filename, source in sources.items():
            name = Path(filename).stem
            print(json.dumps({"module": name, "phase": "checking"}), flush=True)
            result = replay_cell(
                directory,
                name,
                source,
                args.lean,
                setup,
                context,
                resume=args.resume,
                verify_only=args.verify_only,
            )
            manifest["modules"][name] = result
            if not args.verify_only:
                write_json(directory / "batch.json", manifest)
            print(
                json.dumps(
                    {
                        "module": name,
                        "status": result["status"],
                        "olean_bytes": result["olean_bytes"],
                    }
                ),
                flush=True,
            )
        if environment_fingerprint(args.lean, setup) != context:
            raise ValueError(
                "checking environment changed during the batch; reverify before reuse"
            )
        manifest["status"] = "passed"
    except BaseException:
        manifest["status"] = "failed"
        raise
    finally:
        if not args.verify_only:
            write_json(directory / "batch.json", manifest)
    print(
        json.dumps(
            {
                "status": "passed",
                "cells": len(selections),
                "environment_sha256": context["sha256"],
                "axiom_reports": sum(
                    len(r["reports"]) for r in manifest["modules"].values()
                ),
            }
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
