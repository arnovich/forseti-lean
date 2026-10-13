"""Hostile bookkeeping checks for the optional family replay path."""

from __future__ import annotations

import ast
import json
import tempfile
import unittest
from pathlib import Path
from typing import Any
from unittest.mock import patch

import aif_family_replay as family


class FamilyReplayTests(unittest.TestCase):
    """Exercise batch provenance independently of mathematical validity."""

    def setUp(self) -> None:
        """Create synthetic inputs; no mock compiler result is proof evidence."""
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.out = self.root / ".lake" / "batch"
        self.candidate = self.root / "candidate.gz"
        self.candidate.write_bytes(b"fixture")
        self.compiler = self.root / "lean"
        self.compiler.write_bytes(b"fixture compiler")
        self.setup = self.root / "setup.json"
        self.setup.write_text("{}")
        self.context = {"sha256": "context", "inputs": {}}
        self.sources = {"AIFPolynomialBin0Slab81.lean": "fixture source"}
        self.inputs = {"fixture.py": "digest"}
        for target, value in (
            ("ROOT", self.root),
            ("input_hashes", self.inputs),
            ("make_setup", {"name": "fixture", "importArts": {}}),
        ):
            mock = (
                patch.object(family, target, value)
                if target == "ROOT"
                else patch.object(family, target, return_value=value)
            )
            mock.start()
            self.addCleanup(mock.stop)
        for obj, attr, value in (
            (family.replay, "environment_fingerprint", self.context),
            (family.producer, "generate", self.sources),
            (family.shutil, "disk_usage", type("Space", (), {"free": 20 * 1024**3})()),
        ):
            mock = patch.object(obj, attr, return_value=value)
            mock.start()
            self.addCleanup(mock.stop)
        self.calls = []
        mock = patch.object(family.replay, "replay_cell", side_effect=self.cell)
        mock.start()
        self.addCleanup(mock.stop)

    def cell(
        self,
        directory: Path,
        name: str,
        source: str,
        lean: Path,
        setup: dict,
        context: dict,
        **kwargs: Any,
    ) -> dict:
        """Return only synthetic bookkeeping, recording requested verification."""
        self.calls.append(kwargs)
        if not kwargs["verify_only"]:
            for suffix in (".lean", ".setup.json", ".olean", ".log", ".receipt.json"):
                (directory / (name + suffix)).write_text("synthetic evidence")
        return {
            "module": name,
            "status": "reused" if kwargs["verify_only"] else "compiled",
            "olean_bytes": 12,
            "reports": [1, 2, 3],
        }

    def run_batch(self, **kwargs: Any) -> dict:
        """Invoke one explicitly selected synthetic cell."""
        return family.run_batch(
            self.candidate, self.compiler, [self.setup], self.out, ((0, 81),), **kwargs
        )

    def test_verify_is_nonmutating_and_requires_exact_batch(self) -> None:
        """Missing evidence and changed variant, selection or module are rejected."""
        with self.assertRaises((ValueError, FileNotFoundError)):
            self.run_batch(verify_only=True)
        self.assertFalse(self.out.exists())
        self.run_batch()
        paths = list(self.out.iterdir())
        before = {p.name: (p.read_bytes(), p.stat().st_mtime_ns) for p in paths}
        self.run_batch(verify_only=True)
        self.assertTrue(self.calls[-1]["verify_only"])
        self.assertEqual(
            before, {p.name: (p.read_bytes(), p.stat().st_mtime_ns) for p in paths}
        )
        path = self.out / "batch.json"
        baseline = json.loads(path.read_text())
        for key, value in (
            ("variant", "original"),
            ("cells", []),
            ("modules", {}),
            ("status", "failed"),
            ("inputs", {}),
        ):
            with self.subTest(key=key):
                path.write_text(json.dumps({**baseline, key: value}))
                with self.assertRaises(ValueError):
                    self.run_batch(verify_only=True)
        path.write_text(json.dumps(baseline))
        (self.out / "environment.json").write_text("{}")
        with self.assertRaises(ValueError):
            self.run_batch(verify_only=True)

    def test_failure_is_durable_and_stops_next_cell(self) -> None:
        """A compiler failure cannot leave a successful batch."""
        with patch.object(
            family.replay, "replay_cell", side_effect=ValueError("failed")
        ):
            with self.assertRaisesRegex(ValueError, "failed"):
                self.run_batch()
        self.assertEqual(
            json.loads((self.out / "batch.json").read_text())["status"], "failed"
        )

    def test_postguard_rejects_changed_inputs_and_environment(self) -> None:
        """Success requires stable producer inputs and a stable Lean context."""
        with patch.object(
            family,
            "input_hashes",
            side_effect=[self.inputs, self.inputs, {"changed": "hash"}],
        ):
            with self.assertRaisesRegex(ValueError, "inputs changed"):
                self.run_batch()
        self.assertEqual(
            json.loads((self.out / "batch.json").read_text())["status"], "failed"
        )
        with patch.object(
            family.replay,
            "environment_fingerprint",
            side_effect=[self.context, {"sha256": "changed"}],
        ):
            with self.assertRaisesRegex(ValueError, "environment changed"):
                self.run_batch()

    def test_output_and_selection_guards(self) -> None:
        """No writes outside .lake and no generated selection drift are allowed."""
        with self.assertRaises(ValueError):
            family.run_batch(
                self.candidate,
                self.compiler,
                [self.setup],
                self.root / "outside",
                ((0, 81),),
            )
        with patch.object(family.producer, "generate", return_value={}):
            with self.assertRaisesRegex(ValueError, "selection"):
                self.run_batch()
        self.assertFalse(self.out.exists())

    def test_disk_guard_runs_before_compile(self) -> None:
        """Low space stops without invoking the compiler."""
        with patch.object(
            family.shutil, "disk_usage", return_value=type("Space", (), {"free": 0})()
        ):
            with self.assertRaisesRegex(ValueError, "space"):
                self.run_batch()
        self.assertFalse(self.calls)

    def test_receipt_payload_must_match_manifest(self) -> None:
        """A valid per-cell receipt cannot hide altered aggregate bookkeeping."""
        self.run_batch()
        path = self.out / "batch.json"
        batch = json.loads(path.read_text())
        batch["modules"]["AIFPolynomialBin0Slab81"]["olean_bytes"] = 99
        path.write_text(json.dumps(batch))
        with self.assertRaisesRegex(ValueError, "receipt"):
            self.run_batch(verify_only=True)

    def test_extra_or_pending_artifact_rejected_without_mutation(self) -> None:
        """An exact manifest cannot conceal unselected or unfinished files."""
        self.run_batch()
        for name in (
            "AIFPolynomialBin7Slab369.receipt.json",
            "AIFPolynomialBin0Slab81.pending.olean",
        ):
            path = self.out / name
            path.write_text("foreign artifact")
            with self.assertRaisesRegex(ValueError, "inventory"):
                self.run_batch(verify_only=True)
            self.assertEqual(path.read_text(), "foreign artifact")
            path.unlink()

    def test_final_recheck_is_required_before_success(self) -> None:
        """Artifact changes after compilation fail the completed batch audit."""

        def changed(*args: Any, **kwargs: Any) -> dict:
            if kwargs["verify_only"]:
                raise ValueError("stale verified receipt")
            return self.cell(*args, **kwargs)

        with patch.object(family.replay, "replay_cell", side_effect=changed):
            with self.assertRaisesRegex(ValueError, "stale verified receipt"):
                self.run_batch()
        self.assertEqual(
            json.loads((self.out / "batch.json").read_text())["status"], "failed"
        )

    def test_failed_module_status_is_not_normalized_away(self) -> None:
        """A manifest module must describe successful compilation or reuse."""
        self.run_batch()
        path = self.out / "batch.json"
        batch = json.loads(path.read_text())
        batch["modules"]["AIFPolynomialBin0Slab81"]["status"] = "failed"
        path.write_text(json.dumps(batch))
        with self.assertRaisesRegex(ValueError, "receipt status"):
            self.run_batch(verify_only=True)

    def test_interrupted_batch_stops_and_resumes_exact_selection(self) -> None:
        """Failure retains the completed prefix and does not call later cells."""
        cells = ((0, 81), (0, 82), (0, 83))
        sources = {f"AIFPolynomialBin0Slab{i}.lean": "fixture source" for _, i in cells}
        visited = []

        def fail_second(directory: Path, name: str, *args: Any, **kwargs: Any) -> dict:
            visited.append(name)
            if name.endswith("82"):
                raise ValueError("second cell failed")
            return self.cell(directory, name, *args, **kwargs)

        with patch.object(family.producer, "generate", return_value=sources):
            with patch.object(family.replay, "replay_cell", side_effect=fail_second):
                with self.assertRaisesRegex(ValueError, "second cell failed"):
                    family.run_batch(
                        self.candidate, self.compiler, [self.setup], self.out, cells
                    )
            self.assertEqual(
                visited, ["AIFPolynomialBin0Slab81", "AIFPolynomialBin0Slab82"]
            )
            batch = json.loads((self.out / "batch.json").read_text())
            self.assertEqual(set(batch["modules"]), {"AIFPolynomialBin0Slab81"})
            self.assertTrue(
                (self.out / "AIFPolynomialBin0Slab81.receipt.json").is_file()
            )
            self.calls.clear()
            result = family.run_batch(
                self.candidate,
                self.compiler,
                [self.setup],
                self.out,
                cells,
                resume=True,
            )
            self.assertEqual(result["status"], "passed")
            self.assertEqual(len(result["modules"]), 3)
            self.assertTrue(
                all(c["resume"] for c in self.calls if not c["verify_only"])
            )
            self.assertEqual(sum(c["verify_only"] for c in self.calls), 3)

    def test_write_modes_reject_links_before_touching_targets(self) -> None:
        """Regular and dangling links cannot redirect writes during recovery."""
        self.run_batch()
        target = self.root / "untouched.txt"
        target.write_text("must survive")
        for resume in (False, True):
            for suffix in (".lean", ".log", ".setup.json", ".receipt.json.tmp"):
                path = self.out / ("AIFPolynomialBin0Slab81" + suffix)
                before = path.read_bytes() if path.exists() else None
                path.unlink(missing_ok=True)
                for destination in (target, self.root / "missing.txt"):
                    path.symlink_to(destination)
                    self.calls.clear()
                    with self.assertRaisesRegex(ValueError, "unsafe entry"):
                        self.run_batch(resume=resume)
                    self.assertFalse(self.calls)
                    self.assertEqual(target.read_text(), "must survive")
                    self.assertFalse((self.root / "missing.txt").exists())
                    path.unlink()
                if before is not None:
                    path.write_bytes(before)


class SetupAndClosureTests(unittest.TestCase):
    """Check the real setup gate and local import closure without mock Lean."""

    def test_source_closure_includes_every_local_import(self) -> None:
        """New local dependencies must be explicitly pinned before use."""
        root = Path(family.__file__).resolve().parent
        for name in family.INPUT_MODULES:
            tree = ast.parse((root / (name + ".py")).read_text())
            for node in ast.walk(tree):
                names = (
                    [a.name for a in node.names]
                    if isinstance(node, ast.Import)
                    else (
                        [node.module]
                        if isinstance(node, ast.ImportFrom) and node.module
                        else []
                    )
                )
                for imported in names:
                    if (root / (imported + ".py")).is_file():
                        self.assertIn(imported, family.INPUT_MODULES)

    def test_helper_is_explicitly_required(self) -> None:
        """A source import alone does not supply an unambiguous Lake context."""
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "setup.json"
            setup = {"name": "fixture", "plugins": [], "importArts": {}}
            path.write_text(json.dumps(setup))
            with self.assertRaisesRegex(ValueError, "helper"):
                family.make_setup([path])
            setup["importArts"][family.HELPER] = ["helper.olean"]
            path.write_text(json.dumps(setup))
            self.assertEqual(family.make_setup([path]), setup)


if __name__ == "__main__":
    unittest.main()
