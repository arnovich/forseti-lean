"""Control-flow and stale-evidence regressions for the AIF batch runner."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any
from unittest.mock import patch

import aif_replay as replay


class ReplayTests(unittest.TestCase):
    """Synthetic compiler outputs test bookkeeping, never mathematical validity."""

    def setUp(self) -> None:
        """Create isolated synthetic source and compiler fixtures."""
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.compiler = self.root / "toolchain" / "bin" / "lean"
        self.compiler.parent.mkdir(parents=True)
        self.compiler.write_bytes(b"synthetic compiler fixture")
        self.imported = self.root / "Imported.olean"
        self.imported.write_bytes(b"import fixture")
        self.setup = {
            "name": "test",
            "plugins": [],
            "options": {},
            "importArts": {"Imported": [str(self.imported)]},
        }
        self.context = replay.environment_fingerprint(self.compiler, self.setup)
        self.name = "AIFPolynomialBin3Slab369"
        self.calls = 0

    def fake_compile(
        self, command: list[str], **kwargs: Any
    ) -> subprocess.CompletedProcess:
        """Emit the exact report set expected by the bookkeeping fixture."""
        self.calls += 1
        Path(command[command.index("-o") + 1]).write_bytes(b"fixture artifact")
        kwargs["stdout"].write(self.valid_log())
        return subprocess.CompletedProcess(command, 0)

    def valid_log(self) -> str:
        """Return the exact allowed report set for the current fixture."""
        return "\n".join(
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            for name in replay.expected_reports(self.name)
        )

    def run_cell(self, *, resume: bool = False, verify_only: bool = False) -> dict:
        """Replay the fixture with the chosen cache policy."""
        return replay.replay_cell(
            self.root,
            self.name,
            "fixture source\n",
            self.compiler,
            self.setup,
            self.context,
            resume=resume,
            verify_only=verify_only,
        )

    def test_resume_rechecks_outputs_and_source(self) -> None:
        """Only matching source, artifact, log and context permit reuse."""
        with patch.object(replay.subprocess, "run", side_effect=self.fake_compile):
            first = self.run_cell()
            self.assertEqual(self.calls, 1)
            self.assertEqual(first["status"], "compiled")
            self.assertEqual(self.run_cell(resume=True)["status"], "reused")
            self.assertEqual(self.calls, 1)
            for suffix in (".lean", ".olean", ".log", ".setup.json", ".receipt.json"):
                (self.root / (self.name + suffix)).write_text("changed")
                self.run_cell(resume=True)
                self.assertEqual(
                    self.calls,
                    2
                    + (".lean", ".olean", ".log", ".setup.json", ".receipt.json").index(
                        suffix
                    ),
                )

    def test_changed_import_or_compiler_invalidates_reuse(self) -> None:
        """A matching source cannot conceal a changed checking environment."""
        with patch.object(replay.subprocess, "run", side_effect=self.fake_compile):
            self.run_cell()
            for path in (self.imported, self.compiler):
                path.write_bytes(b"changed environment")
                previous = self.context
                self.context = replay.environment_fingerprint(self.compiler, self.setup)
                self.assertNotEqual(previous, self.context)
                self.assertEqual(self.run_cell(resume=True)["status"], "compiled")
            self.assertEqual(self.calls, 3)

    def test_verify_only_is_nonmutating_and_rejects_missing_or_changed(self) -> None:
        """Read-only verification never creates or repairs a receipt."""
        before = {p.name: p.read_bytes() for p in self.root.iterdir() if p.is_file()}
        with self.assertRaises(ValueError):
            self.run_cell(verify_only=True)
        self.assertEqual(
            before, {p.name: p.read_bytes() for p in self.root.iterdir() if p.is_file()}
        )
        with patch.object(replay.subprocess, "run", side_effect=self.fake_compile):
            self.run_cell()
        stamps = {
            p.name: p.stat().st_mtime_ns for p in self.root.iterdir() if p.is_file()
        }
        self.assertEqual(self.run_cell(verify_only=True)["status"], "reused")
        self.assertEqual(
            stamps,
            {p.name: p.stat().st_mtime_ns for p in self.root.iterdir() if p.is_file()},
        )
        (self.root / (self.name + ".olean")).write_bytes(b"changed")
        with self.assertRaises(ValueError):
            self.run_cell(verify_only=True)
        self.assertEqual((self.root / (self.name + ".olean")).read_bytes(), b"changed")

    def test_failure_never_leaves_an_accepted_receipt(self) -> None:
        """An old artifact and receipt cannot mask a later failed compiler."""
        with patch.object(replay.subprocess, "run", side_effect=self.fake_compile):
            self.run_cell()
        with patch.object(
            replay.subprocess, "run", return_value=subprocess.CompletedProcess([], 1)
        ):
            with self.assertRaises(ValueError):
                self.run_cell()
        self.assertFalse((self.root / (self.name + ".receipt.json")).exists())
        with self.assertRaises(ValueError):
            self.run_cell(verify_only=True)

    def test_reports_require_exact_names_and_allowed_axioms(self) -> None:
        """Reject missing/duplicate/foreign reports, warnings and forbidden axioms."""
        good = self.valid_log()
        replay.audit_log(good, self.name)
        for bad in (
            "",
            good + "\n" + good.splitlines()[0],
            good.replace("drift_bound_physical", "unrelated"),
            good.replace("Quot.sound", "sorryAx"),
            good + "\nwarning: bad",
            good + "\nerror: bad",
        ):
            with self.subTest(log=bad), self.assertRaises(ValueError):
                replay.audit_log(bad, self.name)

    def test_receipt_size_is_rechecked(self) -> None:
        """A receipt cannot report an artifact size different from the file."""
        with patch.object(replay.subprocess, "run", side_effect=self.fake_compile):
            self.run_cell()
        path = self.root / (self.name + ".receipt.json")
        receipt = json.loads(path.read_text())
        receipt["olean_bytes"] += 1
        path.write_text(json.dumps(receipt))
        with self.assertRaises(ValueError):
            self.run_cell(verify_only=True)

    def run_batch(self, cells: list[str], *options: str) -> list[dict]:
        """Exercise the CLI with generated fixtures and a synthetic compiler."""
        setup_path = self.root / "setup.json"
        if not setup_path.exists():
            setup_path.write_text(json.dumps(self.setup))
        args = [
            "aif_replay.py",
            "candidate",
            "--lean",
            str(self.compiler),
            "--setup",
            str(setup_path),
            "--output-directory",
            str(self.root / ".lake" / "batch"),
            *options,
        ]
        for cell in cells:
            args.extend(["--cell", cell])
        with patch.object(sys, "argv", args), patch.object(replay, "ROOT", self.root):
            with contextlib.redirect_stdout(io.StringIO()) as output:
                replay.main()
        return [json.loads(line) for line in output.getvalue().splitlines()]

    def test_batch_failure_and_resume_are_explicit(self) -> None:
        """Partial work stays failed; resume reuses only the successful cell."""
        second = "AIFPolynomialBin4Slab369"
        sources = {self.name + ".lean": "fixture source", second + ".lean": "second"}
        for name in ("lean-toolchain", "lake-manifest.json"):
            (self.root / name).write_text("fixture")

        def compile_cell(
            command: list[str], **kwargs: Any
        ) -> subprocess.CompletedProcess:
            self.name = Path(command[-1]).stem
            return self.fake_compile(command, **kwargs)

        def fail_second(
            command: list[str], **kwargs: Any
        ) -> subprocess.CompletedProcess:
            if Path(command[-1]).stem == second:
                return subprocess.CompletedProcess(command, 1)
            return compile_cell(command, **kwargs)

        with patch.object(replay.coverage, "generate", return_value=sources):
            with patch.object(replay.subprocess, "run", side_effect=fail_second):
                with self.assertRaises(ValueError):
                    self.run_batch(["3:369", "4:369"])
            directory = self.root / ".lake" / "batch"
            manifest = json.loads((directory / "batch.json").read_text())
            self.assertEqual(manifest["status"], "failed")
            self.assertEqual(len(manifest["modules"]), 1)
            with patch.object(replay.subprocess, "run", side_effect=compile_cell):
                self.run_batch(["3:369", "4:369"], "--resume")
            self.assertEqual(self.calls, 2)
            manifest = json.loads((directory / "batch.json").read_text())
            self.assertEqual(manifest["status"], "passed")
            self.assertEqual(len(manifest["modules"]), 2)
            stamps = {p.name: p.stat().st_mtime_ns for p in directory.iterdir()}
            with patch.object(
                replay.subprocess,
                "run",
                side_effect=AssertionError("unexpected compile"),
            ):
                output = self.run_batch(["3:369", "4:369"], "--verify-only")
            self.assertEqual(
                output[-1]["environment_sha256"], manifest["environment_sha256"]
            )
            self.assertEqual(
                {r["module"] for r in output if r.get("status") == "reused"},
                {Path(name).stem for name in sources},
            )
            self.assertEqual(
                stamps, {p.name: p.stat().st_mtime_ns for p in directory.iterdir()}
            )
            sources.pop(second + ".lean")
            with self.assertRaisesRegex(ValueError, "declared batch"):
                self.run_batch(["3:369", "4:369"], "--resume")

    def test_core_artifacts_invalidate_environment(self) -> None:
        """Implicit core imports outside Lake's map must affect provenance."""
        core = self.compiler.parent.parent / "lib" / "lean" / "Init" / "Prelude.olean"
        core.parent.mkdir(parents=True)
        core.write_bytes(b"core import")
        before = replay.environment_fingerprint(self.compiler, self.setup)
        core.write_bytes(b"changed core import")
        self.assertNotEqual(
            before, replay.environment_fingerprint(self.compiler, self.setup)
        )

    def test_external_libraries_are_rejected(self) -> None:
        """Plugins and dynlibs cannot enter an incompletely hashed environment."""
        path = self.root / "setup.json"
        for key in ("plugins", "dynlibs"):
            path.write_text(json.dumps({**self.setup, key: ["external.dylib"]}))
            with self.subTest(key=key), self.assertRaises(ValueError):
                replay.merge_setups([path])

    def test_relative_imports_use_compiler_working_directory(self) -> None:
        """A caller outside ROOT must hash the same paths that Lean resolves."""
        setup = {**self.setup, "importArts": {"Imported": ["Imported.olean"]}}
        with patch.object(replay, "ROOT", self.root):
            for name in ("lean-toolchain", "lake-manifest.json"):
                (self.root / name).write_text("fixture")
            context = replay.environment_fingerprint(self.compiler, setup)
        self.assertEqual(
            context["inputs"]["artifacts"][str(self.imported.resolve())],
            replay.sha256(self.imported),
        )

    def test_setup_merge_rejects_conflicting_imports(self) -> None:
        """Import resolution cannot silently select one of two different artifacts."""
        first = self.root / "one.json"
        second = self.root / "two.json"
        first.write_text(json.dumps(self.setup))
        changed = {
            **self.setup,
            "name": "other",
            "importArts": {"Imported": ["elsewhere"]},
        }
        second.write_text(json.dumps(changed))
        with self.assertRaises(ValueError):
            replay.merge_setups([first, second])


if __name__ == "__main__":
    unittest.main()
