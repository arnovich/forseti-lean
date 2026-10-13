"""Regression coverage for nonmutating circuit-solution source checks."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import aif_circuit_solution as solution


class CircuitSolutionTests(unittest.TestCase):
    """Check that source verification never creates or repairs evidence."""

    def test_check_rejects_missing_directory_without_creating_it(self) -> None:
        """A missing artifact is a failure, not an invitation to generate it."""
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "missing"
            argv = ["solution", "--output-directory", str(destination), "--check"]
            with patch("sys.argv", argv), self.assertRaises(SystemExit):
                solution.main()
            self.assertFalse(destination.exists())

    def test_check_preserves_files_and_rejects_changed_source(self) -> None:
        """A successful check preserves timestamps; a failed one preserves edits."""
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory)
            argv = ["solution", "--output-directory", str(destination)]
            with patch("sys.argv", argv):
                solution.main()
            before = {
                p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                for p in destination.iterdir()
            }
            self.assertTrue(before)
            with patch("sys.argv", argv + ["--check"]):
                solution.main()
            self.assertEqual(
                before,
                {
                    p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                    for p in destination.iterdir()
                },
            )
            changed = destination / next(iter(before))
            changed.write_bytes(b"changed proof source\n")
            with patch("sys.argv", argv + ["--check"]):
                with self.assertRaises(SystemExit):
                    solution.main()
            self.assertEqual(changed.read_bytes(), b"changed proof source\n")


if __name__ == "__main__":
    unittest.main()
