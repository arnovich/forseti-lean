"""Regressions for the companion experiment's coverage and nonmutating checks."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import aif_error_containment as containment


class ErrorContainmentTests(unittest.TestCase):
    """Keep companions bound to the existing six slab modules."""

    def test_six_companions_check_all_four_coefficients(self) -> None:
        """Every old slab is imported, with its own four kernel checks."""
        sources = containment.generate()
        self.assertEqual(len(sources), 6)
        for b in (0, 7):
            for i in (0, 40, 80):
                source = sources[f"AIFContainmentBin{b}Slab{i}.lean"]
                self.assertIn(
                    f"import Gimle.Forseti.Examples.AIFCoverageBin{b}Slab{i}", source
                )
                self.assertEqual(source.count("decide +kernel"), 4)
                self.assertIn("error_contained_of_certificates", source)
                self.assertIn("exact drift_bound_physical t p e ht hp", source)
                self.assertIn(
                    "(he : matrixForm (metric slab (timeCoordinate slab t)) e ≤ 1/40000)",
                    source,
                )
                self.assertEqual(source.count("#print axioms"), 2)
                self.assertNotIn("def slab", source)

    def test_check_is_nonmutating_and_detects_changed_source(self) -> None:
        """Checking cannot silently repair or delete experimental artifacts."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "output"
            argv = ["aif_error_containment", "--output-directory", str(root)]
            with patch("sys.argv", argv + ["--check"]):
                with self.assertRaises(SystemExit):
                    containment.main()
            self.assertFalse(root.exists())
            with patch("sys.argv", argv):
                containment.main()
            sentinel = root / "unrelated.log"
            sentinel.write_text("keep")
            original = {
                p.name: (p.read_bytes(), p.stat().st_mtime_ns) for p in root.iterdir()
            }
            with patch("sys.argv", argv + ["--check"]):
                containment.main()
            self.assertEqual(
                original,
                {
                    p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                    for p in root.iterdir()
                },
            )
            changed = root / "AIFContainmentBin7Slab80.lean"
            changed.write_text("tampered")
            with patch("sys.argv", argv + ["--check"]):
                with self.assertRaises(SystemExit):
                    containment.main()
            self.assertEqual(changed.read_text(), "tampered")
            self.assertEqual(sentinel.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
