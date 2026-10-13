"""Regression tests for selected output certificates and nonmutating checks."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import aif_output_certificates as output


class OutputCertificateTests(unittest.TestCase):
    """Keep cell selections exact and preserve evidence during checks."""

    def test_selections_and_binding_modes_have_exact_distinct_names(self) -> None:
        """Expanded and polynomial imports remain separate for the same cells."""
        cells = ((0, 0), (7, 369))
        expanded = output.generate(selections=cells)
        polynomial = output.generate(selections=cells, polynomial_binding=True)
        self.assertEqual(
            set(expanded), {f"AIFOutputBin{b}Slab{i}.lean" for b, i in cells}
        )
        self.assertEqual(
            set(polynomial),
            {f"AIFPolynomialOutputBin{b}Slab{i}.lean" for b, i in cells},
        )
        self.assertTrue(set(expanded).isdisjoint(polynomial))

    def test_invalid_selections_are_rejected(self) -> None:
        """Reject empty, duplicate, malformed and out-of-mesh selections."""
        for cells in ((), ((0, 0), (0, 0)), ((8, 0),), ((0, 370),), ((True, 0),)):
            with self.subTest(cells=cells), self.assertRaises(ValueError):
                output.generate(selections=cells)

    def test_cli_check_preserves_evidence_and_rejects_modified_source(self) -> None:
        """A requested selection reaches generation, and check never repairs it."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "missing"
            argv = [
                "output",
                "--output-directory",
                str(root),
                "--polynomial-binding",
                "--cell",
                "2:20",
            ]
            with patch("sys.argv", argv + ["--check"]), self.assertRaises(SystemExit):
                output.main()
            self.assertFalse(root.exists())
            with patch("sys.argv", argv):
                output.main()
            self.assertEqual(
                {p.name: p.read_text() for p in root.iterdir()},
                output.generate(selections=((2, 20),), polynomial_binding=True),
            )
            sentinel = root / "unrelated.log"
            sentinel.write_text("keep")
            before = {
                p.name: (p.read_bytes(), p.stat().st_mtime_ns) for p in root.iterdir()
            }
            with patch("sys.argv", argv + ["--check"]):
                output.main()
            self.assertEqual(
                before,
                {
                    p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                    for p in root.iterdir()
                },
            )
            path = root / "AIFPolynomialOutputBin2Slab20.lean"
            path.write_text("changed")
            with patch("sys.argv", argv + ["--check"]), self.assertRaises(SystemExit):
                output.main()
            self.assertEqual(path.read_text(), "changed")
            self.assertEqual(sentinel.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
