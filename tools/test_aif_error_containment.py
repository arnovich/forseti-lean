"""Regressions for the companion experiment's coverage and nonmutating checks."""

from __future__ import annotations

import tempfile
import unittest
from contextlib import redirect_stderr
from io import StringIO
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

    def test_polynomial_selections_import_exact_slabs_without_name_collisions(
        self,
    ) -> None:
        """Selected companions compose checked polynomial drift without copied data."""
        cells = ((1, 200), (7, 300))
        sources = containment.generate(selections=cells, polynomial_binding=True)
        self.assertEqual(
            set(sources),
            {
                "AIFPolynomialContainmentBin1Slab200.lean",
                "AIFPolynomialContainmentBin7Slab300.lean",
            },
        )
        for b, i in cells:
            source = sources[f"AIFPolynomialContainmentBin{b}Slab{i}.lean"]
            self.assertIn(
                f"import Gimle.Forseti.Examples.AIFPolynomialBin{b}Slab{i}\n", source
            )
            self.assertIn(
                f"namespace Gimle.Forseti.Examples.AIFPolynomialContainmentBin{b}Slab{i}",
                source,
            )
            self.assertNotIn("AIFCoverage", source)
            self.assertNotIn("def slab", source)
            self.assertEqual(source.count("decide +kernel"), 4)
            self.assertEqual(source.count("#print axioms"), 2)
        expanded = containment.generate(selections=cells)
        self.assertEqual(
            set(expanded), {f"AIFContainmentBin{b}Slab{i}.lean" for b, i in cells}
        )

    def test_invalid_selections_are_rejected(self) -> None:
        """Companion generation shares the drift generator's exact mesh bounds."""
        for cells in ((), ((0, 0), (0, 0)), ((8, 0),), ((0, 370),), ((True, 0),)):
            with self.subTest(cells=cells), self.assertRaises(ValueError):
                containment.generate(selections=cells)

    def test_selected_cli_check_is_exact_and_nonmutating(self) -> None:
        """CLI selections reach the generator; check mode never repairs altered bytes."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "selected"
            argv = [
                "containment",
                "--output-directory",
                str(root),
                "--polynomial-binding",
                "--cell",
                "1:200",
                "--cell",
                "7:300",
            ]
            with patch("sys.argv", argv):
                containment.main()
            expected = containment.generate(
                selections=((1, 200), (7, 300)), polynomial_binding=True
            )
            self.assertEqual({p.name: p.read_text() for p in root.iterdir()}, expected)
            before = {
                p.name: (p.read_bytes(), p.stat().st_mtime_ns) for p in root.iterdir()
            }
            with patch("sys.argv", argv + ["--check"]):
                containment.main()
            self.assertEqual(
                before,
                {
                    p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                    for p in root.iterdir()
                },
            )
            changed = root / "AIFPolynomialContainmentBin1Slab200.lean"
            changed.write_bytes(changed.read_bytes().replace(b"\n", b"\r\n"))
            altered = changed.read_bytes()
            with patch("sys.argv", argv + ["--check"]), self.assertRaises(SystemExit):
                containment.main()
            self.assertEqual(changed.read_bytes(), altered)

    def test_invalid_cli_does_not_create_output(self) -> None:
        """Reject malformed and duplicate requests before making a destination."""
        for cells in (("8:0",), ("1:200", "1:200")):
            with self.subTest(cells=cells), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp) / "absent"
                argv = ["containment", "--output-directory", str(root)]
                argv += [part for cell in cells for part in ("--cell", cell)]
                with patch("sys.argv", argv), redirect_stderr(
                    StringIO()
                ), self.assertRaises(SystemExit):
                    containment.main()
                self.assertFalse(root.exists())

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
