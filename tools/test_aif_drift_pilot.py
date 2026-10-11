"""Regression tests for the exact, untrusted AIF drift proposal generator."""

from __future__ import annotations

import tempfile
import unittest
from contextlib import redirect_stderr
from fractions import Fraction as F
from io import StringIO
from math import comb
from pathlib import Path
from unittest.mock import patch

import aif_drift_pilot as drift


class DriftProposalTests(unittest.TestCase):
    """Check scaling, both polynomial axes and rejected input bytes."""

    def test_compact_certificate_preserves_kernel_check(self) -> None:
        """Compact proposals change data construction, never the validity rule."""
        matrix = [[F(2), F(1)], [F(1), F(2)]]
        literal = drift.certificate_source(0, 1, matrix, compact=False)
        compact = drift.certificate_source(0, 1, matrix, compact=True)
        proof = literal.partition("set_option")[2]
        self.assertEqual(compact.partition("set_option")[2], proof)
        self.assertIn("decide +kernel", proof)
        self.assertIn("RationalLDL.propose (coefficients 0 1)", compact)
        self.assertNotIn("weight :=", compact)

    def test_compact_mode_requires_separate_output(self) -> None:
        """An experiment cannot overwrite the checked literal pilot by default."""
        for extra in ([], ["--output-directory", str(drift.ROOT)]):
            with (
                patch(
                    "sys.argv", ["aif_drift_pilot.py", "unused.gz", "--compact", *extra]
                ),
                redirect_stderr(StringIO()),
            ):
                with self.assertRaises(SystemExit) as error:
                    drift.main()
            self.assertEqual(error.exception.code, 2)

    def test_compact_check_never_creates_or_repairs_outputs(self) -> None:
        """Check mode validates the selected representation without writing."""
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "compact"
            expected = "-- compact proposal\n"
            with (
                patch.object(
                    drift, "generate", return_value={"Example.lean": expected}
                ) as gen,
                patch(
                    "sys.argv",
                    [
                        "aif_drift_pilot.py",
                        "unused.gz",
                        "--compact",
                        "--check",
                        "--output-directory",
                        str(destination),
                    ],
                ),
            ):
                with self.assertRaises(SystemExit):
                    drift.main()
                self.assertFalse(destination.exists())
                destination.mkdir()
                output = destination / "Example.lean"
                output.write_text(expected)
                stamp = output.stat().st_mtime_ns
                drift.main()
                self.assertEqual(output.stat().st_mtime_ns, stamp)
                gen.assert_called_with(Path("unused.gz"), compact=True)
                output.write_text("changed")
                with self.assertRaises(SystemExit):
                    drift.main()
                self.assertEqual(output.read_text(), "changed")

    def test_hermite_physical_endpoint_derivatives(self) -> None:
        """Endpoint slopes are physical rates on a slab of width 1/10."""
        polynomial = drift.hermite(F(2), F(3), F(5), F(7))
        rate = drift.dt(polynomial)
        self.assertEqual(rate[(0, 0)], F(5))
        self.assertEqual(sum(rate.values()), F(7))
        self.assertEqual(polynomial[(0, 0)], F(2))
        self.assertEqual(sum(polynomial.values()), F(3))

    def test_all_candidate_step_sizes_preserve_physical_slopes(self) -> None:
        """Every mesh scale interpolates endpoint values and physical rates."""
        for step in (F(1, 200), F(1, 50), F(1, 10)):
            with self.subTest(step=step):
                p = drift.hermite(F(2), F(3), F(5), F(7), step=step)
                rate = drift.dt(p, step=step)
                self.assertEqual(p[(0, 0)], 2)
                self.assertEqual(sum(p.values()), 3)
                self.assertEqual(rate[(0, 0)], 5)
                self.assertEqual(sum(rate.values()), 7)
                self.assertEqual(
                    drift.dt({(1, 0): F(1)}, step=step), {(0, 0): 1 / step}
                )
        for step in (F(0), F(-1)):
            with self.assertRaisesRegex(ValueError, "positive"):
                drift.hermite(F(2), F(3), F(5), F(7), step=step)
            with self.assertRaisesRegex(ValueError, "positive"):
                drift.dt({}, step=step)

    def test_tensor_reconstruction_retains_both_axes(self) -> None:
        """Reconstruct a mixed degree-nine/degree-three polynomial exactly."""
        polynomial = {(0, 0): F(2), (9, 3): F(7, 11), (2, 1): F(-3, 5)}
        for s, u in ((F(0), F(0)), (F(1), F(1)), (F(2, 7), F(3, 11))):
            expected = sum(v * s**i * u**j for (i, j), v in polynomial.items())
            actual = sum(
                drift.bernstein(polynomial, a, b)
                * comb(9, a)
                * s**a
                * (1 - s) ** (9 - a)
                * comb(3, b)
                * u**b
                * (1 - u) ** (3 - b)
                for a in range(10)
                for b in range(4)
            )
            self.assertEqual(actual, expected)
        for exponent in ((10, 0), (0, 4)):
            with self.assertRaisesRegex(ValueError, "exceeds declared degree"):
                drift.bernstein({exponent: F(1)}, 0, 0)

    def test_check_rejects_changed_bytes_without_writing(self) -> None:
        """Check mode must not normalize line endings or repair bad output."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "Example.lean"
            expected = "-- exact proposal\n"
            with (
                patch.object(drift, "ROOT", root),
                patch.object(drift, "generate", return_value={output.name: expected}),
                patch("sys.argv", ["aif_drift_pilot.py", "unused.gz", "--check"]),
            ):
                output.write_bytes(expected.encode())
                stamp = output.stat().st_mtime_ns
                drift.main()
                self.assertEqual(output.stat().st_mtime_ns, stamp)
                for changed in (b"changed", expected.replace("\n", "\r\n").encode()):
                    output.write_bytes(changed)
                    with self.assertRaises(SystemExit):
                        drift.main()
                    self.assertEqual(output.read_bytes(), changed)
                output.unlink()
                with self.assertRaises(SystemExit):
                    drift.main()
                self.assertFalse(output.exists())

    def test_rejects_unbound_candidate_before_parsing(self) -> None:
        """Different bytes cannot silently replace the selected proposal."""
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / "candidate.json.gz"
            candidate.write_bytes(b"unbound input")
            with self.assertRaisesRegex(ValueError, "SHA-256 mismatch"):
                drift.generate(candidate)


if __name__ == "__main__":
    unittest.main()
