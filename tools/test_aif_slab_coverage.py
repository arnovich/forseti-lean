"""Independent endpoint checks for the multi-scale AIF proposal experiment."""

from __future__ import annotations

import gzip
import hashlib
import json
import tempfile
import unittest
from contextlib import redirect_stderr
from fractions import Fraction as F
from io import StringIO
from pathlib import Path
from unittest.mock import patch

import aif_slab_coverage as coverage


class SlabCoverageTests(unittest.TestCase):
    """Exercise physical slopes, eta endpoints and nonmutating verification."""

    def test_target_entries_retain_physical_rates_and_eta_endpoints(self) -> None:
        """Compare independently calculated block entries at both endpoints."""
        zero = [F(0)] * 4
        vectors = [zero, zero, [F(5), *zero[1:]], [F(7), *zero[1:]]] * 2
        metrics = [
            [[F(scale * (i == j)) for j in range(4)] for i in range(4)]
            for scale in (1, 2, 2, 3)
        ]
        for step in (F(1, 200), F(1, 50), F(1, 10)):
            tables = coverage.coefficient_matrices(
                vectors, metrics, step, F(23, 2), F(12)
            )
            for label, table in tables.items():
                ec = F(-3 if label == "Negative" else 3, 200)
                self.assertEqual(table[0][0][0][1], 5)
                self.assertEqual(table[9][3][0][1], 14)
                self.assertEqual(
                    table[0][0][4][4], -2 + 2 * F(23, 2) * (2 + ec) - F(1, 100)
                )
                self.assertEqual(
                    table[9][3][4][4], -3 + 4 * F(12) * (2 + ec) - F(2, 100)
                )
                self.assertEqual(table[0][0][0][0], F(3, 16000000))

    def test_selected_candidate_inputs_are_decoded(self) -> None:
        """Distinct array/bin/node values catch selection and slope-index swaps."""
        times = ["0"] * 82
        for index, start, end in (
            (0, "0", "1/200"),
            (40, "1/5", "11/50"),
            (80, "1", "11/10"),
        ):
            times[index], times[index + 1] = start, end
        tubes = []
        for bin_index in range(8):
            arrays = []
            for array in range(6):
                nodes = []
                for node in range(82):
                    base = 100000 * bin_index + 10000 * array + 100 * node
                    nodes.append(
                        [base + i for i in range(4)]
                        if array < 4
                        else [[base + 10 * i + j for j in range(4)] for i in range(4)]
                    )
                arrays.append(nodes)
            tubes.append(arrays)
        data = {
            "denominator": 1,
            "time_nodes": times,
            "eta_edges": [str(F(8) + F(k, 2)) for k in range(9)],
            "tubes": tubes,
        }
        payload = gzip.compress(json.dumps(data).encode())
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candidate.gz"
            path.write_bytes(payload)
            with (
                patch.object(
                    coverage, "CANDIDATE_SHA256", hashlib.sha256(payload).hexdigest()
                ),
                patch.object(coverage, "coefficient_matrices", return_value={}),
            ):
                output = coverage.generate(path)
        self.assertEqual(
            set(output),
            {f"AIFCoverageBin{b}Slab{i}.lean" for b in (0, 7) for i in (0, 40, 80)},
        )
        source = output["AIFCoverageBin7Slab40.lean"]
        for field, expected in (
            ("tStart", "1 / 5"),
            ("step", "1 / 50"),
            ("etaLo", "23 / 2"),
            ("etaHi", "12 / 1"),
        ):
            self.assertIn(f"  {field} := ({expected})", source)
        for field, value in (
            ("loStart", 704000),
            ("loEnd", 704100),
            ("loStartSlope", 724000),
            ("loEndSlope", 724100),
            ("hiStart", 714000),
            ("hiEnd", 714100),
            ("hiStartSlope", 734000),
            ("hiEndSlope", 734100),
        ):
            self.assertIn(f"  {field} := ![({value} / 1), ({value+1} / 1)", source)
        for field, value in (
            ("startMetric", 744000),
            ("endMetric", 744100),
            ("startMetricSlope", 754000),
            ("endMetricSlope", 754100),
        ):
            self.assertIn(f"  {field} := ![![({value} / 1), ({value+1} / 1)", source)

    def test_polynomial_binding_uses_checked_model_identity(self) -> None:
        """The optional backend replaces only the binding, retaining all certificates."""
        zero_matrix = [[F(0) for _ in range(5)] for _ in range(5)]
        tables = [[zero_matrix for _ in range(4)] for _ in range(10)]
        for label, sign in (("Negative", -1), ("Positive", 1)):
            source = coverage.endpoint_source(label, tables, polynomial_binding=True)
            self.assertIn("theorem checked", source)
            self.assertIn("RationalPolynomial.equivalent", source)
            self.assertIn(f"AIFPolynomialBinding.block slab ({sign} * (3/200))", source)
            self.assertIn("AIFPolynomialBinding.tensor coefficients", source)
            self.assertIn("decide +kernel", source)
            self.assertIn("AIFPolynomialBinding.binding slab", source)
            self.assertIn("target_nonnegative certificates valid (binding s u)", source)
            self.assertNotIn("ring1", source)
            self.assertEqual(source.count("theorem valid_"), 40)

    def test_rejects_changed_candidate(self) -> None:
        """Different bytes never become a new candidate implicitly."""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candidate.gz"
            path.write_bytes(b"unbound")
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                coverage.generate(path)

    def test_check_never_creates_or_repairs(self) -> None:
        """Verification requires exact bytes and preserves missing or bad output."""
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory) / "batch"
            with (
                patch.object(
                    coverage, "generate", return_value={"Sample.lean": "exact\n"}
                ),
                patch(
                    "sys.argv",
                    [
                        "coverage",
                        "unused",
                        "--output-directory",
                        str(destination),
                        "--check",
                    ],
                ),
            ):
                with self.assertRaises(SystemExit):
                    coverage.main()
                self.assertFalse(destination.exists())
                destination.mkdir()
                path = destination / "Sample.lean"
                path.write_bytes(b"exact\n")
                stamp = path.stat().st_mtime_ns
                coverage.main()
                self.assertEqual(stamp, path.stat().st_mtime_ns)
                path.write_bytes(b"exact\r\n")
                with self.assertRaises(SystemExit):
                    coverage.main()
                self.assertEqual(path.read_bytes(), b"exact\r\n")

    def test_canonical_output_is_rejected(self) -> None:
        """The experiment cannot overwrite canonical pilot modules."""
        with (
            patch(
                "sys.argv",
                ["coverage", "unused", "--output-directory", str(coverage.drift.ROOT)],
            ),
            redirect_stderr(StringIO()),
        ):
            with self.assertRaises(SystemExit) as error:
                coverage.main()
            self.assertEqual(error.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
