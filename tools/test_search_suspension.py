"""Regression tests for the untrusted search and its read-only replay mode."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch

import search_suspension as search


class ExactSearchTests(unittest.TestCase):
    """Exercise reconstruction, rejected proposals and the CLI boundary."""

    def test_every_square_decomposition_reconstructs_its_target(self) -> None:
        """Replay all matrix entries independently from the LDL algorithm."""
        _, _, _, _, _, targets = search.search()
        for name, _, matrix in targets:
            with self.subTest(target=name):
                weights, vectors = search.ldl(matrix)
                self.assertTrue(all(isinstance(w, F) and w > 0 for w in weights))
                reconstructed = [
                    [
                        sum(
                            w * v[i] * v[j]
                            for w, v in zip(weights, vectors, strict=True)
                        )
                        for j in range(len(matrix))
                    ]
                    for i in range(len(matrix))
                ]
                self.assertEqual(matrix, reconstructed)

    def test_rejects_asymmetric_and_nonpositive_candidates(self) -> None:
        """No tolerance can turn invalid square targets into accepted ones."""
        for matrix in (
            [[F(1), F(1)], [F(0), F(1)]],
            [[F(1), F(2)], [F(2), F(1)]],
            [[F(0)]],
        ):
            with self.subTest(matrix=matrix), self.assertRaises(ValueError):
                search.ldl(matrix)

    def test_exhaustion_does_not_claim_refutation(self) -> None:
        """An impossible proposal family reports search exhaustion only."""
        with patch.object(search, "INITIAL_FACTOR", F(0)):
            with self.assertRaisesRegex(ValueError, "root goal is not refuted"):
                search.search()

    def test_check_recomputes_and_never_repairs_corruption(self) -> None:
        """A stale artifact is rejected without being silently rewritten."""
        script = Path(search.__file__)
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "candidate.lean"
            command = [sys.executable, str(script), "--output", str(output)]
            subprocess.run(command, check=True, capture_output=True)
            original = output.read_bytes()
            stamp = output.stat().st_mtime_ns
            subprocess.run(command + ["--check"], check=True, capture_output=True)
            self.assertEqual(output.stat().st_mtime_ns, stamp)
            self.assertEqual(output.read_bytes(), original)
            corrupted = original.replace(b"def alpha :", b"def tamperedAlpha :", 1)
            self.assertNotEqual(corrupted, original)
            output.write_bytes(corrupted)
            rejected = subprocess.run(command + ["--check"], capture_output=True)
            self.assertNotEqual(rejected.returncode, 0)
            self.assertEqual(output.read_bytes(), corrupted)
            output.write_bytes(original.replace(b"\n", b"\r\n"))
            newline_variant = subprocess.run(command + ["--check"], capture_output=True)
            self.assertNotEqual(newline_variant.returncode, 0)
            output.unlink()
            missing = subprocess.run(command + ["--check"], capture_output=True)
            self.assertNotEqual(missing.returncode, 0)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
