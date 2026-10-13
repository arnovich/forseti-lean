"""Preservation and rejection regressions for whole-family kernel proofs."""

from __future__ import annotations

import gzip
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import aif_family_checks as subject
import aif_slab_coverage as original
import aif_slab_data as baseline


class FamilyCheckTests(unittest.TestCase):
    """Use portable synthetic candidate data to exercise the full producer."""

    @classmethod
    def setUpClass(cls) -> None:
        """Generate valid-shaped data at both parameter and mesh extremes."""
        zero = [0] * 4
        identity = [[int(i == j) for j in range(4)] for i in range(4)]
        tube = [[zero] * 371 for _ in range(4)] + [[identity] * 371] * 2
        payload = gzip.compress(
            json.dumps(
                {
                    "denominator": 1,
                    "time_nodes": list(range(371)),
                    "eta_edges": list(range(8, 17)),
                    "tubes": [tube] * 8,
                }
            ).encode()
        )
        cls.cells = ((0, 0), (0, 369), (7, 0), (7, 369))
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / "candidate.gz"
            candidate.write_bytes(payload)
            with patch.object(
                original, "CANDIDATE_SHA256", hashlib.sha256(payload).hexdigest()
            ):
                cls.before = baseline.generate(candidate, selections=cls.cells)
                cls.after = subject.generate(candidate, selections=cls.cells)

    def test_data_binding_and_drift_statements_are_preserved(self) -> None:
        """Retain every certificate and both universally quantified families."""
        self.assertEqual(set(self.before), set(self.after))
        for name, after in self.after.items():
            before = self.before[name]
            self.assertEqual(
                before.split("namespace Negative\n", 1)[0],
                after.split("namespace Negative\n", 1)[0],
            )
            for label in ("Negative", "Positive"):
                old = before.split("namespace " + label + "\n", 1)[1].split(
                    "end " + label, 1
                )[0]
                new = after.split("namespace " + label + "\n", 1)[1].split(
                    "end " + label, 1
                )[0]
                self.assertEqual(
                    old.split("def cert_0_0", 1)[0], new.split("def cert_0_0", 1)[0]
                )
                for a in range(10):
                    for b in range(4):
                        declaration = f"def cert_{a}_{b} : WeightedSquares 5 :=\n  Gimle.Forseti.RationalLDL.propose (coefficients {a} {b})\n"
                        self.assertEqual(old.count(declaration), 1)
                        self.assertEqual(new.count(declaration), 1)
                old_table = (
                    old.split("def certificates", 1)[1]
                    .split("theorem valid", 1)[0]
                    .strip()
                )
                new_table = (
                    new.split("def certificates", 1)[1]
                    .split("set_option", 1)[0]
                    .strip()
                )
                self.assertEqual(old_table, new_table)
                self.assertEqual(
                    old.split("theorem binding", 1)[1],
                    new.split("theorem binding", 1)[1],
                )
                self.assertEqual(
                    old.split("theorem checked", 1)[1].split(" := by", 1)[0],
                    new.split("theorem checked", 1)[1].split(" := by", 1)[0],
                )
            self.assertEqual(
                before.split("end Positive", 1)[1], after.split("end Positive", 1)[1]
            )
            self.assertEqual(after.count("theorem valid : ∀ i j,"), 2)
            self.assertEqual(after.count("theorem checked : ∀ i j,"), 2)
            self.assertEqual(after.count("decide +kernel"), 7)
            self.assertNotIn("theorem valid_", after)

    def reject_changed_shape(self, old: str, new: str) -> None:
        """Reject unexpected upstream proof shapes during generation."""
        name, source = next(iter(self.before.items()))
        changed = source.replace(old, new, 1)
        self.assertNotEqual(changed, source)
        with patch.object(baseline, "generate", return_value={name: changed}):
            with self.assertRaises(ValueError):
                subject.generate(Path("unused"), selections=((0, 0),))

    def test_missing_certificate_proof_is_rejected(self) -> None:
        """Do not silently skip an endpoint certificate proof."""
        self.reject_changed_shape("theorem valid_9_3 :", "theorem changed_9_3 :")

    def test_changed_validity_dispatch_is_rejected(self) -> None:
        """Require every expected entry of the original finite dispatch."""
        self.reject_changed_shape("  · exact valid_9_3\n", "")

    def test_changed_polynomial_check_is_rejected(self) -> None:
        """Reject changes to the original model-binding proof shape."""
        self.reject_changed_shape(
            "fin_cases i <;> fin_cases j <;> decide +kernel",
            "fin_cases i <;> fin_cases j <;> decide",
        )

    def test_check_does_not_create_or_repair_outputs(self) -> None:
        """Verification must leave missing and stale outputs unchanged."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / ".lake" / "check"
            args = [
                "aif_family_checks",
                "unused",
                "--cell",
                "0:0",
                "--output-directory",
                str(target),
                "--check",
            ]
            with patch.object(subject, "ROOT", root), patch.object(
                subject, "generate", return_value={"Cell.lean": "expected"}
            ), patch.object(sys, "argv", args):
                with self.assertRaises(SystemExit):
                    subject.main()
                self.assertFalse(target.exists())
                target.mkdir(parents=True)
                file = target / "Cell.lean"
                file.write_text("stale")
                before = file.stat().st_mtime_ns
                with self.assertRaises(SystemExit):
                    subject.main()
                self.assertEqual(file.read_text(), "stale")
                self.assertEqual(file.stat().st_mtime_ns, before)

    def test_output_outside_generated_directory_is_rejected(self) -> None:
        """The optional producer writes only beneath the repository .lake."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "outside"
            args = [
                "aif_family_checks",
                "unused",
                "--cell",
                "0:0",
                "--output-directory",
                str(target),
            ]
            with patch.object(subject, "ROOT", root), patch.object(sys, "argv", args):
                with self.assertRaises(SystemExit):
                    subject.main()
                self.assertFalse(target.exists())


if __name__ == "__main__":
    unittest.main()
