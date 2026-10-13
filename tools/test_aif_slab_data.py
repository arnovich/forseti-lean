"""Preservation and nonmutating CLI checks for rational slab-data proofs."""

from __future__ import annotations

import gzip
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import aif_slab_coverage as original
import aif_slab_data as subject


class SlabDataTests(unittest.TestCase):
    """Exercise exact proof replacement without a private candidate dependency."""

    def test_candidate_cell_bodies_are_preserved(self) -> None:
        """Retain full generated bodies at both bin and mesh extremes."""
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
        cells = ((0, 0), (0, 369), (7, 0), (7, 369))
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / "candidate.gz"
            candidate.write_bytes(payload)
            with patch.object(
                original, "CANDIDATE_SHA256", hashlib.sha256(payload).hexdigest()
            ):
                baseline = original.generate(
                    candidate, polynomial_binding=True, selections=cells
                )
                proposal = subject.generate(candidate, selections=cells)
        self.assertEqual(set(proposal), set(baseline))
        for name, body in proposal.items():
            reverted = body.replace(
                "import Gimle.Forseti.Examples.AIFSlabData\n", "", 1
            )
            reverted = reverted.replace(subject.NEW_SYMMETRY, subject.OLD_SYMMETRY, 1)
            reverted = reverted.replace("(by decide +kernel)", "(by norm_num [slab])")
            self.assertEqual(reverted, baseline[name], name)
            self.assertEqual(body.count("theorem drift_bound_physical"), 1)

    def test_rejects_unrecognized_source_shape(self) -> None:
        """Generator drift must fail instead of silently changing proof scope."""
        with patch.object(
            original, "generate", return_value={"Test.lean": "unexpected"}
        ):
            with self.assertRaises(ValueError):
                subject.generate(Path("unused"), selections=((0, 0),))

    def test_rejects_changed_interval_proof_shape(self) -> None:
        """Do not replace an unexpected number of rational side conditions."""
        source = (
            "import Gimle.Forseti.Examples.AIFPolynomialBinding\n"
            + subject.OLD_SYMMETRY
        )
        source += subject.DRIFT_MARKER + "\n(by norm_num [slab])\n"
        with patch.object(original, "generate", return_value={"Test.lean": source}):
            with self.assertRaisesRegex(ValueError, "two rational interval"):
                subject.generate(Path("unused"), selections=((0, 0),))

    def test_check_does_not_repair_or_create_files(self) -> None:
        """A stale or absent output fails without any filesystem mutation."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / ".lake" / "check"
            args = [
                "aif_slab_data",
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


if __name__ == "__main__":
    unittest.main()
