"""Hostile shape and exact nodal-data regressions for the complete AIF mesh."""

from __future__ import annotations

import copy
import gzip
import hashlib
import json
import re
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

import aif_mesh as mesh


def fixture() -> dict:
    """Use unique bin, field, node and coordinate values to expose swaps."""
    return {
        "denominator": 1000,
        "time_nodes": [str(k) for k in range(371)],
        "eta_edges": [str(k + 8) for k in range(9)],
        "tubes": [
            [
                [
                    (
                        [100000 * b + 10000 * a + 100 * k + i for i in range(4)]
                        if a < 4
                        else [
                            [
                                100000 * b + 10000 * a + 100 * k + 10 * i + j
                                for j in range(4)
                            ]
                            for i in range(4)
                        ]
                    )
                    for k in range(371)
                ]
                for a in range(6)
            ]
            for b in range(8)
        ],
    }


class MeshTests(unittest.TestCase):
    """Check complete dimensions before emitting Lean data."""

    def test_decode_exact_fields(self) -> None:
        """Decoding uses both endpoint families and physical slopes in order."""
        data = fixture()
        for b in (0, 3, 7):
            source = mesh.bin_source(data, b)
            self.assertIn(f"namespace Gimle.Forseti.Examples.AIFMeshBin{b}", source)
            records = source.split("noncomputable def data : Array Knot := #[\n", 1)[
                1
            ].split("\n},\n{\n")
            self.assertEqual(len(records), 371)
            for k in (0, 40, 80, 370):
                record = records[k]
                for a, name in enumerate(
                    ("lo", "hi", "loSlope", "hiSlope", "value", "slope")
                ):
                    field = re.split(
                        r"\n  [A-Za-z]+ :=",
                        record.split(name + " := ", 1)[1],
                        maxsplit=1,
                    )[0]
                    values = [
                        Fraction(int(n), int(d))
                        for n, d in re.findall(r"\((-?\d+) / (\d+)\)", field)
                    ]
                    expected = (
                        [
                            Fraction(100000 * b + 10000 * a + 100 * k + i, 1000)
                            for i in range(4)
                        ]
                        if a < 4
                        else [
                            Fraction(
                                100000 * b + 10000 * a + 100 * k + 10 * i + j, 1000
                            )
                            for i in range(4)
                            for j in range(4)
                        ]
                    )
                    self.assertEqual(values, expected, (b, k, name))

    def test_missing_bin_node_coordinate_or_positive_width_rejected(self) -> None:
        """No fallback zeros or omitted intervals may pass shape validation."""
        data = fixture()
        changes = (
            lambda d: d["tubes"].pop(),
            lambda d: d["tubes"][0][4].pop(),
            lambda d: d["tubes"][0][0][0].pop(),
            lambda d: d["tubes"][0][4][0][0].pop(),
            lambda d: d["time_nodes"].__setitem__(40, d["time_nodes"][39]),
            lambda d: d["eta_edges"].__setitem__(8, d["eta_edges"][7]),
            lambda d: d.__setitem__("denominator", 0),
            lambda d: d.__setitem__("denominator", True),
        )
        for change in changes:
            with self.subTest(change=change):
                altered = copy.deepcopy(data)
                change(altered)
                with self.assertRaises(ValueError):
                    mesh.validate(altered)

    def test_hash_and_nonmutating_check(self) -> None:
        """Only exact candidate bytes are decoded; check mode never writes."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            candidate = root / "candidate.gz"
            payload = gzip.compress(json.dumps(fixture()).encode())
            candidate.write_bytes(payload)
            with self.assertRaisesRegex(ValueError, "SHA-256"):
                mesh.generate(candidate)
            with patch.object(
                mesh, "CANDIDATE_SHA256", hashlib.sha256(payload).hexdigest()
            ):
                outputs = mesh.generate(candidate)
            self.assertEqual(
                len(outputs), 16
            )  # geometry, eight bins, root, six bindings
            destination = root / "output"
            argv = ["aif_mesh", str(candidate), "--output-directory", str(destination)]
            with patch.object(mesh, "generate", return_value=outputs):
                with patch("sys.argv", argv + ["--check"]):
                    with self.assertRaises(SystemExit):
                        mesh.main()
                self.assertFalse(destination.exists())
                with patch("sys.argv", argv):
                    mesh.main()
                before = {
                    p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                    for p in destination.iterdir()
                }
                with patch("sys.argv", argv + ["--check"]):
                    mesh.main()
                self.assertEqual(
                    before,
                    {
                        p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                        for p in destination.iterdir()
                    },
                )
                changed = destination / "AIFCandidateMesh.lean"
                changed.write_text("changed")
                with patch("sys.argv", argv + ["--check"]):
                    with self.assertRaises(SystemExit):
                        mesh.main()
                self.assertEqual(changed.read_text(), "changed")


if __name__ == "__main__":
    unittest.main()
