"""Regression tests for the Galerkin generator and its read-only check mode."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from fractions import Fraction as F
from pathlib import Path
from unittest.mock import patch

import galerkin_ns as gen


class DerivationTests(unittest.TestCase):
    """The single triad of T3, the invariants, and the certificate."""

    def test_t3_is_one_triad_with_the_textbook_coefficients(self) -> None:
        member = gen.MEMBERS[0]
        [triad] = gen.triads(member.modes)
        self.assertEqual(triad.modes, ((1, 0), (1, 1), (2, 1)))
        self.assertEqual(triad.coefficients, (F(-3, 20), F(2, 5), F(-1, 4)))

    def test_every_triad_conserves_energy_and_enstrophy(self) -> None:
        for member in gen.MEMBERS:
            for triad in gen.triads(member.modes):
                with self.subTest(member=member.name, triad=triad.modes):
                    weighted = sum(c / gen.lam(m) for m, c in zip(triad.modes, triad.coefficients))
                    self.assertEqual(weighted, 0)
                    self.assertEqual(sum(triad.coefficients), 0)

    def test_member_sizes_and_triad_counts(self) -> None:
        sizes = {m.name: (len(m.modes), len(gen.triads(m.modes))) for m in gen.MEMBERS}
        self.assertEqual(sizes, {"T3": (3, 1), "K5": (5, 3), "B2": (12, 22)})

    def test_the_energy_identity_has_no_cubic_terms(self) -> None:
        for member in gen.MEMBERS:
            with self.subTest(member=member.name):
                for powers in gen.rate(member):
                    self.assertLessEqual(sum(powers), 2)

    def test_verify_accepts_every_member_and_rejects_a_bad_bound(self) -> None:
        for member in gen.MEMBERS:
            gen.verify(member)
        bad = gen.Member("bad", gen.MEMBERS[0].modes, F(1, 10), F(1), F(12), 9, F(1))
        with self.assertRaises(AssertionError):
            gen.verify(bad)

    def test_the_laminar_energy_is_below_every_bound(self) -> None:
        for member in gen.MEMBERS:
            self.assertLess(member.f**2 / (8 * member.nu**2), member.bound)

    def test_the_family_coupling_summed_over_both_orders_is_the_triad_field(self) -> None:
        for member in gen.MEMBERS:
            with self.subTest(member=member.name):
                self.assertEqual(gen.family_field(member), gen.field(member))

    def test_the_family_coupling_by_hand_on_t3(self) -> None:
        # c((1,1),(2,1),(1,0)) + c((2,1),(1,1),(1,0)) is T3's coefficient of a11 a21 in a10'
        self.assertEqual(gen.coupling((1, 1), (2, 1), (1, 0)), F(-1, 4))
        self.assertEqual(gen.coupling((2, 1), (1, 1), (1, 0)), F(1, 10))
        self.assertEqual(gen.selector((1, 1), (2, 1), (1, 0)), 1)
        self.assertEqual(gen.selector((1, 0), (1, 1), (2, 1)), -1)
        self.assertEqual(gen.selector((1, 0), (1, 1), (0, 2)), 0)


class EmissionTests(unittest.TestCase):
    """The Lean text is deterministic and --check never writes."""

    def test_emission_is_deterministic(self) -> None:
        for member in gen.MEMBERS:
            self.assertEqual(gen.emit(member), gen.emit(member))

    def test_emission_bridges_each_member_to_the_family(self) -> None:
        for member in gen.MEMBERS:
            with self.subTest(member=member.name):
                text = gen.emit(member)
                forced = member.modes.index(gen.FORCED)
                self.assertIn("import Gimle.Forseti.GalerkinNS.Family", text)
                self.assertIn(f"def forcedIndex : Fin {len(member.modes)} := {forced}", text)
                self.assertIn("theorem field_eq_family :", text)
                self.assertIn("theorem decrease_family", text)
                self.assertIn("#print axioms field_eq_family", text)
                self.assertEqual(text.count("private theorem coordinate_"), len(member.modes))

    def test_check_mode_reports_stale_output_without_writing(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            destination = Path(directory)
            with patch.object(gen, "DESTINATION", destination):
                with patch.object(sys, "argv", ["galerkin_ns.py", "--check"]):
                    with self.assertRaises(SystemExit):
                        gen.main()
            self.assertEqual(list(destination.iterdir()), [])

    def test_the_committed_files_are_current(self) -> None:
        result = subprocess.run(
            [sys.executable, str(Path(__file__).with_name("galerkin_ns.py")), "--check"],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
