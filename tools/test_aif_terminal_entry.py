"""Regression checks for the complete terminal bin set and read-only verification."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import aif_terminal_entry as terminal


class TerminalEntryTests(unittest.TestCase):
    """Keep generation complete and prevent check mode from repairing evidence."""

    def test_complete_terminal_bin_set(self) -> None:
        """The generator always includes every bin and its shared rational binding."""
        self.assertEqual(
            set(terminal.generate()),
            {"AIFTerminalEnergy.lean"}
            | {f"AIFTerminalEntryBin{b}.lean" for b in range(8)},
        )

    def test_cli_check_is_nonmutating_and_rejects_mismatches(self) -> None:
        """Missing, correct and modified outputs exercise each verification path."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "missing"
            argv = ["terminal", "--output-directory", str(root)]
            with patch("sys.argv", argv + ["--check"]), self.assertRaises(SystemExit):
                terminal.main()
            self.assertFalse(root.exists())
            with patch("sys.argv", argv):
                terminal.main()
            self.assertEqual(
                {p.name: p.read_text() for p in root.iterdir()}, terminal.generate()
            )
            sentinel = root / "unrelated.log"
            sentinel.write_text("keep")
            before = {
                p.name: (p.read_bytes(), p.stat().st_mtime_ns) for p in root.iterdir()
            }
            with patch("sys.argv", argv + ["--check"]):
                terminal.main()
            self.assertEqual(
                before,
                {
                    p.name: (p.read_bytes(), p.stat().st_mtime_ns)
                    for p in root.iterdir()
                },
            )
            path = root / "AIFTerminalEntryBin7.lean"
            path.write_text("changed")
            with patch("sys.argv", argv + ["--check"]), self.assertRaises(SystemExit):
                terminal.main()
            self.assertEqual(path.read_text(), "changed")
            self.assertEqual(sentinel.read_text(), "keep")


if __name__ == "__main__":
    unittest.main()
