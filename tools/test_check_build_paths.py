"""Regression coverage for build-path leakage in authenticated Lean artifacts."""

import tempfile
import unittest
from pathlib import Path

from check_build_paths import SUFFIXES, check_build_paths


class BuildPathTests(unittest.TestCase):
    """Fail closed on missing builds and inspect every replay-loaded suffix."""

    def test_unbuilt_checkout_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "no compiled Lean modules"):
                check_build_paths(Path(directory))

    def test_detects_each_loaded_artifact_but_ignores_build_traces(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory).resolve()
            library = project / ".lake/build/lib/lean/Gimle"
            library.mkdir(parents=True)
            (library / "Clean.olean").write_bytes(b"portable module")
            (library / "Clean.trace").write_text(str(project))
            self.assertEqual(check_build_paths(project), [])
            for suffix in SUFFIXES:
                with self.subTest(suffix=suffix):
                    path = library / ("Warning" + suffix)
                    path.write_bytes(
                        b"lintLogExt\0" + str(project).encode() + b"/A.lean\0"
                    )
                    self.assertEqual(check_build_paths(project), [path])
                    path.unlink()


if __name__ == "__main__":
    unittest.main()
