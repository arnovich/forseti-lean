"""Reject checkout paths persisted in Lean artifacts (for example by linter logs).

Run after ``lake build``. Forseti replay authenticates compiled bytes, so even a
warning's absolute source path makes otherwise identical builds nonportable.
This regression guard complements, rather than replaces, two-root hash comparison.
"""

from __future__ import annotations

import argparse
from pathlib import Path

SUFFIXES = (".olean", ".ir", ".olean.server", ".olean.private")


def check_build_paths(project: Path) -> list[Path]:
    """Return compiled modules containing this checkout's absolute path.

    Refuse an unbuilt checkout so a skipped build cannot pass the guard.
    """
    project = project.resolve()
    library = project / ".lake/build/lib/lean"
    artifacts = sorted(
        path
        for path in library.rglob("*")
        if path.is_file() and path.name.endswith(SUFFIXES)
    )
    if not any(path.suffix == ".olean" for path in artifacts):
        raise ValueError(f"no compiled Lean modules in {library}")
    root = str(project).encode()
    return [path for path in artifacts if root in path.read_bytes()]


def main() -> int:
    """Report paths that would prevent byte-identical release replay."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", nargs="?", type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        affected = check_build_paths(args.project)
    except ValueError as error:
        parser.error(str(error))
    for path in affected:
        print(f"checkout path embedded in {path}")
    return int(bool(affected))


if __name__ == "__main__":
    raise SystemExit(main())
