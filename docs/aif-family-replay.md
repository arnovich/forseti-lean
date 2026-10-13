# Optional family-check replay

`tools/aif_family_replay.py` replays explicit cells from the fixed AIF candidate
using the [family-check encoding](aif-family-checks.md). It leaves the original
runner and its active batches unchanged. Supply the Lake setup maps for
`AIFSlab`, `AIFPolynomialBinding`, and `AIFSlabData`, a Lean executable, an output
directory under `.lake`, and one or more `--cell BIN:SLAB` selections.

The batch records `family-checks-v1`, the exact selection, local producer source
hashes, candidate hash, setup maps, and the full checking-environment fingerprint.
Per-cell receipts retain the exact source, setup, compiled artifact, compiler log,
and three named standard-axiom reports. Compilation is sequential and requires
more than 5 GiB free before each cell. Input changes and a changed final checking
environment leave the batch failed. Use separate output directories for other
encodings or checking contexts.

`--resume` rechecks receipts before reuse. Write modes reject symlinks and
nonregular entries before touching existing evidence. `--verify-only` regenerates exact
sources, rehashes the checking environment, verifies every cell receipt and the
complete batch inventory, and compares the aggregate receipts without creating or
repairing evidence. The original runner cannot audit this encoding; use this
runner's explicit verification mode. Batch files are bookkeeping, not proof
certificates. Lean remains the mathematical authority.

This runner proves selected drift obligations only. Containment, mesh binding,
output certificates, complete coverage, and the final trajectory theorem require
separate checked composition. A passing batch alone establishes none of those.
