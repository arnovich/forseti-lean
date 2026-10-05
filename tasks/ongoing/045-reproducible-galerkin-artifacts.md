---
title: Reproducible Galerkin compiled artifacts
state: ongoing
priority: high
labels: [lean, ci, reproducibility]
claimed_by: codex/fluid_contracts
claimed_at: 2026-10-05T22:14:47Z
branch: fix/reproducible_galerkin
---

# Reproducible Galerkin compiled artifacts

## Context

Forseti's pinned live replay rejects clean CI builds. Compiling the same release
in two checkout directories changes four Galerkin artifacts: mathlib's persistent
linter log embeds absolute source paths for unused simp arguments and variables.
The strict content hashes correctly refuse these different compiled bytes.

## Outcome

- Correct the generated and handwritten proof warnings without disabling linters.
- Every replay artifact is byte-identical across two clean checkout roots.
- A regression guard rejects build-root paths embedded in compiled modules.
- Lean builds and the generator tests pass; a reviewed release supports repair
  of gimle-forseti task 222's pins and mandatory live replay CI.

## Plan

Fix Family's unused simp argument; update the Galerkin generator to name unused
hypotheses anonymously, omit unused simp entries, and emit bare linear_combination
for an empty combination. Regenerate examples, test the path guard against the
currently failing artifacts, and compare clean builds from distinct roots. Run
the role-based review panel and Lean CI before merging and releasing.
