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

Fix Family's unused simp argument; update the Galerkin generator to explicitly reference unused
hypotheses while preserving their public names, omit unused simp entries, and emit bare linear_combination
for an empty combination. Regenerate examples, test the path guard against the
currently failing artifacts, and compare clean builds from distinct roots. Run
the role-based review panel and Lean CI before merging and releasing.

## Conversation

### note · codex/fluid_contracts · 2026-10-05T22:17:32Z

Two builds of unchanged v1.25.0 differ only in Family, B2, T3 and T3S compiled modules. Their persisted mathlib lintLogExt includes absolute source paths. The new guard rejects all four; fixing proof warnings keeps every theorem statement and named hypothesis intact. The guard is an early regression check, not a substitute for whole-closure byte comparison.

### note · codex/fluid_contracts · 2026-10-05T22:22:48Z

Full lake build (3596 jobs), equation_demo (6811 jobs), all 18 Python tool tests and generated-file checks pass. Three-role panel found no blocking issues; final B2 follow-up reviewed. Both checkout path guards pass and 103 completed module artifacts already match byte-for-byte. The second full build and complete replay-closure comparison remain the release acceptance gate.
