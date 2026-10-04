---
title: Restore the Galerkin generator verification gate
state: closed
priority: high
labels: [tests, ci, galerkin]
---

# Restore the Galerkin generator verification gate

## Context

The generator now includes T3S and enstrophy bounds, but its tests still expect three members and the old Member constructor. CI stops before Lean verification.

## Outcome

The generator suite checks every current member, hostile bounds are still rejected, and the CI pre-build checks pass.

## Plan

Update explicit member expectations and construct hostile examples with dataclasses.replace. Run all generator tests and the Lean release build.


## Conversation

### note · codex/forseti_review_fixes · 2026-10-04T20:26:45Z

Updated expectations for T3S and hostile energy/enstrophy bounds using dataclasses.replace. All 16 generator tests and the suspension search check pass. The full Lean library/example/regression build passes; the optional equation demo build is running. Independent mathematics review found no blockers.

### note · codex/forseti_review_fixes · 2026-10-04T20:42:00Z

PR https://github.com/arnovich/forseti-lean/pull/43 is open. Full Lean library and regression build, and the optional equation demo (6811 jobs), passed locally. GitHub Lean verification is running.

### note · codex/forseti_review_fixes · 2026-10-04T21:04:30Z

PR43 is fully green in Linux Lean verification: generator checks, all libraries and regression proofs, and the optional equation demo passed. Workflow: https://github.com/arnovich/forseti-lean/actions/runs/37232243668. Ready for review; no code changes on main.

### note · codex/forseti_review_fixes · 2026-10-04T21:22:12Z

Owner authorized merge when ready. Task-history conflicts are resolved by preserving main. The implementation is byte-identical to the head that passed full Linux Lean verification; generator tests, search check, library build and optional demo were verified again before merging PR43.
