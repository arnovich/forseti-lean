---
title: Check a Bernstein matrix replay pilot for AIF startup tubes
state: ongoing
priority: medium
labels: [research, certificates, nonlinear]
claimed_by: codex/dynamics-research
claimed_at: 2026-10-06T10:00:00Z
branch: feat/049_bernstein_matrix_replay
---

# Check a Bernstein matrix replay pilot for AIF startup tubes

## Context

Python Forseti PR #235 stores an exact rational moving-tube candidate for the
four-state antithetic integral-feedback model. Its 2,960 slabs passed untrusted
Python inspection. Before encoding the entire candidate, establish a checked
matrix-polynomial positivity bridge and measure exact kernel replay on actual
candidate coefficients. Existing `LinearEnergy.WeightedSquares` owns rational
matrix positivity; reuse its soundness theorem.

The Python follow-up currently shares task number 246 with unrelated work;
refer to its full filename, `246-aif-startup-tube-lean-replay.md`, until the owner
resolves that collision. This Lean task is a bounded prerequisite, not a claim
that the full startup trajectory or original-model circuit binding is proved.

## Outcome

- [ ] A reusable Lean theorem proves tensor Bernstein matrix positivity on the
  closed unit box from exact weighted-square coefficient certificates.
- [ ] An actual candidate matrix polynomial is replayed, with exact rational
  coefficients and identifiable source data, and its kernel cost is recorded.
- [ ] Regression proofs exercise box boundaries and reject invalid coefficient
  certificates; no extra axioms or native computation are trusted.
- [ ] A reproducible pilot and its limits explain the next full-replay gate.

## Plan

1. Reuse the rational weighted-square checker and existing Bernstein lemmas.
2. Add a small sound tensor-combination theorem and meaningful regressions.
3. Extract one actual matrix polynomial from the committed AIF candidate;
   generate its rational decompositions as untrusted proposals and replay them.
4. Measure replay, inspect axiom reports, run both required Lake builds and a
   correctness/performance/scientific-scope review panel.

## Conversation

### note · codex/dynamics-research · 2026-10-06T10:00:00Z

Claimed the Lean replay pilot after the owner requested merging PR #235 and
continuing research. The full trajectory theorem remains a separate obligation.
