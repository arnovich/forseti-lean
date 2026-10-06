---
title: Check a Bernstein matrix replay pilot for AIF startup tubes
state: closed
priority: medium
labels: [research, certificates, nonlinear]
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

- [x] A reusable Lean theorem proves tensor Bernstein matrix positivity on the
  closed unit box from exact weighted-square coefficient certificates.
- [x] An actual candidate matrix polynomial is replayed, with exact rational
  coefficients and identifiable source data, and its kernel cost is recorded.
- [x] Regression proofs exercise box boundaries and reject invalid coefficient
  certificates; no extra axioms or native computation are trusted.
- [x] A reproducible pilot and its limits explain the next full-replay gate.

## Plan

1. Reuse the rational weighted-square checker and existing Bernstein lemmas.
2. Add a small sound tensor-combination theorem and meaningful regressions.
3. Extract one actual matrix polynomial from the committed AIF candidate;
   generate its rational decompositions as untrusted proposals and replay them.
4. Measure replay, inspect axiom reports, run both required Lake builds and a
   correctness/performance/scientific-scope review panel.

## Results

`BernsteinMatrix.lean` proves tensor positivity and the cubic conversion.
`AIFMetricPilot.lean` recomputes the selected Hermite metric's coefficients and
checks four exact square decompositions, proving coercivity for every real
error vector throughout physical time [33/5,67/10]. The source retains the
rational endpoint values/slopes and identifies the original candidate hash.
No trajectory or circuit theorem is inferred from this metric inequality.

Validation: `lake build` passed (3,658 jobs); `lake build equation_demo` passed
(6,811 jobs). New regressions, generator reproduction, altered-input rejection,
Black, isort, Flake8 and whitespace checks passed. A fresh source replay passed
in 42.42 seconds wall time, 11.60 seconds Lean CPU, with 2.58 GiB peak RSS;
see [the measurement and limits](../../docs/aif-replay-pilot.md). The new
mathematical results depend only on the three standard axioms.

The review panel covered mathematical correctness, exact arithmetic and
reproducibility, and scientific scope. Its sole medium finding requested the
replay measurement; that is recorded and re-reviewed. No open findings remain.
Next, replay a complete drift polynomial before expanding to all 2,960 slabs.

## Conversation

### note · codex/dynamics-research · 2026-10-06T10:00:00Z

Claimed the Lean replay pilot after the owner requested merging PR #235 and
continuing research. The full trajectory theorem remains a separate obligation.

### note · codex/dynamics-research · 2026-10-06T12:01:10Z

Completed the checked one-slab metric pilot and both required builds. The full
startup trajectory theorem remains open; explicit drift certificates and
original-model binding are the next proof obligations.
