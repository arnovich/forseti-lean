---
title: Bind field bounds to stream circuits through asgard-lean 024
state: open
priority: high
labels: [streams, pde, certificates, fields]
depends_on: ["020"]
related: ["018", "019"]
---

# Bind field bounds to stream circuits through asgard-lean 024

## Context

Task 020 delivered the coefficient adapter (`Gimle/Forseti/StreamObservation.lean`,
through asgard-lean 023) and the algebraic half of the evaluated-field adapter
(`Gimle/Forseti/FieldBound.lean`, `Examples/HeatStripBound.lean`): a checked
strip bound `0 ≤ a·x² + c + 2·a·t ≤ c + a·R² + 2·a·T` on the explicit candidate
polynomial, the concrete `a=1, c=0, R=T=1` case (bound 3 proved, bound 2 refuted
at `(1, 1)`), and hostile tests. What 020 could not do is tie that candidate to
a stream circuit: asgard-lean
[024](https://github.com/arnovich/asgard-lean/blob/main/tasks/open/024-polynomial-stream-realization.md)
(finite polynomial streams, their evaluated real fields, and the heat
construction and uniqueness in the finite polynomial class) was being built in
parallel and is not in the pinned asgard-lean v1.1.0.

Until this lands, a field refutation refutes the candidate function only, and a
field bound is not a property of Asgard's heat circuit.

## Outcome

- [ ] Bump the asgard-lean pin to a release containing 024.
- [ ] Define the evaluated-field predicate adapter from 024's finite-support
      realization theorem: formula variables are space-time coordinates and
      fixed parameters; the claim names the original circuit, the full input
      streams, the initial profile, the finite polynomial solution class, the
      analytic interpretation and the stated domain. A finite-support witness
      for the whole stream is required; a window or prefix is not one.
- [ ] Prove the adapter sound with reusable theorems, separate from the
      coefficient rule: field positivity needs its own bridge theorem and
      hypotheses, never coefficient constraints alone.
- [ ] Restate `HeatStripBound.strip_bound` for the actual heat solution with
      initial profile `a·x² + c`, obtained through 024 (existence and uniqueness
      in the finite polynomial class only), with task 017 certificates for the
      algebraic leaves.
- [ ] Lift the `(t, x) = (1, 1)` leaf counterexample for bound 2 into a root
      refutation only after Lean verifies an admissible full input, its related
      output and the failing root postcondition.
- [ ] Negative tests: an altered initial profile, a narrowed domain reused as a
      wider claim, a finite prefix presented as a full stream, and `u = x` at
      negative `x` against its nonnegative coefficients — each at the circuit
      level. All new declarations audited against `propext`,
      `Classical.choice`, `Quot.sound` only; document the field transfer rule
      in `docs/properties.md`.
