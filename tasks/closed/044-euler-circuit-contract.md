---
title: Euler contracts over Asgard Fourier stream circuits
state: closed
priority: medium
labels: [circuits, euler, formal-methods]
---

## Context

The existing Euler results are ordinary Asgard stream theorems. The owner requested a Forseti contract over an actual Asgard circuit, reusing those results. This depends on Asgard task 071.

## Outcome

- A reusable contract for Asgard Fourier-stream circuits states existence, uniqueness and the postcondition for every output.
- The three-mode Euler example has a contract identifying its output, certifying its truncation/band and proving the local classical solution property.
- Regression proofs and axiom audits are built with the library.
- Documentation explains the circuit boundary and preserves the limits of the PDE claims.
- Full build and panel review pass.

## Plan

Study the existing stream and continuous circuit semantics. Add regression statements first, implement the circuit/contract bridge, then check all build targets and independent panel findings. Keep the mathematical stream as the semantic reference and keep feedback relational; never assume an arbitrary loop has a solution.

## Validation

Implemented `Fourier.lean` (total contracts, consequence, composition,
expression and feedback-solution rules), `Examples/EulerContract.lean` and
`Tests/EulerContract.lean`. Regression statements first failed on the absent
example module. The completed contract binds initial data to the actual circuit
and transports the existing analytical results to every related output.

Asgard is pinned to `b6a8420f185df7bdc7c63030ad00c88bb96b8927`, submitted in
https://github.com/arnovich/asgard-lean/pull/32. The final dependency checkout
is clean at that exact commit. `lake build` (3,596 jobs), `lake build equation_demo`,
`python3 tools/search_suspension.py --check`, and all 16 tool unittests pass.
The 24 existing Galerkin linter warnings are unchanged; no new module warns.
The guarded Euler contract axiom report has only propext, Classical.choice
and Quot.sound. `git diff --check` passes.

A three-role panel (architecture, mathematical proof boundaries, integration
and claims) passed without blocking findings. The Python notebook and decider
still use their existing release: adopting the new contract there requires a
separate release-pin and theorem-root migration, rather than silently changing
old checked claims.

## Conversation

### note · codex/euler_circuit · 2026-10-05T10:43:08Z

Merged https://github.com/arnovich/forseti-lean/pull/44. Full local builds and panel review passed. The notebook migration is a separate application update.
