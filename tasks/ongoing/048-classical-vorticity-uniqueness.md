---
title: Classical vorticity uniqueness on certified intervals
state: ongoing
priority: medium
labels: [lean, analysis, navier-stokes]
claimed_by: codex/ns_uniqueness
claimed_at: 2026-10-06T07:41:53Z
branch: feat/048_classical_vorticity_uniqueness
---

# Classical vorticity uniqueness on certified intervals

## Context

The owner requested a bounded proof spike toward uniqueness among independently
defined classical solutions of the periodic vorticity initial-value problem.
The existing mild contract proves uniqueness of its formal circuit output and
classical realization, but does not compare arbitrary classical fields.
The goal is to make certified trajectory bounds apply to every classical
solution in an explicitly stated regularity class, with the same periodic
stream-function velocity convention (zero mean velocity).

## Outcome

- [ ] Define the comparison solution class independently of circuit streams,
      with explicit periodicity, regularity, initial data, and velocity convention.
- [ ] Prove a difference estimate and uniqueness on a common closed interval,
      with no additional axioms or unproved analytic assumptions hidden in the class.
- [ ] Connect the existing mild realization to this class and derive equality
      with the constructed field for the notebook initial data.
- [ ] Add regression proofs, axiom reports, and documentation stating exact scope.
- [ ] Record any unresolved analysis bridge explicitly if the bounded spike
      cannot establish the full classical comparison; do not rename a restricted
      spectral uniqueness result as arbitrary classical uniqueness.

## Plan

1. Audit the existing classical regularity, Fourier cancellation and Gronwall
   interfaces; choose the smallest honest comparison class containing the mild field.
2. State a regression theorem before implementation. Prove the difference
   estimate and zero-initial-difference consequence with checked Lean terms.
3. Prove the mild-field membership bridge and package a reusable Forseti
   comparison theorem. Integrate the notebook only after the full bridge checks.
4. Build the library, regressions and Checker, inspect transitive axioms, and
   panel-review mathematical scope, proof correctness and integration.

## Conversation

### note · codex/ns_uniqueness · 2026-10-06T07:41:53Z

Started the owner-authorized proof spike. Existing dissipation is spectral and
the classical-solution structure is stream-indexed; the independent-field
comparison bridge is the main risk to test first.
