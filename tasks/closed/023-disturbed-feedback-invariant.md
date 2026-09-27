---
title: Compositional invariant for disturbed continuous feedback
state: closed
priority: medium
labels: [proof, dynamics, example]
---

# Compositional invariant for disturbed continuous feedback

## Context

The owner requested a first bottom-up proof through an actual Asgard trace:
components x' = -x + 2u + d and z' = -z - v, connected with u = z and v = x.
For continuous disturbances with |d(t)| ≤ 1 and initial x² + 2z² ≤ 1,
prove |x(t)| ≤ 1 at every forward time. Local storage identities should compose
into the invariant, making the certificate a later proof-search target.

## Outcome

- [x] Typed component circuits and their wiring define the actual traced system.
- [x] Local storage identities combine into V = x² + 2z² and V' ≤ 1 - V.
- [x] A Lean trajectory Contract proves existence, forward uniqueness and safety
      for every admitted continuous disturbance and initial state.
- [x] Regressions cover initialization, disturbance admission, output projection
      and rejection of an invalid certificate; axiom reports contain only the
      three permitted axioms.
- [x] Documentation explains the hand-proved baseline and the remaining search
      experiment; all libraries, regressions, Checker and equation_demo build.

## Plan

1. Add a regression that demands the complete contract before implementation.
2. Define component fields with Asgard's existing polynomial compiler and wiring;
   close their combined field using Dynamics.close and reuse close_correct.
3. Prove local storage identities and the weighted cancellation, then use an
   integrating factor to lift the differential inequality to all-forward safety.
4. Establish forced-linear existence by variation of constants and uniqueness
   from the homogeneous difference equation, without assuming realizability.
5. Compose the loop contract with the output projection, add hostile regressions,
   document the example, run builds and the mathematical/integration review panel.

## Validation

- The initial regression failed because the root contract module did not exist.
- `lake build`: all 3501 jobs pass, including the new example and regressions.
- `lake build equation_demo`: all 6811 jobs pass. The native build required writable access to the existing dependency cache; the proof build passed within the sandbox.
- `git diff --check` passes; no warnings, admitted proofs, new axioms or unresolved comment markers in the added modules.
- Guarded reports permit only `propext`, `Classical.choice`, and `Quot.sound`.
- The mathematical, circuit-fidelity and regression/trust review panel found no blocking issues. Its optional varying-disturbance regression is included and passes with `sin t`.
- Scope delivered: the hand-proved trace baseline. Invariant search remains a separate experiment; no checker interfaces or Python release pins changed.

## Conversation

### note · codex/feedback_invariant · 2026-09-27T21:28:24Z

Starting the owner-requested hand-checked baseline. The existing homogeneous
linear energy rule does not cover arbitrary continuous disturbances; the proof
will include forced existence and uniqueness rather than a safety-only result.

### note · codex/feedback_invariant · 2026-09-27T21:39:40Z

The root Contract and all regressions pass the full 3501-job Lean build. The three-role review found no blocking issues; its suggestion to test a sinusoidal disturbance is included and checked. All new guarded axiom reports contain only propext, Classical.choice and Quot.sound. The required optional executable is compiling native dependency objects.

### note · codex/feedback_invariant · 2026-09-27T21:41:16Z

Both required builds pass. The total trace contract, observer composition, adverse certificate example and stronger-bound refutation are checked; the proof branch is ready for review.
