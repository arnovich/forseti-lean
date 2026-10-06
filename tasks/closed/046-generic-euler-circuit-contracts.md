---
title: Generic classical Euler contracts over Fourier circuits
state: closed
priority: medium
labels: [lean, circuits, euler, contracts]
related: ["044", "045"]
---

# Generic classical Euler contracts over Fourier circuits

## Context

The complete Euler circuit contract is currently tied to one three-mode example.
The owner requested reusable contracts and notebook decisions for suitable finite
Fourier initial data, followed by the viscous mild circuit development. The
reproducible Lean release is merged; its Python enrollment PR229 is awaiting CI.
This independent library work uses the merged Lean release, with consumer merges
remaining in the requested order.

## Outcome

- A reusable total contract for Asgard's actual Euler feedback circuit, with only
  the initial slice in its precondition and classical realization of every output.
- Explicit mean-zero, parity, finite-support and convergence premises, with finite
  table certificates and support for zero data at every finite requested radius.
- Requested closed-radius truncation/band properties compose with the classical
  guarantee; producer certificate constants do not alter the claimed property.
- The existing three-mode example retains its stronger open classical interval.
- Valid and adverse regression proofs, allowed axioms, complete builds and a
  panel-reviewed PR with passing CI, then a release for the consumer.

## Plan

Add Gimle/Forseti/Euler.lean with a semantic contract over MeanZero, IsEven,
SizeLE and GeometricBound hypotheses. Layer decidable finite-table certificates
separately; aggregate duplicate coefficients when proving parity and semantic
zero. Use positive growth bounds with rho*r < 1 to obtain the PDE on the closed
requested interval, including endpoints. For zero data repackage the zero norm
bound at arbitrary positive rho, avoiding division by zero. Preserve higher
boundary coefficients as unconstrained. Refactor EulerContract using reusable
lemmas without shrinking its classical interval. Add regression proofs after
Tests/EulerContract, covering another initial field, zero and cancelling data,
wrong input/circuit, zero radius and exact convergence threshold. Run complete
builds, optional executable, path guard and axiom audit; review and release.

The three-role plan review approved circuit ownership and mathematics with
explicit guards for closed endpoints, semantic zero and interpretation relabeling
in the subsequent Python integration. Python retains its existing distinct,
nonempty mode syntax; duplicate cancellation tests belong to the Lean API.

## Conversation

### note · codex/fluid_contracts · 2026-10-05T23:27:57Z

Claimed the authorized second-stage library work from the merged replay repair; implementation and consumer releases remain isolated from PR229.

### note · codex/fluid_contracts · 2026-10-05T23:34:01Z

Generic semantic and finite-table contracts compile with allowed axioms. Regression proofs cover a new two-frequency start, requested truncation, both closed endpoints, zero radius, unconstrained higher boundary coefficients, wrong input and a wrong identity circuit, plus duplicate cancellation at a large finite radius. The existing three-mode theorem retains its original statement and stronger open classical interval. Complete build and implementation panel are next.

### note · codex/fluid_contracts · 2026-10-05T23:35:52Z

All three implementation reviewers pass with no findings: circuit architecture, mathematical semantics and consumer/test adequacy. Full build3598, optional executable6811, path guard, 18 tooling tests and exact certificate regeneration pass. A second checkout is rebuilding without own-package artifacts before release enrollment. Python dispatch/relabeling/zero-bound integration remains the subsequent consumer task.

### note · codex/fluid_contracts · 2026-10-06T03:46:42Z

Merged https://github.com/arnovich/forseti-lean/pull/46 at `444d4a574c782c88a2bac3f6f4b7305cddf2429d`. Published v1.27.0 from the audited merge tree. The complete build, optional examples, regression proofs, path guard and CI pass. All 109 owned compiled artifacts match independent checkout roots, all 19 consumer replay closures verify, and the circuit, mathematical and consumer review panel passes.
