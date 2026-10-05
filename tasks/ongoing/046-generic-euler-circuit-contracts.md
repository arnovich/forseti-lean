---
title: Generic classical Euler contracts over Fourier circuits
state: ongoing
priority: medium
labels: [lean, circuits, euler, contracts]
related: ["044", "045"]
claimed_by: codex/fluid_contracts
claimed_at: 2026-10-05T23:27:57Z
branch: feat/generic_euler_contracts
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
Tests/FourierCircuit, covering another initial field, zero and cancelling data,
wrong input/circuit, zero radius and exact convergence threshold. Run complete
builds, optional executable, path guard and axiom audit; review and release.

The three-role plan review approved circuit ownership and mathematics with
explicit guards for closed endpoints, semantic zero and interpretation relabeling
in the subsequent Python integration. Python retains its existing distinct,
nonempty mode syntax; duplicate cancellation tests belong to the Lean API.

## Conversation

### note · codex/fluid_contracts · 2026-10-05T23:27:57Z

Claimed the authorized second-stage library work from the merged replay repair; implementation and consumer releases remain isolated from PR229.
