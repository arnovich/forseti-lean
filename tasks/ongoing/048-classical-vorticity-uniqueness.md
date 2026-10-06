---
title: Classical vorticity uniqueness on certified intervals
state: ongoing
claimed_by: codex/ns_uniqueness
claimed_at: 2026-10-06T09:27:56Z
branch: feat/048_classical_vorticity_uniqueness
priority: medium
labels: [lean, analysis, navier-stokes]
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

- [x] Define the comparison solution class independently of circuit streams,
      with explicit periodicity, regularity, initial data, and velocity convention.
- [ ] Prove a difference estimate and uniqueness on a common closed interval,
      with no additional axioms or unproved analytic assumptions hidden in the class.
- [ ] Connect the existing mild realization to this class and derive equality
      with the constructed field for the notebook initial data.
- [x] Add regression proofs, axiom reports, and documentation stating exact scope.
- [x] Record any unresolved analysis bridge explicitly if the bounded spike
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

## Proof route after the spike

The independent class is in Forseti because it is a property of ordinary
fields and an adapter of Asgard's proved realization; it introduces no circuit
syntax, interpretation, or replacement of the pinned Asgard semantics.

For `ν ≥ 0` and `T ≥ 0`, let `d = ω₁ - ω₂`, let
`v = (-∂₂(ψ₁-ψ₂), ∂₁(ψ₁-ψ₂))`, and set
`D(t) = ∫_[0,2π]² d(t,x)² dx`. The remaining obligations are:

1. Derive periodicity of the spatial derivative witnesses from periodicity of
   each value field, then lift the checked one-dimensional integration-by-parts
   and transport identities to the square using Fubini.
2. Prove a coarse periodic Poincare inequality for a C¹ scalar field minus its
   spatial average. Combine it with integration by parts and Cauchy–Schwarz to
   obtain `||v||₂ ≤ C ||d||₂` from `Δ(ψ₁-ψ₂)=d`. No optimal constant is needed.
3. Differentiate `D` under the square integral using the given joint continuity
   and time derivative on `(0,T)`. Obtain
   `D' = -2ν ||∇d||₂² - 2∫ d v·∇ω₂`.
4. Compactness bounds `∇ω₂` on the closed time-space cell. Cauchy–Schwarz and
   step 2 give `D' ≤ K D`. Apply `difference_eq_zero` and convert the vanishing
   square integral to pointwise equality by continuity and periodicity.
5. Package the comparison for `of_mild` and transport the existing notebook
   band/truncation postconditions. Only then update its uniqueness claim.

The installed Mathlib provides interval integration by parts, integral
differentiation and Gronwall tools, but the repository audit found no packaged
periodic Poincare/elliptic inequality. Existing real cosine spectral
cancellation cannot replace this bridge for arbitrary nonsymmetric fields.
The spike proves the membership interface, pointwise difference equation,
one-dimensional integration identities, and scalar comparison; it does not
claim completion of steps 1–5.

## Spike validation

- The regression module initially failed because the new comparison interface
  did not exist; it now checks the generic certified membership bridge and the
  concrete notebook profile, an odd sine Euler field, gauge freedom, wrong
  initial data, the closed upper endpoint, zero horizon, and viscous sign.
- `lake build` passed for the library, examples, all regression proofs and
  Checker (3641 jobs). `lake build equation_demo` also passed (6811 jobs).
- Public helper and membership axiom reports contain only `propext`,
  `Classical.choice`, and `Quot.sound`; no new axioms or unfinished proof terms.
- The plan and implementation were reviewed by mathematical-scope, analytic
  correctness, and integration judges. All approved the preparatory milestone,
  explicitly conditional on the build and without treating it as uniqueness.

## Attempts

- 2026-10-06 — The bounded spike established the independent solution class,
  mild membership, pointwise difference equation, periodic one-dimensional
  calculus and the closed-interval scalar comparison. Full classical uniqueness
  remains unproved: the periodic elliptic estimate and two-dimensional energy
  argument require new analysis infrastructure. The checked foundations are
  retained on the feature branch; task 048 remains open for that continuation.

## Reviews

The plan panel examined mathematical scope, analytic feasibility and integration.
All three identified the independent-field bridge, velocity normalization,
stream-function gauge, symmetry of the comparator and endpoints as material.
The implementation preserves all of these. It keeps the energy estimate out
of the solution predicate and makes it an explicit premise only in the scalar
comparison helper. The code review also asked documentation to state continuity
of a time-dependent gauge explicitly; that correction was applied.

## Conversation

### note · codex/ns_uniqueness · 2026-10-06T07:41:53Z

Started the owner-authorized proof spike. Existing dissipation is spectral and
the classical-solution structure is stream-indexed; the independent-field
comparison bridge is the main risk to test first.

### note · codex/ns_uniqueness · 2026-10-06T08:43:44Z

The foundation milestone checks, including the concrete notebook field and an
odd comparison solution. The broader theorem is not proved; the remaining
physical-space estimates are listed above. No notebook or release-pin change
has been made.

### note · codex/ns_uniqueness · 2026-10-06T09:25:35Z

Checked foundation checkpoint: [draft PR #48](https://github.com/arnovich/forseti-lean/pull/48),
branch `feat/048_classical_vorticity_uniqueness`. Both builds passed. Releasing
the claim with the task open; the broader PDE uniqueness outcome is unfinished.

### note · codex/ns_uniqueness · 2026-10-06T09:27:56Z

Owner requested continuation on draft PR #48 toward the full theorem.
Starting with the periodic elliptic estimate and two-dimensional integral
identities, then connecting the energy difference to the checked comparison.
