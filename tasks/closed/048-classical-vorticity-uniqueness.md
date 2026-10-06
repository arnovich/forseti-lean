---
title: Classical vorticity uniqueness on certified intervals
state: closed
priority: medium
labels: [lean, analysis, navier-stokes]
---

# Classical vorticity uniqueness on certified intervals

## Context

The owner requested a proof of uniqueness among independently
defined classical solutions of the periodic vorticity initial-value problem.
The existing mild contract proves uniqueness of its formal circuit output and
classical realization, but does not compare arbitrary classical fields.
After the initial foundation spike, the owner requested continuation on draft
PR #48. The goal is to make certified trajectory bounds apply to every classical
solution in an explicitly stated regularity class, with the same periodic
stream-function velocity convention (zero mean velocity).

## Outcome

- [x] Define the comparison solution class independently of circuit streams,
      with explicit periodicity, regularity, initial data, and velocity convention.
- [x] Prove a difference estimate and uniqueness on a common closed interval,
      with no additional axioms or unproved analytic assumptions hidden in the class.
- [x] Connect the existing mild realization to this class and derive equality
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

## Checked proof

The independent class is in Forseti because it is a property of ordinary
fields and an adapter of Asgard's proved realization; it introduces no circuit
syntax, interpretation, or replacement of the pinned Asgard semantics.

For `ν ≥ 0` and `T ≥ 0`, let `d = ω₁ - ω₂`, let
`v = (-∂₂(ψ₁-ψ₂), ∂₁(ψ₁-ψ₂))`, and let `D(t)` be the normalized
area average of `d²` over `[0,2π]²`.

1. `poincare_pointwise` in `IntervalEstimates` derives the one-dimensional estimate
   from the fundamental theorem of calculus and a proved square-integral
   inequality. `square_poincare` in `SquareEstimates` tensorizes it using Fubini,
   obtaining `average((f-average(f))²) ≤ 2L² average(|∇f|²)`.
2. `periodic_elliptic_estimate` in `SquareCalculus` combines this with periodic
   integration by parts and Young's inequality. `SpatialCalculus` derives
   derivative periodicity from value periodicity and applies the estimate to
   the two stream functions: `average(|v|²) ≤ 2(2π)² D(t)`.
3. `hasDerivAt_squareAverage` in `TimeCalculus` proves time differentiation under
   the square integral. Closed-strip continuity supplies uniform domination;
   no endpoint time derivative or stream-function time derivative is added.
4. `EnergyCalculus` proves the diffusion and incompressible transport
   pairings. `Solves.difference_energy_identity` gives
   `D' = -2ν average(|∇d|²) - 2 average(d v·∇ω₂)`.
5. Compactness bounds `|∇ω₂|²` by `M`; Young's inequality and the elliptic
   estimate give `D' ≤ (M+2(2π)²)D`. `Solves.vorticity_unique` uses the scalar
   comparison, continuity, and periodic reduction to obtain equality on the
   whole covering space and both time endpoints, including `T=0`.
   `Solves.velocity_unique` identifies the velocities and retains gauge freedom.
6. `MildComparison` packages the comparison as a consequence of the certified
   mild output and its total Hoare contract. `Examples.ClassicalNavierStokes`
   proves that the notebook's field band and four-term truncation error hold
   for every comparison solution with the same initial data.

No Fourier symmetry, spectral representation, energy estimate, or externally
supplied gradient bound is assumed of a comparison solution. The theorem
compares existing classical fields on a common finite interval. Global
existence and weak-solution uniqueness are outside its statement.

The Python notebook's release pin and displayed source have not changed. The
new theorems are available in this Lean branch; adopting that release in the
notebook application remains a separate integration step.

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

## Continuation validation

- `lake build` passed (3655 jobs), including all libraries, examples,
  regression proofs and Checker, with no warnings.
- `lake build equation_demo` passed (6811 jobs).
- All 34 classical-comparison axiom reports in the final build contain only
  `propext`, `Classical.choice`, and `Quot.sound`.
- New regression modules were first checked with their target theorem modules
  absent, then passed against the completed implementation. Coverage includes
  both spatial directions, mixed modes, the concrete notebook data, odd Euler
  data, vorticity and velocity with a continuous corner gauge, zero horizon,
  and points outside the fundamental square.
- Mathematical-scope, analytic-correctness and integration panels approved the
  final proof. The review led to generalizing the elliptic helper to different
  initial data, adding the velocity-gauge regression, and clarifying that the
  velocity's mean is fixed while the stream-function mean remains free.
- `git diff --check` passed. No release pin, checker allowlist, circuit
  semantics, or notebook application source was changed.

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

### note · codex/ns_uniqueness · 2026-10-06

The continuation closes the analytic gap. The full vorticity and velocity
uniqueness theorems have elaborated with only the allowed axioms, and all three
review roles approve their mathematical scope and argument. Full repository
builds and final example/regression checks are in progress before commit.

### note · codex/ns_uniqueness · 2026-10-06

Full vorticity and velocity uniqueness is checked, including the notebook bounds; both builds and the three-role review passed. Implementation is on draft PR #48; the notebook release pin is unchanged.
