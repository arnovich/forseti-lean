---
title: Replay one complete AIF drift box in Lean
state: closed
priority: medium
labels: [research, certificates, nonlinear]
related: [049]
---

# Replay one complete AIF drift box in Lean

## Context

Task 049 checks metric coercivity on one AIF startup slab. The next scaling and
soundness gate is its full drift matrix polynomial: time [33/5,67/10], fixed
eta in [8,17/2], and nonlinear error coordinate in [-3/200,3/200]. The original
candidate is pinned by SHA-256 in the metric pilot. No trajectory theorem or
full startup bound has yet been proved.

## Outcome

- [x] Recompute the drift target from the actual rational Hermite center and
  metric, the shifted AIF field, physical-time derivatives, and constants.
- [x] Kernel-check both endpoint Bernstein coefficient families and their
  polynomial identities, then cover every intermediate error coordinate.
- [x] State the resulting quadratic drift inequality on the entire closed box,
  keeping any unproved trajectory and circuit bindings explicit.
- [x] Test invalid coefficient identities and witnesses, reproduce the proposal,
  record replay cost, run both required builds and the review panel.

## Plan

1. Extend the existing Bernstein positivity bridge with entrywise target binding.
2. Preserve the selected center's endpoints/slopes beside the existing metric.
3. Generate exact endpoint Bernstein coefficients and square proposals; verify
   their identities against the independently defined target with ordinary Lean
   proofs, without trusting the generator.
4. Prove affine interpolation in the error coordinate and its drift consequence.
5. Measure replay before considering whole-candidate expansion. Scope remains
   one closed box; existence, tube invariance and circuit enrollment are later.

## Conversation

### note · codex/dynamics-research · 2026-10-06T12:48:22Z

Claimed after merging PR #49 at the owner's request. The experiment checks the
larger drift certificates before scaling to all 2,960 startup slabs.

### note · codex/dynamics-research · 2026-10-06T13:35:00Z

The entrywise target bridge compiles, and the exact producer reproduces both
endpoint coefficient families. Three judges reviewed the field/derivative
identities, exact arithmetic and target binding, and scientific scope. No
material mathematical defect was found; a varying two-axis binding regression
was requested and added. Concrete endpoint replay and performance remain under
verification. Profiling the first run identified eager expansion of the large
coefficient tables in the target identity; the next run expands finite sums
before selecting their rational entries.

### note · codex/dynamics-research · 2026-10-06T16:00:46Z

Completed the one-box drift theorem: both 40-matrix certificate families, their
entrywise polynomial bindings, physical derivative identities and interpolation
are kernel-checked. Explicit matrix entries and vector/binomial normalization
resolved the binding elaboration cost. The full build passed 3,665 jobs without
warnings; equation_demo passed 6,811 jobs. All 22 Python tool tests, exact-byte
regeneration, format/lint checks and the compiled-path guard passed. New axiom
reports contain only propext, Classical.choice and Quot.sound.

The three-role review found no remaining mathematical, arithmetic or scope
defect; its two-axis binding regression was added and checked. Replay timings
and limitations are recorded in docs/aif-drift-pilot.md. Task 051 tracks compact
representation and measured scaling before whole-candidate expansion. This
closes the algebraic box experiment, not startup trajectory containment.
