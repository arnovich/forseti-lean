---
title: Replay one complete AIF drift box in Lean
state: ongoing
priority: medium
labels: [research, certificates, nonlinear]
claimed_by: codex/dynamics-research
claimed_at: 2026-10-06T12:48:22Z
branch: feat/050_aif_drift_box
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

- [ ] Recompute the drift target from the actual rational Hermite center and
  metric, the shifted AIF field, physical-time derivatives, and constants.
- [ ] Kernel-check both endpoint Bernstein coefficient families and their
  polynomial identities, then cover every intermediate error coordinate.
- [ ] State the resulting quadratic drift inequality on the entire closed box,
  keeping any unproved trajectory and circuit bindings explicit.
- [ ] Test invalid coefficient identities and witnesses, reproduce the proposal,
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
