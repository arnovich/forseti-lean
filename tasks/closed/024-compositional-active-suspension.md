---
title: Compositional active suspension with discovered safety certificate
state: closed
priority: medium
labels: [proof, dynamics, example, search]
related: [023]
---

# Compositional active suspension with discovered safety certificate

## Context

The owner selected an actively controlled two-mass suspension as the next
bottom-up trace example after 023. Model body/wheel positions and velocities
and actuator force, with continuous bounded road input. Prove meaningful
travel, force and acceleration bounds for an independently specified initial
region. Inner component contracts should support the outer feedback proof and
an actuator replacement without redoing the outer theorem.

## Outcome

- [x] Exact typed plant, controller and actuator circuits; actual nested feedback
      traces with checked correspondence to the assembled state equations.
- [x] Reusable component behavior/storage contracts and a sound feedback rule
      requiring independent existence and uniqueness, not circular admission.
- [x] A reproducible untrusted exact certificate search supplies a quadratic
      invariant; Lean rechecks its rational square decompositions and every
      link to the original circuits.
- [x] A total root Contract gives forward existence, uniqueness, suspension
      travel, actuator force and body acceleration bounds under explicit input
      and initialization assumptions chosen independently of the certificate.
- [x] A second actuator implementation meets the same stated interface and
      inherits the outer safety theorem.
- [x] Hostile regressions, all permitted-axiom guards, complete builds and a
      three-role review pass; docs distinguish the normalized mathematical model
      from a calibrated vehicle and record the measured certificate search.

## Plan

1. Fix a normalized rational five-state model and independent initial/input/output
   specifications; write the root regression before implementation.
2. Prove generic forced-linear circuit contracts and an integrating-factor storage
   rule, reusing 023 and existing weighted-square verification.
3. Build actuator and plant as separate integrated traces with explicit wiring;
   prove their relational interfaces and the nested outer interconnection.
4. Search an exact rational quadratic certificate outside core imports. Check
   positivity, dissipation under bounded forcing, initial inclusion and output
   containment in Lean. Search both selected actuator variants against one
   certificate so the outer proof can be reused.
5. Add regression proofs, documentation, review and full Lean verification;
   publish a reviewable branch without changing Python release enrollment.

## Conversation

### note · codex/suspension · 2026-09-27T21:57:51Z

Owner authorized the suspension example and asked to save nonlinear oscillators
and vehicle chains for later; those are filed separately without queue ranks.

### note · codex/suspension · 2026-09-27T22:22:12Z

Steps 1–4 implemented in the isolated feature worktree. Both total output
contracts compile using the same searched storage (19 candidates), with exact
rate-specific supply decompositions. Full Lean and equation_demo builds passed.
Three-role implementation review found no blockers; corrected a cancelling
pre-start test and made replay byte-exact. Final validation and publication remain.

### note · codex/suspension · 2026-09-27T22:25:04Z

Completed in draft PR [15](https://github.com/arnovich/forseti-lean/pull/15),
feature commit `04f65f2`. Final lake build (3507 jobs), equation_demo build
(6811 jobs), all root axiom guards, exact search reproduction, four Python tests,
formatting/lint/type checks and diff checks passed. The mathematical, composition
and search/replay panel approved with no remaining blockers. Added an explicit
body-acceleration observation theorem and fixed both review findings. Tasks 025
and 026 remain open for later; no checker admission or release pin changed.

### note · codex/suspension · 2026-09-29T12:45:47Z

Merged PR [15](https://github.com/arnovich/forseti-lean/pull/15) as `d61af4d`
after the owner authorized integration. Updated against current main and
Asgard v1.7.0; retained all newer documentation links when resolving the README
conflict. The suspension proof required no changes. Full lake build (3531 jobs),
equation_demo (6811 jobs), permitted-axiom checks, exact certificate reproduction
and all four Python search regressions passed. Task 024 is complete and merged;
the separate future examples 025 and 026 remain open.
