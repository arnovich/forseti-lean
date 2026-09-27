---
title: Compositional active suspension with discovered safety certificate
state: ongoing
priority: medium
labels: [proof, dynamics, example, search]
claimed_by: codex/suspension
claimed_at: 2026-09-27T21:57:51Z
branch: feat/compositional_active_suspension
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

- [ ] Exact typed plant, controller and actuator circuits; actual nested feedback
      traces with checked correspondence to the assembled state equations.
- [ ] Reusable component behavior/storage contracts and a sound feedback rule
      requiring independent existence and uniqueness, not circular admission.
- [ ] A reproducible untrusted exact certificate search supplies a quadratic
      invariant; Lean rechecks its rational square decompositions and every
      link to the original circuits.
- [ ] A total root Contract gives forward existence, uniqueness, suspension
      travel, actuator force and body acceleration bounds under explicit input
      and initialization assumptions chosen independently of the certificate.
- [ ] A second actuator implementation meets the same stated interface and
      inherits the outer safety theorem.
- [ ] Hostile regressions, all permitted-axiom guards, complete builds and a
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
