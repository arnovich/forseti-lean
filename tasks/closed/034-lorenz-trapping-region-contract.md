---
title: Lorenz trapping-region contract — nonlinear existence, uniqueness and invariant
state: closed
priority: medium
labels: [proof, dynamics, nonlinear, showcase]
related: [025]
---

# Lorenz trapping-region contract — nonlinear existence, uniqueness and invariant

## Context

gimle-forseti task 180: a Lean-checked trapping region for the Lorenz system
(σ = 10, ρ = 28, β = 8/3) from (1, 1, 1) at t = 0, as the second rung of the
showcase-notebook ladder. Every trajectory contract so far comes from
`LinearEnergyContract` and a `LinearView`; Lorenz has none, so this is the
first nonlinear total `Contract` (task 025 asked for nonlinear existence and
uniqueness "separately"; this delivers them for one model).

Mathematics, verified symbolically: with `V = x² + y² + (z − 38)²`,
`V' = −20x² − 2y² − (16/3)z² + (608/3)z`, hence `V' + 2V − 2C ≤ 0` for every
state once `C ≥ 23104/15`; with `C = 1600` and `V(1,1,1) = 1371` the
integrating factor `e^{2t}(V − 1600)` is non-increasing, the
`DisturbedFeedback.invariant` pattern. The model is declared here as the
oscillators are (`Body`/`equations%` against the pinned asgard), so no
asgard-lean change is needed.

## Outcome

- [x] `Gimle/Forseti/Examples/Lorenz.lean`: `body`, `evolution`, `compiled`,
      `initial_eq`, `energyIndex`, `energy_at`, `energy_at_initial`,
      `observed`, `admitted` (definitionally `Initialized … (· = initial)`),
      `compiled_exists`, `feedback_reads`, `declared_input_admitted`, and
      `energy_contract : Contract observed evolution.time admitted (Always … (0 ≤ V ∧ V ≤ 1600))`.
- [x] Existence for all `t ≥ 0` proved by hand (clamped field, Picard–Lindelöf
      per `[0, T]`, gluing, invariant keeps the solution where fields agree);
      uniqueness on the compact sublevel set; both reusable beyond Lorenz where
      practical.
- [x] A refutation lemma for a bound below `V(0)` (`1300`), as `five_refuted`.
- [x] `Tests/Lorenz.lean` pins every interface name; `lake build` clean; axiom
      reports show only propext, Classical.choice, Quot.sound.

## Notes

The clamp–glue–fence existence machinery in `Examples/Lorenz.lean` is generic
(any C¹ field with a compact sublevel set on whose boundary `V' < 0`); the
review recommended extracting it as a reusable lemma. Deferred to task 025,
which needs it next.

## Conversation

### note · claude/17d157a0 · 2026-09-30T12:22:06Z

PR #26 merged; released as v1.10.0 (asgard v1.7.0 unchanged). Filed as
`34-…` by mistake; renamed to the zero-padded form on closing.
