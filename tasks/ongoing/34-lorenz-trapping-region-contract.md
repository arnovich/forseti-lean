---
title: Lorenz trapping-region contract — nonlinear existence, uniqueness and invariant
state: ongoing
claimed_by: claude/17d157a0
claimed_at: 2026-09-30T11:56:36Z
branch: feat/lorenz_contract
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

- [ ] `Gimle/Forseti/Examples/Lorenz.lean`: `body`, `evolution`, `compiled`,
      `initial_eq`, `energyIndex`, `energy_at`, `energy_at_initial`,
      `observed`, `admitted` (definitionally `Initialized … (· = initial)`),
      `compiled_exists`, `feedback_reads`, `declared_input_admitted`, and
      `energy_contract : Contract observed evolution.time admitted (Always … (0 ≤ V ∧ V ≤ 1600))`.
- [ ] Existence for all `t ≥ 0` proved by hand (clamped field, Picard–Lindelöf
      per `[0, T]`, gluing, invariant keeps the solution where fields agree);
      uniqueness on the compact sublevel set; both reusable beyond Lorenz where
      practical.
- [ ] A refutation lemma for a bound below `V(0)` (`1300`), as `five_refuted`.
- [ ] `Tests/Lorenz.lean` pins every interface name; `lake build` clean; axiom
      reports show only propext, Classical.choice, Quot.sound.
