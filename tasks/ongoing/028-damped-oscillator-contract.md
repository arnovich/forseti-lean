---
title: Trajectory contract for the damped oscillator compiled from source equations
state: ongoing
claimed_by: claude-f028
claimed_at: 2026-09-28T10:42:58Z
branch: feat/damped_oscillator_contract
priority: medium
labels: [trajectory, contracts, examples, energy]
related: ["gimle-forseti/148", "asgard-lean/032"]
---

## Context

asgard-lean 032 (released in v1.5.0) compiles the damped oscillator
`x'' + 3x' + 2x = 0` with a declared velocity `v`
(`Examples/DampedOscillator.lean`). gimle-forseti's deciders can only reach a
model through a trajectory contract, like `Examples/ThreeStateContract.lean`
for the three-state model. The oscillator has none, and its source body
declares no observation.

Along any solution, the energy `E = 2x² + v²` has
`dE/dt = 4xv + 2v(−3v − 2x) = −6v² ≤ 0`. So `0 ≤ E ≤ E(0)`, which is `2` for
`x(0) = 1`, `v(0) = 0`. `LinearEnergy.certificate_energy_bound` proves exactly
this shape, from a weighted-square certificate for `P = diag(2, 1)` and its
dissipation `diag(0, 6)`.

## Outcome

- [ ] `Examples/DampedOscillator.lean` (forseti-lean namespace) defines its own
      source `body`: the oscillator equations with the declared velocity, plus
      observations `x`, `v` and `E := 2*x^2 + v^2` with stable port IDs
      (`obs-x`, `obs-v`, `obs-e`). It also defines a concrete `evolution`
      (no arguments; start 0, `x(0) = 1`, `v(0) = 0`) and the compiled `model`.
      Proved: `initial_eq`, `energyIndex`, `energy_at`, `energy_at_initial`
      (`= 2`), `compiled_exists`, `compiled_unique`, and `compiled_energy_bound`
      (`0 ≤ E ≤ 2` for `t ≥ 0`, via `LinearEnergy` with an exact certificate).
- [ ] `Examples/DampedOscillatorContract.lean` mirrors
      `ThreeStateContract`. It defines `observed`, `admitted` and
      `feedback_reads`, a `loop_contract`, an `energy_contract`
      (`Contract observed evolution.time admitted (Always … 0 ≤ E ∧ E ≤ 2)`),
      `declared_input_admitted`, and a refutation `one_refuted` showing `E ≤ 1`
      is not a bound.
- [ ] `#guard_msgs` axiom audits (only propext, Classical.choice,
      Quot.sound), a clean `lake build`, and `docs/properties.md` and the
      README examples table updated.
- [ ] No release tag: gimle-forseti 148 consumes it through a release.
