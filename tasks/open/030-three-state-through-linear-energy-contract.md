---
title: Express the three-state contract through the generic linear-energy construction
state: open
priority: low
labels: [trajectory, contracts, cleanup]
related: ["029"]
---

## Context

029 added `LinearEnergyContract`, the generic construction for compiled linear
models, and re-expressed `DampedOscillatorContract` through it.
`ThreeStateContract` still carries its own copies of the same steps:
`feedback_reads`, `loop_contract`, the composed `energy_contract`,
`declared_input_admitted` and `five_refuted`. `Examples/ThreeState.lean` also
has a bespoke diagonal energy bound (`energy_bound`) where a
`LinearEnergy.Certificate` for `P = I` would do.

## Outcome

- [ ] `ThreeState` gains a `LinearEnergyContract.Spec` (view, `energyIndex`,
      `P = I`, and a certificate for its dissipation), and `ThreeStateContract`
      is expressed through it. Every public name and statement gimle-forseti's
      registry cites stays unchanged, pinned by a test.
- [ ] The generic parameterized lemmas (`energy_bound` for any nonnegative
      `(a, b, c)`) stay, if anything still uses them.
- [ ] Clean `lake build` and axiom audits.
