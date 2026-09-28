---
title: Build trajectory contracts for compiled linear models from an energy certificate
state: closed
priority: medium
labels: [trajectory, contracts, energy, linear]
related: ["028", "gimle-forseti/148"]
---

## Context

gimle-forseti's deciders reach a model only through a trajectory contract in
the shape of `Examples/ThreeStateContract.lean`, and each is written by hand.
028's damped oscillator needed about 200 lines that mirror the three-state
ones:
- compiled existence and uniqueness through the model's `LinearView`;
- `feedback_reads`;
- an energy bound through `LinearEnergy.certificate_energy_bound`;
- the composed `energy_contract`;
- the admitted input and a refutation at the start.

Only the model, the energy matrix, its certificate and the initial energy
differ between them.

asgard-lean's source compiler now reaches higher-order equations, lower-order
atoms and integrals (027, 028, 032, 034). Every new model the deciders should
know still costs a hand-written contract.

## Outcome

- [x] A generic construction (e.g. `Trajectory.LinearEnergyContract`) takes:
      a compiled continuous model with a `LinearView`; an energy observation
      index with a proof that it computes `xᵀPx`; a `LinearEnergy.Certificate`
      that is `Valid` for the view's matrix and `P`; and a bound at least the
      initial energy. It yields the same `energy_contract`, `feedback_reads`,
      `declared_input_admitted` and existence facts the renderer cites, with
      exactly the shapes of `ThreeStateContract`.
- [x] A refutation lemma: an initial energy above a claimed bound refutes it.
- [x] `DampedOscillatorContract` is re-expressed through it, with its public
      names and statements unchanged, so gimle-forseti's registry entry keeps
      working, and it gets shorter.
- [x] A second model is added using only the construction (e.g. a compiled
      higher-order or integral example from asgard-lean's source compiler),
      and its size is recorded.
- [x] Axiom audits and a clean `lake build`. `docs/dynamics.md` states the
      construction.
