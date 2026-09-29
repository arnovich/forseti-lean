---
title: Trajectory contract for a driven model under its driver precondition
state: ongoing
claimed_by: claude-170
claimed_at: 2026-09-29T10:03:53Z
branch: task/033_driven_forcing_contract
priority: medium
labels: [trajectory, contracts, examples, drivers]
related: ["asgard-lean/031", "gimle-forseti/170", "028"]
---

## Context

asgard-lean 031 (released in v1.7.0) lets a source declaration name a driver:
`Examples/DrivenForcing.lean` compiles `D_t(x) + x = D_t(u) + u`, `x(0) = 0`,
where `u` is a declared differentiable driver with derivative port `du`, and
`Evolution.Admitted` requires `u` continuous on `t ≥ 0` with `du` its actual
derivative there. gimle-forseti 170 must bind a driven model's driver
precondition in its trajectory root theorem, instead of `fun _ => True`, and
show a driven model deciding `PROVEN` under it. No trajectory contract over a
driven model exists yet, and that body declares no observation.

With `y = x − u` the relation gives `y' = −y`, so `x(t) = u(t) − u(0)·e^(−t)`
and `|x| ≤ 2` for every admitted driver with `|u| ≤ 1`.

## Outcome

- `Examples/ForcedDecay.lean` declares the same equations with an observation
  `obs-x` of `x`, compiles them with `compileSourceDriven`, and states the
  compiled field, initial state and observation index, as
  `Examples/DampedOscillator.lean` does for 028.
- `Examples/ForcedDecayContract.lean` defines the observed circuit (the driven
  feedback, with the drivers forwarded to the observation) and proves a
  well-posed `Contract` over it: for every input whose drivers are admitted
  with `|u| ≤ 1` on the domain and whose initial wire starts at `x(0) = 0`,
  an output exists, outputs agree on `t ≥ 0`, and `|x| ≤ 2` at every `t ≥ 0`.
- The precondition is not vacuous: a named driver (`u = sin`, `du = cos`) is
  admitted, and one admitted input has an output with `|x| > 1` at some time,
  so `1` is not a bound.
- Full `lake build` is clean and axiom reports show only `propext`,
  `Classical.choice` and `Quot.sound`; a release tag follows for
  gimle-forseti to pin.
