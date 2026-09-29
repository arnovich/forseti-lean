---
title: Trajectory contract for a driven model under its driver precondition
state: closed
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
  compiled field (`rates_expressions`), initial state (`initial_eq`), the
  observation read (`x_at`, `x_at_initial`), the driver coordinates (`index_u`,
  `index_du`), and `same_source`: inputs, assignments, differentials, evolution
  and drivers equal asgard-lean's `DrivenForcing`.
- `Driven.lean` holds the model-independent `forwarded F obs` (the driven
  feedback, with the driver wires forwarded to the observation) and
  `forwarded_rel`, which states its relation without unfolding `F`.
- `Examples/ForcedDecayContract.lean` proves `contract_within B`, a well-posed
  `Contract` over `observed`: for every input whose drivers are admitted
  (`Evolution.Admitted`) with `|u| ≤ B` on the domain and whose initial wire
  starts at `x(0) = 0`, an output exists, outputs agree on `t ≥ 0`, and
  `|x| ≤ 2B` at every `t ≥ 0`. `driven_contract` is `B = 1` with the band
  `[−2, 2]`, under the precondition `admitted`, which is not `True`.
- `feedback_reads` equates the feedback relation with asgard's
  `DrivenModel.Realizes`; `compiled_exists` realizes every admitted driver.
- The precondition is not vacuous and neither part is idle:
  `witness_input_admitted` (`u = sin`); `one_refuted` (`u = cos` breaks the
  band `[−1, 1]` at `t = π`); `bound_needed` (without `|u| ≤ 1`, `u = 3` breaks
  `[−2, 2]` at `t = 2`).
- `Tests/ForcedDecay.lean` pins the IDs a renderer cites (`obs-x`,
  `driver-u`, `driver-du`, `initial-x`, `time`), the precondition's shape, a
  non-admitted driver, and the axiom reports with `#guard_msgs`.
- Full `lake build` is clean and axiom reports show only `propext`,
  `Classical.choice` and `Quot.sound`; the release is tagged `v1.9.0` for
  gimle-forseti 170 to pin.
