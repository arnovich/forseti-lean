---
title: Rebase discrete recurrences on asgard-lean's semantics
state: open
priority: low
labels: [discrete, migration]
depends_on: ["asgard-lean/045"]
---

## Context

gimle-forseti `docs/model-family-contracts.md` (task 084), "Initialized discrete updates": once asgard-lean owns the
recurrence semantics and its compiler (045), `Discrete.lean` should reuse it
rather than keep its own. `LinearCircuit.lean` unfolds `Discrete.step`,
`LinearCircuitHoare.lean` uses `Discrete.run` and `Discrete.run_realizes`,
and gimle-forseti's `notebook/evidence.py` names
`Gimle.Forseti.Discrete.step`.

## Outcome

- `Discrete.lean` builds on asgard-lean's recurrence, with
  `Gimle.Forseti.Discrete.run`, `step` and every lemma other files use
  (at least `run_realizes`) kept as aliases.
- Every existing statement is textually unchanged; the `#print axioms` audits
  are re-recorded and show only standard axioms.
- The rebase lands after an asgard-lean release containing 045 and does not by
  itself require a gimle-forseti re-pin.
