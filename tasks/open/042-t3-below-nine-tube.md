---
title: The 3-mode member's degree-4 tube below E ≤ 9
state: open
priority: medium
labels: [lean, nonlinear, research]
related: ["040", "041"]
---

# The 3-mode member's degree-4 tube below E ≤ 9

## Context

`PolynomialTrapping` (task 041) and its 5-mode instance `K5Below6` exist.
gimle-forseti's task 214 ran the same degree-4 search on the 3-mode member
at `ν = 1/10` and found a tube around the stable focus the start approaches,
feasible at caps 10 and 8, with inward boundary field by about `0.025` and no
forward orbit leaving; made exact with the containment at `E ≤ 9`, the
scratch replay `Task214T3.lean` checks `V ≤ 1 → V' ≤ α (inner − V)` and
`V ≤ 1 → E ≤ 9` in twelve seconds (`docs/spikes/196-cross-term-trapping/`
there). The member's standing undecided claim is `E ≤ 10`; `T3Below12`
(task 040) gives `12`.

## Outcome

- `Examples/GalerkinNS/T3Below9.lean`, generated from the exact data by
  gimle-forseti's emitter (a parameterised `emit_k5below6.py`), with
  `below9_contract`: `0 ≤ E ≤ 9` for all time from `(1, 1, 1)`, the laminar
  point outside the set, the start inside, `V'` tied to the library's
  partials and the field; audited; the tests pin it beside `T3Below12`
- a release
