---
title: Measure and reduce AIF certificate replay cost
state: open
priority: medium
labels: [research, certificates, performance]
depends_on: [050]
related: [049]
---

# Measure and reduce AIF certificate replay cost

## Context

Task 050 kernel-checks one complete AIF drift box, including both 40-matrix
Bernstein families and their binding to the independently defined drift target.
Its two generated endpoint files occupy 355,609 bytes. A direct repetition over
all 2,960 candidate slabs would require 236,800 matrix certificates and roughly
1 GB of source. This extrapolation does not establish feasible whole-candidate
replay. See [the measured pilot](../../docs/aif-drift-pilot.md).

The next gate is replay cost and representation, before generating the whole
candidate. A compact proposal function may replace repeated literal square
data, but every accepted result must still have an ordinary kernel-checked
representation proof and a binding to the actual drift polynomial. No enlarged
axiom policy, native evaluation authority or Python release-pin change is implied.

## Outcome

- [ ] Record a reproducible baseline separating certificate checking,
  polynomial binding and final algebraic assembly, with source/compiled size,
  CPU time, wall time and peak memory on a declared machine.
- [ ] Compare at least one compact representation or reusable binding proof
  against the task 050 literals on the identical box and theorem statement.
- [ ] Kernel-check the selected approach, preserving exact coefficients,
  derivative factors, endpoint coverage and hostile-certificate regressions.
- [ ] Measure a small batch spanning more than one parameter bin and time slab;
  report measured scaling separately from a 2,960-slab extrapolation.
- [ ] Record a go/no-go assessment and the remaining trajectory obligations;
  run both required builds and a mathematical/performance review panel.

## Notes

Potential experiments include computing square proposals from rational matrices
inside Lean and proving polynomial identities through a shared coefficient-level
bridge. Choose from measurements; neither approach is prescribed. Full startup
containment, joins, terminal continuation and original-circuit binding remain
separate mathematical obligations.
