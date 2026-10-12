# AIF moving-energy chain rule

[`AIFTrajectory.lean`](../Gimle/Forseti/Examples/AIFTrajectory.lean) connects the
algebraic `AIFSlabModel.energyRate` to the derivative of the existing physical-time
`AIFMesh.tubeEnergy` along a supplied trajectory of `AIFDriftModel.field`.

The proof has three parts:

- `matrixForm_hasDerivWithinAt` differentiates a moving real quadratic form in any
  finite dimension, retaining the matrix derivative and both state product terms.
  It needs neither symmetry nor positivity.
- `error_derivative` subtracts the physical center derivative from the supplied
  field derivative. The parameter is fixed, and the inverse eta-coordinate
  identity connects the physical parameter to the slab's normalized coordinate.
- `tubeEnergy_derivative` composes those facts with the physical metric derivative.
  It requires nonzero slab width, ordered eta endpoints and component derivatives
  of the supplied trajectory. It imposes no tube-membership assumption.

All three use derivatives within an arbitrary time domain, so they can be applied
on a closed slab without extending the solution past its endpoints. No claim of
ordinary differentiability outside that domain follows.

[`Tests/AIFTrajectory.lean`](../Gimle/Forseti/Tests/AIFTrajectory.lean) checks all
three saved mesh widths on closed intervals, a nonsymmetric moving matrix with
energy `5*t^3`, rejection of a rate that omits the metric derivative, and the
physical energy rate at a center with nonzero slope.

This closes the chain-rule obligation, not the trajectory theorem. It does not
prove existence, uniqueness, nonnegativity, tube invariance, complete local drift
coverage, or binding of this polynomial field to the typed circuit. The checked
cell counts remain 30 local drift results, 22 conditional containment results and
22 mesh transports. Next comes a local invariance argument using the strict
negative boundary rate, followed by composition across the mesh. The existing
`Dissipative.sublevel` rule assumes its differential inequality throughout the
domain, so applying it directly to an in-tube-only bound would be circular.

A suitable next-step API is mathlib's
`image_le_of_deriv_right_lt_deriv_boundary` in `Analysis/Calculus/MeanValue.lean`:
it preserves a bound using strict derivative control only at its boundary.
Applying it still requires continuity, the right-domain derivative conversion,
initial membership and the cell's checked boundary drift.

Validation passes under the pinned Lean 4.32.1: the implementation and concrete
regression proofs, `lake build` (737 axiom reports), `lake build equation_demo`
(63 reports), all 57 Python tests, and the build-path and suspension checks.
No Lean warnings or errors remain; reported axioms are limited to `propext`,
`Classical.choice` and `Quot.sound`. The mathematical, integration and evidence
panel found no blockers. Logs, source/artifact hashes, the checking-environment
fingerprint and review synthesis are retained under `.lake/aif_energy_chain_rule/`.
Existing generated certificate modules were unchanged and were not replayed.
