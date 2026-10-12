# AIF physical and shifted coordinates

[`AIFPhysicalCoordinates.lean`](../Gimle/Forseti/Examples/AIFPhysicalCoordinates.lean)
relates the four physical species `(x1,x2,z1,z2)` to the tube coordinates
`(x1-2,x2-2,z1-2,eta*z2-1)`. The physical field uses plant gain one and reference
two, as specified in the startup research target.

The forward field identity scales the fourth velocity by the same fixed eta.
It holds even at eta zero because it uses no division. The inverse and reverse
trajectory rule explicitly require eta to be nonzero; eta in `[8,12]` satisfies
that condition. Both trajectory rules work with derivatives within an arbitrary
domain, so they retain closed interval endpoints. Eta is one fixed real
parameter throughout each trajectory.

The module proves that physical zero has shifted state `(-2,-2,-2,-1)`, and that
`x2 <= 16/5` is equivalent to the shifted coordinate-one bound `y1 <= 6/5`.
`physical_tubeEnergy_derivative` applies the previously checked moving-energy
chain rule to a supplied solution of the physical equations after the shift.

The [regression file](../Gimle/Forseti/Tests/AIFPhysicalCoordinates.lean) checks
zero-startup velocities and the output coordinate, rejects a missing fourth
velocity scale at eta eight, and shows why inversion at eta zero loses a state
coordinate.

This checkpoint is an algebraic model specification, not yet the binding to the
original compiled circuit. Circuit compilation and feedback semantics remain
Asgard's responsibility. It does not assert trajectory existence, uniqueness,
nonnegativity, complete startup certificate coverage or the final output bound.

Validation passed: full Lean build (759 axiom reports), optional `equation_demo`
build (63 reports), all 57 Python tests, and the build-path and suspension
checks. The eight implementation lemmas and two named hostile tests use only
standard axioms. The corrected regression artifact is recorded from the
successful full build with its source, setup and log provenance. The mathematical,
integration and evidence panel found no blockers. Evidence is retained under
`.lake/aif_physical_coordinates/`; verification SHA-256:
`8359b37ab8272f25f532cf223db4ac48198ea43487afa2910aeded0a1bc598b5`.
