# Nonnegative physical AIF trajectories and finite-time bounds

`Gimle/Forseti/Examples/AIFNonnegative.lean` proves that a supplied solution of
`AIFPhysicalCoordinates.physicalField`, starting with all four species zero,
has nonnegative species on every closed interval [0,T] where it solves the ODE.
The only parameter restriction is eta >= 0, including eta = 0.

For each time t in that interval it also proves:

- z1 <= 2t;
- x1 <= t^2;
- x2 <= t^3/3;
- z2 <= t^4/12.

These deliberately loose polynomial estimates will support a finite-horizon
existence and continuation argument. They do not establish existence or
uniqueness themselves, and do not replace the certified x2 <= 16/5 moving-tube
output bound. Derivatives, initial state, and a fixed parameter remain explicit
premises. Both endpoints are included.

The scalar helper permits zero rates at zero, but requires nonnegative rates
throughout the nonpositive region. A strict perturbed barrier proves the result.
For the physical field, a strict boundary argument first establishes z1 >= 0;
the weak comparison then establishes x1, x2, and z2 in order. Polynomial upper
bounds follow by dropping nonpositive decay or reaction terms.

The regression module `Gimle/Forseti/Tests/AIFNonnegative.lean` checks zero-rate
and zero-length intervals, all four physical endpoint signs, polynomial bounds
at eta = 0, and a negative cubic showing why a weak boundary-only condition is
insufficient. Run `lake build` to check the proofs and their axiom reports.
