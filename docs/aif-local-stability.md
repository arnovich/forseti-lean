# Local AIF continuation after entry

`Gimle/Forseti/Examples/AIFLocalStability.lean` checks the fixed rational
Lyapunov quadratic from Task 243 against the shifted AIF vector field. For
fixed eta in [8,12], its sublevel V <= 1/100 is invariant along any supplied
solution on a closed interval that starts in that sublevel. The corresponding
physical output satisfies x2 <= 5/2 throughout that interval, including its
right endpoint.

The exact square certificates establish V >= ||y||²/25 and four endpoint
bounds for the energy rate. Bilinear interpolation in eta and the third
shifted coordinate gives dV/dt <= -||y||²/25 inside the region. The proof also
checks V <= ||y||²; together these bounds make the derivative strictly negative
on V = 1/100. The existing scalar boundary theorem then supplies invariance.
The derivative is proved from the component ODEs and the existing affine
physical-to-shifted coordinate identity.

The certificate coefficients and endpoint square decompositions originate in
`gimle-forseti/docs/spikes/243-targets/evidence/AifLocal.lean`; their identities
and positivity are rechecked by the Lean kernel in this repository. No result
is trusted from that old research artifact.

Regression proofs cover both parameter endpoints, zero energy at equilibrium,
the fact that the physical zero start is outside the local region, and a
conditional output bound at time 100 given local entry at time 30. Entry is
an explicit premise: the terminal startup certificates must still establish
it. This increment adds no moving-tube cell coverage and does not prove the
full zero-start safety theorem. It changes neither the Asgard pin nor checker
enrollment. Run `lake build` to check the implementation and regressions.
