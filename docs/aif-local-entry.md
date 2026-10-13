# Certified terminal entry into local AIF stability

`Gimle/Forseti/Examples/AIFLocalEntry.lean` supplies the algebraic bridge from a
startup tube's closed right endpoint to the local Lyapunov region. It requires
an exact weighted-square certificate for P_end - I/50, plus local energy at
most 1/400 for each parameter-edge endpoint center.

Convexity of the local quadratic bounds every affine interpolation of those
centers. Tube membership with radius squared 1/40000 then bounds the error's
squared norm by 1/800. Since the local quadratic is at most the squared norm,
the quadratic triangle estimate gives V(state) <= 3/400 < 1/100. The physical
time wrapper uses start + step and the slab's original parameter interval.
All hypotheses are explicit; no trajectory entry is assumed or fabricated.

The regression module checks a concrete identity-metric slab with an exact
diagonal certificate, all parameter interpolation values, its physical right
endpoint at time 31, and a concrete member of that tube. The example's energy
and time scales agree with the production theorem's constants.

This generic bridge does not certify the candidate's eight terminal cells.
Those cells still need their metric certificates and center checks, followed
by composition with startup membership and local continuation. No moving-tube
coverage, unconditional zero-start safety conclusion, dependency pin change,
or checker enrollment is added. Run `lake build` for the proof checks.
