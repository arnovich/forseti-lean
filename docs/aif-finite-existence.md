# Original physical AIF solutions on finite horizons

`Gimle/Forseti/Examples/AIFFiniteExistence.lean` constructs a zero-start solution
of the original physical AIF field on every closed interval [0,m], for a natural
number m and any fixed eta >= 0. In particular m = 100 covers the requested
safety horizon. The conclusion provides the original coordinate derivatives
at both endpoints as well as in the interior.

The construction uses `Nonlinear.Trapping.clamped_solution_on`, the existing
Picard-Lindelof implementation. Its auxiliary species box is [0,B]^4, with
B = 1 + 2m + m^2 + m^3/3 + m^4/12. The proof establishes nonnegativity and the
same polynomial growth bounds for the clamped solution itself. Those estimates
put every coordinate inside the box throughout [0,m], where the clamp is the
identity. Only then does the proof conclude that the original ODE is solved.

The module checks smoothness of the original field and both saturation
semantics of the clamp. The regression module checks the requested horizon,
eta zero with a zero-length interval, concrete coordinate saturation, and an
outside-box state where the auxiliary and original fields differ.

This is finite-horizon existence. It does not yet prove uniqueness or select a
single solution on all forward times. The compiled circuit's current `Realizes`
relation requires that full forward domain, so its existence premise is not
yet discharged. The moving-tube x2 <= 16/5 proof and complete certificate
coverage remain separate. Run `lake build` for the proof and regression checks.
