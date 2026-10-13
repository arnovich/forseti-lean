# A unique nonnegative forward physical AIF solution

`Gimle/Forseti/Examples/AIFGlobalSolution.lean` constructs one zero-start physical
AIF trajectory on the full forward domain [0,infinity), for every fixed eta >= 0.
It proves the component ODEs within that domain at every nonnegative time,
including time zero. Every species is nonnegative. Any other zero-start physical
solution agrees with it at every nonnegative time.

Uniqueness is stated as `Set.EqOn` on the forward domain: no constraint or
uniqueness is claimed for negative times.

The proof first uses the polynomial bounds to place any two supplied finite
solutions in a common compact box, where the existing Lipschitz uniqueness
theorem applies. It then chooses a solution on every natural-number horizon.
Those choices agree on overlap. At time t, the global function selects the
piece with horizon ceiling(t) + 1; agreement gives its derivative on a
neighborhood within the forward domain, including integer joins.

The regression module checks eta zero, the full-domain initial derivative,
agreement at every integer join, all four nonnegative species at time 100,
and agreement with any competing solution at that time.

This establishes existence, forward uniqueness and nonnegativity for the
original physical field. Transport through the existing compiled-circuit
identity is the next step. It does not add moving-tube certificates or extend
the sharp x2 <= 16/5 safety interval. Run `lake build` for all proof checks.
