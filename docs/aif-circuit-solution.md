# A realizable, unique, nonnegative compiled biochemical circuit

The checked `AIFCircuitSolution` research composition binds the constructed global
physical trajectory to Asgard's original compiled AIF feedback relation.
For every fixed eta >= 0, that feedback has a realization, all of its realizations
agree on nonnegative times, and every physical species and the compiled x2
observation are nonnegative there.

Combining this with the existing startup output proofs gives a nonempty behavior
set and universal bounds 0 <= x2 <= 16/5 on these closed intervals:

- eta in [8,12], time in [0,1/200];
- eta in [8,17/2], time in [0,21/200].

Both statements explicitly prove existence and bound every realization of the
same fixed-parameter source-compiled feedback. Initialization is physically zero,
and the observed quantity is its compiled `AIF.output` circuit.

This discharges the realization assumption for those startup intervals. It does
not add cell certificates or prove the requested bound through time 100. Complete
startup coverage through 30 and the terminal/local continuation proof remain.
Uniqueness is only asserted on the declared forward domain.

Generate the seven-theorem composition with:

```sh
python3 tools/aif_circuit_solution.py --output-directory .lake/aif_circuit_solution
```

Add `--check` to compare existing source bytes without creating or repairing
files. Lean checking in the archived research context supplies proof authority;
the generator does not. The Task #248 `circuit-solution` evidence records the
startup-output and global-solution prerequisites, shared import byte identities,
compiler result, axiom reports and exact artifacts. This uses the research
Asgard binding; the production dependency pin and checker enrollment are unchanged.
