# Compiled linear circuits and Hoare invariants

The [execution bridge](../Gimle/Forseti/LinearCircuit.lean) retains the original
Asgard polynomial update and readout expressions. Existing
`LinearSyntax.coefficients` acceptance identifies their homogeneous rational
linear coefficients; existing compilation soundness relates those coefficients
to the original circuits. `Program.state` uses initialized `Discrete.run` with
empty input and parameter ports. `Program.observe` reads its compiled output.

Two such programs of dimensions `d₁` and `d₂`, at specified real initial states,
agree at every natural step exactly when their first `d₁+d₂` outputs agree.
Time zero observes initialization. Empty dimensions are allowed. Rational
initial states additionally admit exact rational matrix calculations through
proved cast identities.

The [logic bridge](../Gimle/Forseti/LinearCircuitHoare.lean) constructs an actual
`Syntax.Formula`: the finite conjunction saying that the next `d₁+d₂` outputs
agree. It reuses Asgard's polynomial substitution and Forseti's formula
renaming. Its denotation is the finite compiled-observation condition.

Writing this predicate as `K`, the exported `prefix_hoare` theorem has the
existing judgment

```lean
ExactHoare (prefixFormula P Q).toPredicate (pairedUpdate P Q)
  (prefixFormula P Q).toPredicate
```

Thus `{K} pairedUpdate {K}` holds over arbitrary real states. The algebraic
finite-prefix theorem supplies preservation and entailment to current output
equality. `prefix_safety` applies the existing `Discrete.certificate_sound`.
`observations_eq_of_prefixFormula` consumes that safety result, initialized
execution, and the paired-run correspondence to conclude equality forever.

The [Fibonacci examples](../Gimle/Forseti/Examples/LinearCircuitFibonacci.lean)
demonstrate this route with differing state dimensions, real-scaled
initialization and a consistent coordinate permutation.
The [Jordan-chain examples](../Gimle/Forseti/Examples/LinearCircuitJordan.lean)
apply the same interface to damped Jordan chains of dimensions one, two and
three. They establish the initial formula from exact rational observations
and use the same Hoare-derived endpoint; the two larger cases have distinct
compiled transitions.
Both files are also native Forseti notebooks: Markdown prose, Lean definitions
and checked claims in one canonical source, with observation metadata beside
each file. Open either file directly with the `gimle-forseti` notebook workbench;
the [notebook guide](https://github.com/arnovich/gimle-forseti/blob/main/examples/notebooks/README.md)
gives the setup and commands. Lake continues to compile the same proofs.
The [regression proofs](../Gimle/Forseti/Tests/LinearCircuit.lean) keep the
independent initial observations, empty-state cases, exact casts, deliberate
mutations and unsupported-syntax controls.

```sh
lake build Gimle.Forseti.Examples.LinearCircuitFibonacci
lake build Gimle.Forseti.Examples.LinearCircuitJordan
lake build Gimle.Forseti.Tests.LinearCircuit
```

This is exact discrete output equivalence for fixed initialization and readout.
It does not imply hidden-state stability or state-space conjugacy. Recognition
is sufficient and incomplete: rejection does not establish nonlinearity.
Repeated substitution can enlarge the formula; no efficiency claim is made.
These optional property modules do not change the checker's admitted interface,
verify Python export, or establish floating-point, continuous-time or PDE claims.
