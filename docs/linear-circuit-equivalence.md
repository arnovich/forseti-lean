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

The [acceptance proofs](../Gimle/Forseti/Tests/LinearCircuit.lean) exercise this
route on original compiled expressions, including differing state dimensions,
real-scaled initialization, empty spaces and deliberate mutations.
The [separate reuse proofs](../Gimle/Forseti/Tests/LinearCircuitReuse.lean)
apply the same interface to damped Jordan chains of dimensions one, two and
three. They establish the initial formula from exact rational observations
and use the same Hoare-derived endpoint; the two larger cases have distinct
compiled transitions.

```sh
lake build Gimle.Forseti.Tests.LinearCircuit
lake build Gimle.Forseti.Tests.LinearCircuitReuse
```

This is exact discrete output equivalence for fixed initialization and readout.
It does not imply hidden-state stability or state-space conjugacy. Recognition
is sufficient and incomplete: rejection does not establish nonlinearity.
Repeated substitution can enlarge the formula; no efficiency claim is made.
These optional property modules do not change the checker's admitted interface,
verify Python export, or establish floating-point, continuous-time or PDE claims.
