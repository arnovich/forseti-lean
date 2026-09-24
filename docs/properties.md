# Predicates and Hoare rules

Import [`Gimle.Forseti`](../Gimle/Forseti.lean) for the core property language.
Circuits and their real semantics come from Asgard.

| Type | Meaning |
| --- | --- |
| `Predicate n` | Any property of an `n`-dimensional real point |
| `PredicateEntailment P Q` | Every point satisfying `P` satisfies `Q` |
| `ExactHoare P c Q` | Circuit `c` sends each admitted input into `Q` |
| `QuantitativeHoare P c Q ε` | Each admitted input's output has a witness in `Q` within coordinatewise distance `ε` |

The quantitative claim includes **both `Q` and `ε`**. Fattening `Q` changes what
the budget measures. An infimum-distance test is not a substitute for the witness.

## Formula syntax

[`Syntax.lean`](../Gimle/Forseti/Syntax.lean) provides rational polynomial
comparisons, Boolean combinations, and coordinate products. `Formula.toPredicate`
connects this syntax to the semantic core.

- Coordinates are positional `Fin n`; ordered variable names remain planned work.
- Arbitrary predicates need not have a formula. No transcendental operations are included.
- `Fattened` uses an existential witness and an exact nonnegative rational radius.
  Zero radius, radius monotonicity, and inclusion of the core are proved.
- No verified general entailment solver, solver-certificate checker, or serializer is supplied.

## Composition

`Circuit.compose first second` runs `first` first.

| Rule | Required evidence | Resulting error |
| --- | --- | --- |
| `exactHoareSequential` | Exact triples with a shared intermediate predicate | Exact |
| `exactThenQuantitativeHoareSequential` | Exact first triple, quantitative second | Second error |
| `quantitativeHoareSequential` | Both triples, a modulus for the second circuit, and actual/ideal intermediate coverage | Amplified first error + second error |
| `canonicalSequential` | Modulus on the intermediate neighbourhood; nonnegative first error | Amplified first error + second error |
| `coverageSequential` | The second precondition contains `Neighbourhood middle sourceError` | Second error |

Errors do not generally add through a pipeline: multiplying by 10 amplifies an
input error of 1 to 10. Sensitivity and region coverage need proofs.
See [SequentialHoare tests](../Gimle/Forseti/Tests/SequentialHoare.lean).

## Approximation transport

[`Approximation.lean`](../Gimle/Forseti/Approximation.lean) consumes a proved Asgard
claim tied to the actual circuits, region, and budget. `transportExact` and
`transportQuantitative` transfer properties with region coverage; the latter
adds the existing property allowance. Labels and numerical samples provide no proof.
