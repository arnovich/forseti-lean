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

- A bare `Formula n` addresses coordinates by position. [`Syntax/Context.lean`](../Gimle/Forseti/Syntax/Context.lean)
  names them: a `Context` is an ordered list of distinct, non-blank names that
  fixes the dimension, and a `NamedFormula` pairs a formula with one. Products
  concatenate contexts and refuse shared names. A solver's answer is read back
  by name (`Context.read`, proved sound by `read_mem`, round trip `read_assign`),
  refusing a missing, repeated or unknown name. Coordinates are written by name
  (`Context.var`, checked when the formula is built), and a `Goal` puts both
  sides of an entailment over one context for a checker to bind.
- Arbitrary predicates need not have a formula. No transcendental operations are included.
- `Fattened` uses an existential witness and an exact nonnegative rational radius.
  Zero radius, radius monotonicity, and inclusion of the core are proved.
- [`Syntax/Certificate.lean`](../Gimle/Forseti/Syntax/Certificate.lean) checks
  evidence an untrusted producer supplies for a `Goal` `P ⊨ Q`:
  - **Entailment certificates**, when both sides are conjunctions of `p ≤ 0` or
    `p ≥ 0` (and `tru`): for each consequent constraint `q_j`, an identity
    `−q_j = σ_j0 + Σ_i σ_ji · (−p_i)` with one multiplier per antecedent
    constraint and every `σ` a nonnegatively weighted sum of squares. The
    identity is decided by normalizing the difference to a sparse polynomial,
    computably (Mathlib's `MvPolynomial` cannot be evaluated by `decide`), with
    `Sparse.eval_ofExpr` tying the normal form to `Polynomial.Expr.eval`.
    `EntailmentCertificate.sound` proves the goal from a check that passes. The
    family is incomplete: no certificate means nothing.
  - **Counterexamples**, for any quantifier-free goal: a rational point named
    coordinate by coordinate and read through the goal's context, where the
    antecedent holds and the consequent does not, decided exactly over ℚ
    (`Formula.holdsQ_iff`). `refutes_sound` proves `¬ P ⊨ Q`.
  - A failed check rejects the evidence and establishes nothing about the goal.
    [Examples/PredicateCertificates.lean](../Gimle/Forseti/Examples/PredicateCertificates.lean)
    checks the shared corpus and weakens a Hoare postcondition with a checked
    entailment; `Tests/Certificate.lean` holds the hostile evidence and asserts
    the axiom policy with `#guard_msgs`.
- No general entailment solver, CAD/SMT proof-log checker, algebraic-number
  witness or serializer is supplied; producers live outside this repository.

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
