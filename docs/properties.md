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

## Stream contracts

[`Stream.lean`](../Gimle/Forseti/Stream.lean) states properties of Asgard's
formal stream circuits (`Streams.Circuit basis d n m`: `n` ports of exact
coefficient streams over `d` ordered axes, OGF or EGF). Their semantics is
partial and deterministic, so `StreamHoare P c Q` is the **total** contract:
every admitted input is in the domain and its output satisfies `Q`.
`streamHoare_iff_rel` restates it as "an output exists and every related output
satisfies `Q`". An undefined series substitution never makes it vacuous, even
when its result is discarded or multiplied by zero.

- Rules: `consequence`, `congr` (along `StreamEquality`), `route`, `identity`,
  `compose` (wiring, not time), `parallel` and `pair` (explicit port blocks via
  `Both`; `both_equals` reads them as one point), `and`, `or`, `substitute`
  (along `Circuit.Equivalent`) and `expr` for compiled expressions.
- Predicates: `Equals` (a full stream point), `Boundary` / `NamedBoundary` (a
  port's whole zero slice along an axis) and `Window` (a finite coefficient
  window, which never gives full equality). `boundary_reindex` and
  `window_reindex` transport `Boundary` and `Window` through `reindex`.
  `NamedBoundary.iff_boundary` resolves a named axis; an unresolved name makes
  `NamedBoundary` false, so resolve it before using it as a precondition.
- Operations: `StreamHoare.derivative`, `integral` / `integralFrom` (keeps the
  whole boundary profile, reads only its zero slice, and inverts the
  derivative), `product` (in the declared basis) and `seriesCompose` (only under
  `CanCompose`). `eq_integral_of_boundary`: a stream is fixed by its derivative
  along an axis and its zero slice there.
- [`Examples/FormalHeatContract.lean`](../Gimle/Forseti/Examples/FormalHeatContract.lean)
  restates Asgard's two-axis heat circuit as `heat_contract`, derived through
  `pair`, `route`, `compose` and `integralFrom`: inputs `u`, any boundary port
  with the declared zero slice, and anything; output `[u_xx, u]`, boundary kept
  along `t`.

This is exact formal coefficient reasoning only. The evaluated field of a
polynomially realized output (asgard-lean 024) is read by the field transfer
rule below; certified tails (025) are not checked here.

## From polynomial certificates to stream and field properties

Two transfer rules, for two different claims. Neither stands in for the other.

**Coefficients of a formal output.** [`StreamObservation.lean`](../Gimle/Forseti/StreamObservation.lean)
- An `Observation` is an Asgard lowering `Manifest` (ordered axis IDs, port IDs,
  coefficient slots; basis in the type) with the `Context` naming each slot,
  `u[t^0, x^2]`. The names are computed from the manifest (`named`), so a
  formula written by name reads the slot the name describes.
  `Observation.Observes φ` reads a 017 formula on those exact rational
  coefficients cast into ℝ, and constrains nothing else (`observes_congr`).
- `lift`: a point `ExactHoare` over the lowered circuit, plus a proof that every
  input admitted by the full-stream precondition meets its precondition on the
  dependency coefficients, gives `StreamHoare pre c (Observes φ)` for the
  **original** circuit. Definedness comes from `lower_defined`, values from
  asgard-lean 023's `lower_correct`; `pre` is kept.
- `leafGoal` poses the leaf as a 017 `Goal` over the named input coefficients,
  each output coordinate replaced by the polynomial the lowering computes
  (`lower_spec`). `leaf_hoare` turns its entailment into the point triple, and
  `lift_certificate` chains everything from a certificate that checks.
- `refutes_root`: a leaf counterexample refutes the root only with a full input
  admitted by `pre` whose named coefficients are the counterexample's values.
- A finite observation is never a full stream (`observed_is_not_full`).
- [Example](../Gimle/Forseti/Examples/StreamObservation.lean): the halo of `∂²/∂x²`
  and a coefficient outside the output window that changes the observed result;
  the formal heat circuit's observed output `x² + 2t` under task 018's
  precondition (`heat_observed`); a leaf refutation that does not reach the root,
  and an altered initial profile that does. Hostile cases (basis, axis, port and
  slot swaps) are in `Tests/StreamObservation.lean`.

**Values of the represented field.** [`FieldBound.lean`](../Gimle/Forseti/FieldBound.lean)
- Formula variables are space-time coordinates and fixed parameters, read at
  real points. `sq_le_sq_of_box` (`-R ≤ x ≤ R → x² ≤ R²`, including `R = 0`) and
  `box_constraint` turn a box into constraints a certificate can use.
- [Example](../Gimle/Forseti/Examples/HeatStripBound.lean): for rational
  `a, c ≥ 0`, `strip_bound` proves `0 ≤ a·x² + c + 2·a·t ≤ c + a·R² + 2·a·T` on
  `0 ≤ t ≤ T, -R ≤ x ≤ R`; at `a=1, c=0, R=T=1` bound `3` checks and bound `2` is
  refuted at `(1, 1)`. Widened domains, altered profiles and `u = x` at `x = -1`
  are refuted in `Tests/FieldBound.lean`.
- These bound the **candidate** polynomial, and a refutation here refutes the
  candidate only.

**Values of a circuit's output field.** [`FieldObservation.lean`](../Gimle/Forseti/FieldObservation.lean)
- A `FieldSpec` names the formula coordinates: the stream's axes in axis order,
  fixed parameters, then the field value (`named`). `FieldSpec.Observes basis
  port θ domain post` holds of an output point when that port is realized, as a
  **whole** stream, by a rational polynomial `q` (asgard-lean 024's
  `Realizes`, equivalently finite support) and `post` holds at `(x, θ, q(x))`
  wherever `domain` does, `q(x)` being `Streams.field`. A window or prefix is not
  a realization; an unrealized port fails the predicate (`not_observes`).
- **Field transfer rule** `lift`: `StreamHoare pre c (port realized by q)` and a
  bound on `q`'s field over the domain give `StreamHoare pre c (Observes …)`.
  `leaf_bound` gets the bound from a 017 `leafGoal` (`post` with the value
  coordinate replaced by an expression) plus two separate obligations: the
  expression **is** `q`'s field (`agrees`), and the stated domain implies the
  leaf antecedent (`strengthen`, e.g. `sq_le_sq_of_box`). `lift_certificate`
  chains them from a certificate that checks. Coefficient constraints are never
  an input: `u = x` has nonnegative coefficients and a negative field.
- `refutes_root`: a field contract fails only through an input admitted by
  `pre`, its related output with the port realized by `q`, and a domain point
  where `q`'s field fails `post`. `refutes_root_answer` lifts a 017 leaf
  counterexample that names `(z, θ, q(z))` through those same facts.
- [Example](../Gimle/Forseti/Examples/HeatFieldBound.lean): `Solves basis p`
  admits the inputs of Asgard's heat circuit whose boundary port is the full
  profile `p` and whose port `0` the circuit reconstructs; `solves_iff` (024's
  existence and uniqueness) makes port `0` exactly the constructed heat stream,
  and `solution_realized` realizes output port `1` by `Heat.solution p`. For
  `p = a·x² + c`, `field_solution` is `a·x² + c + 2·a·t` (from 024's
  `field_unique`), and `heat_strip_bound` is the strip bound over the circuit,
  in either basis. At `p = x²` on `[0, 1] × [-1, 1]`, `unit_heat_bound_three`
  proves `0 ≤ u ≤ 3` and `unit_heat_bound_two_refuted` refutes `u ≤ 2` at
  `(1, 1)` from the admitted input `[x² + 2t, x², 0]`.
  `Tests/FieldObservation.lean` refutes, at the circuit level, an altered
  profile, a wider domain, a boundary known only on a window, and `u = x` at
  `x = -1`.

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
