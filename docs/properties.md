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
- [`Syntax/AlgebraicWitness.lean`](../Gimle/Forseti/Syntax/AlgebraicWitness.lean)
  refutes goals whose only counterexamples are irrational, such as
  `x² = 2 ⊨ x < 0`. An `AlgebraicWitness` is a box of rational intervals, one
  per coordinate, each with a univariate polynomial, and evidence for each atom:
  - `Root.check` requires an ordered interval, a sign change across it and an
    interval enclosure of the derivative that excludes zero. The intermediate
    value theorem gives a root (`Root.exists_zero`), and the derivative's fixed
    sign makes it the only one (`Root.root_unique`). A wrong interval, an
    interval with several roots and a repeated root are rejected. A rational
    coordinate `q` is `x − q` on `[q, q]`.
  - Each atom is decided for every point of the box: by a sound interval
    `enclose`ure of its polynomial that excludes zero (a strict sign), or, for
    a zero, by a checked identity `q = Σᵢ sᵢ · pᵢ(xᵢ)`. Nothing the producer
    says about signs is used.
  - `algebraicRefutes_sound` proves `¬ P ⊨ Q` from a check that passes.
    [Examples/AlgebraicCounterexamples.lean](../Gimle/Forseti/Examples/AlgebraicCounterexamples.lean)
    refutes goals at `±√2`, at `(√2, √3)`, at a point with one rational
    coordinate, and with a consequent that is exactly zero at the point;
    `Tests/AlgebraicWitness.lean` holds the hostile witnesses.
- [`Syntax/Positivstellensatz.lean`](../Gimle/Forseti/Syntax/Positivstellensatz.lean)
  widens the certificate to a degree-2 Positivstellensatz. A
  `PsatzCertificate` names pairs `(i, j)` of antecedent constraints and gives
  ordinary rows against the antecedent augmented with `−(pᵢ · pⱼ) ≤ 0`:
  - `augment_nonpositive` is the only new fact: a product of two nonpositive
    reals is nonnegative, so every derived constraint holds where the
    antecedent does. A pair out of range reads the constant `0` and only
    weakens the certificate.
  - `PsatzCertificate.sound` proves `P ⊨ Q` from a check that passes, by 017's
    `Row.check_sound` over the augmented list.
  - `check_ofCertificate`: a 017 certificate is a Psatz certificate with no
    pairs, and the two checks agree, so existing evidence keeps its meaning.
  - [Examples/PositivstellensatzCertificates.lean](../Gimle/Forseti/Examples/PositivstellensatzCertificates.lean)
    proves three goals: `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0`, `x ≥ 1 ∧ y ≥ 1 ⊨ x·y ≥ 1`
    (neither has a quadratic-module certificate), and `x² ≤ 1 ∧ y² ≤ 1 ⊨
    x·y ≤ 1` by the off-diagonal square `(x − y)²`.
    `Tests/Positivstellensatz.lean` holds the hostile certificates: a dropped
    product, an out-of-range pair, a negative weight, a wrong identity, a wrong
    multiplier count, a false goal and a strict goal.
  - The format was selected by gimle-forseti 034's comparison of solver proof
    logs, exact quantifier elimination and widened certificates. Products of
    three or more constraints, and strict goals, are outside it.
- No general entailment solver, CAD/SMT proof-log checker or serializer is
  supplied; producers live outside this repository.

## Trajectory contracts

Properties of continuous feedback circuits over forward time — `Contract`,
`Always`, `Initialized` and their rules — are in
[Dynamics and safety certificates](dynamics.md#trajectory-contracts). Two
undriven compiled models carry a whole-system contract there:
[`Examples/ThreeStateContract.lean`](../Gimle/Forseti/Examples/ThreeStateContract.lean)
(`0 ≤ V ≤ 6` for `t ≥ 2`) and
[`Examples/DampedOscillatorContract.lean`](../Gimle/Forseti/Examples/DampedOscillatorContract.lean),
the damped oscillator compiled from source equations with a declared velocity
(`0 ≤ 2x² + v² ≤ 2` for `t ≥ 0`, the bound 1 refuted). One driven model does
too:
[`Examples/ForcedDecayContract.lean`](../Gimle/Forseti/Examples/ForcedDecayContract.lean),
`x' + x = u' + u` with a declared driver `u` (`|x| ≤ 2` for `t ≥ 0` under the
driver precondition `|u| ≤ 1`, never `True`).

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

## Fourier-stream contracts

[`Fourier.Contract`](../Gimle/Forseti/Fourier.lean) is a total Hoare contract
for Asgard's `Streams.Fourier.Circuit`. Wires carry whole formal time series
of Fourier polynomials. It requires an output for every admitted input,
uniqueness of that output, and the postcondition for every related output.
`Contract.consequence` and `Contract.compose` provide the usual predicate
transport and sequential composition rules. An arbitrary feedback circuit
receives no unconditional existence or uniqueness rule.

`solution_contract` uses Asgard's proved feedback semantics: for any rational
viscosity and either OGF or EGF, fixing the boundary's degree-zero slice fixes
the circuit output to `NS.stream`. The precondition does not provide a solution
or constrain the boundary's higher coefficients.

[`Euler.contract`](../Gimle/Forseti/Euler.lean) lifts the analytical results to
any initial Fourier polynomial. Its premises are mean zero, evenness, finite
support, a geometric coefficient bound `M ρⁿ`, `ρ > 0`, `r ≥ 0` and `ρr < 1`.
The sole input condition remains `input 0 0 = boundary 0`. Every actual output
satisfies `Euler.Certified boundary r`: equality to the complete formal solution,
mean-zero/even coefficients, the prescribed initial field, convergence, and the
classical Euler equation with all named derivatives and continuity on the closed
interval `|t| ≤ r`. The strict inequality `ρr < 1` includes both requested
endpoints inside the theorem's open convergence disc. The certificate constants
`K`, `M` and `ρ` do not occur in the postcondition.

`Euler.contract_with` conjoins any additional proved output property, such as a
truncation error or band, with this classical guarantee. `Euler.Table.contract`
discharges the semantic premises from finite mode/coefficient data, checking
zero mean and parity on aggregate coefficients so duplicate entries and exact
cancellation are handled correctly. `Euler.Table.zero_contract` uses a zero norm
bound at an arbitrary positive growth rate and covers every finite nonnegative
radius. It does not grant an arbitrary band or error tolerance: such a property
still needs its own proof. [Regression proofs](../Gimle/Forseti/Tests/GenericEuler.lean)
cover a different multimode start, zero data, both endpoints, unconstrained higher
boundary coefficients, and altered input/circuit claims.

[`Examples.EulerContract.euler_contract`](../Gimle/Forseti/Examples/EulerContract.lean)
applies this to the three-mode initial vorticity at zero viscosity. Its
postcondition identifies the whole output and proves mean-zero/even coefficients,
truncation error `1/100` through degree two on `|t| ≤ 1/6480`, the `1/50` band
around the initial field there, and the classical Euler vorticity equation on
`|t| < 1/648`. The analytic results are transported from Asgard's existing
proofs using equality of the circuit output, not repeated in Forseti.

Uniqueness here is of the formal stream. It does not assert uniqueness among
arbitrary classical fields, global-time behavior, or convergence of the viscous
time series. Building this optional module does not enroll it in an external
checker's import allowlist or update the Python application's pinned release.

## Mild vorticity circuit contracts

[`Mild.Contract`](../Gimle/Forseti/Mild.lean) follows the same total relational
contract pattern as the Fourier adapter: existence for every admitted input,
uniqueness of its whole output, and a postcondition for every related output.
Its consequence and sequential composition rules preserve all three. A missing
feedback solution cannot certify a false postcondition.

[`MildVorticity.contract`](../Gimle/Forseti/MildVorticity.lean) admits precisely
inputs whose initial slice is the embedded finite Fourier profile `P`.
Higher boundary slices are unrestricted. Its `Certified ν P T output` binds
all conclusions to that output: equality to the entire Wild stream, evenness,
mean zero, the initial field, absolute convergence on `[0,T]`, reconstruction
from the summed Fourier coefficients, classical realization and spectral
dissipation. Numerical parameters are proof premises, never part of admission.

The classical time derivative and PDE hold on `(0,T)`. The initial time has a
right derivative for `T>0`; spatial regularity and all required continuity
hold on `[0,T]`. Spectral quantities use `Z=ΣW_k²`, `E=ΣW_k²/|k|²`, with zero
inverse weight at the mean mode and no factor of one half. They satisfy
`Z'=-2νΣ|k|²W_k²`, `E'=-2νZ` and are nonincreasing on the closed interval.

`Table.euler_contract` and `Table.catalan_contract` prove the same certified
postcondition using the two physical bounds. `Table.zero_contract` accepts
aggregate cancellation, including the mean mode, at any nonnegative finite
horizon and viscosity. Finite symmetry and zero-mean certificates are reused
from `Euler.Table`. Zero viscosity uses the Euler-scale route; the Catalan
route explicitly requires positive viscosity. Both require strict geometric
convergence. `contract_with` conjoins a truncation or band with the full
`Certified` property, so a band never silently drops convergence or the PDE.

[Regression proofs](../Gimle/Forseti/Tests/MildVorticity.lean) reject a wrong
initial slice and replacement of feedback by a wire, prove nonvacuous total
existence with arbitrary higher boundary data, and cover both numerical
conjunctions, zero data, zero viscosity and closed endpoints. No uniqueness
among arbitrary classical fields, continuation or inviscid-limit result is
asserted. Consumers must enroll the new imports and the audited release pair
before these declarations are available to foreign-candidate checking.


## Independent classical vorticity fields

[`ClassicalVorticity.Solves`](../Gimle/Forseti/ClassicalVorticity.lean) describes
ordinary scalar fields and a periodic stream function on a closed time strip.
It records spatial derivative witnesses, joint continuity, the vorticity PDE,
and initial data. Time derivatives and the PDE are required only in the
interior. Velocity is `(-ψ_y, ψ_x)`; a spatially constant, continuous time-dependent gauge
may be added to `ψ`. Competing fields need not have even symmetry or a stream
representation.

`of_mild` puts every existing `IsMildClassicalSolution` in this independent
class, proving periodicity directly from the integer Fourier modes.
`Solves.difference_equation` subtracts two independent PDEs. The separate
[`Comparison`](../Gimle/Forseti/ClassicalVorticity/Comparison.lean) module proves
`D(t) ≤ exp(C*t)*D(0)` from the explicit premise `D' ≤ C*D`, with continuity on
`[0,T]` and derivatives only on `(0,T)`. Nonnegative `D` with zero initial value
then vanishes, including at both endpoints. These are conditional scalar
lemmas, not a classical PDE uniqueness theorem.

[`PeriodicCalculus`](../Gimle/Forseti/ClassicalVorticity/PeriodicCalculus.lean)
proves one-dimensional periodic integration by parts and the nonpositive
viscous pairing. The two-dimensional energy difference estimate, differentiation under its
integral, periodic elliptic norm estimate, and passage from zero square
integral to pointwise equality remain unproved (task 048). Consequently the notebook's
bounds have not been transferred to arbitrary classical solutions.

[Regressions](../Gimle/Forseti/Tests/ClassicalVorticity.lean) include the mild
membership bridge, an odd sine Euler solution, a continuous stream-function
gauge with a time corner, refusal of wrong initial data, the closed upper
endpoint, a collapsed time interval, and the viscous sign on a sine profile.
