# Dynamics and safety

These modules extend the property library; they are separate from the
[checker's admitted import interface](checker.md).

## Continuous linear energy

[`LinearEnergy.lean`](../Gimle/Forseti/LinearEnergy.lean) handles homogeneous
linear systems with exact rational matrices:

```text
x' = A x       V(x) = xᵀ P x       D = −(AᵀP + PA)
```

- A certificate gives nonnegative rational weighted-square decompositions of `P` and `D`.
- `Certificate.Valid` checks every matrix entry against the recomputed targets.
- `certificate_sound` connects the original RHS/energy circuits to these matrices
  through explicit equalities, then proves existence, forward uniqueness, and sublevel safety.
- Initial energy at most `b` implies `0 ≤ V(t) ≤ b` for every realization on `t ≥ start`.
- Semidefinite energy need not bound the state norm or prove asymptotic stability.
  Nonlinear fields, forcing, and switching are outside this result.

[ThreeState.lean](../Gimle/Forseti/Examples/ThreeState.lean) uses Asgard's compiled
model with damping `(1/3,1/2,2)`, initial state `(1,2,-1)`, and start `2`.
`compiled_energy_bound` proves the fourth compiled observation stays in `[0,6]`
for every exact realization and `t ≥ 2`. Bound `5` fails at the initial state.
The bound comes from one `LinearEnergy.Certificate`: `P = I` as three unit
squares, and its dissipation `diag(2a, 2b, 2c)` as weighted unit squares, valid
for any nonnegative `(a, b, c)` (`certificate_valid`). The generic
`energy_bound` applies it to any such triple; `spec` applies it at the compiled
`(1/3, 1/2, 2)`.

[ProofSearchContract.lean](../Gimle/Forseti/Examples/ProofSearchContract.lean)
shows proposed certificate data checked by exact arithmetic and soundness theorems.
Search itself and numerical simulation supply no authority.

## Trajectory contracts

[`Trajectory.lean`](../Gimle/Forseti/Trajectory.lean) states properties of
Asgard's relational continuous circuits (`Dynamics.Circuit.Rel`) over the
forward time domain. A `Contract circuit time pre post` is three separate,
checked obligations for every admitted input: an output exists (`Realizable`),
all outputs agree on the domain (`Unique`), and **every** output satisfies the
postcondition (`Holds`). `Holds` alone is the partial contract: it is true of a
circuit with no behaviour, so it is never a system theorem on its own.

| Rule | Premises | Gives |
| --- | --- | --- |
| `Contract.consequence` | a contract; stronger pre, weaker post | the weakened contract |
| `Contract.transport` | `Dynamics.Equivalent` circuits | the same contract |
| `Contract.lift` | an exact real `ExactHoare` | pointwise `Always` contract for `lift` only |
| `Contract.compose` | two contracts, the second `DomainRespecting` | the composite |
| `Contract.parallel` | two contracts, same clock | the product on owned ports |
| `Contract.linear` | a `Linear.Problem` | existence, uniqueness, source solutions |
| `Contract.energy` | `LinearEnergy.certificate_sound`'s premises | sublevel safety for all forward time |
| `LinearEnergyContract.Spec.energy_contract` | a compiled model's `LinearView`, an observation computing `xᵀPx`, a valid certificate, `β ≥` the initial energy | the observed contract in `ThreeStateContract`'s shape |

`Always` observes a state predicate at every forward time and `At` at one time;
all-forward safety implies the endpoint, not conversely. `Initialized` inputs
constrain initial wires only at the start, which is all a closed loop reads
(`close_rel_reads_start`). Sequential composition needs the second stage to be
`DomainRespecting`, because the first stage's outputs are unique only on the
domain; `lift` is. No rule gives a `trace` an *unconditional* contract:
feedback can have no solution or many, and `Tests/Trajectory.lean` shows one
with every signal as output. Only loop-specific premises, such as linear
well-posedness or an energy certificate, give a loop a contract.

[`Examples/ThreeStateContract.lean`](../Gimle/Forseti/Examples/ThreeStateContract.lean)
packages the compiled three-state loop and its observation circuit into one
contract: for the declared initial state, `0 ≤ V ≤ 6` at every `t ≥ 2`; the bound
5 is refuted by the admitted initial state (`five_refuted`). Its parameters
`(1/3, 1/2, 2)` are compiled into the model, not bound by the input predicate,
which constrains only the drivers and initial wires. Every piece is
`LinearEnergyContract` (below) applied to `ThreeState.spec`;
`Tests/ThreeState.lean` pins the names and statements gimle-forseti's trajectory
registry cites.

[`Examples/DampedOscillatorContract.lean`](../Gimle/Forseti/Examples/DampedOscillatorContract.lean)
does the same for a model compiled from **source** equations: the damped
oscillator `x'' + 3x' + 2x = 0` with the declared velocity `dx : D_t(x) = v`,
compiled by asgard-lean's `compileSourceContinuous`
([`Examples/DampedOscillator.lean`](../Gimle/Forseti/Examples/DampedOscillator.lean)).
Its source body adds the observations `x`, `v` and the assignment
`E := 2*x^2 + v^2` (ports `obs-x`, `obs-v`, `obs-e`). `E` is bounded by
`LinearEnergy.certificate_energy_bound` with the exact certificate
`P = diag(2, 1)` as `2·e₀² + e₁²` and its dissipation `diag(0, 6)` as `6·e₁²`:
from `x(0) = 1`, `v(0) = 0`, `0 ≤ E ≤ 2` at every `t ≥ 0` (`energy_contract`),
and the bound 1 is refuted by the admitted initial state (`one_refuted`).

[`Examples/ForcedDecayContract.lean`](../Gimle/Forseti/Examples/ForcedDecayContract.lean)
is the first contract for a **driven** model: `x' + x = u' + u`, `x(0) = 0`,
with `u` a declared driver whose port `du` must carry its derivative, compiled
by `compileSourceDriven`
([`Examples/ForcedDecay.lean`](../Gimle/Forseti/Examples/ForcedDecay.lean);
`same_source` ties it to asgard-lean's `DrivenForcing`). A driven observation
reads `[drivers, state]`, so the observed circuit forwards the driver wires
beside the feedback ([`Driven.lean`](../Gimle/Forseti/Driven.lean),
`forwarded_rel`). The precondition binds the drivers — `Evolution.Admitted` and
`|u| ≤ B` — and the initial wire; it is never `True`. The unique output is
`u(t) − u(0)·e^(−t)`, so `|x| ≤ 2B` for `t ≥ 0` (`contract_within`,
`driven_contract` at `B = 1`). The bound 1 is refuted under `u = cos`
(`one_refuted`), and dropping the driver bound refutes 2 under `u = 3`
(`bound_needed`). `feedback_reads` equates the relation with asgard's
`DrivenModel.Realizes`.

[`Examples/Lorenz.lean`](../Gimle/Forseti/Examples/Lorenz.lean) is the first
contract whose field has **no linear view**: Lorenz's `x' = σ(y − x)`,
`y' = x(ρ − z) − y`, `z' = xy − βz` with `σ = 10, ρ = 28, β = 8/3`, from
`(1, 1, 1)` at `t = 0`, observing `V = x² + y² + (z − σ − ρ)²`. Along every
solution `V' = −2σx² − 2y² − 2βz² + 2β(σ+ρ)z`, so `V' + 2V ≤ 2·1541` at every
state (`storage_bound`; the least such constant is `23104/15`), and the
integrating factor `e^{2t}(V − 1600)` is non-increasing from `V(0) = 1371`
(`storage_bound`). Everything else is
[`Nonlinear.lean`](../Gimle/Forseti/Nonlinear.lean), the **general trapping
theorem**: for any compiled model — every compiled field is a polynomial, hence
`C¹` (`contDiff_eval`) — and any weighted sum of squares `V = Σ wᵢ(xᵢ − cᵢ)²`
with `V' ≤ α(C' − V)` at every state, `C' < C`, and a sup-norm radius about the
centre covering `{V ≤ C}` (a `Trapping`), a realization from any start with
`V ≤ C` exists for all forward time, is unique, and keeps `V ≤ C`. Existence is
by hand, since Mathlib's Picard–Lindelöf is local: the field clamped
coordinatewise to the box is bounded and globally Lipschitz
(`clamped_lipschitz`); Picard–Lindelöf gives a solution on every
`[t₀, t₀ + n]` (`clamped_solution_on`); they are glued by uniqueness
(`piece_agree`, `glued_deriv`); Mathlib's fencing lemma keeps the glued
solution in `{V ≤ C}`, where the clamp is the identity, because at a contact
point `V' ≤ α(C' − C) < 0` (`glued_energy_le`); so it solves the true field
(`exists_solution`). Uniqueness is `ODE_solution_unique_of_mem_Icc_right` on the
compact box, with membership from the invariant (`unique`). `energy_contract`
and `refuted` deliver the observed contract and the refutation of a bound below
the initial value in the registry's interface shape. Lorenz supplies its
`trapping` (weights `1`, centre `(0, 0, 38)`, `α = 2`, `C' = 1541`, `C = 1600`,
radius `40`), `decrease` and `initial_le`, and gets `compiled_exists`,
`compiled_unique`, `energy_contract` (`0 ≤ V ≤ 1600`) and
`thirteen_hundred_refuted`; `Tests/Lorenz.lean` and `Tests/Nonlinear.lean` pin
the names.

**Decrease local to the set**
([`LocalTrapping.lean`](../Gimle/Forseti/LocalTrapping.lean)). The global
hypothesis `V' ≤ α(C' − V)` at *every* state has a cost: at an equilibrium the
rate is zero, so `V(x*) ≤ C'`, and every set a `Trapping` can trap contains
every equilibrium of the field — for the Galerkin members the laminar point,
so no level below the laminar energy is reachable. A `LocalTrapping` takes a
general quadratic `V = (x − c)ᵀP(x − c)`, `P` symmetric with `P ≽ lower · I`
(`coercive`), and asks the decrease only on the set: `∀ x, V x ≤ C → V' x ≤
α(C' − V x)` (`Decreases`). Invariance is Mathlib's barrier lemma rather than
the integrating factor: at a first contact `V = C` the rate is `≤ α(C' − C) <
0` (`invariant`). Existence and uniqueness reuse the clamped field through the
diagonal ball `lower · Σ(xᵢ − cᵢ)²`, which the quadratic dominates
(`ball_energy_le`), so `{V ≤ C}` lies in that ball's box and the glued solution
is fenced as before (`glued_energy_le`, `exists_solution`, `unique`);
`local_bounded_contract` lifts any bound every realization keeps to the
observed contract. The decrease on the set is what a sum-of-squares certificate
with an S-procedure multiplier states: `α(C' − V) − V' + σ(V − C) ≥ 0`
everywhere with `σ ≥ 0`. The instance is
[`GalerkinNS/T3Below12.lean`](../Gimle/Forseti/Examples/GalerkinNS/T3Below12.lean):
for the 3-mode member at `ν = 1/10`, an ellipsoid with cross terms and a centre
near the equilibrium the start approaches in simulation (gimle-forseti's spike
196; not a Lean statement), on which the
decrease holds by an explicit degree-4 sum of squares (`certificate_sos`), and
which lies in `{E ≤ 12}` by an S-lemma certificate (`contained`); the contract
`below12_contract` states `0 ≤ E ≤ 12` for all time, below the laminar `25/2`
and the family bound `13`. The laminar point `(0, 5, 0)` has `V = 2.54 > 1` for
that ellipsoid's `V`, so it lies outside the set (`laminar_equilibrium`,
`laminar_outside`); `Tests/LocalTrapping.lean` pins the shape and the data.

**A polynomial `V`**
([`PolynomialTrapping.lean`](../Gimle/Forseti/PolynomialTrapping.lean)). The
5-mode member's below-laminar set (gimle-forseti's spike 213) is a sublevel set
of a degree-4 polynomial, a thin tube around the member's attractor, which in
simulation is a rotating wave of energy about `4.75`; no quadratic form about a
centre was found for it (spike 213). A `PolynomialTrapping` takes `V` as a polynomial
expression (`Gimle.Asgard.Polynomial.Expr`), differentiates it symbolically
(`Expr.diff`, with the chain rule `Expr.eval_hasDerivWithinAt` along any
differentiable signal), asks the decrease on the set as before, and places
`{V ≤ C}` in a sup-norm box by a checkable hypothesis (`boxed`), which for the
tube follows from its containment in `{E ≤ 6}`. Invariance, existence,
uniqueness and `poly_bounded_contract` are as for `LocalTrapping`, through a
`Trapping` of that radius whose only job is the box. The instance is
[`GalerkinNS/K5Below6.lean`](../Gimle/Forseti/Examples/GalerkinNS/K5Below6.lean):
`below6_contract` states `0 ≤ E ≤ 6` for all time from `(1, …, 1)`, the level of
the member's standing undecided claim, below the laminar `25/2` and the family
bound `13`. Its decrease certificate is a degree-6 sum of squares written as the
columns of a rounded Cholesky factor of the Gram matrix less `εI` with the exact
remainder absorbed pair by pair, since an exact `LDLᵀ` of a 56×56 matrix has
thousand-digit entries; `V'` is tied to the written-out partials and the field.
`Tests/PolynomialTrapping.lean` pins the shape, the derivative and the data.
The 3-mode member has the same kind of set
([`GalerkinNS/T3Below9.lean`](../Gimle/Forseti/Examples/GalerkinNS/T3Below9.lean)):
a degree-4 tube around the focus the start approaches in simulation, inside
`{E ≤ 9}`, so `below9_contract` states `0 ≤ E ≤ 9` for all time from
`(1, 1, 1)`, below the ellipsoid's `12` and the laminar `25/2`; the member's
standing undecided claim was `E ≤ 10`.

[`Examples/GalerkinNS/`](../Gimle/Forseti/Examples/GalerkinNS/) applies the
general theorem to a family: Galerkin truncations of 2D incompressible
Navier–Stokes on the 2π-periodic square, vorticity form, cosine modes only,
forced in the single mode `cos(x + y)`, with rational `ν` and `f`. A member is
a finite set of integer wavevectors `K`; with `ω = Σ a_k cos(k·x)` and
`λ_k = |k|²` the projected equations are `a_k' = −νλ_k a_k + f[k = (1,1)] +
Σ C_k a_P a_Q` over **triads** `P + Q + R = 0`, each three rational monomials
with `C_P = (σ/2)(1/λ_R − 1/λ_Q)` and cyclically, `σ = P × Q`. Every triad
conserves the energy `E = Σ a_k²/λ_k` and the enstrophy `Z = Σ a_k²`
(`triad_i`: its weighted flows sum to zero), so per-mode storage identities
(`storage_k`) sum to `E' = −2νZ + f a₍₁,₁₎` (`energy_identity`), and at every
state `2ν(f²/(8ν²) − E) − E' = ν(a₍₁,₁₎ − f/(2ν))² + 2ν Σ (1 − 1/λ_k) a_k²`
(`certificate`, checked by `ring`), which is the `decrease` a `Trapping` needs;
`f²/(8ν²)` is the laminar equilibrium's energy, so no smaller level is
positively invariant (a one-line argument on the laminar line, not a Lean
statement). The members `T3` (3 modes, one triad), `K5` (5 modes,
three triads) and `B2` (12 modes, 22 triads; irregular in simulation at
`ν = 1/50`, step-dependent) are written by [`tools/galerkin_ns.py`](../tools/galerkin_ns.py),
which derives the triads with exact rationals, verifies every identity by
polynomial expansion, and emits the model, the identities and the contract in
the registry's interface shape; `--check` compares without writing, and
`Tests/GalerkinNS.lean` pins the names. Nothing is claimed about the PDE.

[`GalerkinNS/Family.lean`](../Gimle/Forseti/GalerkinNS/Family.lean) proves the
identity, the certificate and the trapping once, for **every member**. The
family is `field ν f k forced` for any `n`, modes `k : Fin n → ℤ × ℤ` and an
index `forced`: `a_i' = −ν λ(k i) a_i + f [i = forced] + Σ_{j,l} c(k j, k l, k i) a_j a_l`
over **ordered** pairs, with the coupling
`c(p, q, k) = (p × q)/(2 λ_p) · ([p − q = ±k] − [p + q = ±k])` (`coefficient`;
the projection `(1/2π²) ∫∫ · cos(k·x)` of `−J(ψ, ω)` with `Δψ = ω`, a paper derivation
checked with sympy against direct integration for `T3` and `K5`, not a Lean
statement), `E = Σ a_i²/λ(k i)` (`energy`) and `Z = Σ a_i²` (`enstrophy`). Under
the hypotheses `∀ i, k i ≠ 0` and `k forced = (1, 1)`, and nothing else:

- `E' = −2νZ + f a_forced` (`energy_identity`): the cubic flux
  `Σ_{i,j,l} (2/λ(k i)) a_i c(k j, k l, k i) a_j a_l` vanishes because exchanging
  the ψ-index `j` and the energy index `i` flips the summand's sign,
  `(k × q) S(k, q, p) = −(p × q) S(p, q, k)` (`energy_antisymm`), so the sum
  equals its own negative by `Finset.sum_comm` (`cubic_flux_zero`);
- `2ν(f²/(8ν²) − E) − E' = ν(a_forced − f/(2ν))² + 2ν Σ_{i ≠ forced} (1 − 1/λ(k i)) a_i²`
  (`certificate`), algebra from the identity with `λ(1, 1) = 2`; its weights are
  nonnegative since `λ ≥ 1` on nonzero modes, so `E' ≤ 2ν(f²/(8ν²) − E)`
  (`decrease_rate`);
- for `ν > 0` and any `C > f²/(8ν²)`, `trapping` (weights `1/λ(k i)`, centre `0`,
  `α = 2ν`, `C' = f²/(8ν²)`, radius `1 + C Σ λ(k i)`, which covers `{E ≤ C}` since
  `C λ_i ≤ C Σ λ ≤ (1 + C Σ λ)²`) satisfies `decrease`, and the field is `C¹` as a
  finite sum of polynomials (`contDiff_field`), so `Nonlinear.lean` gives, from
  any start with `E ≤ C`, a forward solution for all `t ≥ start`, its uniqueness
  and `E ≤ C` along it (`exists_solution`, `unique`, `invariant`; together
  `trapped`).

The derivation assumes the modes are pairwise distinct up to sign, so that
`a_i'` is the coefficient of `cos(k_i·x)`; the half-plane convention only fixes
a representative, and the coupling is even in each argument, so the choice does
not change the field. This is not a hypothesis of any theorem: a duplicated
mode, or a mode and its negative, gives a field the theorems still cover, but
one whose triad terms are doubled relative to the PDE's projection. Each
generated member states `field_eq_family` — its compiled field is the family
field at its modes, the triad coefficients being the ordered-pair coupling
summed over both orders — and derives `decrease_family` from
`Family.decrease_rate` through it, beside its `ring` route.
`Tests/GalerkinNSFamily.lean` applies the theorems to members the generator
does not emit (a 2-mode list and a list with a `±` pair), evaluates the identity
by hand on a real triad, shows the identity fails when the forced mode has
`λ ≠ 2`, and pins the axiom footprint.

The same module proves the **enstrophy** versions for every member, from a
different antisymmetry: exchanging the ω-index `l` and the enstrophy index
`i`, the ψ-index `j` fixed, `(p × q) S(p, q, k) = −(p × k) S(p, k, q)`
(`enstrophy_antisymm`, the discrete `∫ ω J(ψ, ω) = 0`; the weight `1/λ_p` sits on
the fixed index and is untouched), so the cubic enstrophy flux vanishes
(`cubic_enstrophy_flux_zero`) and `Z' = −2νP + 2 f a_forced` with the
palinstrophy `P = Σ λ(k i) a_i²` (`enstrophy_identity`). With `λ ≥ 1` and
`λ(1, 1) = 2`, `2ν(f²/(4ν²) − Z) − Z' = 2ν Σ_{i ≠ forced} (λ(k i) − 1) a_i² + 2ν (a_forced − f/(2ν))²`
(`enstrophy_certificate`), so every ball `Z ≤ C`, `C > f²/(4ν²)`, traps
(`trappingZ`, `trapped_enstrophy`), uniformly in the member, and bounds every
mode by `√C` (`mode_sq_le_enstrophy`). Each generated member exposes `Z` as its
last observation and states `enstrophy_identity`, `certificateZ`,
`decreaseZ_family` and the contract `enstrophy_contract`. Each member also
states `only_two_diagonal`: a weighting for which every triad is lossless, one
hypothesis per triad, is a combination of `1/λ` and `1`, by an exact linear
combination of the triad equations the generator computes; and a member whose
mode set has a reflection symmetry (`K5`, exchanging `(1,0) ↔ (0,1)` and
`(2,1) ↔ (1,2)`) states the further conserved quadratic form that symmetry
gives (`symmetric_invariant_0`), whose flux along the field has no cubic part.
The design study behind these is gimle-forseti's
`docs/galerkin-compositional-invariants-design.md`.

**Forcing small relative to viscosity: the laminar line attracts.** The unforced modes' energy
`E_rest = E − a_forced²/λ(k forced)` (`restEnergy`) loses what the triads
through the forced mode feed it and nothing else: exactly,
`E_rest' = −2ν Z_rest − a_forced N_forced(a)` (`rest_identity`), where
`N_forced` is the forced mode's own cubic term (`forcedCubic`), a quadratic
form in the unforced amplitudes (`forcedCubic_sym`; a mode couples to nothing
through itself, `coefficient_self_left`/`right`). Its symmetric matrix's
absolute entries sum to `K` (`couplingSum`), so `|N_forced| ≤ K Z_rest`
(`abs_forcedCubic_le`), and on the enstrophy ball `Z ≤ r²` with
`γ = 2ν − K r ≥ 0`, `E_rest' ≤ −γ Z_rest ≤ −γ E_rest` (`rest_decrease_rate`,
`restEnergy_le_restEnstrophy`, the second step because `E_rest ≤ Z_rest`).
`Dissipative.decay` (the integrating factor `e^{γt} E_rest` is antitone) gives
`E_rest(t) ≤ E_rest(start) e^{−γ (t − start)}` along every solution that stays
on the ball (`rest_decay`), and with `trapped_enstrophy` the whole statement
`laminar_attracts`: below the threshold `K r < 2ν`, from any start with
`Z ≤ r²`, a solution exists, is unique, keeps `Z ≤ r²` and its unforced energy
decays exponentially — the laminar line attracts, on the whole ball. `K` is the
entrywise sum of the symmetrised coefficients, a loose bound; the threshold is
`f < 4ν²/K` in the forcing, read through `r² > f²/(4ν²)`. The
generated member `T3S` (T3's modes at `ν = 1/2`, `f = 1`; `K = 2/5`, `r = 2`,
`γ = 1/5`) states it (`rest_decays`) and the contract `rest_contract`,
`0 ≤ E_rest ≤ 6/5` for all time, through `Nonlinear.bounded_contract`; every
member exposes `E_rest` as its last observation, and the three at `ν = 1/10`
and `1/50` are above the threshold, where nothing is claimed.

[`LinearEnergyContract.lean`](../Gimle/Forseti/LinearEnergyContract.lean) is
the generic construction behind the oscillator's contract. For any compiled
continuous model, a `Spec` holds:
- its `LinearView`;
- the index of an observation, with a proof that it computes `xᵀPx`;
- a `LinearEnergy.Certificate` checked against the recognized matrix and `P`.

From a `Spec` it derives `feedback_reads`, `declared_input_admitted`,
`energy_bound`, the loop and observed contracts for any `β` at least the initial
energy, and `refuted` for any `β` below it. `ThreeStateContract` and
`DampedOscillatorContract` are this construction applied to `ThreeState.spec`
and `DampedOscillator.spec`.
[`Examples/HarmonicOscillator.lean`](../Gimle/Forseti/Examples/HarmonicOscillator.lean)
is a second model built only from it:
- the undamped `4x'' + x = 0`, from source with a declared velocity;
- its energy `x² + 4v²` is conserved, so the certificate's decrease is the
  empty sum;
- its contract and refutation are two one-line applications of the
  construction;
- what remains is the model's data: the source, `P`, the certificate, and
  reading `E` off the compiled circuit.

PDE, stream and stochastic contracts are specified separately (tasks 018, 020)
and are not checked here.

## A disturbance invariant through trace

[`Examples/DisturbedFeedback.lean`](../Gimle/Forseti/Examples/DisturbedFeedback.lean)
is a hand-proved example of bottom-up reasoning about feedback. Two polynomial
component circuits compute `x' = -x + 2u + d` and `z' = -z - v`. An explicit
routing circuit connects `u = z` and `v = x`; `Dynamics.close` feeds their
outputs through integrators and an actual two-wire trace.

The open components have storage identities

```text
(x²)' = -2x² + 4xu + 2xd
(z²)' = -2z² - 2zv
```

`storage_cancellation` combines the two identities with weights 1 and 2.
After wiring, `V = x² + 2z²` satisfies `V' = -2V + 2xd`. For `|d| ≤ 1`,
`storage_bound` proves `V' ≤ 1 - V`. The derivative of `exp(t)(V(t)-1)`
is therefore nonpositive. Initial `V ≤ 1` implies `V(t) ≤ 1` at every forward
time; the trace proof never assumes the invariant on an arbitrary feedback
signal.

`loop_contract` includes existence and forward uniqueness as well as this
invariant. [`ForcedLinear.lean`](../Gimle/Forseti/ForcedLinear.lean) supplies
existence by variation of constants for a continuous forcing; uniqueness
reduces the difference of two trajectories to Asgard's homogeneous linear
uniqueness theorem. These are analytic helpers for contracts, not new circuit
semantics.

`output_contract` composes the loop theorem with a typed projection to expose
only `x`, proving `|x(t)| ≤ 1`. Its assumptions are explicit: the disturbance
signal is continuous on ℝ and bounded by one on `t ≥ start`, and the initial
state satisfies `x₀² + 2z₀² ≤ 1`. Initial wires are read only at `start` and
uniqueness is only on the forward domain. This is a loop-specific proof, not
an unrestricted trace rule or a treatment of discontinuous disturbances.

The [regressions](../Gimle/Forseti/Tests/DisturbedFeedback.lean) also reject the
unweighted-circle candidate: at `(x,z,d) = (3/5,4/5,1)`, `x²+z²=1` but its
derivative is positive. Rejecting this candidate does not refute the root goal.
The output bound `1/2`, however, is refuted by the admitted initial state `(1,0)`.

The weights are supplied in this baseline, not discovered by an agent. A later
search experiment can withhold the invariant, start from `(1,0)`, propose exact
storage weights and replay a concrete proof. Building this example does not
enroll it in the standalone checker's import interface or change Python
Forseti's release pins.

## A discovered invariant for nested feedback

For a larger continuous example, [active suspension](active-suspension.md)
combines a mechanical plant, controller and actuator through three traces.
An exact search finds a common quadratic invariant for two actuator response
rates; Lean checks the certificate and proves total travel, force and
acceleration bounds for an independently specified input and initial region.
The outer contract is shared by both implementations.

## Discrete invariants

[`Discrete.lean`](../Gimle/Forseti/Discrete.lean) iterates a circuit with ordered
inputs `[old state, current input, fixed parameters]`. Updates are simultaneous.

- `certificate_sound` combines an admissible-input witness, initialization inside
  an invariant, invariant preservation, and inclusion in the safe set.
- The conclusion includes run existence, uniqueness for fixed inputs, and all-step safety.
- `finite_certificate_sound` distinguishes endpoint safety from safety at every
  step through `N`; uniqueness concerns only that prefix. `N=0` is included.

See [Discrete tests](../Gimle/Forseti/Tests/Discrete.lean) for averaging, swaps,
fixed parameters, and rejected claims. This is unit-delay iteration, not a new
interpretation of Asgard's continuous trace.
