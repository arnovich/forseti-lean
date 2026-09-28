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
