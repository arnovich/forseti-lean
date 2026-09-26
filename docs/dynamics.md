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
which constrains only the drivers and initial wires.

PDE, stream and stochastic contracts are specified separately (tasks 018, 020)
and are not checked here.

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
