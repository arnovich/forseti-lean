# Forseti Lean

Lean 4 proofs about [Asgard](https://github.com/arnovich/asgard-lean) circuits:
predicates, Hoare rules, approximation, and continuous/discrete safety.

Public showcase, licensed under [MIT](LICENSE). External pull requests are not accepted.

## Build

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build
```

Lean, Asgard, and mathlib are pinned. The build checks the library, examples,
regression proofs, and checker. No Python or private repository access is needed.

## Explore

Open an example in VS Code with the Lean 4 extension:

| Example | What it proves |
| --- | --- |
| [Energy](Gimle/Forseti/Examples/EnergyDemo.lean) | Sharp bounds for an exact circuit |
| [Compiled equations](Gimle/Forseti/Examples/EquationWorkflow.lean) | Properties of the same circuits produced by Asgard's equation compiler |
| [Three-state model](Gimle/Forseti/Examples/ThreeState.lean) | Forward existence, uniqueness, and the compiled energy bound `0 ≤ V ≤ 6` |
| [Damped oscillator](Gimle/Forseti/Examples/DampedOscillatorContract.lean) | A trajectory contract for `x'' + 3x' + 2x = 0` compiled from source equations with a declared velocity: `0 ≤ 2x² + v² ≤ 2` for `t ≥ 0`, from an exact energy certificate |
| [Forced decay](Gimle/Forseti/Examples/ForcedDecayContract.lean) | A trajectory contract for a driven model, `x' + x = u' + u` with `x(0) = 0`, compiled from source equations with a declared driver: `|x| ≤ 2` for `t ≥ 0` under the driver precondition (admitted, `|u| ≤ 1`), never `True` |
| [Harmonic oscillator](Gimle/Forseti/Examples/HarmonicOscillator.lean) | `4x'' + x = 0` with its conserved energy `x² + 4v²` in `[0, 1]`, contracted only through the generic `LinearEnergyContract` construction |
| [Lorenz](Gimle/Forseti/Examples/Lorenz.lean) | The first nonlinear trajectory contract: Lorenz's system with `σ = 10, ρ = 28, β = 8/3` from `(1, 1, 1)` stays in `V = x² + y² + (z − 38)² ≤ 1600` for `t ≥ 0`; one instance of [`Nonlinear.lean`](Gimle/Forseti/Nonlinear.lean), the general trapping theorem for any compiled polynomial field (existence for all time by a clamped Picard–Lindelöf argument glued on `[t₀, t₀ + n]` and fenced by the invariant, uniqueness on the compact box) |
| [Disturbed feedback](Gimle/Forseti/Examples/DisturbedFeedback.lean) | Component storage identities compose through a trace to prove `\|x(t)\| ≤ 1` under continuous disturbances bounded by one |
| [Active suspension](Gimle/Forseti/Examples/ActiveSuspension.lean) | A searched invariant proves travel, force and acceleration bounds through nested traces, shared by two actuator implementations |
| [Approximation](Gimle/Forseti/Examples/CircuitApproximation.lean) | Property transport with an explicit certified error |
| [Certificate checking](Gimle/Forseti/Examples/ProofSearchContract.lean) | Exact validity conditions for proposed linear-energy certificates |
| [Stream observations](Gimle/Forseti/Examples/StreamObservation.lean) | Polynomial certificates lifted to total contracts over Asgard's formal heat circuit |
| [Heat field bound](Gimle/Forseti/Examples/HeatFieldBound.lean) | Bounds on the evaluated real field of the heat circuit's output, proved and refuted |
| [Algebraic counterexamples](Gimle/Forseti/Examples/AlgebraicCounterexamples.lean) | Entailments refuted only at irrational points, such as `x² = 2 ⊨ x < 0` at `√2` |
| [Positivstellensatz certificates](Gimle/Forseti/Examples/PositivstellensatzCertificates.lean) | Entailments that need a product of constraints, such as `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0`, checked by `PsatzCertificate` |

Check one directly with `lake env lean Gimle/Forseti/Examples/EnergyDemo.lean`.

## Guides

- [Predicates and Hoare rules](docs/properties.md)
- [Dynamics and safety certificates](docs/dynamics.md)
- [Active suspension and exact invariant search](docs/active-suspension.md)
- [Finite linear output equivalence](docs/finite-linear-equivalence.md)
- [Compiled linear circuits and Hoare invariants](docs/linear-circuit-equivalence.md)
- [Standalone proof checker](docs/checker.md)

Optional numerical demo: `lake build equation_demo`, then
`lake exe equation_demo /absolute/venv/bin/python`. It requires a separately
supplied Asgard Python worker; see [worker setup](https://github.com/arnovich/asgard-lean/blob/0f828828b94e1e89c68cbdeca89009297f3bd8a9/docs/simulation.md).
Its output is numerical observations, not proof evidence.
