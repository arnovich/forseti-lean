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
| [Approximation](Gimle/Forseti/Examples/CircuitApproximation.lean) | Property transport with an explicit certified error |
| [Certificate checking](Gimle/Forseti/Examples/ProofSearchContract.lean) | Exact validity conditions for proposed linear-energy certificates |
| [Stream observations](Gimle/Forseti/Examples/StreamObservation.lean) | Polynomial certificates lifted to total contracts over Asgard's formal heat circuit |

Check one directly with `lake env lean Gimle/Forseti/Examples/EnergyDemo.lean`.

## Guides

- [Predicates and Hoare rules](docs/properties.md)
- [Dynamics and safety certificates](docs/dynamics.md)
- [Standalone proof checker](docs/checker.md)

Optional numerical demo: `lake build equation_demo`, then
`lake exe equation_demo /absolute/venv/bin/python`. It requires a separately
supplied Asgard Python worker; see [worker setup](https://github.com/arnovich/asgard-lean/blob/297215668e9d60fa06188de353a3467c9d1cbce2/docs/simulation.md).
Its output is numerical observations, not proof evidence.
