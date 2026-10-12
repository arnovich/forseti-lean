# AIF circuit transport

The research generator `tools/aif_circuit_transport.py` connects the original
compiled Asgard AIF feedback to Forseti's shifted-coordinate and moving-energy
proofs. Its six Lean theorems refer to the actual compiled circuit and its
`Realizes` relation. They establish field equality, physical ODE semantics,
shifted zero initialization, derivatives on closed time intervals, the tube-energy
derivative, and equivalence of the physical x2 threshold with the shifted bound.

Every trajectory statement assumes a realization of the circuit. This checkpoint
does not prove existence, uniqueness, nonnegativity, complete startup coverage,
or the output bound itself.

## Source and checking context

The checked research binding uses these committed prerequisites:

- Asgard `87e5389120f910dc813680e7b30ca4e23b1fb923`: named biochemical source,
  compiled field, zero-initialized feedback, and physical x2 observation.
- Forseti `a0e7ca3bfed6ab0680357975fa999f9624438d75`: physical/shifted coordinates
  and derivative transport.

Forseti's production dependency pin predates the Asgard AIF module. Therefore the
binding is emitted under `.lake` and checked with an explicit import map. This
checkpoint does not change that pin or add the experiment to the default checker.
The archived runner verifies prerequisite source and artifact hashes, checks that
shared imports from both worktrees have identical bytes, and fingerprints the
complete compiler/import context before and after checking. Each of the six
axiom reports is restricted to Lean's standard axioms.

Generate the source with:

```sh
python3 tools/aif_circuit_transport.py --output-directory .lake/aif_circuit_transport
```

Add `--check` to compare existing source without creating or modifying files.
Generation alone provides no proof authority. Replaying the checked experiment
also requires the two prerequisite archives and their matching import artifacts;
the Task #248 `circuit-transport` evidence archive contains the runner, setup,
source, logs, artifact hashes, and verification records for that replay.

## Remaining work

The startup certificate still needs complete cell coverage and output enclosure.
The trajectory must also be constructed and shown unique and nonnegative, and
startup invariance must be connected to the terminal/local continuation proof.
The circuit transport supplies the correct trajectory interface for those steps.
