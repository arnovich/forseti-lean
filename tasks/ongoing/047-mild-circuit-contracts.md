---
title: Total contracts for the classical dissipative mild vorticity circuit
state: ongoing
priority: medium
labels: [streams, lean, contracts]
related: ["046"]
claimed_by: codex/fluid_contracts
claimed_at: 2026-10-06T02:12:43Z
branch: feat/mild_circuit_contracts
---

# Total contracts for the classical dissipative mild vorticity circuit

## Context

The owner authorized the full fluid-equation flow through PRs and merges.
Asgard tasks 068–070 supply the typed mild circuit, both physical convergence
bounds, classical realization and infinite energy/enstrophy dissipation.
The property layer must expose these as total contracts of that actual circuit
before Python can certify mild claims. Only the initial boundary slice is
admission; numerical certificate parameters belong in theorem premises.

## Outcome

A Forseti total contract over Asgard's mild circuit certifies the actual whole
output stream, initial field, mean zero, evenness, convergence, classical PDE
and dissipation on the caller's closed forward interval. Conjoining truncation
or band claims preserves that complete guarantee. Finite initial-table
certificates support both bounds and exact-zero data, including zero viscosity
through the Euler-scale bound. Tests reject wrong output/initial bindings and
cover higher boundary noise, endpoints, and total existence. Full builds,
standard-axiom audit, replay-path guard, panel review and CI pass before release.

## Plan

Follow the existing total relational contract pattern with a mild-circuit
adapter. Instantiate solution totality and uniqueness from Asgard, then package
classical and dissipation results for the actual output. Reuse finite Fourier
initial-table certificates from Euler. Export both rational bound constructors
without making solver choices part of admission. Add regressions and docs,
review with three roles, build and publish in dependency order.

## Conversation

Development follows the reviewed Asgard task070 commit while earlier CI runs.
The merge order remains replay repair, generalized Euler consumer, Asgard
mild circuit/bounds/classical releases, then this contract and Python consumers.

## Implementation and validation

`Mild.Contract` supplies total existence, uniqueness, consequence and sequential
composition over Asgard's actual typed circuit relation. `MildVorticity.Certified`
binds the full Wild output, invariants, initial field, absolute convergence,
Fourier reconstruction, classical solution and spectral dissipation to one
postcondition. Both finite-table bound constructors and semantic-zero data are
supported. `contract_with` preserves this guarantee for numerical claims.

Focused regression proofs pass (3443 jobs), including wrong-initial and wire
replacement rejection, nonvacuous existence, higher-boundary noise, both
numerical conjunctions, ν=0, zero data and endpoints. Standard axiom reports
only. Full build passes (3637 jobs), the optional equation demo passes (6811 jobs),
all 18 path-guard tests pass and compiled artifacts contain no checkout paths.
All three panel roles passed; the added exact carrier replay roots were also
reviewed. CI and ordered publication remain pending.
The Asgard development pin is reviewed task070 commit b7664107a3cc12477d6479015b0c5d5220b41813;
publication will follow the ordered upstream merges and release.
