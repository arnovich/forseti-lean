# AIF mesh composition and startup membership

[`AIFMeshComposition.lean`](../Gimle/Forseti/Examples/AIFMeshComposition.lean)
composes the [local invariance theorem](aif-local-invariance.md) across a finite
time mesh for one fixed parameter bin.

`chain_invariant` proves propagation for a finite family of scalar energies. It
requires ordered endpoints, a local rule on every interval, agreement between
adjacent energies at their common endpoint, and one initial bound. Finite
induction uses the previous interval's closed right-endpoint bound as the next
interval's initial bound.

`mesh_invariant_of_local` supplies endpoint compatibility from the shared mesh
nodes. `mesh_invariant` supplies each local rule from the checked in-tube drift
interface and the component ODE derivatives of a supplied solution. The bound
holds for every interval, with no assumed trajectory membership beyond the one
initial premise. `covered_energy` combines this with finite interval coverage,
including the last endpoint of the mesh span.

Every local drift obligation remains explicit and is quantified over the entire
finite index type. Missing cells cannot be replaced by a partial list of checked
examples. This theorem does not prove ODE existence, output containment, or the
original typed-circuit relation.

`initial_energy_of_centers` proves exact zero energy whenever the supplied initial
state equals both rational center endpoints. It is independent of metric
positivity and the parameter value.

[`Tests/AIFMeshComposition.lean`](../Gimle/Forseti/Tests/AIFMeshComposition.lean)
checks a one-interval chain, a two-interval shared-node mesh, coverage of the last
closed endpoint, and exact zero initial energy. A counterexample shows that local
rules and first-interval membership are insufficient if energy equality at a join
is omitted.

The generated `AIFStartupInitial` module checks the saved candidate itself:
`time_zero` proves the first mesh time is zero, `centers_initial` checks both
initial centers in every one of the eight bins, and `initial_energy` proves
exactly zero tube energy for `(-2,-2,-2,-1)` at every parameter value. Its artifact
is 47,472 bytes. The coordinate transformation from the original zero state is
not established by these theorems and must still be bound to the typed circuit.

Evidence under `.lake/aif_mesh_composition/` retains `initial.py`, the generated
source, setup, logs, artifact, prerequisite records and checking-environment
fingerprint. The archived mesh verification and binding-stage environment anchor
all ten foundation artifacts. The new initial-state proof imports that mesh and
the checked composition module; complete environment hashes are rechecked.

Initial membership is separate from local drift coverage. The existing counts
remain 30 drift cells, 22 conditional coordinate-containment results, 22 mesh
transports and sixteen interior local-invariance applications. The concurrent
startup-prefix replay is not included in these historical counts until its own
batch audit succeeds.

Validation passed: the full Lean build (749 axiom reports), optional
`equation_demo` build (63 reports), all 57 Python tests, build-path and suspension
checks. The ten direct reports cover five implementation lemmas, two named
regressions and three concrete startup-membership lemmas. Only the standard
axioms `propext`, `Classical.choice` and `Quot.sound` occur. The mathematical,
integration and evidence review panel found no blockers after the final audit
linked every imported foundation artifact to the archived mesh evidence and
recomputed the checking environment. This checkpoint's verification SHA-256 is
`0e43b2b8ee869564a4ded0a595cfb8cd14a841606a873ccc7145f314a3804f44`.
