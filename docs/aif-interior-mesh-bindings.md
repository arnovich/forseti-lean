# AIF interior drift on the global mesh

This increment binds the [sixteen interior containment results](aif-interior-containment.md)
to the existing complete startup mesh: all eight parameter bins at interval
indices 200 and 300, physical times `[13,13.1]` and `[23,23.1]`.

Each new binding proves equality of the entire mesh-derived `Slab` with the
imported polynomial drift module's slab using `decide +kernel`. This checks the
time and parameter endpoints, both center families, metrics and physical slopes.
The theorem then rewrites its premises and conclusion with that equality and
applies the imported `drift_bound_in_tube`. The resulting `drift_in_mesh` theorem
uses the actual `AIFCandidateMesh.mesh.slab` entry throughout.

## Generation

`tools/aif_mesh.py` accepts repeated `--cell BIN:SLAB` selections,
`--polynomial-binding`, and `--bindings-only`. Polynomial mode imports the matching
`AIFPolynomialContainmentBin…Slab…` module and emits a distinct
`AIFPolynomialMeshBindingBin…Slab…` namespace. Bindings-only output omits the ten
shared geometric/nodal modules but still validates the immutable candidate.
All default sources, including the original six bindings, remain byte-identical.
Invalid selections fail before output creation; check mode compares exact bytes
without writing.

For each `BIN` from `0` through `7`:

```sh
python3 tools/aif_mesh.py /path/to/candidate.json.gz \
  --polynomial-binding --bindings-only \
  --cell "${BIN}:200" --cell "${BIN}:300" \
  --output-directory .lake/aif_interior_mesh_bindings/bindings
```

Repeat with `--check` to verify generation. Revalidate containment artifacts and
their imports first. Build `Gimle.Forseti.Tests.AIFMesh`, and preserve Lake's resolved
import map when adding the checked experiment modules. Compile geometry and the
eight nodal modules before the candidate-mesh root, then compile the bindings.
Use pinned Lean with `-j1 -DElab.async=false`; generated output stays under `.lake/`.
The archived `run.py` records the exact commands and stage dependency maps.

## Scope

The transported drift inequality still assumes metric-tube membership and closed
time/parameter bounds. Exact representation equality supplies no missing local
drift certificates and does not prove trajectory existence or invariance.
The full 2,960-cell geometry and 2,952 time joins are unchanged. Initial containment,
remaining local bounds, the energy chain rule, typed circuit binding, output
bounds and terminal continuation remain obligations for the trajectory theorem.

## Verified result and evidence

All **26 modules** pass: nine geometry/nodal modules, the candidate-mesh root,
and sixteen new binding modules. The audit requires **40 exact named axiom
reports**, including 32 for the new slab equalities and transported drift results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed; axiom-free reports
are also accepted. The eight nodal modules have no reports but still require
successful compilation and nonempty, hash-checked artifacts.

All ten rebuilt foundation artifacts are byte-identical to the earlier checked
versions and total 36,221,544 bytes. The sixteen new bindings total
**4,281,360 bytes (4.28 MB)**, additional to the mesh and containment imports.

Evidence is retained under `.lake/aif_interior_mesh_bindings/`: separate
`foundation` and `bindings` directories, prerequisite records, three stage
environments, the batch manifest, `run.py`, `audit.py` and
`proof-verification.json`. Every receipt is linked to the exact environment used
at its stage. The root-stage environment adds only the nine checked foundation
artifacts; the binding stage adds only the checked root. Artifact hashes must
match preceding receipts. The base environment preserves the containment
prerequisites and their compiler/import hashes.

The independent audit checks exact module sets, freshly regenerated sources,
setup maps, receipts, logs, successful exits, report names and artifact hashes.
It rejects incomplete batches, extra artifacts and leftover pending files, and
rehashes the complete final import environment and the new binding outputs.
Candidate hashes agree across mesh, containment and archived prior evidence.

The historical totals are now **22 mesh-transported in-tube drift results**,
**22 conditional error-coordinate containment results**, and **30 local drift
cells**. This increment adds no local drift cells or containment results and
establishes no trajectory theorem. The remaining composition work includes the
moving-energy chain rule and an invariance argument that derives tube membership
along solutions rather than assuming it.

Repository validation passes: `lake build` (732 axiom reports),
`lake build equation_demo` (63 reports), all 57 Python tests, build-path and
suspension checks, scoped Black/isort/Flake8 checks, and all six default/selected
regeneration checks. The four added tests failed before implementation and pass
afterward. Neither Lean build reports warnings or errors.

The required panel reviewed mathematical scope, generator integration and
evidence integrity, with no blockers. Its synthesis and the consolidated check
record are retained as `panel-review.json` and `verification.json` in the evidence
directory, alongside the complete logs.

The [moving-energy chain rule](aif-energy-chain-rule.md) now supplies the derivative
identity for a supplied solution. Tube invariance remains a separate obligation.
