# AIF complete mesh geometry and time joins

This task 248 increment represents the candidate's full 370-interval, eight-bin
mesh in Lean. Its geometric coverage and endpoint identities are separate from
the [six checked drift slabs](aif-error-containment.md): this increment does not
replay the remaining 2,954 drift certificates or prove a trajectory invariant.

`AIFMesh.Knot` stores center values, metric entries and their physical slopes at
one time node. `Mesh.slab` takes both endpoints from the shared nodal arrays and
computes the physical step from the time nodes. All 2,960 slabs therefore have
explicit finite indices; neighboring time slabs use exactly the same endpoint.
Each bin uses a 371-element array with a kernel-checked length and a bounds-proved
finite-index getter. These transparent nodal constants and their root mesh are
marked `noncomputable` to avoid unnecessary machine-code generation; their
values and the slab equality checks still reduce in the ordinary kernel.
The candidate generator rejects missing bins, nodes, coordinates or matrix rows,
nonintegral nodal data, nonpositive denominators and nonpositive mesh widths.
Its input is bound to the existing candidate gzip SHA-256
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.

The generic Lean theorems establish closed interval coverage and exact endpoint
agreement of centers, metrics and their physical rates. The same physical state
has the same moving-center metric energy from either side of a time join. The
concrete generated mesh checks every positive width and covers `[0,30] × [8,12]`,
including both step-size transitions and the final endpoints. Its time-join
theorems quantify over all eight bins and all 369 internal time boundaries,
for 2,952 joins. No equality of metrics across parameter-bin boundaries is
claimed or required by these time-join statements.

Six additional binding modules check equality of the mesh-derived slab with the
previously verified slab definition using `decide +kernel`. They transport the
existing tube drift theorem to that exact mesh entry. Thus geometric coverage
does not silently stand in for a missing drift proof. The producer has no proof
authority; every generated module must compile with the ordinary Lean kernel.

## Reproduction

Use the repository's pinned Lean and dependencies. First reproduce the coverage
and containment experiments linked above. Verify their saved artifact hashes
and exact source regeneration before reusing their compiled modules.

```sh
lake build Gimle.Forseti.Tests.AIFMesh Gimle.Forseti.Tests.AIFSlabContainment
python3 tools/aif_mesh.py /path/to/candidate.json.gz --output-directory .lake/aif_mesh
python3 tools/aif_mesh.py /path/to/candidate.json.gz --output-directory .lake/aif_mesh --check
python3 - <<'PY'
import json
from pathlib import Path

root = Path('.lake/aif_mesh')
setup = json.loads(Path('.lake/build/ir/Gimle/Forseti/Tests/AIFMesh.setup.json').read_text())
containment = json.loads(Path(
    '.lake/build/ir/Gimle/Forseti/Tests/AIFSlabContainment.setup.json').read_text())
setup['importArts'].update(containment['importArts'])
for directory, pattern in (
    (Path('.lake/aif_coverage'), 'AIFCoverage*.lean'),
    (Path('.lake/aif_containment'), 'AIFContainment*.lean'),
    (root, '*.lean'),
):
    for source in directory.glob(pattern):
        setup['importArts']['Gimle.Forseti.Examples.' + source.stem] = [
            str(source.with_suffix('.olean').resolve())]
for source in root.glob('*.lean'):
    setup['name'] = 'Gimle.Forseti.Examples.' + source.stem
    source.with_suffix('.setup.json').write_text(json.dumps(setup))
PY
lean_bin=$(lake env which lean)
for source in .lake/aif_mesh/AIFMeshGeometry.lean \
    .lake/aif_mesh/AIFMeshBin[0-7].lean \
    .lake/aif_mesh/AIFCandidateMesh.lean \
    .lake/aif_mesh/AIFMeshBinding*.lean; do
  "$lean_bin" -j1 -DElab.async=false --setup "${source%.lean}.setup.json" \
    -o "${source%.lean}.olean" "$source" > "${source%.lean}.log" 2>&1 || exit $?
done
```

The dependency order matters: geometry and all eight nodal modules precede the
root, and the root precedes the six bindings. Setup maps preserve Lake's
resolution of the shared `Gimle` namespace. Expect 16 successful compilations
and 20 named axiom reports: three geometry, five root, and two for each binding.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted (some exact
rational checks need no axioms). Preserve hashes of sources, compiled modules,
setup maps, logs and the imported coverage/containment artifacts.

## Validation and remaining work

All 16 generated modules compiled successfully. The 20 expected named axiom
reports use only the permitted standard axioms. The full mesh covers 2,960
geometric slabs and verifies 2,952 time joins; six exact slab equalities
transport the previously checked drift theorems. Sources, compiled modules,
setup maps, logs, binding exit statuses and the hash/provenance manifest are
retained under `.lake/aif_mesh/`.

The full repository build (3,673 jobs), demo build (6,811 jobs), artifact-path
audit, exact suspension check and all 36 Python tests pass. The final audit
checks all 727 repository reports (including two axiom-free reports) and 63
demo reports; no forbidden axioms or warnings occur. Black, isort and flake8
(with the existing E501 exclusion) pass, and generated sources reproduce exactly.
Independent mathematical, generator and evidence reviewers found no blockers.
Their node-order, matrix-coordinate, denominator and slope regressions are included.

Regression tests exercise closed endpoint coverage,
unequal step-size joins, and rejection of altered time, center, metric and slope data.
Generator tests check missing data, node order through the final endpoint, every
matrix coordinate in selected records, strict integer denominators, candidate hash
rejection and nonmutating check mode.

Remaining task 248 obligations include drift replay and metric/output bounds
throughout the mesh, initial containment, trajectory existence and the energy
chain rule, original typed circuit binding, and terminal continuation. Endpoint
agreement preserves energy at a join but does not itself prove that a trajectory
stays inside the tube on either neighboring interval.
