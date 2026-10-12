# AIF metric error containment

This task 248 increment removes the external nonlinear-error bound from the
[six representative slab drift theorems](aif-slab-coverage.md). It proves a
pointwise implication from metric tube membership; trajectory invariance and
coverage of all 2,960 slabs remain separate obligations.

For the same Hermite metric `P(s)`, Lean binds four rational Bernstein matrices
to `P(s) - (1/9) E₂₂`. Checked positive-semidefinite certificates imply

```
0 ≤ eᵀ(P(s) - (1/9) E₂₂)e = eᵀP(s)e - e₂²/9.
```

Consequently `eᵀP(s)e ≤ 1/40000` implies `-3/200 ≤ e₂ ≤ 3/200`, including
both boundary values. The coefficient is exact: `(1/40000)/(3/200)² = 1/9`.
`AIFSlabContainment` proves the binding and implication for arbitrary slab data;
no candidate decoder or LDL proposal algorithm is trusted.

Each generated companion imports its existing `AIFCoverageBin…Slab…` module,
uses that module's `slab` definition, and checks four `Represents` propositions
with `decide +kernel`. It then derives `error_contained_physical` and composes
that result with `drift_bound_physical` to obtain `drift_bound_in_tube`.
No duplicate slab data or new drift polynomial tables are introduced. There are
24 new matrix checks across bins 0 and 7, interval indices 0, 40 and 80.

## Reproduction

First reproduce the six full coverage modules using the linked guide. Their
source regeneration checks the hash-bound candidate; their complete successful
Lean compilations establish the imported drift proofs. Companion generation by
itself does not validate those artifacts or confer proof authority.

```sh
lake build Gimle.Forseti.Tests.AIFSlabContainment
python3 tools/aif_error_containment.py --output-directory .lake/aif_containment
python3 tools/aif_error_containment.py --output-directory .lake/aif_containment --check
python3 - <<'PY'
import json
from pathlib import Path

root = Path('.lake/aif_containment')
setup = json.loads(Path(
    '.lake/build/ir/Gimle/Forseti/Tests/AIFSlabContainment.setup.json').read_text())
for source in sorted(root.glob('AIFContainment*.lean')):
    base = source.stem.replace('AIFContainment', 'AIFCoverage')
    compiled = Path('.lake/aif_coverage', base + '.olean').resolve()
    if not compiled.is_file():
        raise SystemExit(f'Missing checked dependency: {compiled}')
    companion = dict(setup)
    companion['name'] = 'Gimle.Forseti.Examples.' + source.stem
    companion['importArts'] = dict(setup['importArts'])
    companion['importArts']['Gimle.Forseti.Examples.' + base] = [str(compiled)]
    source.with_suffix('.setup.json').write_text(json.dumps(companion))
PY
lean_bin=$(lake env which lean)
for source in .lake/aif_containment/AIFContainment*.lean; do
  "$lean_bin" -j1 -DElab.async=false --setup "${source%.lean}.setup.json" \
    -o "${source%.lean}.olean" "$source" > "${source%.lean}.log" 2>&1 || exit $?
done
```

The setup map is taken from Lake's built containment regression module, then
extended with one existing coverage artifact per companion. This preserves
Lake's resolution of the shared `Gimle` namespace. Check every exit status and
all 12 named axiom reports (two per companion) after six successful compilations;
only `propext`, `Classical.choice`
and `Quot.sound` are allowed. Retain source and compiled-artifact hashes with
the logs, including the imported coverage source and artifact hashes. There is
no timing claim.

## Validation and remaining work

All six companions compiled successfully: 24 new ordinary-kernel matrix checks,
six containment theorems and six composed drift theorems. All 12 companion axiom
reports contain only the three permitted axioms. Sources, compiled modules,
setup maps, logs and the verification manifest (including imported coverage
hashes) are retained under `.lake/aif_containment/`.

The full repository build (3,671 jobs), demo build (6,811 jobs), artifact-path
audit, exact suspension check and all 33 Python tests pass. All 720 full-build
and 63 demo axiom reports are standard-only; no warnings were emitted. Black,
isort and flake8 (the existing E501 exclusion) pass. Coverage and companion
sources regenerate exactly. Independent mathematical, generator and evidence
reviewers found no blockers; their provenance and report-count clarifications
are included.

Regressions cover the exact positive and negative error boundaries, an outside
point, rejection of a zero-metric proposal for the required margin, and
deterministic nonmutating companion generation.

These six pointwise results do not establish containment along any trajectory.
The remaining slabs, coercivity and output bounds across the candidate, slab
joins, initial containment, trajectory existence and the energy chain rule,
original typed circuit binding, and terminal continuation still require proofs.
