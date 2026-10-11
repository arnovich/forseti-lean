# AIF multi-scale slab replay

This task 248 increment extends the [compact proposal experiment](aif-compact-replay.md)
with a parameterized model and a six-slab binding check. It does not establish
coverage of all 2,960 slabs or a startup trajectory theorem.

`AIFSlabModel.Slab` stores rational time/eta bounds, center endpoint values and
physical slopes, and metric endpoint values and physical slopes. The Hermite
polynomials use the declared step; physical rates divide by that same step.
Lean proves the center and metric chain rules for every nonzero step, interval
normalization for positive time/eta widths, eta reconstruction, the exact
nonlinear field difference, and the algebraic drift inequality under explicit
endpoint nonnegativity and metric symmetry hypotheses.

The model reuses the existing shifted AIF field. The original fixed-box model
and literal pilot remain unchanged. The Python interpolation helpers now accept
a positive step, defaulting to 1/10; the original pilot regenerates exactly.

## Representative batch

The hash-bound candidate supplies these six slabs, chosen before verification:

| Eta bin | Eta interval | Time intervals | Step sizes |
| --- | --- | --- | --- |
| 0 | [8, 17/2] | [0, 1/200], [1/5, 11/50], [1, 11/10] | 1/200, 1/50, 1/10 |
| 7 | [23/2, 12] | [0, 1/200], [1/5, 11/50], [1, 11/10] | 1/200, 1/50, 1/10 |

Each generated module contains exact slab inputs, both 40-matrix endpoint
families, ordinary-kernel certificate checks, independent polynomial identities
binding the supplied coefficients to `AIFSlabModel.block`, and a closed physical
time/eta drift inequality. The generator's successful exit is not proof evidence.
Generated source and compiled artifacts stay under ignored `.lake/`.

## Reproduction

Use the pinned toolchain and dependencies in the repository manifest. The
candidate gzip SHA-256 remains
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.

```sh
lake build Gimle.Forseti.Tests.AIFSlab
python3 tools/aif_slab_coverage.py /path/to/candidate.json.gz \
  --output-directory .lake/aif_coverage
python3 tools/aif_slab_coverage.py /path/to/candidate.json.gz \
  --output-directory .lake/aif_coverage --check
python3 - <<'PY'
import json
from pathlib import Path

root = Path('.lake/aif_coverage')
setup = json.loads(Path(
    '.lake/build/ir/Gimle/Forseti/Tests/AIFSlab.setup.json').read_text())
for source in sorted(root.glob('AIFCoverage*.lean')):
    setup['name'] = 'Gimle.Forseti.Examples.' + source.stem
    source.with_suffix('.setup.json').write_text(json.dumps(setup))
PY
lean_bin=$(lake env which lean)
for source in .lake/aif_coverage/AIFCoverage*.lean; do
  "$lean_bin" -j1 -DElab.async=false --setup "${source%.lean}.setup.json" \
    -o "${source%.lean}.olean" "$source" > "${source%.lean}.log" 2>&1 || exit $?
done
```

The setup map comes from a built test module with the same two imports, avoiding
search-path ambiguity in the shared `Gimle` namespace. These runs check complete
bindings and drift statements; they are not timing comparisons. A successful batch
has six compiled modules and 18 standard-only axiom reports: two endpoint
nonnegativity theorems and one physical drift theorem per slab.

## Validation and remaining work

The full repository build (3,669 jobs), optional demo (6,811 jobs), artifact-path
and suspension-policy checks, and all 31 Python tests pass. Black and isort pass;
flake8 passes with the existing E501 exclusion for long generated-source strings.
Literal-pilot and six-slab source regeneration are exact. All six generated Lean
modules passed: 480 ordinary-kernel matrix checks, 12 independent endpoint
bindings and six physical drift theorems. All 18 batch axiom reports, 718
full-build reports and 63 demo reports contain only `propext`, `Classical.choice`
and `Quot.sound`; no warnings were emitted. Sources, setup maps, compiled modules,
logs and a hash manifest are retained in `.lake/aif_coverage/`. The first two
slabs ran sequentially; the remaining four completed with at most two
single-thread compiler workers. No timing comparison is inferred.

Independent mathematical, generator and evidence reviews found no blockers.
Their candidate-decoding regression and documentation clarifications are included.

Regression tests cover all three physical rates, both time endpoints, the upper
eta endpoint, rejection of the old factor 10 on a fine slab, independent target
entries at both endpoints, changed candidate bytes and nonmutating output checks.

The explicit error-coordinate hypothesis still needs containment from the metric.
The other 2,954 slabs, metric/output bounds, joins, initial containment, trajectory
existence and energy chain rule, original typed circuit binding and terminal
continuation remain separate obligations. Six representatives do not establish
whole-candidate feasibility or a speed improvement.
