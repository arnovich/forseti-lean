# Compact AIF polynomial bindings

Task 248's [six-slab replay](aif-slab-coverage.md) binds each Bernstein table to
its physical AIF model using a separately expanded real-polynomial proof. Those
six `.olean` files occupy 91–127 million bytes each. This increment moves the
shared algebra into two checked modules and checks each concrete binding by
ordinary-kernel rational computation.

`RationalPolynomial` represents bivariate polynomials as lists of rational
monomials. Its executable addition collects matching powers; multiplication,
negation and powers have proved evaluation laws. Acceptance means every term
of the collected difference has coefficient zero. The soundness theorem needs
no canonical-form invariant. It is a sufficient equality check, not a complete
decision procedure on arbitrary lists containing repeated monomials.

`AIFPolynomialBinding` encodes the existing `AIFSlabModel` and proves that every
entry evaluates to the original real-valued block matrix. This includes both
Hermite endpoint slopes, division by the physical step, both parameter endpoints,
the nonlinear error coordinate, and every matrix entry. A second generic theorem
binds the polynomial Bernstein reconstruction to `BernsteinMatrix.tensorMatrix`.
The per-slab obligation is then a Boolean rational equality checked with
`decide +kernel`. The Python producer and native evaluation have no proof authority.

The optional generator mode preserves all 80 matrix certificates, both endpoint
nonnegativity theorems and the physical drift statement per slab. Default generation
continues to reproduce the older experiment exactly. This increment does not
expand drift coverage beyond the existing six slabs or prove trajectory safety.

## Reproduction

Use the repository's pinned Lean toolchain and dependency manifest, and Python
3.10 or newer. The immutable candidate hash is recorded in the generated sources
and checked before decoding, as in the original replay.

```sh
lake build Gimle.Forseti.Tests.AIFPolynomialBinding Gimle.Forseti.Tests.AIFSlab
python3 tools/aif_slab_coverage.py /path/to/candidate.json.gz \
  --polynomial-binding --output-directory .lake/aif_polynomial_binding
python3 tools/aif_slab_coverage.py /path/to/candidate.json.gz \
  --polynomial-binding --output-directory .lake/aif_polynomial_binding --check
```

Merge the two Lake setup maps to preserve resolution of the shared `Gimle`
namespace, then compile all six complete modules sequentially:

```sh
python3 - <<'PYSETUP'
import json
from pathlib import Path

base = Path('.lake/build/ir/Gimle/Forseti/Tests')
setup = json.loads((base / 'AIFSlab.setup.json').read_text())
setup['importArts'].update(json.loads(
    (base / 'AIFPolynomialBinding.setup.json').read_text())['importArts'])
sources = sorted(Path('.lake/aif_polynomial_binding').glob('AIFPolynomialBin*.lean'))
assert {s.stem for s in sources} == {
    f'AIFPolynomialBin{b}Slab{i}' for b in (0, 7) for i in (0, 40, 80)}
for source in sources:
    setup['name'] = 'Gimle.Forseti.Examples.' + source.stem
    source.with_suffix('.setup.json').write_text(json.dumps(setup))
PYSETUP
lean_bin=$(lake env which lean)
for source in .lake/aif_polynomial_binding/AIFPolynomialBin*.lean; do
  "$lean_bin" -j1 -DElab.async=false --setup "${source%.lean}.setup.json" \
    -o "${source%.lean}.olean" "$source" > "${source%.lean}.log" 2>&1 || exit $?
done
```

Retain exit codes, sources, setup maps, logs and `.olean` hashes. A complete batch
has six successful modules and 18 named standard-only axiom reports: two endpoint
nonnegativity theorems and one physical drift theorem in each namespace.

## Validation

All six complete modules pass: 480 matrix-certificate checks, 12 polynomial
bindings and six physical drift theorems. The audit requires exactly the six
expected modules and 18 named standard-only axiom reports, verifies the older
baseline against its prior source/artifact hashes, and records every new source,
setup-map, log and compiled-artifact hash in
`.lake/aif_polynomial_binding/verification.json`.

The six `.olean` files shrink from **687.48 MB to 61.16 MB**. The two new shared
modules add **2.44 MB**, making the complete incremental comparison **63.60 MB**,
or **10.81 times smaller** (decimal MB). Individual slabs shrink from 91.11–126.50
MB to 9.56–10.74 MB. This measures compiled proof size, not total workspace size
or a runtime speedup. All six use exactly the same input, coefficient and
certificate data as the baseline.

The full build (3,677 jobs), demo (6,811 jobs), 37 Python tests, exact regeneration
in both modes, artifact-path and suspension checks, Black, isort and flake8
(with the existing E501 exclusion) pass. The 732 full-build reports and 63 demo
reports contain only allowed axioms; no warnings occur. Independent mathematical,
generator and evidence reviews found no blockers. Their duplicate-list regression
and exact-set, baseline-provenance and shared-storage checks are included.

The full-mesh replay remains a later obligation. These measurements do not
establish throughput or drift coverage for the remaining 2,954 cells, metric and
output bounds, or a trajectory theorem. The original checker and the default
expanded-binding generator remain available for comparisons.

For subsequent selected-cell runs and provenance-checked resume, see
[resumable drift batches](aif-replay-batches.md).
