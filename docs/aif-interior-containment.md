# AIF interior tube containment

The [sixteen interior drift cells](aif-interior-batches.md) require an explicit
bound on the nonlinear error coordinate. This increment supplies that bound
from membership in each cell's metric tube, using the existing generic
[AIF containment theorem](aif-error-containment.md).

For each slab, four ordinary-kernel matrix certificates establish
`P(s) - (1/9) E₂₂ ≥ 0` throughout normalized time `[0,1]`. Consequently,
`eᵀP(s)e ≤ 1/40000` implies `e₂²/9 ≤ 1/40000`, hence
`-3/200 ≤ e₂ ≤ 3/200`. Composing this with the imported physical drift theorem
yields `drift_bound_in_tube`, with no separate error-coordinate assumption.
Membership in the tube remains an explicit premise.

## Generator and reproduction

`tools/aif_error_containment.py` now accepts repeated `--cell BIN:SLAB`
selections and `--polynomial-binding`. The polynomial mode imports the existing
`AIFPolynomialBin…Slab…` proof and uses a distinct
`AIFPolynomialContainmentBin…Slab…` namespace. It copies no slab data.
The default mode still reproduces the original six companion sources exactly.
Invalid or duplicate selections fail before creating an output directory, and
`--check` compares exact bytes without changing files.

For every bin `0` through `7`, generate both interior companions:

```sh
python3 tools/aif_error_containment.py --polynomial-binding \
  --cell "${BIN}:200" --cell "${BIN}:300" \
  --output-directory .lake/aif_interior_containment/companions
```

Repeat each selection with `--check` to verify generation. Before compilation,
revalidate the imported drift receipts against the immutable candidate and the
current checking environment. Build `Gimle.Forseti.Tests.AIFSlabContainment`
and merge its Lake setup map with those used by the drift replay. Add each
imported drift module's checked `.olean` to `importArts`, assign the companion's
module name, and compile with pinned Lean using `-j1 -DElab.async=false`.
The archived `run.py` records the exact setup and compilation procedure.

## Scope

This establishes pointwise drift conditional on metric-tube membership. It does
not prove that a trajectory enters or remains in the tube. The new companions
are tied to their imported slab definitions; binding those definitions to exact
global-mesh entries is still separate work. Initial containment, full-mesh local
bounds, trajectory existence, the energy chain rule, typed circuit binding,
output bounds and terminal continuation remain obligations for the final theorem.

## Verified result

All sixteen complete companions pass: **64 metric certificates** and **32 named
axiom reports**, one error-containment and one in-tube drift theorem per cell.
Only `propext`, `Classical.choice` and `Quot.sound` appear. The compiled companions
total **7,171,096 bytes (7.17 MB)**, additional to their imported drift artifacts.

Before compilation, all sixteen drift receipts were revalidated against freshly
generated candidate-bound sources and the current checking environment. The
companion audit requires a passed batch, exactly the sixteen expected modules,
exact generated sources, receipt and artifact hashes, sizes, setup-map identity,
successful exits and both named reports for every cell. It also verifies that
the companion environment preserves every prerequisite compiler/import hash;
matching import paths alone is insufficient. The full environment is rehashed
at completion and again by the independent audit.

Proof evidence is retained under `.lake/aif_interior_containment/`, including
`prerequisites.json`, `environment.json`, `batch.json`, `proof-verification.json`,
`run.py`, `audit.py` and every companion's source, setup, log, artifact and receipt.
The orchestration is an experiment runner, not a resumable public API; individual
receipts are never accepted independently of a successful whole-batch audit.

The historical totals are now **22 cells with conditional error-coordinate
containment**, **30 local drift cells**, and **6 cells with global-mesh transport**.
No new drift cells or mesh-transport results are added here. The next composition
step is to bind these new slab definitions to their exact global-mesh entries.

## Validation and review

The full build passes 3,677 jobs with 732 allowed-only axiom reports; the demo
passes 6,811 jobs with 63 reports. All **53 Python tests** pass. New regressions
failed before implementation and pass afterward; they cover explicit selections,
backend-specific names/imports, invalid inputs before writes, and nonmutating
exact-byte check mode. Both default and selected containment sources regenerate
exactly, as do the earlier expanded and polynomial drift sources.

Artifact-path and suspension checks pass. Black, isort and flake8 pass on the six
AIF generator/replay files in scope, including both changed Python files. No Lean
warnings occur. The mathematical, integration and evidence panel found no remaining
blockers after the prerequisite-hash continuity and passed-batch acceptance checks
were made explicit. The consolidated record and prioritized review are saved as
`verification.json` and `panel-review.json` beside the proof evidence.
