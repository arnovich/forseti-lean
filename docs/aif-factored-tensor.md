# Factored AIF Bernstein reconstruction

Task 248's [replay profile](aif-replay-batches.md#runtime-diagnostic) identified
rational polynomial binding as the dominant measured stage in one complete cell.
The reconstruction now sums each parameter row before multiplying by its time
basis. Previously that time-basis multiplication occurred separately for every
parameter coefficient. The generic `eval_tensor` theorem proves the same
`BernsteinMatrix.tensorMatrix` value by finite-sum distributivity and associativity.

The independent physical block polynomial, coefficient tables, matrix
certificates, generator and theorem statements are unchanged. Concrete equality
checks still use `decide +kernel`. New regressions cover unequal degrees, signed
coefficients, asymmetric matrix entries, zero entries, a rejected wrong polynomial,
and degree-zero axes with a negative rational coefficient. They passed before
and after the implementation change.

## Measurement method

The paired experiment compiles the same instrumented complete bin-0, interval-80
module twice, using the pinned Lean 4.32.1 compiler with `-j1 -DElab.async=false`.
The baseline uses a frozen copy of the previous backend artifact, whose source
and compiled hashes match the earlier verified manifest. The two import
environments may differ only in `AIFPolynomialBinding`. Full toolchain and import
hashes are checked before and after each compilation.

The old and new replays run sequentially with no overlapping task builds. An
earlier baseline that overlapped regression builds is retained as exploratory
evidence and excluded from this comparison. In-module markers measure the two
binding checks and the complete proof body; process wall time and child CPU time
also include imports and serialization. Environment hashing is outside those
measurements. This is one observed pair, without repeated or randomized trials;
it does not establish full-mesh throughput.

## Observed result

| Measure | Previous | Factored |
| --- | ---: | ---: |
| Two polynomial binding checks | 160.722 s | 56.294 s |
| In-module proof body | 187.868 s | 73.728 s |
| Complete compiler wall time | 213.294 s | 100.634 s |
| Child user CPU time | 173.583 s | 73.083 s |
| Child system CPU time | 6.832 s | 4.375 s |
| Compiled cell artifact | 10,735,424 bytes | 10,735,424 bytes |

The observed binding-stage speedup is **2.86×**, and the complete compiler run
is **2.12×** faster in this pair. Both pass the exact three named axiom reports;
the generic binding theorem also reports only the standard axioms. The source
and normalized dependency audits pass. These measurements support retaining the
small algebraic change, subject to the single-pair limitation above.

## Scope and evidence

This optimization adds no checked cells. The historical coverage remains 14
local drift cells, with containment and global-mesh transport proved separately
for the original six. The full trajectory theorem remains open. Changing this
shared import invalidates old replay receipts under the current environment;
historical results must not be presented as freshly replayed against this backend.

The paired sources, setup maps, logs, compiled artifacts, environment fingerprints,
results and audit are retained under `.lake/aif_factored_tensor/`. Source freshness
is checked against the immutable candidate after removing only timing commands, their namespace opening and empty lines.
Each complete replay must report both endpoint nonnegativity theorems and the
physical drift theorem with only the standard axioms.

## Validation and review

The full build (3,677 jobs, 732 allowed-only axiom reports), demo (6,811 jobs,
63 reports), all 49 Python tests, exact regeneration in both modes, artifact-path
and suspension checks pass. Black, isort and flake8 pass for the existing four-file
AIF replay/generator scope. An additional `black --check tools` finds existing
formatting differences in `aif_metric_pilot.py`, `galerkin_ns.py` and
`test_galerkin_ns.py`; all three are byte-identical to HEAD and are outside this
change. No Python files were modified.

The mathematical, integration and evidence panel found no remaining blockers.
Its competing-build concern was resolved by excluding the exploratory run and
repeating the pair sequentially. The final audit and review synthesis are in
`.lake/aif_factored_tensor/verification.json` and `panel-review.json`.
