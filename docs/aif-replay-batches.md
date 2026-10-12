# Resumable AIF drift batches

Task 248 now supports explicit selections from the immutable 8-by-370 startup
mesh. `tools/aif_slab_coverage.py --cell BIN:SLAB` can be repeated; omitted
selections preserve the original six-cell experiment exactly. Empty, duplicate,
noninteger and out-of-range selections are rejected. The compact polynomial
backend and its ordinary-kernel proofs are unchanged.

`tools/aif_replay.py` generates and checks one declared batch sequentially.
Each accepted cell has its generated source, Lake import map, compiler log,
compiled artifact and receipt. A receipt records exact hashes, the candidate
hash, the compiler and import environment, successful exit status and all three
named axiom reports. Both endpoint nonnegativity theorems and the physical drift
theorem must report only `propext`, `Classical.choice` and `Quot.sound` (or no
axioms). Missing, duplicate and foreign reports, warnings and errors fail the
replay. Receipts are local build bookkeeping; they have no mathematical authority.

`--resume` rechecks each receipt against freshly generated source and the current
checking environment, including the full pinned toolchain library tree and
implicit core Lean imports. External plugins and dynamic libraries are rejected;
relative import paths resolve against the compiler’s repository working directory.
A changed compiler, import, source, setup, artifact or log invalidates reuse. A failed compile removes its previous receipt; an interrupted
batch can retain completed cells without claiming that the whole batch passed.
`--verify-only` performs these checks without compiling or modifying artifacts.
The batch also rechecks its environment on completion. Use one writer per output
directory, and keep dependencies unchanged while replaying.

## Reproduction

Use the pinned Lean toolchain and Python 3.10 or newer. Build the two imported
regression targets first, so Lake supplies its resolved import maps:

```sh
lake build Gimle.Forseti.Tests.AIFSlab Gimle.Forseti.Tests.AIFPolynomialBinding
python3 tools/aif_replay.py /path/to/candidate.json.gz \
  --lean "$(lake env which lean)" \
  --setup .lake/build/ir/Gimle/Forseti/Tests/AIFSlab.setup.json \
  --setup .lake/build/ir/Gimle/Forseti/Tests/AIFPolynomialBinding.setup.json \
  --output-directory .lake/aif_terminal \
  --cell 0:369 --cell 1:369 --cell 2:369 --cell 3:369 \
  --cell 4:369 --cell 5:369 --cell 6:369 --cell 7:369 --resume
```

Repeat the command with `--verify-only` instead of `--resume` to audit existing
results. Full import hashing can take time before compilation begins. Keep
`environment.json`, `batch.json`, and every cell's five evidence files together.
The candidate gzip SHA-256 remains
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.

## Scope

The terminal experiment checks interval 369, physical time `[29.9,30]`, in all eight
parameter bins, including the six interior bins absent from the earlier replay.
It checks local physical drift with the explicit error-coordinate bound
`-3/200 ≤ e 2 ≤ 3/200`. It does not derive that bound from tube energy, transport
these eight definitions to the global mesh, or establish a trajectory theorem.
The earlier six cells retain their separate containment and mesh-binding proofs.
There are now 14 locally checked drift cells; 2,946 other cells still need local
drift replay, and the trajectory obligations remain open.

See [compact polynomial bindings](aif-polynomial-binding.md) for the unchanged
proof backend and [complete mesh geometry](aif-mesh-joins.md) for the distinct
full-mesh coverage and time-join results.

## Runtime diagnostic

An instrumented replay of the earlier bin-0, interval-80 cell passed with the
same three standard-only axiom reports. Its two rational polynomial-equality
checks occupied 185.055 of 214.528 seconds between the first and last in-module
timing markers (86.3%). This excludes import startup and final serialization.
It identifies the dominant measured stage in that one cell; it is neither a
speedup measurement nor a full-mesh throughput estimate. Reusing Bernstein
expansions or reducing repeated rational work is the next optimization to test.

## Validation

All eight complete terminal modules pass: 640 matrix certificates, 16 polynomial
bindings, eight physical drift theorems and 24 exact named standard-only axiom
reports. Both four-cell batches pass a fresh `--verify-only` run with all
evidence timestamps unchanged. The exact eight-cell audit records sources,
artifacts, setup maps, logs, environment and validation hashes in
`.lake/aif_replay_batches/verification.json`. Their compiled artifacts total **85.01 MB** (85,014,168 bytes). This is
a storage measurement for the new cells, not a speed or full-mesh estimate.

The full build (3,677 jobs, 732 allowed-only reports), demo (6,811 jobs, 63 reports),
49 Python tests, both older generation modes, Black, isort, flake8, artifact-path
and exact suspension checks pass. Mathematical-scope, Python-correctness and
evidence reviews resolved the incomplete toolchain fingerprint, relative-import
resolution, and verification-log matching findings; their regressions are included.

For the subsequent measured optimization, see [factored Bernstein reconstruction](aif-factored-tensor.md). Its changed shared import requires fresh replay receipts.

For the subsequent two interior time slices across all parameter bins, see
[interior drift batches](aif-interior-batches.md).
