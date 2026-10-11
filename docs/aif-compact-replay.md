# Compact AIF certificate experiment

This scaling experiment for internal task 248 follows the
[checked one-box pilot](aif-drift-pilot.md). Both literal and compact versions of
its 40 negative-endpoint coefficient certificates pass ordinary Lean kernel
checking. This does not establish the startup trajectory theorem.

`RationalLDL.propose` computes rational square data from the target matrix.
Acceptance still requires the existing `WeightedSquares.Represents` predicate:
every square weight is nonnegative and every reconstructed entry equals the
target. The producer has no assumed correctness theorem. Division by zero,
negative pivots, or asymmetric inputs cannot bypass that check.

The opt-in generator preserves the target tables, `decide +kernel` proofs, and
polynomial binding statements. Default output remains byte-identical to the
checked pilot. Compact output requires a separate directory; `--check` never
creates or repairs files. Acceptance/rejection regressions cover positive,
empty, zero, singular, indefinite, asymmetric, zero-pivot/nonzero-row and
altered-target matrices, with an exact standard-axiom guard.

## Reproduction

Use Lean 4.32.1, Asgard `411dfdffc44c37320f12b977fc60da7a3117a679`,
Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`, and candidate SHA-256
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.

```sh
lake build Gimle.Forseti.RationalLDL Gimle.Forseti.Tests.RationalLDL
python3 tools/aif_drift_pilot.py /path/to/candidate.json.gz --check
python3 tools/aif_drift_pilot.py /path/to/candidate.json.gz \
  --compact --output-directory .lake/aif_benchmark/full_compact
```

Prepare separate matched modules with the same 40 target matrices, all 40
certificate checks and their aggregate validity theorem. Polynomial binding
and the final drift theorem are deliberately excluded from these measurements.

```sh
python3 - <<'PYCODE'
import json
from pathlib import Path

root = Path('.lake/aif_benchmark')
literal = Path('Gimle/Forseti/Examples/AIFDriftNegative.lean').read_text()
compact = (root / 'full_compact/AIFDriftNegative.lean').read_text()
header = ('import Gimle.Forseti.RationalLDL\n'
          'namespace AIFReplayBenchmark\n'
          'open Gimle.Forseti.LinearEnergy\n')
end = 'end AIFReplayBenchmark\n'
def table(source):
    return source[source.index('def coefficients'):source.index('def cert_0_0')]
assert table(literal) == table(compact)
cut = '\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 16000000 in\n'
setup = json.loads(Path(
    '.lake/build/ir/Gimle/Forseti/Tests/RationalLDL.setup.json').read_text())
for name, source in [('LiteralFamily', literal), ('CompactFamily', compact)]:
    body = source[source.index('def cert_0_0'):source.index(cut)]
    wrapped = ('set_option profiler false\n'
               f'#eval IO.eprintln "BEGIN {name}"\nnamespace {name}\n'
               'set_option profiler true\nset_option profiler.threshold 1\n'
               + body + '\n#print axioms valid\nset_option profiler false\n'
               + f'end {name}\n#eval IO.eprintln "END {name}"\n')
    (root / (name + '.lean')).write_text(header + table(source) + wrapped + end)
    setup['name'] = 'AIFReplayBenchmark.' + name
    (root / (name + '.setup.json')).write_text(json.dumps(setup))
PYCODE

# macOS time -l reports wall/user/system time and maximum RSS in bytes.
# Run sequentially and preserve failed logs. Reverse order for another sample.
lean_bin=$(lake env which lean)
for variant in LiteralFamily CompactFamily; do
  /usr/bin/time -l "$lean_bin" -j1 -DElab.async=false \
    --setup ".lake/aif_benchmark/$variant.setup.json" \
    -o ".lake/aif_benchmark/$variant.olean" \
    ".lake/aif_benchmark/$variant.lean" \
    > ".lake/aif_benchmark/$variant.log" 2>&1 || exit $?
done
```

The setup files reuse Lake's resolved import-artifact map for the test module,
whose sole import is also `RationalLDL`. This handles the shared `Gimle`
namespace across Forseti and Asgard without relying on search-path order.
For the recorded runs the pinned toolchain's `lean` binary was invoked directly
with these arguments, excluding Lake launcher overhead.

## Results and decision

The negative and positive endpoint sources shrink from 177,822 and 177,787 bytes
to 78,770 and 78,776 bytes respectively: 355,609 to 157,546 bytes in total
(55.7% smaller). This source-size comparison includes unchanged target tables
and binding proofs; it is not a runtime or full-coverage claim.

An exploratory combined run checked a compact-first pair, then the compact
40-certificate family, then the literal family. Both aggregate theorems report
only `propext`, `Classical.choice`, and `Quot.sound`. Reported type-checking
entries within the family markers total 8.262 seconds compact versus 6.360
seconds literal. These rounded profiler entries exclude sub-threshold work and
are not total execution times. Whole-process measurements were 216.98 seconds
wall, 22.18 seconds user CPU, 4.58 seconds system CPU and 3,047,915,520 bytes RSS.
The first-pair samples (in both orders) also favored literal checking, but their
small absolute times are insufficient for a performance decision.

The original raw logs and artifacts were in the temporary worktree, which is
no longer available. The table preserves measurements recorded before its
removal; the recipe above produces fresh samples.

Separate sequential runs (literal first) produced:

| Representation | Wall (s) | User CPU (s) | System CPU (s) | Maximum RSS (bytes) | `.olean` (bytes) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Literal | 56.40 | 13.15 | 4.27 | 3,136,274,432 | 8,794,088 |
| Compact | 45.21 | 13.60 | 3.54 | 3,129,786,368 | 5,643,464 |

Both aggregate validity theorems report only the standard three axioms. Compact
reduces the emitted certificate module by 35.8%. Total CPU is similar in this
single sample (17.42 versus 17.14 seconds). The exploratory combined run reported
higher type-checking time for compact certificates; these measurements do not
isolate the source of the total-CPU difference. Cache and scheduling effects
prevent a speed claim.

Keep compact generation as an opt-in format for the next scaling experiment,
while preserving the checked literal pilot as the default. The source and
artifact reductions justify further investigation; they do not establish
feasibility for all 2,960 slabs. These measurements do not check compact
polynomial binding or the final drift theorem.

Measurements used a shared Apple M2 Mac with 24 GiB RAM and warm dependency caches. The owner approved
temporarily suspending a Lean editor worker with approximately 5,900 threads;
the identity-checked worker was resumed after the measurements and initial build
attempt. Import delays remained variable,
so whole-process wall times are not certificate arithmetic measurements.
Earlier interrupted import attempts provide no proof acceptance/rejection result.

## Next coverage gate

The candidate has eight eta bins and 370 intervals per bin: 40 intervals of
width 1/200, 40 of width 1/50, and 290 of width 1/10. A later batch must cover
multiple eta bins and all three step sizes, whose physical-time factors ds/dt
are 200, 50, and 10. The current generator and checked model deliberately remain
the fixed 1/10 pilot. Changing only coefficient data cannot extend its binding
proof to the other intervals. Full binding, trajectory existence, initial
containment, joins and terminal continuation remain separate obligations.

## Repository validation

All 25 Python tests and exact literal/compact regeneration pass in the recovered
persistent worktree. Black and isort pass; flake8 passes with E501 excluded for
the existing long generated-source strings. Fresh ordinary-kernel verification
also passes for both 40-certificate families and their aggregate validity
theorems, reporting only the permitted standard axioms. This fresh combined run
confirms validity; it is not another matched timing sample.

Earlier full builds failed while saving the unchanged `GalerkinNS.K5Below6`
compiled artifact with OS error 28 (no space left on device). After disk space
was freed, validation passed in the recovered persistent worktree: full
`lake build` (3,667 jobs), `lake build equation_demo` (6,811 jobs), the artifact-path
guard and suspension-policy check. The full build includes the new producer
regressions, existing AIF endpoint bindings, drift pilot and its regressions.
All 714 full-build axiom reports and both fresh family reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Fresh logs and generated family
sources are retained under `.lake/aif_benchmark/` in the persistent worktree.

Independent proof-correctness, generator and measurement reviews found no
remaining blocking source issue after singular-case/output-preservation tests
and the timing-interpretation correction. The recovered sources were reviewed
again before this validation run.
