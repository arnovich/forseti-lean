# AIF Bernstein replay pilot

This is a prerequisite for the startup trajectory theorem, not that theorem.
`BernsteinMatrix.tensor_nonnegative` lifts rational weighted-square matrix
certificates to positivity on a closed two-dimensional unit box. It reuses
`LinearEnergy.WeightedSquares.nonnegative`. The caller must establish the
identity between its target and the Bernstein representation. The separate
`cubic_identity` theorem provides that identity for a cubic matrix polynomial
with no parameter dependence.

`Examples/AIFMetricPilot.lean` checks the actual candidate metric for the first
parameter bin, eta in [8,17/2], on physical time [33/5,67/10]. Its normalized time
is s = 10*(t-33/5). The four rational Hermite endpoint matrices are preserved;
Lean recomputes the cubic power coefficients and their Bernstein coefficients.
Four exact LDL weighted-square proposals certify the metric minus I/50.
The resulting theorem controls every real error vector throughout the interval,
including the endpoints. The metric is independent of eta within this bin.

## Reproduction

The input is the committed candidate from gimle-forseti PR #235, gzip SHA-256
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.
The generator uses only standard-library rational arithmetic and the existing
suspension proposal generator's LDL routine. It refuses other candidate bytes.

```sh
python3 tools/aif_metric_pilot.py /path/to/candidate.json.gz --check
lake build Gimle.Forseti.BernsteinMatrix \
  Gimle.Forseti.Tests.BernsteinMatrix Gimle.Forseti.Examples.AIFMetricPilot
lake build
lake build equation_demo
```

The candidate lives at `docs/spikes/245-startup/evidence/candidate.json.gz` in
[gimle-forseti at c2782b3](https://github.com/arnovich/gimle-forseti/tree/c2782b3/docs/spikes/245-startup).
This source hash is provenance, not a trusted decoder. The Lean theorem is
about the rational endpoint matrices explicitly written in its own statement
and definitions. The Python script, hash check and generated data grant no
authority; each `Represents` proposition is checked with `decide +kernel`.

## Replay measurement

On 2026-10-06, a fresh source elaboration of the complete pilot module passed
using Lean 4.32.1 on an Apple M2 with 24 GiB RAM, macOS 27.0.1. It checked all
four coefficient certificates and the whole-interval coercivity theorem;
it did not merely import a cached `AIFMetricPilot.olean`.

- Wall time: 42.42 seconds.
- Lean CPU: 6.356 seconds user plus 5.244 seconds system.
- Peak resident memory: 2,770,845,696 bytes (2.58 GiB).
- Axioms: only `propext`, `Classical.choice` and `Quot.sound`.

The direct Lean invocation used the project's resolved import paths. For an
equivalent fresh source check, with built prerequisites, run:

```sh
lake env /usr/bin/time -l lean Gimle/Forseti/Examples/AIFMetricPilot.lean
```

These figures include loading the imported library; they do not isolate the
cost of the four rational certificates. Concurrent builds caused substantial
I/O contention: the earlier foundation import/check took 555 seconds, while
Lake compiled the pilot in 71 seconds. Neither the wall time nor
the peak memory should be extrapolated linearly to the full certificate.

The complete `lake build` passed 3,658 jobs; `lake build equation_demo` passed
6,811 jobs. Regression proofs cover closed endpoints, degree zero, both tensor
axes, altered cross terms and negative weights. Generator reproduction and
altered-input rejection also passed. The review panel found no remaining
mathematical, reproducibility or scientific-scope issues.

## Remaining gate

The pilot covers one metric inequality on one time interval. It does not check
the other 2,959 intervals, the nonlinear coordinate and output bounds, either
drift block, coverage, derivative identities, joins, existence, nonnegativity,
local continuation or the original typed circuit. Even success here does not
show that replay of the larger 5-by-5 drift coefficients scales acceptably.
The [drift-box pilot](aif-drift-pilot.md) extends this experiment to a full
drift polynomial. Whole-candidate cost still needs measuring before claiming
the startup bound x2 <= 16/5. If explicit
LDL literals dominate source size, a computable Lean proposal function could
construct the square data from each target. Its output would still have to pass
`WeightedSquares.Represents`; the proposal algorithm itself need not be trusted.

No checker import policy, Python release pin or user-facing PROVEN result is
changed by building these modules. Mathematical novelty of the final bound
also remains unresolved.
