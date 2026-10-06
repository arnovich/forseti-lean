# AIF drift-box replay

This extends the [metric pilot](aif-replay-pilot.md) to the full augmented drift
matrix on one closed box: physical time [33/5,67/10], fixed eta in [8,17/2], and
error coordinate e₂ in [-3/200,3/200]. It remains a one-box research certificate;
no full startup trajectory or original-circuit contract is asserted.

## What the proof binds

`AIFDriftModel.lean` defines the shifted four-state AIF field, saved cubic
Hermite center, time-varying metric, physical-time rate formulas, residual,
exact nonlinear difference matrix, and augmented block. The metric reuses the
same endpoint data as the earlier pilot. Both center and metric derivatives
have explicit Lean lemmas, including the factor ds/dt = 10.

With e = y - m, E = eᵀPe, r = F(m) - m', J satisfying F(m+e)-F(m)=Je, and
alpha = 1/100, the block is

```text
[ 3/16000000          -rᵀP                   ]
[    -Pr       -P' - PJ - JᵀP - alpha P     ].
```

The generator proposes its degree-(9,3) tensor Bernstein coefficients at the
two error endpoints. Each of the 80 rational 5-by-5 matrices has a weighted-square
certificate checked by the ordinary kernel. Separate polynomial identities bind
these tables to the independently defined block, rather than to a supplied
replacement target. The entrywise binding theorem lifts them to the real matrix
quadratic form. Affinity in e₂ and nonnegative interpolation weights cover the
entire error interval, including both endpoints.

`AIFDriftPilot.drift_bound_physical` gives the algebraic chain-rule inequality

```text
energyRate <= (1/100) * (1/40000 - E) - 1/16000000.
```

The rate expression uses the exact error velocity; `errorVelocity_eq` identifies
it with F(m+e)-m'. No simulation accuracy assumption appears in the theorem.

## Reproduction

Use the same candidate bytes as task 049, gzip SHA-256
`96c882a6183ef5cd7e42e517092e50d0a78358a378dd94390241ffa4b92f2c39`.
The Python 3.10+ standard-library generator proposes data only; its successful exit is not
proof evidence.

```sh
python3 tools/aif_drift_pilot.py /path/to/candidate.json.gz --check
lake build Gimle.Forseti.Examples.AIFDriftPilot
lake build
lake build equation_demo
```

The checked source is standalone: building it needs neither the Python producer
nor the external candidate file. A new candidate must regenerate and recheck all
identities and square certificates.

## Replay measurements

On Apple M2 (24 GiB), macOS 27.0.1 and Lean 4.32.1, a fresh source check of
all 40 negative-endpoint square certificates took 52.07 s wall time, 21.80 s
user CPU and 5.64 s system CPU, with maximum RSS 3,841,409,024 bytes. This
isolated check imported the built model data and replayed the declarations
through `valid`; it excluded the endpoint polynomial binding. Its axiom report
contained only `propext`, `Classical.choice` and `Quot.sound`.

The complete `lake build` passed all 3,665 jobs, with existing dependencies
cached and the changed model, both endpoint files and the final drift theorem
checked from source. Lake reported 250 s for each endpoint file (running
concurrently), including its 40 certificates and polynomial binding, and 491 s
for the final drift module. The entire build took 930.61 s wall time, 421.63 s
user CPU and 38.07 s system CPU; maximum RSS was 3,845,783,552 bytes. These are
observations on a shared machine, not isolated benchmarks or cached-import
timings. All new axiom reports contain only the three standard axioms above.

`lake build equation_demo` also passed (6,811 jobs), as did all 22 Python tool
tests, exact-byte regeneration, Python formatting/lint checks and the compiled
artifact checkout-path guard. Lean regressions reject a changed coefficient and
a negative square weight, exercise a target varying along both Bernstein axes,
and cover the closed physical endpoint. The review panel found no outstanding
mathematical or scope defect; its requested two-axis regression is included.

The two endpoint files contain about 355 kB of explicit coefficient and square
data plus proofs. Naively repeating this representation for 2,960 slabs would
produce 236,800 matrix certificates and about 1 GB of source. That is an
extrapolation from this box, not a whole-candidate feasibility measurement.
Task [051](../tasks/open/051-aif-replay-scaling.md) records the next scaling gate.

## Remaining trajectory obligations

Applying `energyRate` as the derivative of a trajectory energy still needs the
trajectory chain-rule bridge. The error-coordinate hypothesis is explicit. It
must still be derived from the tube metric, along with the output bound. The
other 2,959 slabs, parameter/time
coverage, initial membership, all joins and terminal continuation remain to be
replayed. The final result also needs existence and the original typed circuit
binding. This module does not enroll new imports in the application checker or
change the Python release pin. Novelty of a resulting global bound is unresolved.
