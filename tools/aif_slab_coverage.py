#!/usr/bin/env python3
"""Generate a six-slab AIF coverage experiment; only Lean grants proof authority."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from fractions import Fraction as F
from pathlib import Path

import aif_drift_pilot as drift
from aif_metric_pilot import CANDIDATE_SHA256, matrix, rat, vector

# The first slab at each mesh scale, in the two extreme eta bins.
SELECTIONS = ((0, 0), (0, 40), (0, 80), (7, 0), (7, 40), (7, 80))
VECTOR_NAMES = (
    "loStart",
    "loEnd",
    "loStartSlope",
    "loEndSlope",
    "hiStart",
    "hiEnd",
    "hiStartSlope",
    "hiEndSlope",
)
MATRIX_NAMES = ("startMetric", "endMetric", "startMetricSlope", "endMetricSlope")


def coefficient_matrices(
    vectors: list[list[F]],
    metrics: list[list[list[F]]],
    step: F,
    eta_lo: F,
    eta_hi: F,
) -> dict[str, list[list[list[list[F]]]]]:
    """Compute both exact degree-(9,3) endpoint tables from physical inputs."""
    result = {}
    u = {(0, 1): F(1)}
    lo = [drift.hermite(*(v[i] for v in vectors[:4]), step=step) for i in range(4)]
    hi = [drift.hermite(*(v[i] for v in vectors[4:]), step=step) for i in range(4)]
    m = [
        drift.add(lo[i], drift.mul(u, drift.add(hi[i], drift.scale(-1, lo[i]))))
        for i in range(4)
    ]
    p = [
        [drift.hermite(*(m[i][j] for m in metrics), step=step) for j in range(4)]
        for i in range(4)
    ]
    eta = drift.add(drift.const(eta_lo), drift.scale(eta_hi - eta_lo, u))
    a, b, c, d = m
    cd = drift.mul(drift.add(drift.const(2), c), d)
    field = [
        drift.add(drift.scale(-1, a), c),
        drift.add(a, drift.scale(-1, b)),
        drift.add(drift.scale(-1, c), drift.scale(-1, cd)),
        drift.mul(eta, drift.add(b, drift.scale(-1, c), drift.scale(-1, cd))),
    ]
    residual = [
        drift.add(field[i], drift.scale(-1, drift.dt(m[i], step=step)))
        for i in range(4)
    ]
    pr = [
        drift.add(*(drift.mul(p[i][k], residual[k]) for k in range(4)))
        for i in range(4)
    ]
    for sign, label in [(-1, "Negative"), (1, "Positive")]:
        ec = F(sign * 3, 200)
        jmat = [
            [drift.const(-1), {}, drift.const(1), {}],
            [drift.const(1), drift.const(-1), {}, {}],
            [
                {},
                {},
                drift.scale(-1, drift.add(drift.const(1), d)),
                drift.scale(-1, drift.add(drift.const(2 + ec), c)),
            ],
            [
                {},
                eta,
                drift.scale(-1, drift.mul(eta, drift.add(drift.const(1), d))),
                drift.scale(-1, drift.mul(eta, drift.add(drift.const(2 + ec), c))),
            ],
        ]
        q = [
            [
                drift.add(
                    drift.scale(-1, drift.dt(p[i][j], step=step)),
                    drift.scale(F(-1, 100), p[i][j]),
                    *(
                        drift.scale(-1, drift.mul(p[i][k], jmat[k][j]))
                        for k in range(4)
                    ),
                    *(
                        drift.scale(-1, drift.mul(jmat[k][i], p[k][j]))
                        for k in range(4)
                    ),
                )
                for j in range(4)
            ]
            for i in range(4)
        ]
        block = [[drift.const(F(3, 16000000))] + [drift.scale(-1, v) for v in pr]]
        block += [[drift.scale(-1, pr[i])] + q[i] for i in range(4)]
        matrices = [
            [
                [
                    [drift.bernstein(block[i][j], a, b) for j in range(5)]
                    for i in range(5)
                ]
                for b in range(4)
            ]
            for a in range(10)
        ]
        result[label] = matrices
    return result


def endpoint_source(label: str, matrices: list[list[list[list[F]]]]) -> str:
    """Bind every compact certificate to the independent parameterized model."""
    sign = -1 if label == "Negative" else 1
    source = f"namespace {label}\n"
    source += "def coefficients : Fin 10 → Fin 4 → QMatrix 5 :=\n  !["
    source += (
        ",\n    ".join(
            "![" + ",\n      ".join(matrix(mat) for mat in row) + "]"
            for row in matrices
        )
        + "]\n\n"
    )
    for a in range(10):
        for b in range(4):
            source += drift.certificate_source(a, b, matrices[a][b], compact=True)
    source += "def certificates : Fin 10 → Fin 4 → WeightedSquares 5 :=\n  !["
    source += (
        ",\n    ".join(
            "![" + ", ".join(f"cert_{a}_{b}" for b in range(4)) + "]" for a in range(10)
        )
        + "]\n\n"
    )
    source += (
        "theorem valid : ∀ i j, (certificates i j).Represents (coefficients i j) := by\n"
        "  intro i j\n  fin_cases i <;> fin_cases j\n"
    )
    source += "".join(f"  · exact valid_{a}_{b}\n" for a in range(10) for b in range(4))
    # Select entries and normalize vector lookups and binomial constants before ring.
    # Entry identities bind supplied Bernstein tables to the independent model.
    source += (
        "\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 16000000 in\n"
    )
    source += f"""theorem binding (s u : ℝ) :
    block slab s u ({sign} * (3/200)) = tensorMatrix coefficients s u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [block, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;>
    simp only [q, pr, tensorMatrix, Finset.sum_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, Pi.add_apply] <;>
    dsimp only [AIFSlabModel.residual, field, errorMatrix, coefficients] <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, metric, metricRate,
      center, centerRate, hermite, hermiteRate, eta,
      slab, basis, Nat.choose] <;> ring1

theorem nonnegative (s u : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 5 → ℝ) :
    0 ≤ matrixForm (block slab s u ({sign} * (3/200))) x :=
  target_nonnegative certificates valid (binding s u) hs hu x

#print axioms nonnegative
end {label}
"""
    return source


def generate(candidate: Path) -> dict[str, str]:
    """Select the six declared slabs from the immutable candidate bytes."""
    payload = candidate.read_bytes()
    if hashlib.sha256(payload).hexdigest() != CANDIDATE_SHA256:
        raise ValueError("candidate SHA-256 mismatch")
    data = json.loads(gzip.decompress(payload))
    times = list(map(F, data["time_nodes"]))
    edges = list(map(F, data["eta_edges"]))
    denominator = data["denominator"]
    output = {}
    for bin_index, index in SELECTIONS:
        raw = data["tubes"][bin_index]
        start, end = (times[index], times[index + 1])
        step = end - start
        eta_lo, eta_hi = (edges[bin_index], edges[bin_index + 1])
        if step <= 0 or eta_hi <= eta_lo:
            raise ValueError("time and eta widths must be positive")
        positions = (
            (0, index),
            (0, index + 1),
            (2, index),
            (2, index + 1),
            (1, index),
            (1, index + 1),
            (3, index),
            (3, index + 1),
        )
        vectors = [[F(v, denominator) for v in raw[k][t]] for k, t in positions]
        metrics = [
            [[F(v, denominator) for v in row] for row in raw[k][t]]
            for k, t in ((4, index), (4, index + 1), (5, index), (5, index + 1))
        ]
        name = f"AIFCoverageBin{bin_index}Slab{index}"
        source = "import Gimle.Forseti.Examples.AIFSlabModel\nimport Gimle.Forseti.RationalLDL\n\n"
        source += f"/-! Candidate SHA-256: {CANDIDATE_SHA256}.\n"
        source += f"Bin {bin_index}, interval {index}: t in [{start},{end}], eta in [{eta_lo},{eta_hi}].\n"
        source += (
            "Generated proposals, independently bound and checked by the kernel. -/\n"
        )
        source += f"namespace Gimle.Forseti.Examples.{name}\n"
        source += "open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix\n"
        source += "open Gimle.Forseti.Examples.AIFSlabModel\n"
        source += "open Gimle.Forseti.Examples.AIFDriftModel (field)\n\n"
        source += "def slab : Slab where\n"
        for field, value in zip(
            ("tStart", "step", "etaLo", "etaHi"),
            (start, step, eta_lo, eta_hi),
            strict=True,
        ):
            source += f"  {field} := {rat(value)}\n"
        for field, values in zip(VECTOR_NAMES, vectors, strict=True):
            source += f"  {field} := {vector(values)}\n"
        for field, values in zip(MATRIX_NAMES, metrics, strict=True):
            source += f"  {field} := {matrix(values)}\n"
        source += "\n"
        for label, matrices in coefficient_matrices(
            vectors, metrics, step, eta_lo, eta_hi
        ).items():
            source += endpoint_source(label, matrices)
        source += """
theorem metric_symmetric (s : ℝ) (i j : Fin 4) :
    metric slab s i j = metric slab s j i := by
  fin_cases i <;> fin_cases j <;> norm_num [metric, hermite, slab]

/-- Algebraic drift inequality on this closed physical-time/eta slab. -/
theorem drift_bound_physical (t p : ℝ) (e : Fin 4 → ℝ)
    (ht : t ∈ Set.Icc (slab.tStart : ℝ) ((slab.tStart : ℝ) + slab.step))
    (hp : p ∈ Set.Icc (slab.etaLo : ℝ) (slab.etaHi : ℝ))
    (he : e 2 ∈ Set.Icc (-3/200 : ℝ) (3/200)) :
    energyRate slab (timeCoordinate slab t) (etaCoordinate slab p) e ≤
      (1/100) * (1/40000 - matrixForm (metric slab (timeCoordinate slab t)) e) -
        1/16000000 := by
  have hs := timeCoordinate_mem slab (by norm_num [slab]) t ht
  have hu := etaCoordinate_mem slab (by norm_num [slab]) p hp
  exact drift_bound slab _ _ e (metric_symmetric _)
    (Negative.nonnegative _ _ hs hu) (Positive.nonnegative _ _ hs hu) he

#print axioms drift_bound_physical
"""
        source += f"end Gimle.Forseti.Examples.{name}\n"
        output[name + ".lean"] = source
    return output


def main() -> None:
    """Write experimental sources separately, or check without modifying them."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    destination = args.output_directory
    if destination.resolve() == drift.ROOT.resolve():
        parser.error("coverage experiments require a separate output directory")
    outputs = generate(args.candidate)
    if not args.check:
        destination.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = destination / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
