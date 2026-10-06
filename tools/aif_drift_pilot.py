#!/usr/bin/env python3
"""Propose exact AIF drift-box certificates; only Lean checks their validity."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from fractions import Fraction as F
from math import comb
from pathlib import Path

from aif_metric_pilot import CANDIDATE_SHA256, matrix, vector
from search_suspension import ldl

Poly = dict[tuple[int, int], F]
ROOT = Path(__file__).resolve().parents[1] / "Gimle/Forseti/Examples"


def add(*polys: Poly) -> Poly:
    """Sum sparse bivariate polynomials exactly."""
    result: Poly = {}
    for p in polys:
        for k, v in p.items():
            result[k] = result.get(k, F(0)) + v
    return {k: v for k, v in result.items() if v}


def scale(value: F | int, p: Poly) -> Poly:
    """Multiply every coefficient by an exact scalar."""
    return {k: value * v for k, v in p.items() if value * v}


def mul(p: Poly, q: Poly) -> Poly:
    """Convolve the two exponent axes."""
    result: Poly = {}
    for (i, j), a in p.items():
        for (k, l), b in q.items():
            key = (i + k, j + l)
            result[key] = result.get(key, F(0)) + a * b
    return {k: v for k, v in result.items() if v}


def const(v: F | int) -> Poly:
    """Embed a rational constant."""
    return {(0, 0): F(v)} if v else {}


def hermite(a: F, b: F, c: F, d: F) -> Poly:
    """Cubic interpolant over the fixed physical step 1/10."""
    return {
        (0, 0): a,
        (1, 0): c / 10,
        (2, 0): 3 * (b - a) - (2 * c + d) / 10,
        (3, 0): 2 * (a - b) + (c + d) / 10,
    }


def dt(p: Poly) -> Poly:
    """Physical time derivative, ds/dt=10."""
    return {(i - 1, j): 10 * i * v for (i, j), v in p.items() if i}


def bernstein(p: Poly, a: int, b: int) -> F:
    """Exact degree-(9,3) coefficient; reject an insufficient degree."""
    if any(i > 9 or j > 3 for i, j in p):
        raise ValueError("target exceeds declared degree")
    return sum(
        (
            v * F(comb(a, i), comb(9, i)) * F(comb(b, j), comb(3, j))
            for (i, j), v in p.items()
            if i <= a and j <= b
        ),
        F(0),
    )


def generate(candidate: Path) -> dict[str, str]:
    """Bind the known candidate bytes and emit both complete endpoint families."""
    payload = candidate.read_bytes()
    if hashlib.sha256(payload).hexdigest() != CANDIDATE_SHA256:
        raise ValueError("candidate SHA-256 mismatch")
    data = json.loads(gzip.decompress(payload))
    times = list(map(F, data["time_nodes"]))
    index = times.index(F(33, 5))
    if times[index + 1] != F(67, 10):
        raise ValueError("unexpected pilot interval")
    raw = data["tubes"][0]
    den = data["denominator"]
    names = [
        "loStart",
        "loEnd",
        "loStartSlope",
        "loEndSlope",
        "hiStart",
        "hiEnd",
        "hiStartSlope",
        "hiEndSlope",
    ]
    entries = [
        (0, index),
        (0, index + 1),
        (2, index),
        (2, index + 1),
        (1, index),
        (1, index + 1),
        (3, index),
        (3, index + 1),
    ]
    vectors = [[F(v, den) for v in raw[k][i]] for k, i in entries]
    center = "import Gimle.Forseti.Examples.AIFMetricPilot\n\n"
    center += "/-! Exact center inputs from the hash-bound startup candidate. -/\n"
    center += "namespace Gimle.Forseti.Examples.AIFDriftData\n\n"
    for name, values in zip(names, vectors, strict=True):
        center += f"def {name} : Fin 4 → ℚ := {vector(values)}\n\n"
    center += "end Gimle.Forseti.Examples.AIFDriftData\n"
    output = {"AIFDriftData.lean": center}
    u = {(0, 1): F(1)}
    lo = [hermite(*(v[i] for v in vectors[:4])) for i in range(4)]
    hi = [hermite(*(v[i] for v in vectors[4:])) for i in range(4)]
    m = [add(lo[i], mul(u, add(hi[i], scale(-1, lo[i])))) for i in range(4)]
    p = [
        [
            hermite(
                *(
                    F(raw[k][t][i][j], den)
                    for k, t in [(4, index), (4, index + 1), (5, index), (5, index + 1)]
                )
            )
            for j in range(4)
        ]
        for i in range(4)
    ]
    eta = add(const(8), scale(F(1, 2), u))
    a, b, c, d = m
    cd = mul(add(const(2), c), d)
    field = [
        add(scale(-1, a), c),
        add(a, scale(-1, b)),
        add(scale(-1, c), scale(-1, cd)),
        mul(eta, add(b, scale(-1, c), scale(-1, cd))),
    ]
    residual = [add(field[i], scale(-1, dt(m[i]))) for i in range(4)]
    pr = [add(*(mul(p[i][k], residual[k]) for k in range(4))) for i in range(4)]
    for sign, label in [(-1, "Negative"), (1, "Positive")]:
        ec = F(sign * 3, 200)
        jmat = [
            [const(-1), {}, const(1), {}],
            [const(1), const(-1), {}, {}],
            [{}, {}, scale(-1, add(const(1), d)), scale(-1, add(const(2 + ec), c))],
            [
                {},
                eta,
                scale(-1, mul(eta, add(const(1), d))),
                scale(-1, mul(eta, add(const(2 + ec), c))),
            ],
        ]
        q = [
            [
                add(
                    scale(-1, dt(p[i][j])),
                    scale(F(-1, 100), p[i][j]),
                    *(scale(-1, mul(p[i][k], jmat[k][j])) for k in range(4)),
                    *(scale(-1, mul(jmat[k][i], p[k][j])) for k in range(4)),
                )
                for j in range(4)
            ]
            for i in range(4)
        ]
        block = [[const(F(3, 16000000))] + [scale(-1, v) for v in pr]]
        block += [[scale(-1, pr[i])] + q[i] for i in range(4)]
        matrices = [
            [
                [[bernstein(block[i][j], a, b) for j in range(5)] for i in range(5)]
                for b in range(4)
            ]
            for a in range(10)
        ]
        source = "import Gimle.Forseti.Examples.AIFDriftModel\n\n"
        source += "/-! Generated exact proposals; every target identity and square is checked. -/\n"
        source += f"namespace Gimle.Forseti.Examples.AIFDrift{label}\n"
        source += "open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix\n"
        source += "open Gimle.Forseti.Examples.AIFDriftModel\n\n"
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
                weights, rows = ldl(matrices[a][b])
                source += f"""def cert_{a}_{b} : WeightedSquares 5 where
  count := 5
  weight := {vector(weights)}
  vector := {matrix(rows)}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem valid_{a}_{b} : cert_{a}_{b}.Represents (coefficients {a} {b}) := by
  unfold WeightedSquares.Represents
  decide +kernel

"""
        source += "def certificates : Fin 10 → Fin 4 → WeightedSquares 5 :=\n  !["
        source += (
            ",\n    ".join(
                "![" + ", ".join(f"cert_{a}_{b}" for b in range(4)) + "]"
                for a in range(10)
            )
            + "]\n\n"
        )
        source += (
            "theorem valid : ∀ i j, (certificates i j).Represents (coefficients i j) := by\n"
            "  intro i j\n  fin_cases i <;> fin_cases j\n"
        )
        source += "".join(
            f"  · exact valid_{a}_{b}\n" for a in range(10) for b in range(4)
        )
        # Select entries and normalize vector lookups and binomial constants before ring.
        # Entry identities bind supplied Bernstein tables to the independent model.
        source += (
            "\nset_option maxRecDepth 100000 in\nset_option maxHeartbeats 16000000 in\n"
        )
        source += f"""theorem binding (s u : ℝ) :
    block s u ({sign} * (3/200)) = tensorMatrix coefficients s u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [block, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;>
    simp only [q, pr, tensorMatrix, Finset.sum_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, Pi.add_apply] <;>
    dsimp only [AIFDriftModel.residual, field, errorMatrix, coefficients] <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, metric, metricRate,
      center, centerRate, hermite, hermiteRate, eta,
      AIFDriftData.loStart, AIFDriftData.loEnd,
      AIFDriftData.loStartSlope, AIFDriftData.loEndSlope,
      AIFDriftData.hiStart, AIFDriftData.hiEnd,
      AIFDriftData.hiStartSlope, AIFDriftData.hiEndSlope,
      AIFMetricPilot.startMetric, AIFMetricPilot.linear,
      AIFMetricPilot.quadraticTerm, AIFMetricPilot.cubicTerm,
      AIFMetricPilot.endMetric, AIFMetricPilot.startSlope,
      AIFMetricPilot.endSlope, scale, basis, Nat.choose] <;> ring1

theorem nonnegative (s u : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 5 → ℝ) :
    0 ≤ matrixForm (block s u ({sign} * (3/200))) x :=
  target_nonnegative certificates valid (binding s u) hs hu x

#print axioms nonnegative
end Gimle.Forseti.Examples.AIFDrift{label}
"""
        output[f"AIFDrift{label}.lean"] = source
    return output


def main() -> None:
    """Generate the fixed drift pilot or check exact reproduction."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, source in generate(args.candidate).items():
        path = ROOT / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode("utf-8"):
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode("utf-8"))


if __name__ == "__main__":
    main()
