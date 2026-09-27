#!/usr/bin/env python3
"""Untrusted, exact finite search for the suspension example's common storage.

Only the standard library is used. The fixed specifications are duplicated here
for proposal generation; Lean rechecks every candidate against SuspensionModel.
Run without flags to regenerate, or with --check to compare without writing.
"""

from __future__ import annotations

import argparse
from fractions import Fraction as F
from pathlib import Path

Matrix = list[list[F]]
N = 5
RATES = (F(2), F(5, 2))
ALPHA = F(1, 40)
ROAD_BOUND = F(1, 1000)
INITIAL_FACTOR = F(100)
OUTPUTS: Matrix = [
    [F(1), F(-1), F(0), F(0), F(0)],
    [F(0), F(0), F(0), F(0), F(1)],
    [F(-1), F(1), F(-1), F(1), F(1, 2)],
]
ROAD = [F(x) for x in (0, 0, 0, 4, 0)]
DESTINATION = Path(__file__).resolve().parents[1] / (
    "Gimle/Forseti/Examples/SuspensionCertificateData.lean"
)


def dynamics(rate: F) -> Matrix:
    """Proposal copy of the model; never an authoritative circuit translation."""
    rows: list[list[int | F]] = [
        [0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0],
        [-1, 1, -1, 1, F(1, 2)],
        [2, -6, 2, -2, -1],
        [-rate, rate, -rate, rate, -rate],
    ]
    return [[F(x) for x in row] for row in rows]


def solve(matrix: Matrix, target: list[F]) -> list[F]:
    """Exact Gaussian elimination, rejecting a singular candidate system."""
    rows = [row[:] + [rhs] for row, rhs in zip(matrix, target, strict=True)]
    size = len(rows)
    for col in range(size):
        pivot = next((i for i in range(col, size) if rows[i][col]), None)
        if pivot is None:
            raise ValueError("singular Lyapunov system")
        rows[col], rows[pivot] = rows[pivot], rows[col]
        divisor = rows[col][col]
        rows[col] = [x / divisor for x in rows[col]]
        for i in range(size):
            if i != col:
                factor = rows[i][col]
                rows[i] = [
                    a - factor * b for a, b in zip(rows[i], rows[col], strict=True)
                ]
    return [row[-1] for row in rows]


def lyapunov_seed() -> Matrix:
    """Solve AᵀP + PA = -I at the midpoint response rate using exact rationals."""
    a = dynamics(F(9, 4))
    equations = []
    target = []
    for i in range(N):
        for j in range(N):
            row = [F(0)] * (N * N)
            for k in range(N):
                row[k * N + j] += a[k][i]
                row[i * N + k] += a[k][j]
            equations.append(row)
            target.append(F(-int(i == j)))
    flat = solve(equations, target)
    return [flat[i * N : (i + 1) * N] for i in range(N)]


def ldl(matrix: Matrix) -> tuple[list[F], Matrix]:
    """Exact positive-definite LDLᵀ decomposition; no tolerance or floats."""
    size = len(matrix)
    if any(matrix[i][j] != matrix[j][i] for i in range(size) for j in range(size)):
        raise ValueError("matrix is not symmetric")
    lower = [[F(int(i == j)) for j in range(size)] for i in range(size)]
    diagonal: list[F] = []
    for j in range(size):
        pivot = matrix[j][j] - sum(lower[j][k] ** 2 * diagonal[k] for k in range(j))
        if pivot <= 0:
            raise ValueError("nonpositive LDL pivot")
        diagonal.append(pivot)
        for i in range(j + 1, size):
            lower[i][j] = (
                matrix[i][j]
                - sum(lower[i][k] * lower[j][k] * diagonal[k] for k in range(j))
            ) / pivot
    vectors = [[lower[i][j] for i in range(size)] for j in range(size)]
    return diagonal, vectors


def supply(p: Matrix, rate: F, beta: F) -> Matrix:
    """Build the augmented exact matrix for beta*d² - alpha*V - V'."""
    a = dynamics(rate)
    result = [[F(0)] * (N + 1) for _ in range(N + 1)]
    for i in range(N):
        for j in range(N):
            result[i][j] = (
                -sum(a[k][i] * p[k][j] + p[i][k] * a[k][j] for k in range(N))
                - ALPHA * p[i][j]
            )
        result[i][N] = result[N][i] = -sum((p[i][k] * ROAD[k] for k in range(N)), F(0))
    result[N][N] = beta
    return result


def fixed_targets(p: Matrix) -> list[tuple[str, str, Matrix]]:
    """Independent initial inclusion and observable containment obligations."""
    return [
        ("positive", "storage", p),
        (
            "initial",
            "initialMatrix storage",
            [
                [INITIAL_FACTOR * int(i == j) - p[i][j] for j in range(N)]
                for i in range(N)
            ],
        ),
        *[
            (
                f"output{k}",
                f"outputMatrix storage {k}",
                [[p[i][j] - row[i] * row[j] for j in range(N)] for i in range(N)],
            )
            for k, row in enumerate(OUTPUTS)
        ],
    ]


def search() -> tuple[Matrix, F, int, int, int, list[tuple[str, str, Matrix]]]:
    """Enumerate a bounded family; exhaustion means only no candidate found."""
    seed = lyapunov_seed()
    attempted = 0
    for denominator in (1, 2, 4, 8, 16, 32, 64):
        rounded = [
            [F(round(x * denominator), denominator) for x in row] for row in seed
        ]
        for scale in (1, 2, 4, 8, 16):
            attempted += 1
            p = [[scale * x for x in row] for row in rounded]
            targets = fixed_targets(p)
            try:
                for _, _, matrix in targets:
                    ldl(matrix)
            except ValueError:
                continue
            for exponent in range(15):
                beta = F(2**exponent)
                if beta * ROAD_BOUND**2 > ALPHA:
                    continue
                extra = [
                    (
                        "slowSupply",
                        "supplyMatrix storage alpha beta 2",
                        supply(p, RATES[0], beta),
                    ),
                    (
                        "fastSupply",
                        "supplyMatrix storage alpha beta (5 / 2)",
                        supply(p, RATES[1], beta),
                    ),
                ]
                try:
                    for _, _, matrix in extra:
                        ldl(matrix)
                except ValueError:
                    continue
                return p, beta, denominator, scale, attempted, targets + extra
    raise ValueError(
        "no certificate found in the finite family; the root goal is not refuted"
    )


def rational(x: F) -> str:
    """Render an exact, explicitly parenthesized Lean rational literal."""
    if x.denominator == 1:
        return str(x.numerator) if x >= 0 else f"({x.numerator})"
    return f"({x.numerator} / {x.denominator})"


def vector(row: list[F]) -> str:
    """Render a Lean finite vector."""
    return "![" + ", ".join(map(rational, row)) + "]"


def render() -> str:
    """Recompute a candidate and emit data checked against hand-written targets."""
    p, beta, denominator, scale, attempted, targets = search()
    lines = [
        "import Gimle.Forseti.Examples.SuspensionCertificates",
        "",
        "/-! Generated by tools/search_suspension.py using exact rational arithmetic.",
        f"First accepted candidate: denominator {denominator}, scale {scale}, "
        f"after {attempted} storage candidates.",
        "All targets below are recomputed from the independent typed suspension model.",
        "These are proposals until the ordinary Lean kernel checks their proofs. -/",
        "",
        "namespace Gimle.Forseti.Examples.ActiveSuspension.CertificateData",
        "",
        "open Gimle.Forseti.LinearEnergy",
        "",
        "/-- Discovered common storage matrix, not part of the input specification. -/",
        "def storage : QMatrix 5 :=",
        "  ![" + ",\n    ".join(vector(row) for row in p) + "]",
        "",
        f"def alpha : ℚ := {rational(ALPHA)}",
        f"def beta : ℚ := {rational(beta)}",
        "",
    ]
    for name, target, matrix in targets:
        weights, vectors = ldl(matrix)
        size = len(matrix)
        lines.extend(
            [
                f"/-- Exact square decomposition for `{target}`. -/",
                f"def {name} : WeightedSquares {size} where",
                f"  count := {size}",
                f"  weight := {vector(weights)}",
                "  vector := ![" + ",\n    ".join(vector(row) for row in vectors) + "]",
                "",
                "set_option maxRecDepth 100000 in",
                "set_option maxHeartbeats 4000000 in",
                f"theorem {name}_valid : {name}.Represents ({target}) := by",
                "  unfold WeightedSquares.Represents",
                "  decide +kernel",
                "",
            ]
        )
    lines.extend(
        [
            "#print axioms slowSupply_valid",
            "#print axioms fastSupply_valid",
            "",
            "end Gimle.Forseti.Examples.ActiveSuspension.CertificateData",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    """Generate or compare the exact artifact; check mode never writes it."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=DESTINATION)
    args = parser.parse_args()
    try:
        content = render()
    except ValueError as error:
        parser.exit(1, f"search exhausted: {error}\n")
    if args.check:
        if not args.output.exists() or args.output.read_bytes() != content.encode(
            "utf-8"
        ):
            parser.exit(1, "certificate data differs from a fresh exact search\n")
        print("fresh exact search reproduces the certificate data")
    else:
        args.output.write_bytes(content.encode("utf-8"))
        print(f"wrote exact candidate to {args.output}; Lean replay still required")


if __name__ == "__main__":
    main()
