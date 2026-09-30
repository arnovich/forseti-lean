#!/usr/bin/env python3
"""Galerkin truncations of 2D Navier–Stokes as compiled models, generated.

2D incompressible Navier–Stokes on the 2π-periodic square, vorticity form,
cosine modes only, forced in the single mode cos(x + y). A member is a finite
set of integer wavevectors K in the half-plane {k_x > 0} ∪ {k_x = 0, k_y > 0}.
With ω = Σ a_k cos(k·x), ψ = −Σ (a_k/λ_k) cos(k·x), λ_k = |k|², the L²
projection of the vorticity equation gives, for every k ∈ K,

    a_k' = −ν λ_k a_k + f [k = (1,1)] + Σ_{triads ∋ k} C_k a_P a_Q,

where a triad is a set {P, Q, R} of vectors with P + Q + R = 0 whose half-plane
representatives are three distinct members of K, σ = P × Q, and

    C_P = (σ/2)(1/λ_R − 1/λ_Q),  and cyclically.

Energy E = Σ a_k²/λ_k and enstrophy Z = Σ a_k² are conserved by every triad
(Σ C/λ = 0 and Σ C = 0), so E' = −2νZ + f a_(1,1), and at every state
E' ≤ 2ν (f²/(8ν²) − E) by the sum of squares
ν (a_(1,1) − f/(2ν))² + 2ν Σ_{k≠(1,1)} (1 − 1/λ_k) a_k²; f²/(8ν²) is the
laminar equilibrium's energy and is optimal (an argument on the laminar line,
not a Lean statement).

The same field, written over ordered pairs of modes with the coupling
c(p, q, k) = (p × q)/(2 λ_p) · ([p − q = ±k] − [p + q = ±k]), is
`Gimle.Forseti.GalerkinNS.Family.field`, and the family module proves the
energy identity, the certificate and the trapping once for every member. Each
emitted member states `field_eq_family` (its compiled field is the family field
at its modes) and derives `decrease_family` from the family theorem through it,
beside the `ring` route above: the same `field_eq` and `trapping`, the identity
by the family theorem instead of `ring`.

Only the standard library is used, with exact rationals. The identities are
verified here by polynomial expansion before anything is written, and Lean
re-checks every one of them (`ring`, `norm_num`, `decide +kernel`); this script
grants nothing. Run without flags to regenerate, or with --check to compare
without writing.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

Vector = tuple[int, int]
Poly = dict[tuple[int, ...], F]

FORCED: Vector = (1, 1)
ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "Gimle/Forseti/Examples/GalerkinNS"


# ----- members ------------------------------------------------------------------


@dataclass(frozen=True)
class Member:
    """One truncation: its name, modes, parameters and the trapped level."""

    name: str
    modes: tuple[Vector, ...]
    nu: F
    f: F
    bound: F
    radius: int
    refuted: F


def half_plane(k: Vector) -> bool:
    return k[0] > 0 or (k[0] == 0 and k[1] > 0)


def block(size: int) -> tuple[Vector, ...]:
    """Every half-plane wavevector with |k_x|, |k_y| ≤ size."""
    return tuple(
        (x, y)
        for x in range(0, size + 1)
        for y in range(-size, size + 1)
        if half_plane((x, y))
    )


MEMBERS = (
    Member("T3", ((1, 0), (1, 1), (2, 1)), F(1, 10), F(1), F(13), 9, F(1)),
    Member("K5", ((1, 0), (0, 1), (1, 1), (2, 1), (1, 2)), F(1, 10), F(1), F(13), 9, F(1)),
    Member("B2", block(2), F(1, 50), F(1), F(313), 51, F(1)),
)


# ----- derivation ---------------------------------------------------------------


def lam(k: Vector) -> int:
    return k[0] ** 2 + k[1] ** 2


def representative(k: Vector) -> tuple[Vector, int]:
    """The half-plane representative of ±k, and the sign taken."""
    return (k, 1) if half_plane(k) else ((-k[0], -k[1]), -1)


@dataclass(frozen=True)
class Triad:
    """Three distinct modes P, Q, R (half-plane) with signed vectors summing to zero,
    and the coefficient each receives on the product of the other two."""

    modes: tuple[Vector, Vector, Vector]
    coefficients: tuple[F, F, F]


def triads(modes: tuple[Vector, ...]) -> list[Triad]:
    """Every triad among the modes, each cubic monomial arising exactly once."""
    found: dict[tuple[Vector, Vector, Vector], Triad] = {}
    for p, q in combinations(modes, 2):
        for sp in (1, -1):
            for sq in (1, -1):
                P = (sp * p[0], sp * p[1])
                Q = (sq * q[0], sq * q[1])
                R = (-P[0] - Q[0], -P[1] - Q[1])
                r, _ = representative(R)
                if r == (0, 0) or r not in modes or r in (p, q):
                    continue
                key = tuple(sorted((p, q, r)))
                if key in found:
                    continue
                sigma = F(P[0] * Q[1] - P[1] * Q[0])
                lp, lq, lr = F(lam(P)), F(lam(Q)), F(lam(R))
                coefficient = {
                    p: sigma / 2 * (1 / lr - 1 / lq),
                    q: sigma / 2 * (1 / lp - 1 / lr),
                    r: sigma / 2 * (1 / lq - 1 / lp),
                }
                ordered = tuple(sorted((p, q, r)))
                found[key] = Triad(ordered, tuple(coefficient[m] for m in ordered))
    return [found[key] for key in sorted(found)]


def field(member: Member) -> list[Poly]:
    """The right-hand side of every mode, as a polynomial in the state."""
    index = {k: i for i, k in enumerate(member.modes)}
    n = len(member.modes)
    rhs: list[Poly] = [{} for _ in member.modes]

    def add(poly: Poly, powers: tuple[int, ...], value: F) -> None:
        poly[powers] = poly.get(powers, F(0)) + value
        if poly[powers] == 0:
            del poly[powers]

    for i, k in enumerate(member.modes):
        powers = [0] * n
        powers[i] = 1
        add(rhs[i], tuple(powers), -member.nu * lam(k))
        if k == FORCED:
            add(rhs[i], tuple([0] * n), member.f)
    for triad in triads(member.modes):
        for m, coefficient in zip(triad.modes, triad.coefficients):
            others = [o for o in triad.modes if o != m]
            powers = [0] * n
            for o in others:
                powers[index[o]] += 1
            add(rhs[index[m]], tuple(powers), coefficient)
    return rhs


def cross(p: Vector, q: Vector) -> int:
    return p[0] * q[1] - p[1] * q[0]


def selector(p: Vector, q: Vector, k: Vector) -> int:
    """`[p − q = ±k] − [p + q = ±k]`, the family's `S`."""
    minus = (p[0] - q[0], p[1] - q[1])
    plus = (p[0] + q[0], p[1] + q[1])
    neg = (-k[0], -k[1])
    return int(minus in (k, neg)) - int(plus in (k, neg))


def coupling(p: Vector, q: Vector, k: Vector) -> F:
    """The family's ordered-pair coefficient of `a_p a_q` in `a_k'`."""
    return F(cross(p, q), 2 * lam(p)) * selector(p, q, k)


def family_field(member: Member) -> list[Poly]:
    """The right-hand sides as `Family.field` writes them: over ordered pairs."""
    n = len(member.modes)
    rhs: list[Poly] = []
    for i, k in enumerate(member.modes):
        poly: Poly = {}
        linear = [0] * n
        linear[i] = 1
        poly[tuple(linear)] = -member.nu * lam(k)
        if k == FORCED:
            poly[tuple([0] * n)] = member.f
        for j, p in enumerate(member.modes):
            for l, q in enumerate(member.modes):
                c = coupling(p, q, k)
                if c == 0:
                    continue
                powers = [0] * n
                powers[j] += 1
                powers[l] += 1
                key = tuple(powers)
                poly[key] = poly.get(key, F(0)) + c
        rhs.append({key: c for key, c in poly.items() if c != 0})
    return rhs


# ----- exact polynomial checks ----------------------------------------------------


def multiply(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for pa, ca in a.items():
        for pb, cb in b.items():
            powers = tuple(x + y for x, y in zip(pa, pb))
            out[powers] = out.get(powers, F(0)) + ca * cb
    return {p: c for p, c in out.items() if c != 0}


def combine(*terms: tuple[F, Poly]) -> Poly:
    out: Poly = {}
    for scale, poly in terms:
        for p, c in poly.items():
            out[p] = out.get(p, F(0)) + scale * c
    return {p: c for p, c in out.items() if c != 0}


def variable(n: int, i: int) -> Poly:
    powers = [0] * n
    powers[i] = 1
    return {tuple(powers): F(1)}


def constant(n: int, value: F) -> Poly:
    return {tuple([0] * n): value} if value != 0 else {}


def weights(member: Member) -> list[F]:
    return [F(1, lam(k)) for k in member.modes]


def rate(member: Member) -> Poly:
    """E' along the field: Σ 2 w_k a_k F_k."""
    n = len(member.modes)
    rhs = field(member)
    return combine(*((2 * w, multiply(variable(n, i), rhs[i])) for i, w in enumerate(weights(member))))


def energy(member: Member) -> Poly:
    n = len(member.modes)
    return combine(*((w, multiply(variable(n, i), variable(n, i))) for i, w in enumerate(weights(member))))


def enstrophy(member: Member) -> Poly:
    n = len(member.modes)
    return combine(*((F(1), multiply(variable(n, i), variable(n, i))) for i in range(n)))


def verify(member: Member) -> None:
    """Fail loudly if any identity the Lean will check does not hold exactly."""
    n = len(member.modes)
    forced = member.modes.index(FORCED)
    for triad in triads(member.modes):
        assert sum(c / lam(m) for m, c in zip(triad.modes, triad.coefficients)) == 0, triad
        assert sum(triad.coefficients) == 0, triad
    # E' = −2νZ + f a_f
    expected = combine((-2 * member.nu, enstrophy(member)), (member.f, variable(n, forced)))
    assert rate(member) == expected, f"{member.name}: energy identity fails"
    assert field(member) == family_field(member), f"{member.name}: triads differ from the family coupling"
    # 2ν(C* − E) − E' = ν (a_f − f/(2ν))² + 2ν Σ_{k≠f} (1 − 1/λ_k) a_k²
    star = member.f**2 / (8 * member.nu**2)
    lhs = combine(
        (2 * member.nu, constant(n, star)),
        (-2 * member.nu, energy(member)),
        (F(-1), rate(member)),
    )
    shifted = combine((F(1), variable(n, forced)), (F(1), constant(n, -member.f / (2 * member.nu))))
    squares = [(member.nu, multiply(shifted, shifted))]
    for i, k in enumerate(member.modes):
        if i != forced:
            squares.append((2 * member.nu * (1 - F(1, lam(k))), multiply(variable(n, i), variable(n, i))))
    assert lhs == combine(*squares), f"{member.name}: certificate fails"
    assert star < member.bound, f"{member.name}: the bound must exceed f²/(8ν²)"
    for w in weights(member):
        assert member.bound <= w * member.radius**2, f"{member.name}: radius too small"
    start = sum(weights(member))
    assert member.refuted < start <= member.bound, f"{member.name}: start energy {start}"


# ----- Lean emission --------------------------------------------------------------


def mode_name(k: Vector) -> str:
    x, y = k
    return f"a{x}{'m' if y < 0 else ''}{abs(y)}"


def rat(value: F) -> str:
    """A non-negative rational in the equation grammar."""
    assert value >= 0
    return f"rat({value.numerator},{value.denominator})"


def constant_expr(value: F) -> str:
    """The compiler's normal form of a `rat` literal: `.constant (p / q)`."""
    return f"(.constant ({value.numerator} / {value.denominator}))"


def term_source(coefficient: F, names: list[str]) -> str:
    coef = rat(abs(coefficient))
    if coefficient < 0:
        coef = f"(-{coef})"
    return " * ".join([coef, *names])


def term_expr(coefficient: F, indices: list[int]) -> str:
    coef = constant_expr(abs(coefficient))
    if coefficient < 0:
        coef = f"(.neg {coef})"
    expr = coef
    for i in indices:
        expr = f"(.mul {expr} (.var {i}))"
    return expr


def sum_source(terms: list[str]) -> str:
    return " + ".join(terms)


def sum_expr(terms: list[str]) -> str:
    expr = terms[0]
    for t in terms[1:]:
        expr = f"(.add {expr} {t})"
    return expr


def ordered_terms(member: Member, poly: Poly) -> list[tuple[F, list[int]]]:
    """Monomials in a fixed order: constant, linear, then products by index."""
    n = len(member.modes)
    terms = []
    for powers, c in sorted(poly.items(), key=lambda item: (sum(item[0]), item[0])):
        indices: list[int] = []
        for i in range(n):
            indices.extend([i] * powers[i])
        terms.append((c, indices))
    return terms


def real_term(coefficient: F, indices: list[int]) -> str:
    """A monomial over `x : Point n`, in closed form."""
    factors = [f"x {i}" for i in indices]
    if coefficient == 1 and factors:
        return " * ".join(factors)
    return " * ".join([f"({coefficient.numerator} / {coefficient.denominator} : ℝ)", *factors])


def emit(member: Member) -> str:
    verify(member)
    n = len(member.modes)
    names = [mode_name(k) for k in member.modes]
    forced = member.modes.index(FORCED)
    rhs = field(member)
    ws = weights(member)
    star = member.f**2 / (8 * member.nu**2)
    alpha = 2 * member.nu
    lines: list[str] = []
    w = lines.append

    w(f"import Gimle.Forseti.Nonlinear")
    w(f"import Gimle.Forseti.GalerkinNS.Family")
    w(f"import Gimle.Asgard.Compile.Syntax")
    w("")
    w("/-! # " + member.name + ": a Galerkin truncation of 2D Navier–Stokes, trapped")
    w("")
    w("Generated by tools/galerkin_ns.py; do not edit by hand. Every identity below")
    w("was checked by exact polynomial expansion before it was written, and is")
    w("checked again here by Lean.")
    w("")
    w(f"Modes: {', '.join(f'{name} = {k}' for name, k in zip(names, member.modes))}.")
    w(f"ν = {member.nu}, f = {member.f} on cos(x + y). Energy E = Σ a_k²/|k|²;")
    w(f"E' ≤ 2ν (f²/(8ν²) − E) = {alpha} · ({star} − E), and the trapped level is")
    w(f"{member.bound} > {star}, from the start (1, …, 1). -/")
    w("")
    ns = f"Gimle.Forseti.Examples.GalerkinNS.{member.name}"
    w(f"namespace {ns}")
    w("")
    w("open Gimle.Forseti")
    w("open Gimle.Forseti.Trajectory")
    w("open Gimle.Asgard Gimle.Asgard.Model Gimle.Asgard.Polynomial")
    w("")
    w("set_option maxRecDepth 4000")
    w("-- Generated tactic chains use `<;>` so that a `simp` closing a goal early is")
    w("-- not an error; the linters that flag that are off for this file.")
    w("set_option linter.unnecessarySeqFocus false")
    w("set_option linter.unusedTactic false")
    w("set_option linter.unreachableTactic false")
    w("")
    # body
    inputs = ", ".join(f'⟨"state-{nm}", "{nm}", .state⟩' for nm in names)
    w("/-- The modes as states, the forced mode's equation carrying `f`, and the")
    w("energy as the last observation. -/")
    w("def body : Body := {")
    w(f"  program := ⟨[{inputs}],")
    w("    equations% {")
    sources = []
    exprs = []
    for i, nm in enumerate(names):
        terms = ordered_terms(member, rhs[i])
        src = sum_source([term_source(c, [names[j] for j in idx]) for c, idx in terms])
        ex = sum_expr([term_expr(c, idx) for c, idx in terms])
        sources.append(src)
        exprs.append(ex)
        w(f"      d{nm} := {src};")
    energy_src = sum_source([term_source(wk, [nm, nm]) for wk, nm in zip(ws, names)])
    energy_expr = sum_expr([term_expr(wk, [i, i]) for i, wk in enumerate(ws)])
    w(f"      E := {energy_src};")
    w("    }⟩")
    obs = ", ".join(f'⟨⟨"obs-{nm}", "{nm}", .output⟩, "state-{nm}"⟩' for nm in names)
    w(f'  observations := [{obs}, ⟨⟨"obs-e", "E", .output⟩, "E"⟩]')
    w("}")
    w("")
    states = ", ".join(f'⟨"state-{nm}", "d{nm}", "initial-{nm}"⟩' for nm in names)
    ports = ", ".join(f'⟨"initial-{nm}", "{nm}_0", .initial⟩' for nm in names)
    values = ", ".join(f'⟨"initial-{nm}", 1⟩' for nm in names)
    w("/-- From `(1, …, 1)` at `t = 0`. -/")
    w("def evolution : Evolution := {")
    w(f"  states := [{states}]")
    w(f"  initialPorts := [{ports}]")
    w(f"  initialValues := [{values}]")
    w('  axis := ⟨"time", "t"⟩')
    w('  evolveAlong := "time"')
    w("  start := 0")
    w("}")
    w("")
    w("def compiled : ContinuousModel body evolution :=")
    w("  (compileContinuous body evolution).toOption.get (by decide +kernel)")
    w("")
    w("/-- The compiled right-hand sides, as the compiler normalises the source. -/")
    w("private theorem rates_expressions : compiled.rates.expressions =")
    w(f"    (![{', '.join(exprs)}] : Fin {n} → Expr {n}) := by decide +kernel")
    w("")
    w(f"def energyIndex : Fin body.observations.length := ⟨{n}, by decide⟩")
    w("")
    w("private theorem energy_expression : compiled.outputs.expressions energyIndex =")
    w(f"    ({energy_expr} : Expr {n}) := by decide +kernel")
    w("")
    ones = ", ".join(["1"] * n)
    w(f"theorem initial_eq : compiled.initial = (![{ones}] : Point {n}) := by")
    w(f"  change (fun i : Fin {n} => (compiled.initials i : ℝ)) = _")
    w(f"  have values : compiled.initials = ![{ones}] := by decide +kernel")
    w("  rw [values]")
    w("  ext i")
    w("  fin_cases i <;> norm_num")
    w("")
    # closed-form field
    w("/-- The field in closed form, in state order. -/")
    w(f"noncomputable def field (x : Point {n}) : Point {n} :=")
    closed = []
    for i in range(n):
        terms = ordered_terms(member, rhs[i])
        closed.append(" + ".join(real_term(c, idx) for c, idx in terms))
    w("  ![" + ",\n    ".join(closed) + "]")
    w("")
    w(f"theorem rates_formula (x : Point {n}) : compiled.rates.circuit.run x = field x := by")
    w("  rw [Selected.circuit, compileOutputs_correct, rates_expressions]")
    w("  ext i")
    w(f"  change Fin {n} at i")
    w("  fin_cases i <;> simp [field, Expr.eval] <;> ring")
    w("")
    w("theorem rates_eval (i : Fin evolution.states.length) (x : Point evolution.states.length) :")
    w("    (compiled.rates.expressions i).eval x = field x i := by")
    w("  have h := congrFun (rates_formula x) i")
    w("  rwa [Selected.circuit, compileOutputs_correct] at h")
    w("")
    w("theorem field_eq : Nonlinear.field compiled = field := by")
    w("  funext x i")
    w("  exact rates_eval i x")
    w("")
    # the member as an instance of the family
    nu_real = f"({member.nu.numerator} / {member.nu.denominator} : ℝ)"
    f_real = f"({member.f.numerator} / {member.f.denominator} : ℝ)"
    family_field_term = f"GalerkinNS.Family.field {nu_real} {f_real} modes forcedIndex"
    w("/-! ## The member as an instance of the family -/")
    w("")
    w("/-- The modes as the family indexes them. -/")
    w(f"def modes : Fin {n} → GalerkinNS.Family.Wave :=")
    w(f"  ![{', '.join(f'({k[0]}, {k[1]})' for k in member.modes)}]")
    w("")
    w("/-- The index of the forced mode `(1, 1)`. -/")
    w(f"def forcedIndex : Fin {n} := {forced}")
    w("")
    w("theorem modes_nonzero : ∀ i, modes i ≠ 0 := by decide")
    w("")
    w("theorem modes_forced : modes forcedIndex = (1, 1) := by decide")
    w("")
    for i in range(n):
        w(f"private theorem coordinate_{i} (x : Point {n}) :")
        w(f"    field x {i} = {family_field_term} x {i} := by")
        w("  simp only [GalerkinNS.Family.field, Fin.sum_univ_succ, Fin.sum_univ_zero, modes,")
        w("    forcedIndex, field]")
        w("  simp [GalerkinNS.Family.coefficient, GalerkinNS.Family.S, GalerkinNS.Family.cross,")
        w("    GalerkinNS.Family.lam, Matrix.cons_val] <;> ring")
        w("")
    w("/-- The compiled field is the family field at these modes: the triad")
    w("coefficients are the ordered-pair coupling summed over both orders. -/")
    w("theorem field_eq_family :")
    w("    Nonlinear.field compiled =")
    w(f"      {family_field_term} := by")
    w("  rw [field_eq]")
    w("  funext x i")
    w("  fin_cases i")
    for i in range(n):
        w(f"  · exact coordinate_{i} x")
    w("")
    energy_closed = " + ".join(real_term(wk, [i, i]) for i, wk in enumerate(ws))
    w("/-- `E = Σ a_k²/|k|²`. -/")
    w(f"noncomputable def energy (x : Point {n}) : ℝ := {energy_closed}")
    w("")
    w(f"theorem energy_at (x : Point {n}) :")
    w("    compiled.outputs.circuit.run x energyIndex = energy x := by")
    w("  rw [Selected.circuit, compileOutputs_correct]")
    w("  change (compiled.outputs.expressions energyIndex).eval x = _")
    w("  rw [energy_expression]")
    w("  simp [energy, Expr.eval] <;> ring")
    w("")
    start_energy = sum(ws)
    w("theorem energy_at_initial :")
    w(f"    compiled.outputs.circuit.run compiled.initial energyIndex = {start_energy.numerator} / {start_energy.denominator} := by")
    w("  rw [energy_at, initial_eq]")
    w("  simp [energy, Matrix.cons_val] <;> norm_num")
    w("")
    w("theorem domain_iff (t : ℝ) : t ∈ evolution.time.domain ↔ 0 ≤ t := by")
    w("  simp [Dynamics.TimeDomain.domain, Evolution.time, evolution]")
    w("")
    # compositional identities
    w("/-! ## The compositional identities: modes store, triads route -/")
    w("")
    tri = triads(member.modes)
    for t_index, triad in enumerate(tri):
        tn = [mode_name(m) for m in triad.modes]
        cs = triad.coefficients
        w(f"/-- Triad {{{', '.join(tn)}}}: its weighted energy flows sum to zero, and so")
        w("do its unweighted enstrophy flows; it is a lossless three-port. -/")
        w(f"theorem triad_{t_index} :")
        flows = " + ".join(
            f"({F(1, lam(m)).numerator} / {F(1, lam(m)).denominator} : ℝ) * ({c.numerator} / {c.denominator})"
            for m, c in zip(triad.modes, cs)
        )
        w(f"    {flows} = 0 ∧")
        w(f"    ({cs[0].numerator} / {cs[0].denominator} : ℝ) + ({cs[1].numerator} / {cs[1].denominator}) + ({cs[2].numerator} / {cs[2].denominator}) = 0 := by")
        w("  norm_num")
        w("")
    w("/-- Each mode's storage identity: dissipation, forcing, and one cubic term per")
    w("triad it belongs to. -/")
    for i, nm in enumerate(names):
        wk = ws[i]
        # 2 w_k x_k F_k = -2ν λ w x² + 2 w f x [forced] + Σ 2 w C x_P x_Q x_R
        parts = [real_term(-2 * member.nu * lam(member.modes[i]) * wk, [i, i])]
        if i == forced:
            parts.append(real_term(2 * wk * member.f, [i]))
        for triad in tri:
            if member.modes[i] in triad.modes:
                c = triad.coefficients[triad.modes.index(member.modes[i])]
                idx = sorted(member.modes.index(m) for m in triad.modes)
                parts.append(real_term(2 * wk * c, idx))
        w(f"theorem storage_{nm} (x : Point {n}) :")
        w(f"    2 * ({wk.numerator} / {wk.denominator} : ℝ) * x {i} * field x {i} = {' + '.join(parts)} := by")
        w("  simp [field] <;> ring")
        w("")
    w("/-- The energy identity, the storage identities summed: the cubic terms cancel")
    w("triad by triad, leaving `E' = −2νZ + f a_(1,1)`. -/")
    enstrophy_closed = " + ".join(real_term(F(1), [i, i]) for i in range(n))
    w(f"theorem energy_identity (x : Point {n}) :")
    w(f"    (∑ i, 2 * (![{', '.join(f'({wk.numerator} / {wk.denominator} : ℝ)' for wk in ws)}] : Fin {n} → ℝ) i * x i * field x i) =")
    w(f"      -2 * ({member.nu.numerator} / {member.nu.denominator} : ℝ) * ({enstrophy_closed}) + ({member.f.numerator} / {member.f.denominator} : ℝ) * x {forced} := by")
    w("  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, field]")
    w("  simp [Matrix.cons_val] <;> ring")
    w("")
    # trapping
    w("/-! ## The trapping data and the contract -/")
    w("")
    w(f"/-- Weights `1/|k|²`, centre `0`, `α = 2ν`, inner level `f²/(8ν²)`, trapped level")
    w(f"`{member.bound}`, sup-norm radius `{member.radius}`. -/")
    w(f"noncomputable def trapping : Nonlinear.Trapping {n} where")
    w(f"  weights := ![{', '.join(f'{wk.numerator} / {wk.denominator}' for wk in ws)}]")
    w("  centre := fun _ => 0")
    w(f"  alpha := {alpha.numerator} / {alpha.denominator}")
    w(f"  inner := {star.numerator} / {star.denominator}")
    w(f"  bound := {member.bound}")
    w(f"  radius := {member.radius}")
    w("  weights_pos := by intro i; fin_cases i <;> simp [Matrix.cons_val] <;> norm_num")
    w("  alpha_pos := by norm_num")
    w("  margin := by norm_num")
    w("  radius_nonneg := by norm_num")
    w("  covers := by intro i; fin_cases i <;> simp [Matrix.cons_val] <;> norm_num")
    w("")
    w(f"theorem energy_eq_trapping (x : Point {n}) : energy x = trapping.energy x := by")
    w("  simp [energy, trapping, Nonlinear.Trapping.energy, Fin.sum_univ_succ] <;> ring")
    w("")
    w("/-- The certificate: `2ν (f²/(8ν²) − E) − E'` is a sum of squares with")
    w("nonnegative rational weights, `ν (a_(1,1) − f/(2ν))² + 2ν Σ (1 − 1/|k|²) a_k²`. -/")
    shift = member.f / (2 * member.nu)
    sos = [f"({member.nu.numerator} / {member.nu.denominator} : ℝ) * (x {forced} - {shift.numerator} / {shift.denominator}) ^ 2"]
    for i, k in enumerate(member.modes):
        if i != forced:
            coef = 2 * member.nu * (1 - F(1, lam(k)))
            if coef != 0:
                sos.append(f"({coef.numerator} / {coef.denominator} : ℝ) * x {i} ^ 2")
    w(f"theorem certificate (x : Point {n}) :")
    w(f"    trapping.alpha * (trapping.inner - trapping.energy x) - trapping.rate (Nonlinear.field compiled) x =")
    w(f"      {' + '.join(sos)} := by")
    w("  rw [field_eq]")
    w("  simp only [trapping, Nonlinear.Trapping.rate, Nonlinear.Trapping.energy, field, Fin.sum_univ_succ, Fin.sum_univ_zero]")
    w("  simp [Matrix.cons_val] <;> ring")
    w("")
    w(f"theorem decrease (x : Point {n}) :")
    w("    trapping.rate (Nonlinear.field compiled) x ≤ trapping.alpha * (trapping.inner - trapping.energy x) := by")
    w("  have h := certificate x")
    w("  have nonneg : 0 ≤ " + " + ".join(sos) + " := by positivity")
    w("  linarith")
    w("")
    w(f"theorem rate_eq_family (F : Point {n} → Point {n}) (x : Point {n}) :")
    w("    trapping.rate F x = GalerkinNS.Family.rate modes F x := by")
    w("  unfold Nonlinear.Trapping.rate GalerkinNS.Family.rate")
    w("  refine Finset.sum_congr rfl fun i _ => ?_")
    w("  fin_cases i <;> simp [trapping, modes, GalerkinNS.Family.lam, Matrix.cons_val,")
    w("    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring")
    w("")
    w(f"theorem energy_eq_family (x : Point {n}) :")
    w("    trapping.energy x = GalerkinNS.Family.energy modes x := by")
    w("  unfold Nonlinear.Trapping.energy GalerkinNS.Family.energy")
    w("  refine Finset.sum_congr rfl fun i _ => ?_")
    w("  fin_cases i <;> simp [trapping, modes, GalerkinNS.Family.lam, Matrix.cons_val,")
    w("    -mul_eq_mul_right_iff, -mul_eq_mul_left_iff] <;> ring")
    w("")
    w("/-- `decrease` again, by the family theorem through `field_eq_family`: a second")
    w("route to the same inequality over the same `field_eq` and `trapping`, with the")
    w("identity by `Family.decrease_rate` instead of `ring`. -/")
    w(f"theorem decrease_family (x : Point {n}) :")
    w("    trapping.rate (Nonlinear.field compiled) x ≤")
    w("      trapping.alpha * (trapping.inner - trapping.energy x) := by")
    w("  rw [rate_eq_family, energy_eq_family, field_eq_family]")
    w(f"  have alpha_eq : trapping.alpha = 2 * {nu_real} := by norm_num [trapping]")
    w(f"  have inner_eq : trapping.inner = {f_real} ^ 2 / (8 * {nu_real} ^ 2) := by")
    w("    norm_num [trapping]")
    w("  rw [alpha_eq, inner_eq]")
    w(f"  exact GalerkinNS.Family.decrease_rate {nu_real} {f_real} (by norm_num) modes modes_nonzero")
    w("    forcedIndex modes_forced x")
    w("")
    w("theorem initial_le : trapping.energy compiled.initial ≤ trapping.bound := by")
    w("  rw [← energy_eq_trapping, initial_eq]")
    w("  simp [energy, trapping, Matrix.cons_val] <;> norm_num")
    w("")
    w("/-! ## The interface gimle-forseti's trajectory registry cites -/")
    w("")
    w("def observed := LinearEnergyContract.observed compiled")
    w("")
    w("def admitted : Trajectory.SignalPredicate (0 + evolution.states.length) :=")
    w("  LinearEnergyContract.admitted compiled")
    w("")
    w("theorem feedback_reads (input : Dynamics.Signal (0 + evolution.states.length))")
    w("    (admit : admitted input) (state : Dynamics.Signal evolution.states.length) :")
    w("    compiled.feedback.Rel evolution.time input state ↔ compiled.Realizes state :=")
    w("  LinearEnergyContract.feedback_reads compiled input admit state")
    w("")
    w("theorem declared_input_admitted :")
    w("    admitted (Dynamics.signalAppend Model.noDrivers fun _ => compiled.initial) :=")
    w("  LinearEnergyContract.declared_input_admitted compiled")
    w("")
    w("theorem compiled_exists : ∃ state, compiled.Realizes state :=")
    w("  Nonlinear.compiled_exists compiled trapping decrease initial_le")
    w("")
    w(f"theorem compiled_unique {{x y : Dynamics.Signal {n}}}")
    w("    (hx : compiled.Realizes x) (hy : compiled.Realizes y) :")
    w("    Set.EqOn x y evolution.time.domain :=")
    w("  Nonlinear.compiled_unique compiled trapping decrease initial_le hx hy")
    w("")
    w(f"theorem energy_at_trapping (x : Point {n}) :")
    w("    compiled.outputs.circuit.run x energyIndex = trapping.energy x := by")
    w("  rw [energy_at, energy_eq_trapping]")
    w("")
    w(f"/-- **The trajectory stays in the ball `E ≤ {member.bound}`**, for every admitted input. -/")
    w("theorem energy_contract :")
    w("    Contract observed evolution.time admitted")
    w("      (Always evolution.time fun observation =>")
    w(f"        0 ≤ observation energyIndex ∧ observation energyIndex ≤ {member.bound}) :=")
    w("  Nonlinear.energy_contract compiled trapping energyIndex energy_at_trapping decrease initial_le")
    w("")
    w(f"/-- `{member.refuted}` is not a bound: `E = {start_energy}` at the start. -/")
    w("theorem refuted :")
    w("    ¬ Holds observed evolution.time admitted")
    w(f"      (Always evolution.time fun observation => observation energyIndex ≤ {member.refuted}) :=")
    w(f"  Nonlinear.refuted compiled trapping energyIndex energy_at_trapping decrease initial_le {member.refuted}")
    w("    (by")
    w(f"      show ({member.refuted} : ℝ) < @Nonlinear.Trapping.energy {n} trapping compiled.initial")
    w("      rw [← energy_eq_trapping, initial_eq]")
    w("      simp [energy, Matrix.cons_val] <;> norm_num)")
    w("")
    w("#print axioms energy_identity")
    w("#print axioms certificate")
    w("#print axioms field_eq_family")
    w("#print axioms decrease_family")
    w("#print axioms energy_contract")
    w("#print axioms refuted")
    w("")
    w(f"end {ns}")
    return "\n".join(lines) + "\n"


def display(path: Path) -> str:
    """A path relative to the repository when it is inside it."""
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare, never write")
    args = parser.parse_args()
    DESTINATION.mkdir(parents=True, exist_ok=True)
    stale = []
    for member in MEMBERS:
        text = emit(member)
        path = DESTINATION / f"{member.name}.lean"
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != text:
                stale.append(path)
        else:
            path.write_text(text, encoding="utf-8")
            print(f"wrote {display(path)}")
    if stale:
        raise SystemExit("stale: " + ", ".join(display(p) for p in stale))
    if args.check:
        print("generated files are current")


if __name__ == "__main__":
    main()
