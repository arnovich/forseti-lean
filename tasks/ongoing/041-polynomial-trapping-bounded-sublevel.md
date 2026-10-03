---
title: Trapping for a polynomial V with a bounded sublevel set, and the 5-mode member's tube below E ≤ 6
state: ongoing
claimed_by: claude/17d157a0
claimed_at: 2026-10-03T18:30:00Z
branch: feat/polynomial_trapping
priority: medium
labels: [lean, nonlinear, research]
related: ["040"]
---

# Trapping for a polynomial V with a bounded sublevel set, and the 5-mode member's tube below E ≤ 6

## Context

`LocalTrapping` (task 040) takes a quadratic `V = (x − c)ᵀP(x − c)` with
`P ≽ lower · I`, which is how `{V ≤ C}` is placed inside the clamp's box.
gimle-forseti's task 213 found, for the 5-mode Galerkin member at
`ν = 1/10`, `f = 1`, a **degree-4** `V` (a sum of squares over the 21
monomials of degree ≤ 2) whose sublevel set `{V ≤ 1}` is a tube around the
member's rotating-wave attractor: it holds the orbit from `(1, …, 1)`, lies
inside `{E ≤ 6}` by an S-lemma certificate, and has `V' ≤ α (inner − V)` on
the set by a degree-6 sum of squares with a quadratic multiplier, all made
exact in rationals (the field's coefficients included) and replayed in a
scratch Lean file (`docs/spikes/196-cross-term-trapping/Task213.lean` there),
which checks the two polynomial inequalities and ties `V'` to the partials
of `V` and the field; invariance is not checked there. That `V` is a degree-4
sum of squares, not a quadratic form about a centre (`V ≈ 21` at the wave's
centre of mass, which lies outside the set), so `LocalTrapping` cannot take
it; the quadratic shape finds nothing below the laminar level for this
member.

## Outcome

- a `Trapping` variant over a polynomial `V : Point n → ℝ` given with its
  derivative along a field (or over `Expr n`, so the chain rule is the
  library's), whose box hypothesis is only that `{V ≤ C}` lies in a sup-norm
  box about some point — stated as a checkable certificate, e.g.
  `V x ≥ C + margin` whenever `‖x − c‖∞ ≥ R`, which a degree-4 sum-of-squares
  lower bound on each face supplies, or an alternative the implementer finds
  cheaper to certify
- decrease local to the set, invariance by the barrier lemma, existence and
  uniqueness through the clamped field as in `LocalTrapping`, and the
  `bounded_contract` analogue
- the instance `Examples/GalerkinNS/K5Below6.lean` with the spike's rational
  data: `below6_contract`, `0 ≤ E ≤ 6` for all time from `(1, …, 1)`, below
  the laminar `25/2` and the family bound `13`; the laminar point outside
  the set
- audited to the three standard axioms; a release
