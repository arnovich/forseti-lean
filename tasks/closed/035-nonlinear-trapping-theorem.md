---
title: General nonlinear trapping theorem, extracted from Lorenz
state: closed
priority: medium
labels: [proof, dynamics, nonlinear]
related: [025, 034]
---

# General nonlinear trapping theorem, extracted from Lorenz

## Context

`Examples/Lorenz.lean` (034) proves existence for all `t ≥ 0`, forward
uniqueness and a trapping bound by hand: clamp the field to a box, Picard–
Lindelöf on each `[0, n]`, glue by uniqueness, fence with the strict decrease
at contact, and `ODE_solution_unique_of_mem_Icc_right` on the box. Its review
noted the block is generic. gimle-forseti task 181 (Galerkin truncations of
2D Navier–Stokes, members with 3, 5 and 12 modes) needs it for every member,
so it becomes a theorem about any compiled model whose field is polynomial.

## Outcome

- [x] `Expr.contDiff_eval`: every `Polynomial.Expr` evaluates to a `ContDiff ℝ 1`
      function of the point, so every compiled field is smooth.
- [x] `Gimle/Forseti/Nonlinear.lean`: for a `ContinuousModel` with a quadratic
      (or C¹) `V` satisfying `V' ≤ α(C' − V)` at every state with `C' < C`, a
      sup-ball containing `{V ≤ C}` and `V(initial) ≤ C`: `∃ state, Realizes`,
      forward uniqueness, and the observed `Contract` with `V ≤ C`, plus the
      refutation of a bound below `V(initial)`, in the registry's interface
      shape; nothing model-specific inside.
- [x] `Examples/Lorenz.lean` is an instance of it with unchanged statements;
      `Tests/Lorenz.lean` still pins the same names. Axioms unchanged.

## Conversation

### note · claude/17d157a0 · 2026-09-30T13:49:18Z

PR #27 merged.
