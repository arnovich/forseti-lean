---
title: Trapping with decrease local to the sublevel set, for general quadratic forms with a centre
state: ongoing
claimed_by: claude/17d157a0
claimed_at: 2026-10-03T13:00:00Z
branch: feat/local_trapping
priority: medium
labels: [lean, nonlinear, research]
related: ["035", "037"]
---

# Trapping with decrease local to the sublevel set, for general quadratic forms with a centre

## Context

`Nonlinear.Trapping` takes a diagonal `V = Σ wᵢ (xᵢ − cᵢ)²` and a **global**
decrease `∀ x, V' ≤ α (inner − V)`. With a global decrease every equilibrium
`x*` has `V(x*) ≤ inner` (its rate is zero), so every trapped set contains
every equilibrium: for the Galerkin members, the laminar point, and no set
below the laminar energy `f²/(8ν²)` is reachable this way. gimle-forseti's
spike 196 found for the 3-mode member at `ν = 1/10` an ellipsoid with cross
terms and a centre, inside `{E ≤ 12}` (below the laminar `25/2`), with
`V' ≤ α(inner − V)` certified **on the set** by a degree-4 sum of squares
with a quadratic S-procedure multiplier, replayed exactly in a scratch Lean
file. Lean needs the theorem that takes it.

## Outcome

- a `Trapping` variant over a general quadratic `V(x) = (x − c)ᵀ P (x − c)`
  with `P` positive definite (given with a certificate Lean checks, e.g. an
  `LDLᵀ` or a sum of squares), whose decrease hypothesis is
  `∀ x, V x ≤ bound → V' x ≤ α (inner − V x)` with `inner < bound`
- forward invariance of `{V ≤ bound}` from the local hypothesis: the
  argument of `Dissipative.sublevel` runs as long as the solution stays in
  the set, and a first-exit argument (continuity of `V ∘ state`) shows it
  never leaves
- existence for all time and uniqueness (`exists_solution`, `unique`)
  re-proved for this variant: the clamped field must be clamped to a box
  containing the ellipsoid, and the glue step must use invariance of the set
  rather than the global decrease
- `energy_contract` for the variant, so the trajectory lane can cite it, and
  the member tests exercising it on T3 with the spike's rational data
  (gimle-forseti task 198 consumes it)
- audited to the three standard axioms
