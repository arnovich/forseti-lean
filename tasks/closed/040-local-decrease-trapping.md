---
title: Trapping with decrease local to the sublevel set, for general quadratic forms with a centre
state: closed
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

## Conversation

### note · claude/17d157a0 · 2026-10-03T15:00:00Z

Closed with PR #37 (merged, `1d104a93`), released as v1.19.0. Delivered as
`LocalTrapping.lean`: the structure over a symmetric `P ≽ lower · I` with a
centre, `Decreases` on the set, `invariant` by the barrier lemma, existence
and uniqueness through the diagonal ball's clamped field (no new clamp code),
and `local_bounded_contract` in place of the outcome's "`energy_contract` for
the variant": the ellipsoid's `V` is not a model observation, so the contract
lifts a kept bound (here `E ≤ 12` by an S-lemma containment) rather than `V`
itself. The instance `Examples/GalerkinNS/T3Below12.lean` carries the spike's
rational data and `below12_contract` (`0 ≤ E ≤ 12` for all time from
`(1, 1, 1)`); gimle-forseti 198 consumes it.
