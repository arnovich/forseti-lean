---
title: Enstrophy identity, certificate and trapping for every Galerkin member, and the two diagonal invariants
state: open
priority: medium
labels: [lean, nonlinear, showcase]
related: [037]
---

# Enstrophy identity, certificate and trapping for every Galerkin member, and the two diagonal invariants

## Context

`GalerkinNS/Family.lean` (task 037) proves the energy identity, certificate
and trapping for every member from `cubic_flux_zero`, the vanishing of the
cubic energy flux by the antisymmetry `(k × q) S(k, q, p) = −(p × q) S(p, q, k)`
under exchange of the ψ-index and the energy index. The enstrophy
`Z = Σ aᵢ²` has the same structure without the `1/λ` weight: the generator
asserts `Σ C = 0` for every triad of every member with exact rationals, and
gimle-forseti's design study (its task 194,
`docs/galerkin-compositional-invariants-design.md`) checked the enstrophy
flux vanishes exactly on the 12-mode member. With `λ ≥ 1` and `λ₍₁,₁₎ = 2`,

    2ν(f²/(4ν²) − Z) − Z' = 2ν Σ_{i ≠ forced} (λ(k i) − 1) aᵢ² + 2ν (a_forced − f/(2ν))²,

so every ball `Z ≤ C`, `C > f²/(4ν²)`, traps, uniformly in the member, and
bounds every mode by `f/(2ν)`. The study also found, exactly, that the
weights `1/λ` and `1` span every diagonal quadratic the triads of T3, K5 and
B2 admit (the lossless-weight space has dimension 2 for each).

## Outcome

- `Family.lean`: `enstrophy_antisymm`, `cubic_enstrophy_flux_zero`,
  `enstrophy_identity` (`Z' = −2ν Σ λ(k i) aᵢ² + 2 f a_forced`),
  `enstrophy_certificate`, `enstrophy_decrease_rate`, a `Trapping` with weights
  `1`, and `trapped_enstrophy`, all audited to the three standard axioms
- a per-member statement that every weight vector making all its triads
  lossless is a combination of `1/λ` and `1` (`T3`, `K5`, `B2`; by exact
  computation on the triad constraints, or by exhibiting the row space),
  checked in each member file
- the generated members (`tools/galerkin_ns.py`) expose an enstrophy
  observation beside the energy and state the enstrophy identity and
  certificate through the family theorem as they do the energy ones
- released; gimle-forseti task 195 consumes the release
