---
title: Enstrophy identity, certificate and trapping for every Galerkin member, and the two diagonal invariants
state: ongoing
claimed_by: claude/17d157a0
claimed_at: 2026-10-02T14:45:00Z
branch: feat/enstrophy_family
priority: medium
labels: [lean, nonlinear, showcase]
related: ["037"]
---

# Enstrophy identity, certificate and trapping for every Galerkin member, and the two diagonal invariants

## Context

`GalerkinNS/Family.lean` (task 037) proves the energy identity, certificate
and trapping for every member from `cubic_flux_zero`, the vanishing of the
cubic energy flux by the antisymmetry `(k × q) S(k, q, p) = −(p × q) S(p, q, k)`
under exchange of the ψ-index and the energy index. The enstrophy
`Z = Σ aᵢ²` is conserved by the triads too — the generator asserts `Σ C = 0`
for every triad of every member with exact rationals, and gimle-forseti's
design study (its task 194, `docs/galerkin-compositional-invariants-design.md`)
checked the enstrophy flux vanishes exactly on all three members — but by a
**different** exchange: the ω-index `l` with the enstrophy index `i`, the
ψ-index `j` fixed, `(p × q) S(p, q, k) = −(p × k) S(p, k, q)`, the `1/λ_p`
weight factoring out because it sits on the fixed index (checked exhaustively
over nonzero waves in `[−3, 3]²`; the energy exchange with its weight dropped
does not hold). With `λ ≥ 1` and `λ₍₁,₁₎ = 2`,

    2ν(f²/(4ν²) − Z) − Z' = 2ν Σ_{i ≠ forced} (λ(k i) − 1) aᵢ² + 2ν (a_forced − f/(2ν))²,

so every ball `Z ≤ C`, `C > f²/(4ν²)`, traps, uniformly in the member, and
bounds every mode by `√C`, just above `f/(2ν)`. The study also found, exactly,
that the weights `1/λ` and `1` span every diagonal quadratic the triads of T3,
K5 and B2 conserve (the lossless-weight space has dimension 2 for each), and
that K5 alone has a third conserved symmetric form,
`(5/3)(a₍₁,₀₎² + a₍₀,₁₎²) + 2(a₍₁,₀₎a₍₁,₂₎ + a₍₀,₁₎a₍₂,₁₎)` modulo `E` and `Z`,
from its reflection symmetry.

## Outcome

- `Family.lean`: `enstrophy_antisymm` (the `(i, l)` exchange above),
  `cubic_enstrophy_flux_zero` (`Finset.sum_comm` over `i` and `l`),
  `enstrophy_identity` (`Z' = −2ν Σ λ(k i) aᵢ² + 2 f a_forced`),
  `enstrophy_certificate`, `enstrophy_decrease_rate`, a `Trapping` with weights
  `1`, and `trapped_enstrophy`, all audited to the three standard axioms
- per member (`T3`, `K5`, `B2`): the triad losslessness conditions stated as
  a linear system over `ℚ` in the weights, one equation per `triad_*` theorem,
  with the theorem that every solution is a combination of `1/λ` and `1`
  (exact row reduction, `decide`-style on `ℚ` or `norm_num` on an exhibited
  basis); for K5 also the third symmetric invariant's conservation, by `ring`
- the generated members (`tools/galerkin_ns.py`) expose an enstrophy
  observation beside the energy and state the enstrophy identity and
  certificate through the family theorem as they do the energy ones
- released; gimle-forseti task 195 consumes the release
