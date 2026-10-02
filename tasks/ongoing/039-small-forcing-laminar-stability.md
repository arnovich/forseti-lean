---
title: Small-forcing laminar stability for the Galerkin family — the unforced energy decays
state: ongoing
claimed_by: claude/17d157a0
claimed_at: 2026-10-02T17:00:00Z
branch: feat/laminar_stability
priority: medium
labels: [lean, nonlinear, showcase, research]
related: ["037", "038"]
---

# Small-forcing laminar stability for the Galerkin family — the unforced energy decays

## Context

Candidate D of gimle-forseti's design study
(`docs/galerkin-compositional-invariants-design.md`, its task 194). With the
enstrophy ball (task 038) bounding the forced amplitude by `√C`, and the
triads among the unforced modes lossless for both `E` and `Z`, only the
triads containing `(1,1)` feed the unforced energy
`E_rest = Σ_{i ≠ forced} a_i²/λ_i`, through the forced mode's own cubic term:
exactly, `E_rest' = −2ν Z_rest − a_forced · N_forced(a)`, where
`N_forced(a) = Σ_{j,l} c(k_j, k_l, k_forced) a_j a_l` has no term with `j` or
`l` the forced index. So `|a_forced N_forced(a)| ≤ |a_forced| K Z_rest` with
`K = Σ_{j,l} |c(k_j, k_l, k_forced)|`, and on the enstrophy ball
`E_rest' ≤ −(2ν − K√C) Z_rest ≤ −γ E_rest` with `γ = 2ν − K√C`. When `γ > 0`,
the laminar line attracts, globally on the ball: a Grashof-type threshold.
Probed off-line: the exact spectral norm of the forced mode's coupling over
the rest modes is `1/5` for T3, K5 and B2 alike, so the threshold is about
`f < 20ν²`; T3 at `ν = 1/2`, `f = 1` is below it, its laminar point is
linearly stable (Jacobian eigenvalues all negative), and a simulation from
`(1, 1, 1)` has `E_rest` decaying to `10⁻²⁶` by `t = 60`.

## Outcome

- `GalerkinNS/Family.lean`: `restEnergy`, `restEnstrophy`, `forcedCubic`,
  the exact `rest_identity`, `restEnergy_le_restEnstrophy`,
  `abs_forcedCubic_le` (the sum-of-absolute-coefficients bound, from
  `|a_j a_l| ≤ Z_rest`), `rest_decrease_rate` (`Z x ≤ r² → E_rest' ≤ −(2ν − K r) Z_rest`
  for `r ≥ 0`), and `rest_decay`: along any solution that stays in
  `{Z ≤ r²}`, `E_rest(t) ≤ E_rest(t₀) e^{−γ (t − t₀)}` with `γ = 2ν − K r > 0`
  (Grönwall through Mathlib), combined with `trapped_enstrophy` into
  `laminar_attracts`; all audited to the three standard axioms
- the generator emits a small-forcing member (T3's modes at `ν = 1/2`,
  `f = 1`) with an `E_rest` observation beside `E` and `Z`, its exact `K`,
  `γ`, the decay theorem instantiated, and a contract `rest_contract`
  (`0 ≤ E_rest ≤ E_rest(start)` for all time) the trajectory registry can
  cite; the existing members gain the `E_rest` observation too, without a
  contract (they are above the threshold)
- released; gimle-forseti task 197 consumes the release
