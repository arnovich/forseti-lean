---
title: Galerkin truncations of 2D Navier–Stokes with compositional energy invariants
state: ongoing
claimed_by: claude/17d157a0
claimed_at: 2026-09-30T13:50:31Z
branch: feat/galerkin_ns
priority: medium
labels: [proof, dynamics, nonlinear, showcase]
related: [025, 034, 035]
---

# Galerkin truncations of 2D Navier–Stokes with compositional energy invariants

## Context

gimle-forseti task 181. 2D incompressible Navier–Stokes on the 2π-periodic
square, vorticity form, cosine modes, forced in the single mode cos(x+y),
rational ν and f. A member is a finite set of integer wavevectors; its ODE has
a diagonal linear part −ν|k|² and a quadratic coupling that is a sum of triads
(P + Q + R = 0), each three rational monomials. Energy E = Σ a_k²/|k|² and
enstrophy Z = Σ a_k² are the coupling's only diagonal quadratic invariants;
each triad is a lossless three-port. E' = −2νZ + f·a₍₁,₁₎ and
E' ≤ 2ν(f²/(8ν²) − E) at every state by an explicit rational sum of squares;
f²/(8ν²) is the laminar equilibrium's energy and is optimal. Contracts come
from `Nonlinear.lean` (035).

## Outcome

- [ ] `tools/galerkin_ns.py` (stdlib, exact Fractions, `--check`) derives a
      member from its wavevectors — triads, coefficients, invariants, the SOS
      certificate — verifies the identities in Python, and emits
      `Examples/GalerkinNS/{T3,K5,B2}.lean`: body, evolution, compiled,
      per-mode storage identities, per-triad cancellations, the energy and
      enstrophy identities, `decrease` by the certificate, the `Trapping`,
      and the registry interface (`observed`, `admitted`, `feedback_reads`,
      `declared_input_admitted`, `compiled_exists`, `energy_contract`, a
      refutation, `energyIndex`, `energy_at_initial`, `initial_eq`).
- [ ] T₃ (3 modes, ν = 1/10, f = 1), K₅ (5 modes), B₂ (12 modes, ν = 1/50)
      build under `decide +kernel`; `Tests/GalerkinNS.lean` pins the names and
      the three-axiom footprint; `tools/test_galerkin_ns.py` covers the
      derivation and `--check` passes.
- [ ] Nothing is claimed about the PDE.
