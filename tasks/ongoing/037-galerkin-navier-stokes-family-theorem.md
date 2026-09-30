---
title: Family-level energy identity, certificate and trapping for Galerkin Navier–Stokes
state: ongoing
priority: medium
labels: [lean, nonlinear, showcase]
related: [035, 036]
claimed_by: claude/17d157a0-family
claimed_at: 2026-09-30T18:26:51Z
branch: feat/galerkin_family
---

# Family-level energy identity, certificate and trapping for Galerkin Navier–Stokes

## Context

Examples/GalerkinNS/{T3,K5,B2}.lean each prove the energy identity and the SOS
certificate by `simp … <;> ring` on their expanded field; the argument that
these hold for every member lives only in the docstring of tools/galerkin_ns.py.
The family is definable in Lean: modes `k : Fin n → ℤ × ℤ`, all nonzero, exactly
one equal to (1,1); coupling `coefficient p q k = (p×q)/(2λ_p)·([p−q=±k] − [p+q=±k])`
over ordered pairs (the projection of J(ψ,ω), Δψ = ω; equal to the triad form and
verified against direct integration for T3/K5); field, E = Σ a²/λ, Z = Σ a².
The cubic energy flux vanishes because exchanging the ψ-index and the energy
index flips the summand's sign (`cross k q · S k q p = −cross p q · S p q k`), a
finite-sum identity closed by `Finset.sum_comm`; the certificate is algebra from
it using λ(1,1) = 2. `Nonlinear.Trapping.exists_solution/unique/invariant` are
already field-generic, so trapping is family-level given `ContDiff ℝ 1` of the
field (`ContDiff.sum`). Injectivity and the half-plane condition are modelling
assumptions of the definition, not hypotheses of any theorem. That the family
field is the Galerkin projection of Navier–Stokes is a paper derivation, checked
with sympy, not a Lean statement.

## Outcome

- [x] `Gimle/Forseti/GalerkinNS/Family.lean`: definitions above; `energy_antisymm`,
  `cubic_flux_zero`, `energy_identity`, `certificate`, `decrease`, a family
  `Trapping` (weights 1/λ, centre 0, α = 2ν, inner f²/(8ν²), bound C, radius
  1 + C Σ λ) and `trapped` (existence for all t ≥ start, uniqueness, E ≤ C) for
  every n, k, ν > 0, f, C > f²/(8ν²) and start with E ≤ C; `#print axioms` shows
  only propext/Classical.choice/Quot.sound
- [x] tools/galerkin_ns.py emits, per member, `field_eq_family` (compiled field =
  family field at its modes) and derives `decrease` from `Family.decrease`,
  keeping the `ring` route; `--check` current; B2 elaborates within the existing
  option budget
- [x] Tests exercise a member the generator does not emit (a 2-mode list and a
  list with a ± pair) so the theorems are seen to be family-wide
- [x] docs/dynamics.md states the family rules citing the Lean names; the README
  row for Galerkin NS says "every member" and drops "chaotic in simulation"

## Conversation

### note · claude/17d157a0-family · 2026-09-30T18:45:14Z

Shipped as named: each member keeps `decrease` (the `ring` route) and adds
`decrease_family`, derived from `Family.decrease_rate` through
`field_eq_family`; `Family.decrease` is the `Nonlinear.Trapping`-shaped wrapper
the family `trapped` consumes. The certificate needs only `∀ i, k i ≠ 0` and
`k forced = (1, 1)`; uniqueness of `(1, 1)` is not a hypothesis.
