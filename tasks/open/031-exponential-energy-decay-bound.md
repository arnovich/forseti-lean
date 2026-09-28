---
title: Prove an exponential decay bound on a damped linear model's energy
state: open
priority: low
labels: [trajectory, contracts, energy, linear]
related: ["029", "030", "gimle-forseti/139"]
---

## Context

gimle-forseti's flagship notebook (`examples/notebooks/ThreeState.lean`,
task 139) asks whether the three-state model's energy `V = x² + y² + z²` stays
at least 1 for all `t ≥ 2`. It does not: with damping `(1/3, 1/2, 2)`,
`V' = -2(a x² + b y² + c z²) ≤ -(2/3) V`, so `V(t) ≤ 6 e^{-2(t-2)/3}` drops
below 1 for every `t > 2 + (3/2) ln 6 ≈ 4.7`. The trajectory decider can only
answer UNKNOWN, because the contracts it has (029's energy contracts) bound
`V` above and below by constants; nothing states the decay, and the notebook
says so ("that argument is ours, not Lean's").

## Outcome

- [ ] A theorem for compiled linear models with an energy certificate whose
      dissipation dominates a positive multiple of the energy
      (`V' ≤ -λ V`, `λ > 0`): every admitted trajectory has
      `V(t) ≤ V(t₀) · exp(-λ (t - t₀))` for all `t ≥ t₀` (a Grönwall-type
      bound), stated in the shape the deciders consume (029's contracts).
- [ ] Instantiated for the three-state model with `λ = 2/3`, together with a
      corollary giving a checked time and state where `V < 1`, so a
      trajectory refutation of "always `V ≥ 1`" becomes possible.
- [ ] The gimle-forseti side (a trajectory decider template that refutes
      "always `V ≥ c`" from this bound) is filed there as its own task when
      this lands.
