---
title: Lift polynomial certificates into stream and PDE properties
state: open
priority: high
labels: [streams, predicates, certificates, pde]
depends_on: ["017", "018"]
related: ["019"]
---

# Lift polynomial certificates into stream and PDE properties

## Context

Task 017 checks finite polynomial entailments. Task 018 states contracts over
whole multidimensional streams. A theorem must connect these layers before a
successful algebraic check can establish a property of the original system.

This task consumes two Asgard bridges:
[023, finite observations](https://github.com/arnovich/asgard-lean/blob/main/tasks/open/023-stream-observation-lowering.md)
and [024, polynomial realization](https://github.com/arnovich/asgard-lean/blob/main/tasks/open/024-polynomial-stream-realization.md).
They serve different claims: coefficients of a formal output versus values of
the function it represents. Neither adapter may silently stand in for the other.

## Outcome

- [ ] Define a finite-observation predicate adapter using an explicit manifest
      of input/output ports and coefficient multi-indices, ordered axes and
      basis. Interpret task 017 formulas on the exact rational coefficients
      cast into reals. Use Asgard/023's theorem to lift a checked point Hoare
      triple over the lowered circuit into task 018's total contract over the
      original full stream circuit. Retain its definedness and input hypotheses.
- [ ] Define a separate evaluated-field adapter using Asgard/024's finite-support
      realization theorem. Polynomial formula variables here denote physical
      space-time coordinates and explicitly fixed parameters, not coefficient
      slots. Bind the claim to the original circuit, full input streams, initial
      profile, solution class, analytic interpretation and stated domain.
- [ ] Prove the adapters sound with reusable Lean theorems. A leaf checker success
      alone never establishes the parent claim. Finite coefficient constraints
      imply only their declared observation predicate; full-stream equality and
      field positivity require their own hypotheses and bridge theorems.
- [ ] Demonstrate coefficient constraints through a second derivative and the
      existing formal heat reconstruction circuit. Compute the dependency halo
      through Asgard/023; include an input coefficient outside the output window
      which changes an observed result.
- [ ] For fixed rational `a,c,R,T ≥ 0`, certify the actual heat solution with
      initial profile `p(x) = a*x²+c`, namely `u(t,x) = a*x²+c+2*a*t`.
      On `0 ≤ t ≤ T` and `-R ≤ x ≤ R`, prove
      `0 ≤ u(t,x) ≤ c+a*R²+2*a*T`. Use task 017 certificates for algebraic
      obligations and Asgard/024 for the solution correspondence. Existence
      and uniqueness are stated in the finite polynomial solution class, not
      inferred for all smooth functions from the same computation.
      Supply a reusable Lean box-bound lemma deriving `x² ≤ R²` (including
      `R=0`); then the upper-bound leaf uses
      `a*(R²-x²)+2*a*(T-t) ≥ 0`. This avoids assuming the default finite square
      dictionary can discover a quadratic bound from linear bounds on its own.
- [ ] Check the concrete case `a=1,c=0,R=1,T=1`: bound 3 succeeds and bound 2
      is refuted at `(t,x)=(1,1)`. A leaf counterexample becomes a root refutation
      only after Lean verifies an admissible full input, related output and
      failing root postcondition. If a coefficient witness cannot be extended
      to an admissible input, report no root refutation.
- [ ] Negative tests catch basis/axis/manifest swaps, an altered initial profile,
      a narrowed domain reused as a wider claim, and a finite prefix presented
      as a full stream. Include `u=x` at negative `x` to show that nonnegative
      coefficients do not by themselves establish field nonnegativity.
- [ ] Build all examples in `lake build`; audit new declarations against only
      `propext`, `Classical.choice`, `Quot.sound`. Document both transfer rules
      with theorem references in local documentation.

## Plan

1. Implement and test the coefficient adapter once Asgard/023 and tasks 017/018
   are available. Preserve original-circuit identity in the theorem statement.
2. Add the evaluated-field adapter and strip-bound fixture after Asgard/024.
3. Exercise proof and refutation lifting separately; review the complete theorem
   dependency chain rather than only its polynomial leaves.

## Scope

This is exact proof transfer, not a new solver or general PDE solution method.
Neither arbitrary smooth-field invariants nor general nonlinear feedback are
decided. Infinite analytic tails and approximation require Asgard/025 and a
separate explicitly normed claim; they do not block this exact baseline.
