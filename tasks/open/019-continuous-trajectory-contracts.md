---
title: Add reusable well-posed continuous trajectory contracts
state: open
priority: high
labels: [dynamics, predicates, hoare, foundations]
related: ["018", "020"]
---

# Add reusable well-posed continuous trajectory contracts

## Context

The three-state ODE already has checked existence, forward uniqueness and energy
safety, and `Discrete.lean` already proves discrete invariant rules. The missing
piece is a reusable continuous property judgment over `Dynamics.Circuit.Rel`,
not another proof of those examples or a claim that dynamics has no coverage.
Existing foundations are `LinearEnergy.lean` and `Examples/ThreeState.lean`.

Use Asgard's `Signal`, `TimeDomain`, `Dynamics.Circuit.Rel`, initialized feedback
and existing linear-analysis results. The initial supported evolution domain is
the existing forward half-line.

## Contract

State separately, for every admissible input signal: (1) an output satisfying the
original relation exists, (2) every related output satisfies the postcondition,
and (3) related outputs agree on the declared time domain. Do not assert merely
that a unique *safe* solution exists while leaving other unsafe solutions free.
Equality outside the observed domain is not a uniqueness requirement.

Input predicates bind initialization, fixed parameters and admissible driving
signals explicitly; initial wires retain Asgard's read-at-start meaning. Output
predicates may express whole-trajectory properties. Provide explicit pointwise
state-predicate lifting and distinguish all-forward safety from observing the
endpoint at a specified time. A witnessed admissible input accompanies demos;
empty preconditions remain logically valid but visibly vacuous.

## Outcome

- [ ] Define the contract and separate projections for realizability, uniqueness
      and the property over the existing `Rel`. A property-only partial contract
      cannot silently be reported as a well-posed system theorem.
- [ ] Prove consequence and relational-equivalence transport. Prove a pointwise
      lift of existing real `ExactHoare` through `Dynamics.Circuit.lift` on the
      stated domain; do not extend that pointwise argument to integrators/trace.
- [ ] Prove sequential wiring composition with intermediate signal contracts
      and the explicit domain-respect assumptions needed to compose uniqueness.
      In particular, equality only on the time domain must suffice for the
      downstream circuit, or a stronger intermediate equality premise is needed.
      Parallel composition uses the same clock/domain and explicit port ownership.
- [ ] Expose named rules that consume existing linear well-posedness and
      `LinearEnergy` certificates to obtain a trajectory contract. Derivative
      inequalities alone cannot discharge existence or uniqueness.
- [ ] Package the original compiled three-state feedback and observation circuit
      into a contract proving `0 ≤ V ≤ 6` for every `t ≥ 2`. Reuse the existing
      model binding, existence/uniqueness, derivative and energy proofs. Bound 5
      is refuted by its admitted initial state, not by a failed proof attempt.
- [ ] Tests separate endpoint from all-time safety, protect the declared start
      time and initial wires, reject unsafe alternative outputs, and show that
      an empty behavior relation satisfies a partial implication but cannot
      satisfy the total contract for a witnessed input. A trace receives no
      unconditional well-posedness rule.
- [ ] `lake build` and an executable transitive axiom audit pass with only
      `propext`, `Classical.choice`, `Quot.sound`. Update `docs/dynamics.md`
      at implementation time to mark only delivered judgments as checked;
      keep the wider PDE/stochastic specification distinct.

## Plan

1. Define the three obligations and pointwise/endpoint observations. Write
   vacuity, nondeterminism and domain-equality tests first.
2. Prove transport and supported composition rules, auditing the global-equality
   clauses in `Dynamics.Rel` rather than assuming all circuits are domain-local.
3. Adapt the existing three-state theorems into the reusable contract; record
   its exact interpretation and assumptions in a worked example.

## Scope

No new ODE solver, generic nonlinear existence theorem, time-concatenation/gluing
rule, finite-horizon replacement of Asgard semantics, or stochastic probability
calculus. Discrete induction remains in `Discrete.lean`; a common presentation
must not erase its different semantics. Stream coefficients use task 018.
