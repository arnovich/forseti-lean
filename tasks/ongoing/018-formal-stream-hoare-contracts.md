---
title: Add total Hoare contracts over multidimensional formal streams
state: ongoing
claimed_by: claude-f018
claimed_at: 2026-09-26T16:20:41Z
branch: feat/formal_stream_hoare_contracts
priority: high
labels: [predicates, streams, hoare, foundations]
related: ["017", "019", "020"]
---

# Add total Hoare contracts over multidimensional formal streams

## Context

Dynamical systems can have ports carrying streams, including multidimensional
coefficient streams for PDEs. `Predicate n` and `ExactHoare` currently cover the separate
`Point n` real feedforward interpretation. Algebraic checking in task 017 is
useful inside a system proof but cannot by itself describe that system's behavior.

Asgard already owns `Streams.Stream d`, `StreamPoint d n`, basis-tagged
`Streams.Circuit`, `Defined`, `value`, `Rel`, and named axis/port contexts.
This task adds the missing property calculus over those exact definitions.
It builds on the sequential Hoare rules in `Gimle/Forseti.lean` and blocks
the stream proof-transfer work in task 020.

## Contract

A precondition ranges over `StreamPoint d n`; a postcondition ranges over
`StreamPoint d m`. The port counts `n,m` and axis count `d` are independent.
For the existing deterministic partial stream interpreter, the total contract is

```text
∀ input, P input → c.Defined input ∧ Q (c.value input).
```

Prove its equivalence to existence of a related output plus satisfaction of `Q`
by every related output, using `Circuit.rel_iff`. Undefined substitution must
not make a total contract vacuously true. Predicates are ordinary Lean properties
of full streams; no claim of a decidable language for arbitrary stream predicates
is made. Keep OGF/EGF interpretation and ordered axes explicit in public claims.

## Outcome

- [x] Introduce stream predicate equality/entailment and a total Hoare judgment
      over Asgard's existing stream type and relation. Preserve the existing
      finite-dimensional API; do not rebuild Asgard's syntax or force all its
      interpretations through a new universal circuit abstraction.
- [x] Prove identity/routing, consequence, sequential and parallel rules with
      explicit intermediate predicates, port maps and common basis/axis context.
      Sequential composition means circuit wiring, not concatenation in time.
      Prove substitution by Asgard stream relational equivalence.
- [x] Supply reusable predicates for equality to a full stream, equality of a
      named-axis boundary slice, and equality on an explicitly finite coefficient
      window. Prove pointwise Boolean/product rules and explicit transport through
      existing axis reindexing. Window equality never implies full-stream equality.
- [x] Supply domain-aware derivative/integral and product contracts by reusing
      Asgard's laws. Integration retains the complete boundary profile along the
      selected axis; product uses the declared OGF/EGF algebra.
- [x] Restate `FormalHeat.circuit_behavior` as a total contract for the original
      compiled two-axis circuit, with arbitrary unused third input, boundary
      preservation, and outputs `[u_xx,u]`. Derive it by named reusable rules and
      existing identities rather than another handwritten interpreter.
- [x] Tests cover distinct port/axis counts, axes `[t,x]` and their transported
      permutation, OGF/EGF conversion, shared/unused ports, a changed boundary,
      equal prefixes with different tails, and a nonzero-constant substitution
      that stays undefined even when discarded or multiplied by zero.
- [x] `lake build` includes all new examples/regressions; an executable axiom
      audit accepts only `propext`, `Classical.choice`, `Quot.sound`. Core imports
      no Python or solver. Document the predicates, totality and composition rules
      with theorem references in `docs/properties.md`, distinguishing delivered
      judgments from planned extensions.

## Plan

1. Add a small property module importing the existing stream semantics; write
   the undefined-input and lost-boundary regressions before deriving rules.
2. Prove the total/relational characterization, then consequence and composition.
   Add boundary and finite-observation predicates without conflating them.
3. Package the two-axis heat fixture as a circuit-rooted contract; review the
   semantic binding and run the complete Lean gate.

## Scope

This is exact formal coefficient reasoning. Analytic realization is owned by
asgard-lean/024; certified tails by asgard-lean/025; continuous trajectories by
019. No norm, probability, analytic PDE existence, or numerical accuracy follows
from this contract. General feedback/trace for `Streams.Circuit` is not added.

## Conversation

### note · claude/88c9ba9a · 2026-09-26T16:29:54Z

Done in `Gimle/Forseti/Stream.lean`. `StreamHoare` is the total contract and
`streamHoare_iff_rel` its relational form. `heat_contract` is derived through
the general rules, ending in `integralFrom` and `eq_integral_of_boundary`, so its
precondition fixes only the boundary port's zero slice, a stronger contract than
Asgard's `circuit_behavior`. For 020: `both_equals` turns `pair` output into the
`Equals` points the operation contracts take, and `Window` with
`window_reindex` is the observation predicate asgard-lean 023's lowering will
need to meet. `NamedBoundary` is false for an unresolved name; resolve it with
`iff_boundary` before relying on a contract.
