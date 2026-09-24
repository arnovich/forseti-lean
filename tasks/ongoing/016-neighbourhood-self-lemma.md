---
title: Promote neighbourhood self-entailment to a named lemma
state: ongoing
priority: medium
labels: [lemmas, predicates, search]
claimed_by: claude-016
claimed_at: 2026-09-24T13:30:00Z
branch: feat/neighbourhood_self_lemma
---

# Promote neighbourhood self-entailment to a named lemma

## Context

Every predicate entails its own neighbourhood at any non-negative radius: each
point is its own witness, at distance zero. The proof is one line:

```lean
intro point hp
exact ⟨point, hp, fun _ => by simpa using h⟩
```

That fact already exists in this library, but only **inline**. It appears as an
anonymous term inside `canonicalSequential` in `Gimle/Forseti.lean`:

```lean
(fun point held => ⟨point, held, fun _ => by simpa using nonnegative⟩)
```

There is no named lemma for it. The syntactic layer does have one:
`Fattened.core_entails` in `Gimle/Forseti/Syntax.lean` states the same thing
for a `Fattened` node. The semantic `Neighbourhood` in `Gimle/Forseti.lean` has
no counterpart, and the semantic layer is where proofs, and the proof-search
agent, actually work.

The reusable goal is:

```lean
{n : Nat} (p : Predicate n) (r : ℝ) (h : 0 ≤ r) :
  PredicateEntailment p (Neighbourhood p r)
```

A named theorem makes this reusable by proofs and lemma-based search.
Retrieval-engine changes are outside this task.

## Outcome

- [ ] A named lemma in `Gimle/Forseti.lean`, stated over the semantic
      `Neighbourhood`: for `0 ≤ r`, `PredicateEntailment p (Neighbourhood p r)`.
- [ ] `canonicalSequential` uses the lemma instead of the inline term, so the
      fact is stated once.
- [ ] A docstring naming `Fattened.core_entails` as the syntactic counterpart,
      so the two layers point at each other.
- [ ] A test showing the lemma closes the goal above in one step.
- [ ] `lake build` green; the axiom report is within `propext`,
      `Classical.choice` and `Quot.sound`.

## Notes

This is the first concrete instance of a pattern worth watching for. Proofs in
this library contain small reusable facts written inline, where a search cannot
find them. Each one promoted to a named lemma is a goal that moves from
"unreachable by search" to "one `apply` away". When a proof-search run fails,
it's worth asking whether the missing step already exists as an anonymous term
somewhere.
