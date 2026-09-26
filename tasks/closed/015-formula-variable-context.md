---
title: Give formulas an ordered variable context
state: closed
priority: medium
labels: [predicates, foundations, solvers]
---

# Give formulas an ordered variable context

## Context

`Formula` in `Gimle/Forseti/Syntax.lean` has no ordered variable context.
Dimensions are a bare `Nat` and coordinates are `Fin n`, with no names.

Why it matters, concretely. The point of the syntax is that a formula can be
handed to a decision procedure and an answer read back. With positional
coordinates only:

- A solver's `sat` model comes back keyed by *its* variable names. Matching those
  to `Fin n` positions is an unchecked convention held in the caller's head.
- `Formula.product` composes two blocks by renaming into `Fin.castAdd` and
  `Fin.natAdd` positions. After a couple of products, which original variable a
  position refers to is recoverable only by re-deriving the nesting.
- Nothing distinguishes a formula over `[x, y]` from the same shape over
  `[y, x]`, so two formulas about different things can be `DecidableEq`-equal.

An ordered coordinate context must determine the dimension and the mapping
between formula coordinates and solver variable names.

## Outcome

- [x] Formulas carry an ordered context of named coordinates, with the dimension
  derived from it rather than supplied independently.
- [x] `Formula.product` composes contexts, and the resulting context records
  which original coordinate each position came from.
- [x] Two formulas of the same shape over different contexts are distinguishable;
  state and test what equality means in the presence of contexts.
- [x] A stated, tested round trip: a formula's coordinates can be named, sent,
  and an answer matched back to the right coordinates without an unchecked
  convention in the caller.
- [x] Naming collisions, empty contexts and context/dimension mismatch are
  rejected at construction with explicit errors.
- [x] Existing `Syntax.lean` theorems and `Tests/Syntax.lean` continue to hold;
  `lake build` green and the axiom audit reports only `propext`,
  `Classical.choice` and `Quot.sound`.

## Notes

Consider whether the context belongs on the type (`Formula ctx`) or beside it in
a wrapper that pairs a `Formula n` with an `n`-vector of names. The wrapper is
less invasive and keeps `DecidableEq` derivable on the bare formula; the indexed
version makes mismatches unrepresentable. A non-uniform index
can prevent deriving eliminators and decidable equality; preserve those capabilities.

## Conversation

### note · claude/88c9ba9a · 2026-09-26T15:57:16Z

Done as a wrapper, per the Notes: `Gimle/Forseti/Syntax/Context.lean` adds
`Context` (ordered, distinct, non-empty names; the dimension is their count),
`NamedFormula`, name-checked products, `Context.read` with `read_mem` and
`read_assign`, `Context.var` for writing coordinates by name, and `Goal`,
both sides of an entailment over one context, which 017 should bind rather than
pairing contexts a second way. Numerals on `Fin c.dimension` are deliberately
not given an instance: they would wrap modulo the dimension.
