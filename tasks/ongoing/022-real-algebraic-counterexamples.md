---
title: Check real-algebraic counterexamples to formula entailments
state: ongoing
claimed_by: claude-022
claimed_at: 2026-09-27T18:46:08Z
branch: feat/real_algebraic_counterexamples
priority: low
labels: [predicates, counterexamples, algebraic-numbers]
depends_on: ["017"]
---

# Check real-algebraic counterexamples to formula entailments

## Context

Task 017 checks rational counterexamples (`refutes`, `refutes_sound`). Some
false entailments have none: `x² = 2 ⊨ x < 0` fails only at `±√2`.
gimle-forseti task 033 wants to refute them with an exact, Lean-checked
real-algebraic point, never a rounded one. The producer (Z3) is untrusted; this
task is the checked half.

## Outcome

- [ ] An algebraic witness is a box of rational intervals, one per coordinate,
      each coordinate with a univariate polynomial. The checker proves, by the
      intermediate value theorem, that each polynomial has a root in its
      interval, and by an enclosure of its derivative that excludes zero,
      that the root is the only one there. A wrong interval, an interval with
      two roots and a double root are rejected.
- [ ] Every atom of the goal's antecedent and consequent is decided at the
      point by sound interval enclosure over the box (strict signs), or, for
      a zero, by a checked polynomial identity `q = Σ sᵢ · pᵢ(xᵢ)`. Nothing
      the producer claims about signs is trusted.
- [ ] `algebraicRefutes goal witness = true → ¬ goal.Entailment`, with only
      `propext`, `Classical.choice` and `Quot.sound`.
- [ ] Tests: `x² = 2 ⊨ x < 0` refuted at `√2`; a negative root; shared and
      independent algebraic coordinates; equality on the boundary; rational
      coordinates as degenerate intervals; and each hostile case above
      rejected by `decide`.

## Notes

Consumed by gimle-forseti task 033 through a pinned release.
