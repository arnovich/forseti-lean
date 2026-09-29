---
title: Check degree-2 Positivstellensatz certificates with constraint products
state: closed
priority: medium
labels: [predicates, certificates, entailment]
related: ["017", "gimle-forseti/034", "gimle-forseti/145"]
---

## Context

`Syntax.Certificate` (017) checks `P ⊨ Q` from `−q = σ₀ + Σᵢ σᵢ·(−pᵢ)`, a
quadratic-module identity in which every antecedent constraint is used alone.
`x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0` has no such identity at any degree.

gimle-forseti 034 compared solver proof logs (Z3, cvc5 CPC), exact QE and
widened certificates on 111's corpus, and selected a degree-2
Positivstellensatz. The certificate names pairs `(i, j)` of antecedent
constraints and gives ordinary rows against the antecedent augmented with
`−(pᵢ·pⱼ) ≤ 0`. Soundness reuses `Row.check_sound` and adds one lemma: a
product of two nonpositive reals is nonnegative.

A prototype checks independently against v1.4.0:
`gimle-forseti/benchmarks/nonlinear-certificates/PsatzPrototype.lean`. Its
four examples are the unit disk, `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0`,
`x ≥ 1 ∧ y ≥ 1 ⊨ x·y ≥ 1`, and `x² ≤ 1 ∧ y² ≤ 1 ⊨ x·y ≤ 1`.

## Outcome

- [x] `Syntax.Psatz` (or an extension of `Syntax.Certificate`) defines the
      certificate (`pairs`, `rows`), the augmented constraint list,
      `PsatzCertificate.check goal` as a `Bool`, and
      `PsatzCertificate.sound : check = true → goal.Entailment`. The
      soundness proof adds only the product lemma to 017's.
- [x] Every 017 certificate is a Psatz certificate with no pairs, with a
      theorem relating the two checks, so existing artifacts keep their meaning.
- [x] Examples: the four prototype goals by `decide +kernel`. Hostile tests:
      a dropped product, a pair out of range (which only weakens, never proves
      a false goal), a negative weight, a wrong identity, and a strict or
      disequality goal (outside the fragment, rejected).
- [x] `#guard_msgs` axiom audits of the checker and soundness theorems
      (only propext, Classical.choice, Quot.sound). `lake build` is clean, and
      `docs/properties.md` states the rule.
- [x] No release tag. gimle-forseti 145 consumes it through a batched release.
