---
title: Check polynomial entailment certificates and rational counterexamples in Lean
state: closed
priority: medium
labels: [predicates, certificates, lean, solvers]
depends_on: ["015"]
---

# Check polynomial entailment certificates and rational counterexamples in Lean

## Context

`Syntax.lean` supplies formulas, interpretation and fattening; task 015 supplies
the ordered variable context. Neither gives an external solver's answer
mathematical authority.

This task supplies the Lean checking half of an exact entailment or rational
counterexample workflow. An external untrusted producer supplies candidates;
automatic discovery and orchestration are outside this task.

Reuse Asgard's `Polynomial.Expr`, `Syntax.Formula`, and the certificate/soundness
pattern in `LinearEnergy.lean` and `Examples/ProofSearchContract.lean`.

## Scope and mathematical contract

There are two evidence forms for the same independently supplied goal `P ⊨ Q`.
Both are finite exact data, never a solver status or a supplied proposition.

**Positive evidence:** restrict `P` and `Q` to `tru`, non-strict polynomial
inequalities and finite conjunctions of them. Normalize `ge` to `le` by exact
negation, with a proved interpretation-preserving extraction into ordered
lists `p_i ≤ 0` and `q_j ≤ 0`. `tru` is the empty conjunction. Preserve each
constraint's position; do not silently omit duplicate or unused constraints.
For every consequent require the coefficient identity

```text
−q_j = σ_j0 + Σ_i σ_ji · (−p_i)
σ = Σ_k w_k · g_k², with every w_k ∈ ℚ and w_k ≥ 0.
```

Each `g_k` is an exact rational polynomial over the goal's coordinates.
There is one explicit multiplier slot per antecedent, including zero sums,
and one identity per consequent. Recompute identities from the supplied goal;
checking sampled evaluations or trusting a supplied target polynomial is not
sufficient. This certificate family is sound but incomplete. No compactness,
strict positivity or completeness assumption is needed for its soundness.

**Negative evidence:** an exact rational point `r` with `P(r) ∧ ¬Q(r)`.
Support all constructors of the existing quantifier-free `Formula` in this
lane, including strict comparisons, equality, disjunction and negation.
Evaluate over ℚ and prove agreement with the existing real interpretation at
the coordinatewise cast of `r`. Refute the original entailment, not a failed
SOS identity. Algebraic non-rational points and `Fattened` are outside this lane.

Task 015's context fixes dimension and coordinate order at the public boundary.
The algebraic lemmas may stay indexed by `n`, but their checked applications
must use the exact formulas and context of the requested goal.

## Outcome

- [x] Finite certificate and rational-point data types, computable validity
      checks, and proved soundness theorems yielding respectively
      `FormulaEntailment P Q` and `¬ FormulaEntailment P Q`. A failed validity
      check rejects evidence; it establishes neither truth nor falsity of the goal.
- [x] A verified exact polynomial identity check, reusing mathlib polynomial
      machinery where practical. Its interpretation theorem connects coefficient
      equality to Asgard's existing `Polynomial.Expr.eval`; syntax-tree equality
      alone is insufficient for algebraically equal expressions.
- [x] A computable rational formula evaluator and its real-interpretation
      theorem, covering every existing formula constructor and boundary equality.
- [x] Public applications bind the expected ordered context, both original
      formulas, and complete evidence. Task 015's mapping is consumed rather
      than replaced by a second variable-context design.
- [x] Supplied exact certificates check for the unit-disk, quartic and box
      cases in the shared corpus below. Rational points check the two false
      claims. These are checker fixtures; automatic discovery belongs to the external producer.
- [x] An example converts the checked unit-disk entailment through
      `Formula.toPredicate` and uses `hoareConsequence` to weaken an identity
      circuit's postcondition. The resulting theorem names the original circuit.
- [x] Regression tests reject negative weights, a one-coefficient perturbation,
      missing/extra identities or multipliers, wrong dimensions, and evidence
      reused against a changed goal for which it is invalid. Equivalent algebraic
      expressions check successfully after normalization, as does altered
      redundant/zero-weight evidence whose identity remains valid. Include empty
      conjunctions, zero polynomials, redundant constraints and an empty domain.
- [x] New generic soundness theorems and concrete accepted examples use only
      `propext`, `Classical.choice` and `Quot.sound`; add an executable assertion
      of the transitive axiom policy, not just `#print axioms` output. No `sorry`,
      custom solver axioms or `native_decide` authority shortcut.
- [x] `lake build` checks the new modules, examples and regressions with no new
      warnings. Core checking imports no Python or external solver and
      works without any producer installed. Update `docs/properties.md`
      with the actual supported certificate fragment and a checked example.

## Shared acceptance corpus

All coordinates have an explicit ordered context. Expressions below are
mathematical notation for existing `Formula` values, not a new parser request.

| Goal | Evidence / expectation |
| --- | --- |
| `x² + y² ≤ 1 ⊨ x² ≤ 1 ∧ y² ≤ 1` | `1−x² = y² + (1−x²−y²)` and its symmetric identity |
| `x² ≤ 1 ⊨ x⁴ ≤ x²` | `x²−x⁴ = x²(1−x²)`, exercising a nonconstant multiplier |
| `−1 ≤ x ∧ x ≤ 1 ⊨ x ≤ 2` | `2−x = 1 + (1−x)`, with an explicit zero slot for the unused lower bound |
| `x² + y² ≤ 1 ⊨ x² + y² ≤ 1/2` | Refutation at `(1,0)` |
| `x ≤ 0 ⊨ y ≤ 0`, context `[x,y]` | Refutation at `(0,1)`; `(1,0)` must be rejected |

## Plan

1. Fix the small public evidence/checking interface for external producers;
   write rejection and interpretation tests before implementing each checker.
2. Implement rational evaluation and prove its cast theorem. Add exact
   polynomial normalization/identity checking and its evaluation theorem.
3. Prove nonnegativity of weighted squares, then the generic entailment
   soundness theorem. Derive the negative theorem from rational evaluation.
4. Instantiate the shared corpus and Hoare consequence example; assert the
   axiom policy and run the full build. Review mathematical correctness and
   hostile-evidence handling before the Python integration relies on it.

## Exclusions

No general CAD/SMT proof-log checker, SDP/SoS optimizer, quantifier elimination,
algebraic-number witness implementation, transcendental extension, or elimination
of metric fattening. No automatic sensitivity analysis or circuit translation.
No change to existing external release pins or checker import enrollment.

## Conversation

### note · claude/88c9ba9a · 2026-09-26T16:06:21Z

Done in `Gimle/Forseti/Syntax/Certificate.lean`, binding 015's `Goal` and
`Context.read`. The identity check uses a small computable sparse normal
form rather than Mathlib's `MvPolynomial`, which is noncomputable and so
cannot be decided in the kernel; `Sparse.eval_ofExpr` is its only trusted link
to `Polynomial.Expr.eval`. Evidence of the wrong dimension is unrepresentable
(certificates are indexed by the goal's context), pinned with
`#check_failure`. The axiom policy is asserted with `#guard_msgs`, verified to
fail the build on a mismatch. For gimle-forseti 111: evidence enters as
`EntailmentCertificate goal.context.dimension` or a named
`Context.Assignment`, and the external release pin must move to a revision
that contains 015 and 017 before 111 can replay them.
