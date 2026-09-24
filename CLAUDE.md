# Forseti Lean development

Use a feature branch and worktree. Forseti owns predicates, Hoare rules, property
proofs, and the checker. Import circuit syntax and semantics from pinned Asgard;
do not duplicate them. Keep Python execution and proof search outside core imports.

Preserve exact coefficients, explicit assumptions, and the checker's import and
transitive-axiom policies. Never add `sorry`, unchecked axioms, or treat simulation
as mathematical authority. Building optional modules does not admit them to the
checker. External consumers must enroll any changed checking environment separately.

Run `lake build` for all libraries, examples, regression proofs, and `Checker`.
Run `lake build equation_demo` to compile the optional simulation entry point.
Inspect axiom reports: only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Review substantial changes for mathematical correctness and integration.

Keep executable roots under `Executables/` and generated output under ignored
`.lake/`. Keep docs short; link to checked examples for details.
Preserve task IDs and the owner's `next:` fields. Keep task states aligned with
`tasks/open/`, `tasks/ongoing/`, and `tasks/closed/`.
Commit only explicitly selected files after review and checks.

This is a public showcase; external pull requests are not accepted.
