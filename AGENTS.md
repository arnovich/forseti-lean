# Forseti Lean development

Use a feature branch and worktree. Forseti owns predicates, Hoare rules, property
proofs, and the checker. Import circuit syntax and semantics from pinned Asgard;
do not duplicate them. Keep Python, simulation and proof search out of this repository;
files marked generated come from an external exact search and are not edited by hand.

Preserve exact coefficients, explicit assumptions, and the checker's import and
transitive-axiom policies. Never add `sorry`, unchecked axioms, or treat simulation
as mathematical authority. Building optional modules does not admit them to the
checker. External consumers must enroll any changed checking environment separately.

Run `lake build` for all libraries, examples, regression proofs, and `Checker`.
Inspect axiom reports: only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Review substantial changes for mathematical correctness and integration.

Keep executable roots under `Executables/` and generated output under ignored
`.lake/`. There is no separate docs folder: explain each result in its module header
and keep the README to a short index.
Commit only explicitly selected files after review and checks.

This is a public showcase; external pull requests are not accepted. It must stand
on its own: never mention internal repositories, research, task or PR numbers,
people, or paths outside this repository in sources, the README or commit messages.
