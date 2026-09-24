# Standalone proof checker

[`Executables/Checker.lean`](../Executables/Checker.lean) checks compiled candidate
proofs against an independently supplied expected statement.

```sh
lake build Checker
.lake/build/bin/Checker IMPORTS CORE EXPECTED_DIR CANDIDATE_DIR ROOT_NAME
```

| Argument | Contents |
| --- | --- |
| `IMPORTS` | Merged directory containing the permitted dependency modules |
| `CORE` | Lean's core module directory |
| `EXPECTED_DIR` | Compiled `Expected.olean`, defining `forsetiExpected` |
| `CANDIDATE_DIR` | Compiled `Candidate.olean`, containing the proposed theorem |
| `ROOT_NAME` | Candidate-owned, monomorphic theorem to check |

## Enforced checks

- Explicit module search paths; no ambient `LEAN_PATH` or candidate environment extensions.
- Direct imports limited to `Gimle.Forseti` and `Init`.
- No unexpected import closure, shadowed declarations, unsafe/partial candidate declarations,
  or more than 10,000 candidate declarations.
- Candidate declarations replayed into the independent expected environment.
- Kernel checks the proof and equality with the original expected statement.
- Transitive axioms limited to `propext`, `Classical.choice`, and `Quot.sound`.

Success prints a sorted JSON array of used axioms and exits zero. Rejection exits nonzero.

## Scope

The caller must prepare trusted dependencies and the expected statement, and
compile untrusted candidate source in a **separate restricted process**. This
executable does not provide that orchestration or authenticate a supplied environment.

Building optional modules does not admit them to the checker. Dynamics and energy
certificates are checked by standalone Lean proofs; they are outside this import
interface. Enrollment in an external validator is a separate reviewed operation.

`#print axioms` elsewhere produces reports; it does not make `lake build` reject
forbidden axioms. The checker actively enforces its allowlist.
