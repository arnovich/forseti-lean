# Forseti Lean

Forseti is a property language and proof system for dynamical systems, written in
Lean 4. Systems are given as [Asgard](https://github.com/arnovich/asgard-lean)
circuits: Asgard compiles ODEs, PDEs, difference equations and formal power series
into circuits with exact real semantics. Forseti states what such a system does and
proves it.

- **Properties:** predicates on real states, a polynomial formula syntax over
  named coordinates, and entailment between formulas.
- **Judgments:** each comes with rules for composition, wiring, feedback traces,
  and transport along equivalence and certified approximation. The judgments are:
  - exact and quantitative Hoare triples for circuits;
  - total contracts over continuous trajectories and formal coefficient streams;
  - invariants for discrete iteration.
- **Certificates:** exact evidence that Lean checks, whether a solver, a search
  or a person found it. The kinds are:
  - sum-of-squares and Positivstellensatz entailment certificates;
  - rational and algebraic counterexamples;
  - energy and trapping certificates for safety over all forward time;
  - Bernstein matrix certificates.
- **Checker:** a standalone executable that checks a compiled candidate proof
  against an expected statement under a fixed import and axiom policy.

Every result is a kernel-checked theorem using only `propext`, `Classical.choice`
and `Quot.sound`. Simulation never counts as evidence.

Public showcase, licensed under [MIT](LICENSE). External pull requests are not accepted.

## Build

Install [elan](https://github.com/leanprover/elan), then:

```sh
lake exe cache get
lake build
```

Lean, Asgard, and mathlib are pinned. The build checks the library, examples,
regression proofs, and checker.

## Explore

Open an example in VS Code with the Lean 4 extension. Each module's header
states what it proves and what it does not.

| Example | What it proves |
| --- | --- |
| [Energy](Gimle/Forseti/Examples/EnergyDemo.lean) | Sharp bounds for an exact circuit |
| [Compiled equations](Gimle/Forseti/Examples/EquationWorkflow.lean) | Properties of circuits produced by Asgard's equation compiler |
| [Three-state model](Gimle/Forseti/Examples/ThreeState.lean) | Forward existence, uniqueness, and the energy bound `0 ≤ V ≤ 6` |
| [Damped oscillator](Gimle/Forseti/Examples/DampedOscillatorContract.lean) | `0 ≤ 2x² + v² ≤ 2` for `x'' + 3x' + 2x = 0`, from an exact energy certificate |
| [Forced decay](Gimle/Forseti/Examples/ForcedDecayContract.lean) | `\|x\| ≤ 2` for the driven `x' + x = u' + u` under `\|u\| ≤ 1` |
| [Hedged spread](Gimle/Forseti/Examples/HedgedSpreadContract.lean) | `\|s\| ≤ B` for the driven `s' = -s - h + d`, `h' = s - h` from `s(0) = h(0) = 0` under every continuous `\|d\| ≤ B`, from the invariant `s² + h² ≤ B²` |
| [Harmonic oscillator](Gimle/Forseti/Examples/HarmonicOscillator.lean) | A conserved energy, through the generic [`LinearEnergyContract`](Gimle/Forseti/LinearEnergyContract.lean) |
| [Lorenz](Gimle/Forseti/Examples/Lorenz.lean) | A trapping region for all forward time, by the general nonlinear theorem in [`Nonlinear.lean`](Gimle/Forseti/Nonlinear.lean) |
| [Galerkin Navier–Stokes](Gimle/Forseti/GalerkinNS/Family.lean) | Energy and enstrophy trapping for every cosine Galerkin truncation of 2D Navier–Stokes, and laminar attraction under small forcing; [members](Gimle/Forseti/Examples/GalerkinNS/) |
| [Below the laminar level](Gimle/Forseti/Examples/GalerkinNS/T3Below12.lean) | Trapping with a decrease local to the set ([`LocalTrapping`](Gimle/Forseti/LocalTrapping.lean), [`PolynomialTrapping`](Gimle/Forseti/PolynomialTrapping.lean)) |
| [Disturbed feedback](Gimle/Forseti/Examples/DisturbedFeedback.lean) | Component storage identities composed through a trace give `\|x(t)\| ≤ 1` under bounded disturbances |
| [Active suspension](Gimle/Forseti/Examples/ActiveSuspension.lean) | Travel, force and acceleration bounds through nested traces, shared by two actuators |
| [AIF drift box](Gimle/Forseti/Examples/AIFDriftPilot.lean) | Bernstein matrix certificates for one box of an antithetic integral feedback drift bound |
| [AIF global solution](Gimle/Forseti/Examples/AIFGlobalSolution.lean) | Existence, forward uniqueness and nonnegativity for `x₁' = z₁ − x₁`, `x₂' = x₁ − x₂`, `z₁' = 2 − η z₁ z₂`, `z₂' = x₂ − η z₁ z₂` from zero, for every fixed `η ≥ 0` |
| [AIF circuit binding](Gimle/Forseti/Examples/AIFCircuitBinding.lean) | The compiled Asgard AIF feedback's realizations are exactly the zero-start solutions of the [AIF ODE](Gimle/Forseti/Examples/AIFGlobalSolution.lean), so for every fixed `η ≥ 0` they exist, agree for `t ≥ 0` and stay nonnegative; its observation reads `x₂`, and `x₂ ≤ 16/5` equals `y₂ ≤ 6/5` in equilibrium-shifted coordinates (no tube or upper output bound claimed) |
| [AIF tube composition](Gimle/Forseti/Examples/AIFMeshComposition.lean) | A moving-tube energy bound carried across a time mesh with exact joins, given a drift bound on every cell, which [per-cell certificates](Gimle/Forseti/Examples/AIFSlabDrift.lean) can discharge (certificates for one cell only) |
| [AIF certified cell](Gimle/Forseti/Examples/AIFCertifiedCell.lean) | For every fixed `η ∈ [8, 17/2]`, the zero-start solution keeps its moving-tube energy `≤ 1/40000` on `t ∈ [0, 1/200]`, with the drift bound discharged by [checked certificates](Gimle/Forseti/Examples/AIFSlabDrift.lean); this encloses only the error coordinate `e₂` (one cell only; no later time or output bound) |
| [AIF local stability](Gimle/Forseti/Examples/AIFLocalStability.lean) | A certified local Lyapunov region giving `x₂ ≤ 5/2` for `η ∈ [8, 12]` once a trajectory [enters](Gimle/Forseti/Examples/AIFLocalEntry.lean) it |
| [Approximation](Gimle/Forseti/Examples/CircuitApproximation.lean) | Property transport with an explicit certified error |
| [Certificate checking](Gimle/Forseti/Examples/ProofSearchContract.lean) | Exact validity conditions for proposed linear-energy certificates |
| [Mild vorticity contracts](Gimle/Forseti/MildVorticity.lean) | Total Hoare contracts for Asgard's mild vorticity circuit |
| [Classical vorticity uniqueness](Gimle/Forseti/ClassicalVorticity/Uniqueness.lean) | Uniqueness among independent periodic classical solutions, [applied](Gimle/Forseti/Examples/ClassicalNavierStokes.lean) to a three-mode start |
| [Euler contracts](Gimle/Forseti/Euler.lean) | Classical Euler solutions from the Fourier feedback circuit; [example](Gimle/Forseti/Examples/EulerContract.lean) |
| [Stream observations](Gimle/Forseti/Examples/StreamObservation.lean) | Polynomial certificates lifted to total contracts over a formal heat circuit |
| [Heat field bound](Gimle/Forseti/Examples/HeatFieldBound.lean) | Bounds on the heat circuit's evaluated field, proved and refuted |
| [Algebraic counterexamples](Gimle/Forseti/Examples/AlgebraicCounterexamples.lean) | Entailments refuted only at irrational points, such as `x² = 2 ⊨ x < 0` |
| [Positivstellensatz certificates](Gimle/Forseti/Examples/PositivstellensatzCertificates.lean) | Entailments that need a product of constraints, such as `x ≥ 0 ∧ y ≥ 0 ⊨ x·y ≥ 0` |

Check one directly with `lake env lean Gimle/Forseti/Examples/EnergyDemo.lean`.

## Checker

[`Checker`](Executables/Checker.lean) checks a compiled candidate proof against an
independently compiled expected statement, without running candidate code:

```sh
lake build Checker
.lake/build/bin/Checker IMPORTS CORE EXPECTED_DIR CANDIDATE_DIR ROOT_NAME
```

`IMPORTS` holds the permitted dependency modules, `CORE` Lean's core modules,
`EXPECTED_DIR` an `Expected.olean` defining `forsetiExpected`, and
`CANDIDATE_DIR` a `Candidate.olean` containing the theorem `ROOT_NAME`. Direct
imports are limited to `Gimle.Forseti` and `Init`; candidate declarations are
replayed into the expected environment; the kernel checks the proof against the
expected statement; and transitive axioms are limited to `propext`,
`Classical.choice` and `Quot.sound`. Success prints the used axioms as JSON and
exits zero. Compiling untrusted source in a restricted process is the caller's job.
