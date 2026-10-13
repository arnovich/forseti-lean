"""Generate compiled AIF existence, uniqueness, nonnegativity and startup safety proofs."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Bind the global physical solution to the checked original circuit context."""
    source = """import Gimle.Forseti.Examples.AIFGlobalSolution
import Gimle.Forseti.Examples.AIFStartupOutput

/-! Existence, forward uniqueness and nonnegativity of the actual compiled AIF
feedback, with output safety on the already certified startup prefixes. -/
namespace Gimle.Forseti.Examples.AIFCircuitSolution
open Gimle.Asgard

/-- The constructed original physical trajectory realizes the source-compiled feedback. -/
theorem solution_realizes (eta : ℝ) (heta : 0 ≤ eta) :
    Gimle.Asgard.Examples.AIF.Realizes eta (AIFGlobalSolution.solution eta heta) :=
  (AIFCircuitTransport.realizes_iff_physical eta _).mpr
    ⟨AIFGlobalSolution.solution_start eta heta, AIFGlobalSolution.solution_derivative eta heta⟩

theorem exists_realization (eta : ℝ) (heta : 0 ≤ eta) :
    ∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state :=
  ⟨AIFGlobalSolution.solution eta heta, solution_realizes eta heta⟩

/-- Every pair of original feedback realizations agrees on the full forward domain. -/
theorem realization_unique (eta : ℝ) (heta : 0 ≤ eta) (x y : Dynamics.Signal 4)
    (hx : Gimle.Asgard.Examples.AIF.Realizes eta x)
    (hy : Gimle.Asgard.Examples.AIF.Realizes eta y) : Set.EqOn x y (Set.Ici 0) := by
  have px := (AIFCircuitTransport.realizes_iff_physical eta x).mp hx
  have py := (AIFCircuitTransport.realizes_iff_physical eta y).mp hy
  intro t ht
  exact (AIFGlobalSolution.solution_unique eta heta x px.1 px.2 ht).trans
    (AIFGlobalSolution.solution_unique eta heta y py.1 py.2 ht).symm

theorem realization_nonnegative (eta : ℝ) (heta : 0 ≤ eta)
    (state : Dynamics.Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 4) : 0 ≤ state t i := by
  have physical := (AIFCircuitTransport.realizes_iff_physical eta state).mp realized
  have eq := AIFGlobalSolution.solution_unique eta heta state physical.1 physical.2 ht
  rw [eq]
  exact AIFGlobalSolution.solution_nonnegative eta heta t ht i

/-- The compiled observation reads a nonnegative physical species. -/
theorem realization_output_nonnegative (eta : ℝ) (heta : 0 ≤ eta)
    (state : Dynamics.Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 := by
  rw [Gimle.Asgard.Examples.AIF.output_correct]
  exact realization_nonnegative eta heta state realized t ht 1

/-- Nonempty original feedback behavior and universal output safety on the checked
all-parameter startup interval. This does not extend the certificate coverage. -/
theorem startup_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    (∀ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) (1/200),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5) := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨exists_realization eta heta, ?_⟩
  intro state realized t ht
  exact ⟨realization_output_nonnegative eta heta state realized t ht.1,
    AIFStartupOutput.all_parameter_output eta hp state realized t ht⟩

/-- The same nonempty universal safety statement for the longer checked bin-zero prefix. -/
theorem bin0_safety (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) (17/2)) :
    (∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    (∀ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5) := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨exists_realization eta heta, ?_⟩
  intro state realized t ht
  exact ⟨realization_output_nonnegative eta heta state realized t ht.1,
    AIFStartupOutput.bin0_prefix_output eta hp state realized t ht⟩

#print axioms solution_realizes
#print axioms exists_realization
#print axioms realization_unique
#print axioms realization_nonnegative
#print axioms realization_output_nonnegative
#print axioms startup_safety
#print axioms bin0_safety
end Gimle.Forseti.Examples.AIFCircuitSolution
"""
    return {"AIFCircuitSolution.lean": source}


def main() -> None:
    """Write the binding source, or compare it without changing any file."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.check:
        args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, source in generate().items():
        path = args.output_directory / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
