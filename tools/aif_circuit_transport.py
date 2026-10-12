#!/usr/bin/env python3
"""Emit the research binding between archived AIF circuit and tube proof layers."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Emit proof source; successful Lean replay is required for proof authority."""
    source = """import Gimle.Asgard.Examples.AIF
import Gimle.Forseti.Examples.AIFPhysicalCoordinates

/-! Research binding of the original compiled AIF feedback to the tube model.
All trajectory statements remain conditional on an actual circuit realization.
No existence, complete certificate coverage or output safety is asserted. -/
namespace Gimle.Forseti.Examples.AIFCircuitTransport
open Gimle.Asgard AIFPhysicalCoordinates

/-- No independently generated substitute field is used in the feedback. -/
theorem compiled_field (eta : ℝ) (x : Point 4) :
    Gimle.Asgard.Examples.AIF.field.run (pointAppend ![eta] x) = physicalField eta x :=
  Gimle.Asgard.Examples.AIF.field_appended eta x

/-- The original feedback's zero initialization and component ODEs. -/
theorem realizes_iff_physical (eta : ℝ) (state : Dynamics.Signal 4) :
    Gimle.Asgard.Examples.AIF.Realizes eta state ↔ state 0 = 0 ∧
      ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
        HasDerivWithinAt (fun s => state s i)
          (physicalField eta (state t) i) (Set.Ici 0) t :=
  Gimle.Asgard.Examples.AIF.realizes_iff eta state

theorem shifted_initial (eta : ℝ) (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    shift eta (state 0) = ![-2,-2,-2,-1] := by
  rw [((realizes_iff_physical eta state).mp realized).1]
  exact shift_zero eta

/-- The closed-interval derivative interface used by local tube invariance. -/
theorem shifted_derivative_on (eta : ℝ) (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (a b : ℝ) (ha : 0 ≤ a) (t : ℝ) (ht : t ∈ Set.Icc a b) (i : Fin 4) :
    HasDerivWithinAt (fun s => shift eta (state s) i)
      (AIFDriftModel.field eta (shift eta (state t)) i) (Set.Icc a b) t := by
  have hx := ((realizes_iff_physical eta state).mp realized).2 t (ha.trans ht.1)
  exact (shift_derivative eta state (Set.Ici 0) t hx i).mono
    (fun _ hs => ha.trans hs.1)

/-- The moving-energy derivative is now for a realization of the compiled circuit. -/
theorem compiled_energy_derivative (d : AIFSlabModel.Slab)
    (hh : d.step ≠ 0) (hp : d.etaLo < d.etaHi) (eta : ℝ)
    (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => AIFMesh.tubeEnergy d s eta (shift eta (state s)))
      (AIFSlabModel.energyRate d (AIFSlabModel.timeCoordinate d t)
        (AIFSlabModel.etaCoordinate d eta)
        (shift eta (state t) - AIFSlabModel.center d (AIFSlabModel.timeCoordinate d t)
          (AIFSlabModel.etaCoordinate d eta))) (Set.Ici 0) t :=
  physical_tubeEnergy_derivative d hh hp eta state (Set.Ici 0) t
    (((realizes_iff_physical eta state).mp realized).2 t ht)

/-- The safety threshold refers to the actual compiled physical x2 observation. -/
theorem compiled_output_bound_iff (eta : ℝ) (x : Point 4) :
    Gimle.Asgard.Examples.AIF.output.run x 0 ≤ 16/5 ↔ shift eta x 1 ≤ 6/5 := by
  rw [Gimle.Asgard.Examples.AIF.output_correct]
  exact output_bound_iff eta x

#print axioms compiled_field
#print axioms realizes_iff_physical
#print axioms shifted_initial
#print axioms shifted_derivative_on
#print axioms compiled_energy_derivative
#print axioms compiled_output_bound_iff
end Gimle.Forseti.Examples.AIFCircuitTransport
"""
    return {"AIFCircuitTransport.lean": source}


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
