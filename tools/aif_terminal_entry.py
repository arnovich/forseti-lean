#!/usr/bin/env python3
"""Emit exact local-entry checks for the eight candidate terminal mesh cells."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Reuse the candidate mesh directly; kernel checking supplies authority."""
    outputs = {"AIFTerminalEnergy.lean": """import Gimle.Forseti.Examples.AIFLocalEntry

/-! Rational evaluation is bound exactly to the already proved real quadratic. -/
namespace Gimle.Forseti.Examples.AIFTerminalEnergy
open AIFLocalEntry AIFLocalStability

def rationalValue (x : Fin 4 → ℚ) : ℚ :=
  (11399/50000)*x 0*x 0+(8053/25000)*x 0*x 1+(-6353/50000)*x 0*x 2+
  (19/2500)*x 0*x 3+(32597/100000)*x 1*x 1+(-3073/6250)*x 1*x 2+
  (-19/10000)*x 1*x 3+(19513/50000)*x 2*x 2+(-13/625)*x 2*x 3+
  (5579/100000)*x 3*x 3

theorem rational_binding (x : Fin 4 → ℚ) :
    (rationalValue x : ℝ) = value (fun i => (x i : ℝ)) := by
  simp [rationalValue,value,energy]

theorem real_bound (x : Fin 4 → ℚ) (h : rationalValue x ≤ 1/400) :
    value (fun i => (x i : ℝ)) ≤ 1/400 := by
  rw [← rational_binding]
  have hc : (rationalValue x : ℝ) ≤ ((1/400 : ℚ) : ℝ) := Rat.cast_le.mpr h
  norm_num at hc ⊢
  exact hc

#print axioms rational_binding
#print axioms real_bound
end Gimle.Forseti.Examples.AIFTerminalEnergy
"""}
    for b in range(8):
        name = f"AIFTerminalEntryBin{b}"
        outputs[name + ".lean"] = f"""import Gimle.Forseti.Examples.AIFCandidateMesh
import Gimle.Forseti.Examples.AIFTerminalEnergy
import Gimle.Forseti.RationalLDL

/-! Terminal entry for candidate bin {b}, slab369, with exact checked premises.
This does not assert that a zero-start trajectory reaches this terminal tube. -/
namespace Gimle.Forseti.Examples.{name}
open Gimle.Forseti.LinearEnergy AIFLocalEntry AIFTerminalEnergy

noncomputable def slab : AIFSlabModel.Slab := AIFCandidateMesh.mesh.slab {b} 369
noncomputable def certificate : WeightedSquares 4 :=
  Gimle.Forseti.RationalLDL.propose (coercivityMargin slab.endMetric)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem valid : certificate.Represents (coercivityMargin slab.endMetric) := by
  unfold WeightedSquares.Represents
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem lo_bound : rationalValue slab.loEnd ≤ 1/400 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem hi_bound : rationalValue slab.hiEnd ≤ 1/400 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem end_time : slab.tStart+slab.step=30 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem step_nonzero : slab.step ≠ 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem eta_order : slab.etaLo < slab.etaHi := by decide +kernel

/-- Membership in this exact candidate mesh cell at time30 implies local entry. -/
theorem entry_at_thirty (eta : ℝ)
    (heta : eta ∈ Set.Icc ((AIFCandidateMesh.mesh.slab {b} 369).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab {b} 369).etaHi : ℝ))
    (x : Fin 4 → ℝ)
    (tube : AIFMesh.tubeEnergy (AIFCandidateMesh.mesh.slab {b} 369) 30 eta x ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  have ht : (slab.tStart : ℝ)+slab.step=30 := by exact_mod_cast end_time
  apply terminal_entry_physical slab step_nonzero eta_order certificate valid
    (real_bound _ lo_bound) (real_bound _ hi_bound) eta heta x
  rw [ht]
  simpa only [slab] using tube

#print axioms valid
#print axioms lo_bound
#print axioms hi_bound
#print axioms end_time
#print axioms step_nonzero
#print axioms eta_order
#print axioms entry_at_thirty
end Gimle.Forseti.Examples.{name}
"""
    return outputs


def main() -> None:
    """Write all terminal companions, or check bytes without modifying evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = generate()
    if not args.check:
        args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, source in outputs.items():
        path = args.output_directory / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
