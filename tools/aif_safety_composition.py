"""Generate the conditional end-to-end AIF safety composition."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Compose exact terminal entry with explicit complete startup certificate obligations."""
    source = """import Gimle.Forseti.Examples.AIFCircuitSolution
import Gimle.Forseti.Examples.AIFTerminalEntryBin0
import Gimle.Forseti.Examples.AIFTerminalEntryBin1
import Gimle.Forseti.Examples.AIFTerminalEntryBin2
import Gimle.Forseti.Examples.AIFTerminalEntryBin3
import Gimle.Forseti.Examples.AIFTerminalEntryBin4
import Gimle.Forseti.Examples.AIFTerminalEntryBin5
import Gimle.Forseti.Examples.AIFTerminalEntryBin6
import Gimle.Forseti.Examples.AIFTerminalEntryBin7

/-! End-to-end safety composition with explicit complete certificate obligations.
The required all-cell drift and output families have not yet been supplied. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Gimle.Forseti.Examples.AIFSafetyComposition
open AIFMesh AIFSlabModel AIFPhysicalCoordinates AIFLocalEntry

/-- Output enclosure obligation for one exact candidate cell. -/
def CellOutput (b : Fin 8) (i : Fin 370) : Prop :=
  ∀ t eta (x : Fin 4 → ℝ),
    t ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b i).tStart : ℝ)
      (((AIFCandidateMesh.mesh.slab b i).tStart : ℝ)+(AIFCandidateMesh.mesh.slab b i).step) →
    eta ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b i).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab b i).etaHi : ℝ) →
    tubeEnergy (AIFCandidateMesh.mesh.slab b i) t eta x ≤ 1/40000 → x 1 ≤ 6/5

theorem full_prefix : AIFStartupPrefix.prefixMesh 370 (by decide)=AIFCandidateMesh.mesh := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem terminal_time : AIFCandidateMesh.mesh.times 370=30 := by decide +kernel

/-- The eight independently checked terminal certificates cover every bin. -/
theorem terminal_entry (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc ((AIFCandidateMesh.mesh.slab b 369).etaLo : ℝ)
      ((AIFCandidateMesh.mesh.slab b 369).etaHi : ℝ))
    (x : Fin 4 → ℝ)
    (tube : tubeEnergy (AIFCandidateMesh.mesh.slab b 369) 30 eta x ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  fin_cases b
  · exact AIFTerminalEntryBin0.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin1.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin2.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin3.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin4.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin5.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin6.entry_at_thirty eta hp x tube
  · exact AIFTerminalEntryBin7.entry_at_thirty eta hp x tube

/-- Every startup cell needs a checked drift result before full propagation applies. -/
theorem startup_membership
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (AIFCandidateMesh.mesh.edges b.castSucc : ℝ)
      (AIFCandidateMesh.mesh.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    ∀ i, ∀ t ∈ Set.Icc (AIFCandidateMesh.mesh.times i.castSucc : ℝ)
      (AIFCandidateMesh.mesh.times i.succ : ℝ),
      tubeEnergy (AIFCandidateMesh.mesh.slab b i) t eta (shift eta (state t)) ≤ 1/40000 := by
  have h := AIFStartupPrefix.prefix_invariant 369 (by decide) b eta hp state realized
    (fun i => drift b i)
  simpa only [full_prefix] using! h

/-- Complete startup drift certification supplies the terminal membership premise. -/
theorem local_entry_of_startup
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (b : Fin 8) (eta : ℝ)
    (hp : eta ∈ Set.Icc (AIFCandidateMesh.mesh.edges b.castSucc : ℝ)
      (AIFCandidateMesh.mesh.edges b.succ : ℝ))
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    value (shift eta (state 30)) < 1/100 := by
  apply (terminal_entry b eta hp (shift eta (state 30)) _).2
  apply startup_membership drift b eta hp state realized 369 30
  have hq := AIFMeshGeometry.time_positive 369
  change AIFCandidateMesh.mesh.times 369 < AIFCandidateMesh.mesh.times 370 at hq
  rw [terminal_time] at hq
  change (AIFCandidateMesh.mesh.times 369 : ℝ) ≤ 30 ∧ 30 ≤ (AIFCandidateMesh.mesh.times 370 : ℝ)
  constructor
  · exact_mod_cast (le_of_lt hq)
  · rw [terminal_time]
    norm_num

/-- Actual compiled output stays below 5/2 after certified local entry. -/
theorem output_after_entry (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (entry : value (shift eta (state 30)) ≤ 1/100)
    (t : ℝ) (ht : 30 ≤ t) : Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2 := by
  have physical := (AIFCircuitTransport.realizes_iff_physical eta state).mp realized
  have hsubset : Set.Icc (30 : ℝ) t ⊆ Set.Ici 0 := by
    intro z hz
    change 0 ≤ z
    linarith [hz.1]
  have h := AIFLocalStability.physical_output_bound eta hp state 30 t
    (fun s hs i => (physical.2 s (hsubset hs) i).mono hsubset) entry t ⟨ht,le_rfl⟩
  rw [Gimle.Asgard.Examples.AIF.output_correct]
  exact h

/-- Sharp startup output requires both complete drift and output certificate families. -/
theorem startup_output
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (output : ∀ b i, CellOutput b i)
    (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 30) :
    Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5 := by
  obtain ⟨b,i,hti,hpi⟩ := AIFCandidateMesh.covers t eta ht hp
  apply (AIFCircuitTransport.compiled_output_bound_iff eta (state t)).mpr
  apply output b i t eta (shift eta (state t)) hti hpi
  apply startup_membership drift b eta hpi state realized i t
  simpa only [Mesh.slab,Rat.cast_sub,add_sub_cancel] using hti

/-- After startup, all future times are covered by the local invariant region. -/
theorem later_output
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (state : Gimle.Asgard.Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 30 ≤ t) : Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 5/2 := by
  obtain ⟨b,_,_,hb⟩ := AIFCandidateMesh.covers 30 eta (by norm_num) hp
  exact output_after_entry eta hp state realized
    (le_of_lt (local_entry_of_startup drift b eta hb state realized)) t ht

/-- Nonempty forward behavior and universal nonnegative output safety, conditional
on supplying every startup drift/output certificate. Those families remain open. -/
theorem forward_safety_of_certificates
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (output : ∀ b i, CellOutput b i)
    (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    (∃ state : Gimle.Asgard.Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state) ∧
    (∀ state : Gimle.Asgard.Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state →
      ∀ t ∈ Set.Ici (0 : ℝ),
        0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 ∧
        Gimle.Asgard.Examples.AIF.output.run (state t) 0 ≤ 16/5) := by
  have heta : 0 ≤ eta := by linarith [hp.1]
  refine ⟨AIFCircuitSolution.exists_realization eta heta, ?_⟩
  intro state realized t ht
  refine ⟨AIFCircuitSolution.realization_output_nonnegative eta heta state realized t ht, ?_⟩
  rcases le_total t 30 with h | h
  · exact startup_output drift output eta hp state realized t ⟨ht,h⟩
  · have hlate := later_output drift eta hp state realized t h
    linarith

#print axioms full_prefix
#print axioms terminal_time
#print axioms terminal_entry
#print axioms startup_membership
#print axioms local_entry_of_startup
#print axioms output_after_entry
#print axioms startup_output
#print axioms later_output
#print axioms forward_safety_of_certificates
end Gimle.Forseti.Examples.AIFSafetyComposition
"""
    return {"AIFSafetyComposition.lean": source}


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
