module

public import Gimle.Forseti.Examples.LoadedSAIFMesh

/-! Mesh regression proofs: time coverage and exact joins are structural obligations. -/

@[expose] public section

namespace Gimle.Forseti.Tests.LoadedSAIFMesh
open Gimle.Forseti.Examples.LoadedSAIFCertificates
open Gimle.Forseti.Examples.LoadedSAIFMesh

/-- Two cells with a gap cannot inhabit a checked contiguous mesh. -/
theorem time_gap_rejected (m : Mesh 1)
    (first_stop : (m.cells 0).tStart + (m.cells 0).step = 1)
    (second_start : (m.cells 1).tStart = 2) : False := by
  have h := m.adjacent_time 0
  norm_num at h
  rw [first_stop, second_start] at h
  norm_num at h

/-- A collapsed cell cannot carry the positive-width moving certificate. -/
theorem collapsed_cell_rejected (d : MovingData) (h : d.step = 0) :
    ¬ Nonempty (MovingCertificate d) := by
  rintro ⟨c⟩
  have hw := c.width
  rw [h] at hw
  exact (lt_irrefl (0 : ℚ)) hw

#check mesh_invariant
#check covered_energy
#print axioms time_gap_rejected
end Gimle.Forseti.Tests.LoadedSAIFMesh
