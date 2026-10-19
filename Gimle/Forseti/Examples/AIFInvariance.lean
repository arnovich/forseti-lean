import Gimle.Forseti.Examples.AIFTrajectory

/-! Local moving-tube invariance from a supplied solution and a supplied drift
inequality on one slab. The argument uses strict boundary drift, never assumed
trajectory membership. Existence and composition across slabs are not part of
this module, and no circuit binding is claimed. -/
namespace Gimle.Forseti.Examples.AIFInvariance
open Gimle.Forseti.BernsteinMatrix AIFSlabModel AIFMesh AIFTrajectory

/-- Strictly negative boundary derivatives preserve a closed scalar sublevel.
The derivative contract also supplies continuity at both closed endpoints. -/
theorem sublevel_of_boundary_derivative (value rate : ℝ → ℝ) (a b bound : ℝ)
    (derivative : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt value (rate t) (Set.Icc a b) t)
    (initial : value a ≤ bound)
    (boundary : ∀ t ∈ Set.Ico a b, value t = bound → rate t < 0) :
    ∀ t ∈ Set.Icc a b, value t ≤ bound := by
  have h := image_le_of_deriv_right_lt_deriv_boundary
    (fun t ht => (derivative t ht).continuousWithinAt)
    (fun t ht => (derivative t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) initial (fun t => hasDerivAt_const t bound) boundary
  intro t ht
  exact h ht

/-- A supplied fixed-parameter solution starting in a slab's metric tube remains
in it through the closed right endpoint. The drift hypothesis is only in-tube. -/
theorem tube_invariant (d : Slab) (hh : 0 < d.step) (hp : d.etaLo < d.etaHi)
    (p : ℝ) (heta : p ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ))
    (state : ℝ → Fin 4 → ℝ)
    (derivative : ∀ t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step), ∀ i,
      HasDerivWithinAt (fun z => state z i) (AIFDriftModel.field p (state t) i)
        (Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step)) t)
    (drift : ∀ t q e,
      t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step) →
      q ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ) →
      matrixForm (metric d (timeCoordinate d t)) e ≤ 1/40000 →
      energyRate d (timeCoordinate d t) (etaCoordinate d q) e ≤
        (1/100) * (1/40000 - matrixForm (metric d (timeCoordinate d t)) e) - 1/16000000)
    (initial : tubeEnergy d d.tStart p (state d.tStart) ≤ 1/40000) :
    ∀ t ∈ Set.Icc (d.tStart : ℝ) ((d.tStart : ℝ) + d.step),
      tubeEnergy d t p (state t) ≤ 1/40000 := by
  apply sublevel_of_boundary_derivative (fun t => tubeEnergy d t p (state t))
    (fun t => energyRate d (timeCoordinate d t) (etaCoordinate d p)
      (state t - center d (timeCoordinate d t) (etaCoordinate d p)))
    (d.tStart : ℝ) ((d.tStart : ℝ) + d.step) (1/40000)
  · intro t ht
    exact tubeEnergy_derivative d (ne_of_gt hh) hp p state _ t (derivative t ht)
  · exact initial
  · intro t ht hb
    have h := drift t p (state t - center d (timeCoordinate d t) (etaCoordinate d p))
      (Set.Ico_subset_Icc_self ht) heta (le_of_eq hb)
    change energyRate d (timeCoordinate d t) (etaCoordinate d p)
      (state t - center d (timeCoordinate d t) (etaCoordinate d p)) ≤
      (1/100) * (1/40000 - tubeEnergy d t p (state t)) - 1/16000000 at h
    rw [hb] at h
    linarith

#print axioms sublevel_of_boundary_derivative
#print axioms tube_invariant
end Gimle.Forseti.Examples.AIFInvariance
