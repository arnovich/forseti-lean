import Gimle.Forseti.Examples.AIFFiniteExistence

/-! Global existence, forward uniqueness and nonnegativity for the antithetic
integral feedback (AIF) ODE `x₁' = z₁ − x₁`, `x₂' = x₁ − x₂`, `z₁' = 2 − η z₁ z₂`,
`z₂' = x₂ − η z₁ z₂` started at zero, for every fixed `η ≥ 0`. The solution is
built by agreeing finite-horizon solutions. No safety bound is claimed here. -/
namespace Gimle.Forseti.Examples.AIFGlobalSolution
open AIFPhysicalCoordinates AIFNonnegative AIFFiniteExistence
open Gimle.Forseti.Nonlinear

/-- The polynomial bounds place every supplied physical solution in the same finite box. -/
theorem physical_clamp_identity (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Icc 0 (m : ℝ)) t) (t : ℝ) (ht : t ∈ Set.Icc 0 (m : ℝ)) :
    (coordinateBox (horizonBound m) (horizonBound_nonnegative m)).clamp (state t) =
      state t := by
  apply clamp_identity
  intro i
  refine ⟨physical_nonnegative eta heta m state initial derivative t ht i, ?_⟩
  obtain ⟨hz1, hx1, hx2, hz2⟩ :=
    physical_polynomial_bounds eta heta m state initial derivative t ht
  obtain ⟨hbz1, hbx1, hbx2, hbz2⟩ := polynomials_le_horizon m t ht
  fin_cases i
  · exact hx1.trans hbx1
  · exact hx2.trans hbx2
  · exact hz1.trans hbz1
  · exact hz2.trans hbz2

/-- Any two zero-start original solutions agree on their common natural horizon. -/
theorem finite_unique (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ)
    (x y : ℝ → Fin 4 → ℝ) (hx0 : x 0 = 0) (hy0 : y 0 = 0)
    (hx : ∀ t ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun s => x s i) (physicalField eta (x t) i)
        (Set.Icc 0 (m : ℝ)) t)
    (hy : ∀ t ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun s => y s i) (physicalField eta (y t) i)
        (Set.Icc 0 (m : ℝ)) t) : Set.EqOn x y (Set.Icc 0 (m : ℝ)) := by
  let box := coordinateBox (horizonBound m) (horizonBound_nonnegative m)
  apply box.clamped_unique_on (physicalField eta) (physical_smooth eta) 0 m x y
  · intro t ht
    have hc := physical_clamp_identity eta heta m x hx0 hx t ht
    simpa only [box, Trapping.clamped, hc] using hasDerivWithinAt_pi.mpr (hx t ht)
  · intro t ht
    have hc := physical_clamp_identity eta heta m y hy0 hy t ht
    simpa only [box, Trapping.clamped, hc] using hasDerivWithinAt_pi.mpr (hy t ht)
  · rw [hx0, hy0]

/-- A chosen original solution on one natural horizon. -/
noncomputable def piece (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ) : ℝ → Fin 4 → ℝ :=
  Classical.choose (finite_solution eta heta m)

theorem piece_start (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ) : piece eta heta m 0 = 0 :=
  (Classical.choose_spec (finite_solution eta heta m)).1

theorem piece_derivative (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ) :
    ∀ t ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun s => piece eta heta m s i)
        (physicalField eta (piece eta heta m t) i) (Set.Icc 0 (m : ℝ)) t :=
  (Classical.choose_spec (finite_solution eta heta m)).2

theorem piece_agree (eta : ℝ) (heta : 0 ≤ eta) {k m : ℕ} (hkm : k ≤ m) :
    Set.EqOn (piece eta heta k) (piece eta heta m) (Set.Icc 0 (k : ℝ)) := by
  have hcast : (k : ℝ) ≤ m := by exact_mod_cast hkm
  apply finite_unique eta heta k _ _ (piece_start eta heta k) (piece_start eta heta m)
    (piece_derivative eta heta k)
  intro t ht i
  exact (piece_derivative eta heta m t ⟨ht.1, ht.2.trans hcast⟩ i).mono
    (Set.Icc_subset_Icc le_rfl hcast)

/-- One chosen trajectory, agreeing with every finite piece on its own interval. -/
noncomputable def solution (eta : ℝ) (heta : 0 ≤ eta) (t : ℝ) : Fin 4 → ℝ :=
  piece eta heta (⌈t⌉₊ + 1) t

private theorem below_horizon (t : ℝ) : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
  push_cast
  linarith [Nat.le_ceil t]

theorem solution_eq_piece (eta : ℝ) (heta : 0 ≤ eta) {m : ℕ} {t : ℝ}
    (ht : t ∈ Set.Icc 0 (m : ℝ)) : solution eta heta t = piece eta heta m t := by
  unfold solution
  rcases le_total (⌈t⌉₊ + 1) m with h | h
  · exact piece_agree eta heta h ⟨ht.1, (below_horizon t).le⟩
  · exact (piece_agree eta heta h ht).symm

theorem solution_start (eta : ℝ) (heta : 0 ≤ eta) : solution eta heta 0 = 0 := by
  rw [solution_eq_piece eta heta (m := 0) (by simp), piece_start]

/-- Derivatives are taken within the full forward domain, not a finite interval. -/
theorem solution_derivative (eta : ℝ) (heta : 0 ≤ eta) (t : ℝ) (ht : 0 ≤ t)
    (i : Fin 4) :
    HasDerivWithinAt (fun s => solution eta heta s i)
      (physicalField eta (solution eta heta t) i) (Set.Ici 0) t := by
  have htn := below_horizon t
  have mem : Set.Icc 0 (((⌈t⌉₊ + 1 : ℕ) : ℝ)) ∈ nhdsWithin t (Set.Ici 0) := by
    apply Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici 0) (Iio_mem_nhds htn))
    intro s hs
    exact ⟨hs.1, hs.2.le⟩
  have h := (piece_derivative eta heta (⌈t⌉₊ + 1) t ⟨ht, htn.le⟩ i).mono_of_mem_nhdsWithin mem
  rw [← solution_eq_piece eta heta ⟨ht, htn.le⟩] at h
  exact h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem mem fun s hs =>
    congrFun (solution_eq_piece eta heta hs) i) rfl

/-- Forward uniqueness concerns only times in the ODE's declared domain. -/
theorem solution_unique (eta : ℝ) (heta : 0 ≤ eta) (state : ℝ → Fin 4 → ℝ)
    (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Ici 0, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Ici 0) t) : Set.EqOn state (solution eta heta) (Set.Ici 0) := by
  intro t ht
  let m := ⌈t⌉₊ + 1
  have hx : ∀ s ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun z => state z i) (physicalField eta (state s) i)
        (Set.Icc 0 (m : ℝ)) s :=
    fun s hs i => (derivative s hs.1 i).mono (fun _ h => h.1)
  have hy : ∀ s ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun z => solution eta heta z i)
        (physicalField eta (solution eta heta s) i) (Set.Icc 0 (m : ℝ)) s :=
    fun s hs i => (solution_derivative eta heta s hs.1 i).mono (fun _ h => h.1)
  exact finite_unique eta heta m state _ initial (solution_start eta heta) hx hy
    ⟨ht, (below_horizon t).le⟩

theorem solution_nonnegative (eta : ℝ) (heta : 0 ≤ eta) (t : ℝ) (ht : 0 ≤ t)
    (i : Fin 4) : 0 ≤ solution eta heta t i := by
  exact physical_nonnegative eta heta t (solution eta heta) (solution_start eta heta)
    (fun s hs j => (solution_derivative eta heta s hs.1 j).mono (fun _ h => h.1))
    t ⟨ht, le_rfl⟩ i

/-- Existence on the full forward domain. -/
theorem exists_global (eta : ℝ) (heta : 0 ≤ eta) :
    ∃ state : ℝ → Fin 4 → ℝ, state 0 = 0 ∧
      ∀ t ∈ Set.Ici 0, ∀ i,
        HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
          (Set.Ici 0) t :=
  ⟨solution eta heta, solution_start eta heta, solution_derivative eta heta⟩

#print axioms finite_unique
#print axioms solution_start
#print axioms solution_derivative
#print axioms solution_unique
#print axioms solution_nonnegative
#print axioms exists_global
end Gimle.Forseti.Examples.AIFGlobalSolution
