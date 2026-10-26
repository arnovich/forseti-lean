import Gimle.Forseti.Examples.LoadedSAIFMoving
import Gimle.Forseti.Examples.AIFMeshComposition

/-! Continuous coverage by a finite chain of certified rational moving regions.
Exact endpoint times, centers, metrics and levels are part of the mesh. The
chain propagates every enclosed state; nominal samples cannot fill a gap or
replace an endpoint transfer. -/
namespace Gimle.Forseti.Examples.LoadedSAIFMesh
open Set LoadedSAIFModel LoadedSAIFCertificates

/-- A nonempty contiguous mesh for one fixed load and energy level. -/
structure Mesh (n : Nat) where
  times : Fin (n + 2) → ℚ
  cells : Fin (n + 1) → MovingData
  load : ℚ
  level : ℚ
  starts : ∀ i, (cells i).tStart = times i.castSucc
  stops : ∀ i, (cells i).tStart + (cells i).step = times i.succ
  loads : ∀ i, (cells i).load = load
  levels : ∀ i, (cells i).radiusSq = level
  centers : ∀ i : Fin n, (cells i.castSucc).centerEnd = (cells i.succ).centerStart
  metrics : ∀ i : Fin n, (cells i.castSucc).metricEnd = (cells i.succ).metricStart

namespace Mesh
variable {n : Nat} (m : Mesh n)

/-- Adjacency excludes gaps and overlaps in physical time. -/
theorem adjacent_time (i : Fin n) :
    (m.cells i.castSucc).tStart + (m.cells i.castSucc).step =
      (m.cells i.succ).tStart := by
  rw [m.stops, m.starts]
  rfl

theorem time_start (i : Fin (n + 1)) :
    movingTime (m.cells i) (m.times i.castSucc) = 0 := by
  rw [← m.starts]
  simp [movingTime]

theorem time_stop (i : Fin (n + 1)) (hw : 0 < (m.cells i).step) :
    movingTime (m.cells i) (m.times i.succ) = 1 := by
  have hr : ((m.cells i).step : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hw
  rw [← m.stops]
  simp [movingTime, Rat.cast_add, hr]

theorem ordered (checked : ∀ i, MovingCertificate (m.cells i))
    (i : Fin (n + 1)) : (m.times i.castSucc : ℝ) ≤ m.times i.succ := by
  have h : m.times i.castSucc ≤ m.times i.succ := by
    rw [← m.starts, ← m.stops]
    linarith [(checked i).width]
  exact_mod_cast h

theorem time_monotone (checked : ∀ i, MovingCertificate (m.cells i)) :
    Monotone (fun i => (m.times i : ℝ)) :=
  Fin.monotone_iff_le_succ.mpr (m.ordered checked)

/-- Restrict the original physical trajectory to any complete cell. -/
theorem cell_solves (checked : ∀ i, MovingCertificate (m.cells i))
    {state : ℝ → State}
    (hs : Solves m.load (m.times 0) (m.times (Fin.last (n + 1))) state)
    (i : Fin (n + 1)) :
    Solves (m.cells i).load (m.cells i).tStart
      ((m.cells i).tStart + (m.cells i).step) state := by
  have hlo := m.time_monotone checked (Fin.zero_le i.castSucc)
  have hhi := m.time_monotone checked (Fin.le_last i.succ)
  have start : ((m.cells i).tStart : ℝ) = m.times i.castSucc := by
    exact_mod_cast m.starts i
  have stop : ((m.cells i).tStart : ℝ) + (m.cells i).step = m.times i.succ := by
    exact_mod_cast m.stops i
  have sub : Icc ((m.cells i).tStart : ℝ)
      ((m.cells i).tStart + (m.cells i).step) ⊆
      Icc (m.times 0 : ℝ) (m.times (Fin.last (n + 1))) := by
    rw [stop, start]
    exact Icc_subset_Icc hlo hhi
  intro t ht j
  simpa only [m.loads i] using (hs t (sub ht) j).mono sub

end Mesh

/-- Local continuous invariants and exact joins propagate the initial region
through every closed cell of the declared mesh. -/
theorem mesh_invariant {n : Nat} (m : Mesh n)
    (checked : ∀ i, MovingCertificate (m.cells i))
    {state : ℝ → State}
    (hs : Solves m.load (m.times 0) (m.times (Fin.last (n + 1))) state)
    (initial : movingEnergy (m.cells 0) 0 (state (m.times 0)) ≤ m.level) :
    ∀ i, ∀ t ∈ Icc (m.times i.castSucc : ℝ) (m.times i.succ),
      movingEnergy (m.cells i) (movingTime (m.cells i) t) (state t) ≤ m.level := by
  apply AIFMeshComposition.chain_invariant
    (fun i t => movingEnergy (m.cells i) (movingTime (m.cells i) t) (state t))
    (fun i => (m.times i : ℝ)) (m.level : ℝ)
  · exact m.ordered checked
  · intro i
    have hend : movingTime (m.cells i.castSucc) (m.times i.succ.castSucc) = 1 := by
      simpa only [Fin.succ_castSucc] using
        m.time_stop i.castSucc (checked i.castSucc).width
    rw [hend, m.time_start i.succ]
    exact movingEnergy_join _ _ (m.centers i) (m.metrics i) _
  · intro i hi
    rw [m.time_start] at hi
    have hstart : ((m.cells i).tStart : ℝ) = m.times i.castSucc := by
      exact_mod_cast m.starts i
    have hstop : ((m.cells i).tStart : ℝ) + (m.cells i).step = m.times i.succ := by
      exact_mod_cast m.stops i
    have hlevel : ((m.cells i).radiusSq : ℝ) = m.level := by
      exact_mod_cast m.levels i
    have h := moving_invariant (m.cells i) (checked i) state
      (m.cell_solves checked hs i) (by simpa only [hstart, hlevel] using hi)
    rw [hstop, hstart, hlevel] at h
    exact h
  · have hz : movingTime (m.cells 0) (m.times 0) = 0 := by
      simpa only [Fin.castSucc_zero] using m.time_start 0
    simpa only [hz] using initial

/-- Every physical time in the full span has an enclosed state in a certified cell. -/
theorem covered_energy {n : Nat} (m : Mesh n)
    (checked : ∀ i, MovingCertificate (m.cells i))
    {state : ℝ → State}
    (hs : Solves m.load (m.times 0) (m.times (Fin.last (n + 1))) state)
    (initial : movingEnergy (m.cells 0) 0 (state (m.times 0)) ≤ m.level)
    (t : ℝ) (ht : t ∈ Icc (m.times 0 : ℝ) (m.times (Fin.last (n + 1)))) :
    ∃ i, t ∈ Icc (m.times i.castSucc : ℝ) (m.times i.succ) ∧
      movingEnergy (m.cells i) (movingTime (m.cells i) t) (state t) ≤ m.level := by
  obtain ⟨i, hi⟩ := AIFMesh.interval_covered n (fun i => (m.times i : ℝ)) t ht
  exact ⟨i, hi, mesh_invariant m checked hs initial i t hi⟩

/-- A property checked over every complete moving region holds at every time
in the mesh span. The predicate may combine several observables. -/
theorem covered_property {n : Nat} (m : Mesh n)
    (checked : ∀ i, MovingCertificate (m.cells i))
    {state : ℝ → State}
    (hs : Solves m.load (m.times 0) (m.times (Fin.last (n + 1))) state)
    (initial : movingEnergy (m.cells 0) 0 (state (m.times 0)) ≤ m.level)
    (property : State → Prop)
    (regions : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
      movingEnergy (m.cells i) s x ≤ (m.cells i).radiusSq → property x)
    (t : ℝ) (ht : t ∈ Icc (m.times 0 : ℝ) (m.times (Fin.last (n + 1)))) :
    property (state t) := by
  obtain ⟨i, hi, he⟩ := covered_energy m checked hs initial t ht
  have hstart : ((m.cells i).tStart : ℝ) = m.times i.castSucc := by
    exact_mod_cast m.starts i
  have hstop : ((m.cells i).tStart : ℝ) + (m.cells i).step = m.times i.succ := by
    exact_mod_cast m.stops i
  have hlevel : ((m.cells i).radiusSq : ℝ) = m.level := by
    exact_mod_cast m.levels i
  exact regions i _ (movingTime_mem _ (checked i).width t
    (by rw [hstop, hstart]; exact hi)) _ (by simpa only [hlevel] using he)

#print axioms Mesh.cell_solves
#print axioms mesh_invariant
#print axioms covered_energy
#print axioms covered_property
end Gimle.Forseti.Examples.LoadedSAIFMesh
