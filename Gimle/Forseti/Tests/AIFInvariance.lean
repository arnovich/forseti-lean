import Gimle.Forseti.Examples.AIFInvariance
import Gimle.Forseti.Tests.AIFSlab

/-! Boundary-only invariance regressions, including the strictness requirement. -/
namespace Gimle.Forseti.Tests.AIFInvariance
open Gimle.Forseti.BernsteinMatrix
open Gimle.Forseti.Examples AIFInvariance AIFSlabModel AIFMesh AIFSlab

-- Starting exactly on the boundary is allowed; both interval endpoints are kept.
theorem boundary_start : ∀ t ∈ Set.Icc (0 : ℝ) 1, -t ≤ 0 := by
  apply sublevel_of_boundary_derivative (fun t : ℝ => -t) (fun _ => -1) 0 1 0
  · intro t _
    exact (hasDerivAt_id t).neg.hasDerivWithinAt
  · norm_num
  · intro t _ _
    norm_num

-- No positive-width assumption is needed by the scalar lemma.
theorem singleton_interval : ∀ t ∈ Set.Icc (2 : ℝ) 2, (7 : ℝ) ≤ 7 := by
  apply sublevel_of_boundary_derivative (fun _ : ℝ => 7) (fun _ => 0) 2 2 7
  · intro t _
    exact (hasDerivAt_const t (7 : ℝ)).hasDerivWithinAt
  · norm_num
  · intro t ht _
    exact False.elim (not_lt_of_ge ht.1 ht.2)

-- Replacing strict boundary drift by nonpositive drift would be unsound:
-- t^3 starts on the boundary with derivative zero but immediately leaves it.
theorem nonstrict_boundary_can_escape :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun z : ℝ => z^3) (3*t^2) (Set.Icc (0 : ℝ) 1) t) ∧
    (0 : ℝ)^3 ≤ 0 ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, t^3 = 0 → 3*t^2 ≤ 0) ∧
    ¬ (∀ t ∈ Set.Icc (0 : ℝ) 1, t^3 ≤ 0) := by
  refine ⟨?_, by norm_num, ?_, ?_⟩
  · intro t _
    simpa using! ((hasDerivAt_id t).pow 3).hasDerivWithinAt
  · intro t _ ht
    have hz : t = 0 := eq_zero_of_pow_eq_zero ht
    simp [hz]
  · intro h
    have := h 1 (by norm_num)
    norm_num at this

-- The slab rule consumes the same local drift interface as mesh-bound certificates.
example (k : Fin 3) (p : ℝ) (state : ℝ → Fin 4 → ℝ)
    (hp : p ∈ Set.Icc (8 : ℝ) (17/2))
    (hx : ∀ t ∈ Set.Icc (1/5 : ℝ) (1/5 + (steps k : ℝ)), ∀ i,
      HasDerivWithinAt (fun z => state z i) (AIFDriftModel.field p (state t) i)
        (Set.Icc (1/5 : ℝ) (1/5 + (steps k : ℝ))) t)
    (drift : ∀ t q e,
      t ∈ Set.Icc (1/5 : ℝ) (1/5 + (steps k : ℝ)) → q ∈ Set.Icc (8 : ℝ) (17/2) →
      matrixForm (metric (sample (steps k) 8) (timeCoordinate (sample (steps k) 8) t)) e
        ≤ 1/40000 →
      energyRate (sample (steps k) 8) (timeCoordinate (sample (steps k) 8) t)
        (etaCoordinate (sample (steps k) 8) q) e ≤
        (1/100) * (1/40000 - matrixForm
          (metric (sample (steps k) 8) (timeCoordinate (sample (steps k) 8) t)) e) -
          1/16000000)
    (initial : tubeEnergy (sample (steps k) 8) (1/5) p (state (1/5)) ≤ 1/40000) :
    ∀ t ∈ Set.Icc (1/5 : ℝ) (1/5 + (steps k : ℝ)),
      tubeEnergy (sample (steps k) 8) t p (state t) ≤ 1/40000 := by
  have h := tube_invariant (sample (steps k) 8)
    (by fin_cases k <;> norm_num [sample, steps]) (by norm_num [sample]) p
    (by norm_num [sample] at hp ⊢; exact hp) state
    (by simpa [sample] using hx) (by norm_num [sample] at drift ⊢; exact drift)
    (by simpa [sample] using initial)
  simpa [sample] using h

#print axioms boundary_start
#print axioms singleton_interval
#print axioms nonstrict_boundary_can_escape
end Gimle.Forseti.Tests.AIFInvariance
