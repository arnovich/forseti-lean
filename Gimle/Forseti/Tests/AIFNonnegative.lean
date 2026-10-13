import Gimle.Forseti.Examples.AIFNonnegative

/-! Regressions for closed-interval nonnegativity, including zero-rate boundaries. -/
namespace Gimle.Forseti.Tests.AIFNonnegative
open Gimle.Forseti.Examples AIFNonnegative AIFPhysicalCoordinates

/-- A zero derivative at zero is allowed; strict boundary drift is not required. -/
theorem stationary_zero (T : ℝ) : ∀ t ∈ Set.Icc 0 T, (0 : ℝ) ≤ 0 := by
  exact nonnegative_of_derivative (fun _ => 0) (fun _ => 0) 0 T
    (fun t _ => (hasDerivAt_const t 0).hasDerivWithinAt) le_rfl
    (fun _ _ _ => le_rfl)

/-- The physical theorem uses every species in its original coordinate order. -/
theorem physical_endpoint (eta T : ℝ) (heta : 0 ≤ eta) (hT : 0 ≤ T)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Icc 0 T) t) :
    0 ≤ state T 0 ∧ 0 ≤ state T 1 ∧ 0 ≤ state T 2 ∧ 0 ≤ state T 3 := by
  have h := physical_nonnegative eta heta T state initial derivative T ⟨hT, le_rfl⟩
  exact ⟨h 0, h 1, h 2, h 3⟩

/-- The four polynomial bounds include the terminal time and eta zero. -/
theorem polynomial_endpoint (T : ℝ) (hT : 0 ≤ T)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField 0 (state t) i)
        (Set.Icc 0 T) t) :
    state T 2 ≤ 2*T ∧ state T 0 ≤ T^2 ∧
      state T 1 ≤ T^3/3 ∧ state T 3 ≤ T^4/12 :=
  physical_polynomial_bounds 0 le_rfl T state initial derivative T ⟨hT, le_rfl⟩

/-- Checking only a weak rate at zero would allow a negative cubic to escape. -/
theorem boundary_only_can_escape :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => -s^3) (-3*t^2) (Set.Icc (0 : ℝ) 1) t) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, -t^3 = 0 → 0 ≤ -3*t^2) ∧
    ¬ (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ -t^3) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t _
    convert! ((hasDerivAt_id t).pow 3).neg.hasDerivWithinAt using 1
    simp only [id_eq]
    ring
  · intro t _ ht
    have hz : t = 0 := eq_zero_of_pow_eq_zero (neg_eq_zero.mp ht)
    simp [hz]
  · intro h
    have := h 1 (by norm_num)
    norm_num at this

/-- A zero-length time interval needs no strict boundary inequality. -/
theorem singleton_interval : ∀ t ∈ Set.Icc (0 : ℝ) 0, (0 : ℝ) ≤ 0 := by
  exact stationary_zero 0

#print axioms boundary_only_can_escape
#print axioms singleton_interval
#print axioms polynomial_endpoint
#print axioms stationary_zero
#print axioms physical_endpoint
end Gimle.Forseti.Tests.AIFNonnegative
