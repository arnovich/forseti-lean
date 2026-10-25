import Gimle.Forseti.Examples.LoadedSAIFContract

/-! The frozen contract uses continuous intervals and the original physical clock. -/
namespace Gimle.Forseti.Tests.LoadedSAIFContract
open Set Gimle.Forseti.Examples.LoadedSAIFContract

/-- A trajectory missing the recovery deadline cannot satisfy the contract. -/
theorem recovery_deadline_rejected (state : ℝ → Fin 5 → ℝ)
    (missed : state 33 1 < 9 / 5) : ¬ ContinuousBounds state := by
  intro h
  exact (not_lt_of_ge (h.recovery 33 (by norm_num)).1) missed

/-- Tail accuracy is stricter than the ordinary tracking interval. -/
theorem ordinary_band_does_not_imply_tail :
    (9 / 5 : ℝ) ∈ Icc (9 / 5) (11 / 5) ∧ ¬ |(9 / 5 : ℝ) - 2| ≤ 3 / 20 := by
  norm_num

#check contract_of_bounds
#check exists_contract_of_bounds
#print axioms recovery_deadline_rejected
end Gimle.Forseti.Tests.LoadedSAIFContract
