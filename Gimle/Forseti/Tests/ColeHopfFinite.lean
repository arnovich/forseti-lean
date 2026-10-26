import Gimle.Forseti.ColeHopfFinite

/-! Regression contracts for finite heat-profile reductions. -/
namespace Gimle.Forseti.Tests.ColeHopfFinite

open Set Real
open Gimle.Forseti.ColeHopfFinite Gimle.Forseti.ColeHopf
open Gimle.Forseti.ResidualPDE

#check profile
#check valid
#check value_lower
#check abs_dx_le
#check abs_dxx_le

/-- One nonconstant heat mode with a strictly positive denominator margin. -/
def frequencies : Fin 1 → ℕ := fun _ => 1

/-- A nonzero retained source coefficient. -/
noncomputable def source : Fin 1 → ℝ := fun _ => 1 / 4

/-- Removing the mode leaves the unit heat background and zero Burgers field. -/
def removed : Fin 1 → ℝ := fun _ => 0

theorem source_moment : moment frequencies source 0 = 1 / 4 := by
  norm_num [moment, frequencies, source, Fin.sum_univ_one]

theorem source_valid (T : ℝ) : (profile (1/8) frequencies source).Valid (1/8) T := by
  exact valid _ _ _ _ (by norm_num) (by rw [source_moment]; norm_num)

theorem source_solves (T : ℝ) :
    Burgers (1/8) T (fun _ _ => 0) (fun _ _ => 0)
      ((profile (1/8) frequencies source).burgersJet (1/8))
      ((profile (1/8) frequencies source).burgersDt (1/8)) :=
  (source_valid T).burgers

/-- The source is not a disguised zero trajectory. -/
theorem source_nonzero :
    ((profile (1/8) frequencies source).burgersJet (1/8)).value 0 (π/2,0) = 1/16 := by
  norm_num [HeatJet.burgersJet, profile, wave, frequencies, source, Fin.sum_univ_one]

/-- The removed candidate has a different initial field. -/
theorem initial_data_changed :
    ¬ ∀ p, ((profile (1/8) frequencies source).burgersJet (1/8)).value 0 p =
      ((profile (1/8) frequencies removed).burgersJet (1/8)).value 0 p := by
  intro h
  have hp := h (π/2,0)
  rw [source_nonzero] at hp
  norm_num [HeatJet.burgersJet, profile, wave, frequencies, removed, Fin.sum_univ_one] at hp

/-- A single reusable comparison theorem handles the nonzero initial discrepancy. -/
theorem removed_enclosure :
    ∀ t ∈ Icc (0 : ℝ) (1/2),
      energy ((profile (1/8) frequencies source).burgersJet (1/8))
        ((profile (1/8) frequencies removed).burgersJet (1/8)) t ≤
          gronwallBound (1/144) 1 0 t := by
  have h := comparison (1/8) (1/2) frequencies source removed
    (by norm_num) (by rw [source_moment]; norm_num)
    (by norm_num [moment, frequencies, removed, Fin.sum_univ_one]) (by norm_num)
  norm_num [initialRadius, growth, moment, frequencies, source, removed,
    Fin.sum_univ_one] at h
  intro t ht
  exact h t ht.1 ht.2

/-- A zero denominator is excluded by the strict coefficient budget. -/
theorem critical_mass_rejected : ¬ moment frequencies (fun _ => (1 : ℝ)) 0 < 1 := by
  norm_num [moment, frequencies, Fin.sum_univ_one]

/-- Signed coefficients are accounted for through absolute moments. -/
theorem signed_second_moment :
    moment (fun i : Fin 2 => i.val + 1) ![(1/4 : ℝ), -1/8] 2 = 3/4 := by
  norm_num [moment, Fin.sum_univ_two]

#print axioms source_solves
#print axioms source_nonzero
#print axioms removed_enclosure
#print axioms initial_data_changed
#print axioms critical_mass_rejected

end Gimle.Forseti.Tests.ColeHopfFinite
