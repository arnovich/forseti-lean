import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! Scalar comparison on a closed interval, conditional on a proved difference
inequality. These lemmas alone assert no uniqueness of PDE solutions. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set Real

set_option backward.isDefEq.respectTransparency false in
/-- A one-sided differential inequality controls a scalar difference on the
closed interval. No two-sided derivative at either endpoint is needed. -/
theorem difference_le_exp {D D' : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn D (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt D (D' t) t)
    (hle : ∀ t ∈ Ioo 0 T, D' t ≤ C * D t) :
    ∀ t ∈ Icc 0 T, D t ≤ Real.exp (C * t) * D 0 := by
  let E := fun t => Real.exp (-C * t) * D t
  have hE (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt E (Real.exp (-C * t) * (D' t - C * D t)) t := by
    convert! (((hasDerivAt_id t).const_mul (-C)).exp.mul (hd t ht)) using 1
    simp only [id_eq]
    ring
  have ha : AntitoneOn E (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc)
    · intro t ht
      exact (hE t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      change deriv E t ≤ 0
      rw [(hE t (by simpa using ht)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _))
        (sub_nonpos.mpr (hle t (by simpa using ht)))
  intro t ht
  have hh := ha ⟨le_rfl, hT⟩ ht ht.1
  dsimp [E] at hh
  simp only [mul_zero, Real.exp_zero, one_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (le_of_lt (Real.exp_pos (C * t)))
  simpa only [← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero,
    one_mul] using hh'

/-- The scalar end of the uniqueness argument. The PDE difference estimate is
an explicit premise and must be proved separately before applying this lemma. -/
theorem difference_eq_zero {D D' : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hc : ContinuousOn D (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt D (D' t) t)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ D t) (h0 : D 0 = 0)
    (hle : ∀ t ∈ Ioo 0 T, D' t ≤ C * D t) :
    ∀ t ∈ Icc 0 T, D t = 0 := by
  intro t ht
  apply le_antisymm _ (hn t ht)
  simpa only [h0, mul_zero] using difference_le_exp hT hc hd hle t ht

#print axioms difference_le_exp
#print axioms difference_eq_zero
end Gimle.Forseti.ClassicalVorticity
