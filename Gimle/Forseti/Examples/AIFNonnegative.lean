module

public import Gimle.Forseti.Examples.AIFInvariance
public import Gimle.Forseti.Examples.AIFPhysicalCoordinates

/-! Nonnegativity of supplied physical AIF solutions on closed finite intervals.
The scalar comparison permits zero boundary rates and requires inward rates
throughout the nonpositive region. No trajectory existence is assumed implicitly. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFNonnegative
open AIFPhysicalCoordinates

/-- Nonnegative rates throughout the nonpositive region prevent a scalar solution
from leaving the nonnegative half-line, including at the closed right endpoint. -/
theorem nonnegative_of_derivative (value rate : ℝ → ℝ) (a b : ℝ)
    (derivative : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt value (rate t) (Set.Icc a b) t)
    (initial : 0 ≤ value a)
    (inward : ∀ t ∈ Set.Ico a b, value t ≤ 0 → 0 ≤ rate t) :
    ∀ t ∈ Set.Icc a b, 0 ≤ value t := by
  intro t ht
  by_contra h
  have hv : value t < 0 := lt_of_not_ge h
  have hab : 0 < b - a + 1 := by linarith [ht.1, ht.2]
  let delta := -value t / (b - a + 1)
  have hd : 0 < delta := div_pos (neg_pos.mpr hv) hab
  have hmul : delta * (b - a + 1) = -value t := div_mul_cancel₀ _ (ne_of_gt hab)
  have fence := AIFInvariance.sublevel_of_boundary_derivative
    (fun s => -value s - delta * (s - a)) (fun s => -rate s - delta) a b 0
    (fun s hs => by
      simpa only [Pi.neg_apply, Pi.sub_apply, id_eq, mul_one] using! (derivative s hs).neg.sub
        (((hasDerivAt_id s).hasDerivWithinAt.sub_const a).const_mul delta))
    (by simpa using neg_nonpos.mpr initial) (by
      intro s hs hb
      have nonpos : value s ≤ 0 := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hs.1)]
      have := inward s hs nonpos
      linarith)
  have := fence t ht
  nlinarith [mul_nonneg hd.le (sub_nonneg.mpr ht.2)]

/-- All four physical species of a supplied zero-start AIF solution stay nonnegative.
The proof first controls z1, then x1, x2, and z2; eta need only be nonnegative. -/
theorem physical_nonnegative (eta : ℝ) (heta : 0 ≤ eta) (T : ℝ)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, 0 ≤ state t i := by
  have hz1 : ∀ t ∈ Set.Icc 0 T, 0 ≤ state t 2 := by
    have h := AIFInvariance.sublevel_of_boundary_derivative
      (fun t => -state t 2) (fun t => -physicalField eta (state t) 2) 0 T 0
      (fun t ht => (derivative t ht 2).neg) (by simp [initial]) (by
        intro t _ hb
        have hz : state t 2 = 0 := neg_eq_zero.mp hb
        simp [physicalField, hz])
    intro t ht
    exact neg_nonpos.mp (h t ht)
  have hx1 : ∀ t ∈ Set.Icc 0 T, 0 ≤ state t 0 := by
    apply nonnegative_of_derivative _ _ 0 T (fun t ht => derivative t ht 0)
      (by simp [initial])
    intro t ht hx
    change 0 ≤ state t 2 - state t 0
    linarith [hz1 t (Set.Ico_subset_Icc_self ht)]
  have hx2 : ∀ t ∈ Set.Icc 0 T, 0 ≤ state t 1 := by
    apply nonnegative_of_derivative _ _ 0 T (fun t ht => derivative t ht 1)
      (by simp [initial])
    intro t ht hx
    change 0 ≤ state t 0 - state t 1
    linarith [hx1 t (Set.Ico_subset_Icc_self ht)]
  have hz2 : ∀ t ∈ Set.Icc 0 T, 0 ≤ state t 3 := by
    apply nonnegative_of_derivative _ _ 0 T (fun t ht => derivative t ht 3)
      (by simp [initial])
    intro t ht hz
    change 0 ≤ state t 1 - eta * state t 2 * state t 3
    have hprod := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg heta (hz1 t (Set.Ico_subset_Icc_self ht))) hz
    linarith [hx2 t (Set.Ico_subset_Icc_self ht)]
  intro t ht i
  fin_cases i
  · exact hx1 t ht
  · exact hx2 t ht
  · exact hz1 t ht
  · exact hz2 t ht

/-- A closed-interval comparison with a supplied differentiable upper function. -/
theorem le_of_derivative_le (value rate bound slope : ℝ → ℝ) (a b : ℝ)
    (derivative : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt value (rate t) (Set.Icc a b) t)
    (bound_derivative : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt bound (slope t) (Set.Icc a b) t)
    (initial : value a ≤ bound a)
    (rates : ∀ t ∈ Set.Ico a b, rate t ≤ slope t) :
    ∀ t ∈ Set.Icc a b, value t ≤ bound t := by
  have h := nonnegative_of_derivative (fun t => bound t - value t)
    (fun t => slope t - rate t) a b
    (fun t ht => (bound_derivative t ht).sub (derivative t ht))
    (sub_nonneg.mpr initial) (fun t ht _ => sub_nonneg.mpr (rates t ht))
  exact fun t ht => sub_nonneg.mp (h t ht)

/-- Loose polynomial bounds on each physical species, sufficient to rule out
finite-time escape for a supplied zero-start solution. These are not sharp: a
sharp output bound would need tube certificates for every mesh cell, which this
repository does not contain. -/
theorem physical_polynomial_bounds (eta : ℝ) (heta : 0 ≤ eta) (T : ℝ)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
        (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, state t 2 ≤ 2*t ∧ state t 0 ≤ t^2 ∧
      state t 1 ≤ t^3/3 ∧ state t 3 ≤ t^4/12 := by
  have positive := physical_nonnegative eta heta T state initial derivative
  have reaction (t : ℝ) (ht : t ∈ Set.Icc 0 T) : 0 ≤ eta*state t 2*state t 3 :=
    mul_nonneg (mul_nonneg heta (positive t ht 2)) (positive t ht 3)
  have hz1 : ∀ t ∈ Set.Icc 0 T, state t 2 ≤ 2*t := by
    apply le_of_derivative_le _ _ _ (fun _ => 2) 0 T
      (fun t ht => derivative t ht 2)
    · intro t _
      simpa using! ((hasDerivAt_id t).const_mul 2).hasDerivWithinAt
    · simp [initial]
    · intro t ht
      change 2 - eta*state t 2*state t 3 ≤ 2
      linarith [reaction t (Set.Ico_subset_Icc_self ht)]
  have hx1 : ∀ t ∈ Set.Icc 0 T, state t 0 ≤ t^2 := by
    apply le_of_derivative_le _ _ _ (fun t => 2*t) 0 T
      (fun t ht => derivative t ht 0)
    · intro t _
      simpa using! ((hasDerivAt_id t).pow 2).hasDerivWithinAt
    · simp [initial]
    · intro t ht
      change state t 2 - state t 0 ≤ 2*t
      have ht' := Set.Ico_subset_Icc_self ht
      linarith [hz1 t ht', positive t ht' 0]
  have hx2 : ∀ t ∈ Set.Icc 0 T, state t 1 ≤ t^3/3 := by
    apply le_of_derivative_le _ _ _ (fun t => t^2) 0 T
      (fun t ht => derivative t ht 1)
    · intro t _
      convert! (((hasDerivAt_id t).pow 3).div_const 3).hasDerivWithinAt using 1
      simp only [id_eq]
      ring
    · simp [initial]
    · intro t ht
      change state t 0 - state t 1 ≤ t^2
      have ht' := Set.Ico_subset_Icc_self ht
      linarith [hx1 t ht', positive t ht' 1]
  have hz2 : ∀ t ∈ Set.Icc 0 T, state t 3 ≤ t^4/12 := by
    apply le_of_derivative_le _ _ _ (fun t => t^3/3) 0 T
      (fun t ht => derivative t ht 3)
    · intro t _
      convert! (((hasDerivAt_id t).pow 4).div_const 12).hasDerivWithinAt using 1
      simp only [id_eq]
      ring
    · simp [initial]
    · intro t ht
      change state t 1 - eta*state t 2*state t 3 ≤ t^3/3
      have ht' := Set.Ico_subset_Icc_self ht
      linarith [hx2 t ht', reaction t ht']
  exact fun t ht => ⟨hz1 t ht, hx1 t ht, hx2 t ht, hz2 t ht⟩

#print axioms le_of_derivative_le
#print axioms physical_polynomial_bounds

#print axioms nonnegative_of_derivative
#print axioms physical_nonnegative
end Gimle.Forseti.Examples.AIFNonnegative
