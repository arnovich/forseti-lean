module

public import Gimle.Forseti.Examples.AIFNonnegative
public import Gimle.Forseti.Nonlinear

/-! Finite-horizon construction of zero-start physical AIF solutions.
A bounded coordinate clamp provides an auxiliary solution; explicit positivity
and growth estimates remove the clamp on the given interval. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFFiniteExistence
open AIFPhysicalCoordinates AIFNonnegative
open Gimle.Forseti.Nonlinear

/-- Use the existing compact-box construction on the species box [0,B]^4. -/
noncomputable def coordinateBox (B : ℝ) (hB : 0 ≤ B) : Trapping 4 where
  weights := fun _ => 1
  centre := fun _ => B/2
  alpha := 1
  inner := -1
  bound := 0
  radius := B/2
  weights_pos := fun _ => by norm_num
  alpha_pos := by norm_num
  margin := by norm_num
  radius_nonneg := by positivity
  covers := fun _ => by positivity

theorem clamp_apply (B : ℝ) (hB : 0 ≤ B) (x : Fin 4 → ℝ) (i : Fin 4) :
    (coordinateBox B hB).clamp x i = max 0 (min B (x i)) := by
  simp [Trapping.clamp, coordinateBox, Set.projIcc]

theorem clamp_nonnegative (B : ℝ) (hB : 0 ≤ B) (x : Fin 4 → ℝ) (i : Fin 4) :
    0 ≤ (coordinateBox B hB).clamp x i := by
  rw [clamp_apply]
  exact le_max_left _ _

theorem clamp_zero_of_nonpositive (B : ℝ) (hB : 0 ≤ B)
    (x : Fin 4 → ℝ) (i : Fin 4) (h : x i ≤ 0) :
    (coordinateBox B hB).clamp x i = 0 := by
  rw [clamp_apply, max_eq_left ((min_le_right _ _).trans h)]

theorem clamp_le_of_nonnegative (B : ℝ) (hB : 0 ≤ B)
    (x : Fin 4 → ℝ) (i : Fin 4) (h : 0 ≤ x i) :
    (coordinateBox B hB).clamp x i ≤ x i := by
  rw [clamp_apply]
  exact max_le h (min_le_right _ _)

theorem clamp_identity (B : ℝ) (hB : 0 ≤ B) (x : Fin 4 → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc 0 B) : (coordinateBox B hB).clamp x = x := by
  funext i
  rw [clamp_apply, min_eq_right (hx i).2, max_eq_right (hx i).1]

theorem physical_smooth (eta : ℝ) : ContDiff ℝ 1 (physicalField eta) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp only [physicalField]
  · exact (contDiff_apply ℝ (fun _ => ℝ) 2).sub (contDiff_apply ℝ (fun _ => ℝ) 0)
  · exact (contDiff_apply ℝ (fun _ => ℝ) 0).sub (contDiff_apply ℝ (fun _ => ℝ) 1)
  · exact contDiff_const.sub ((contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 2)).mul
      (contDiff_apply ℝ (fun _ => ℝ) 3))
  · exact (contDiff_apply ℝ (fun _ => ℝ) 1).sub
      ((contDiff_const.mul (contDiff_apply ℝ (fun _ => ℝ) 2)).mul
        (contDiff_apply ℝ (fun _ => ℝ) 3))

/-- The clamped field points inward whenever an actual state coordinate is nonpositive. -/
theorem clamped_nonnegative (eta : ℝ) (B : ℝ) (hB : 0 ≤ B) (T : ℝ)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => state s i)
        ((coordinateBox B hB).clamped (physicalField eta) (state t) i)
        (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, 0 ≤ state t i := by
  have positive (i : Fin 4) : ∀ t ∈ Set.Icc 0 T, 0 ≤ state t i := by
    apply nonnegative_of_derivative _ _ 0 T (fun t ht => derivative t ht i)
      (by simp [initial])
    intro t _ hi
    have hz := clamp_zero_of_nonpositive B hB (state t) i hi
    have hn := clamp_nonnegative B hB (state t)
    fin_cases i
    · change (coordinateBox B hB).clamp (state t) 0 = 0 at hz
      change 0 ≤ (coordinateBox B hB).clamp (state t) 2 -
        (coordinateBox B hB).clamp (state t) 0
      rw [hz, sub_zero]
      exact hn 2
    · change (coordinateBox B hB).clamp (state t) 1 = 0 at hz
      change 0 ≤ (coordinateBox B hB).clamp (state t) 0 -
        (coordinateBox B hB).clamp (state t) 1
      rw [hz, sub_zero]
      exact hn 0
    · change (coordinateBox B hB).clamp (state t) 2 = 0 at hz
      change 0 ≤ 2 - eta * (coordinateBox B hB).clamp (state t) 2 *
        (coordinateBox B hB).clamp (state t) 3
      rw [hz]
      norm_num
    · change (coordinateBox B hB).clamp (state t) 3 = 0 at hz
      change 0 ≤ (coordinateBox B hB).clamp (state t) 1 -
        eta * (coordinateBox B hB).clamp (state t) 2 *
        (coordinateBox B hB).clamp (state t) 3
      rw [hz]
      simpa using hn 1
  exact fun t ht i => positive i t ht

/-- The bounded auxiliary field obeys the same growth estimates as the physical field. -/
theorem clamped_polynomial_bounds (eta : ℝ) (heta : 0 ≤ eta)
    (B : ℝ) (hB : 0 ≤ B) (T : ℝ)
    (state : ℝ → Fin 4 → ℝ) (initial : state 0 = 0)
    (derivative : ∀ t ∈ Set.Icc 0 T, ∀ i,
      HasDerivWithinAt (fun s => state s i)
        ((coordinateBox B hB).clamped (physicalField eta) (state t) i)
        (Set.Icc 0 T) t) :
    ∀ t ∈ Set.Icc 0 T, state t 2 ≤ 2*t ∧ state t 0 ≤ t^2 ∧
      state t 1 ≤ t^3/3 ∧ state t 3 ≤ t^4/12 := by
  let clip := (coordinateBox B hB).clamp
  have positive := clamped_nonnegative eta B hB T state initial derivative
  have clipped_pos (t : ℝ) (i : Fin 4) : 0 ≤ clip (state t) i :=
    clamp_nonnegative B hB (state t) i
  have clipped_le (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i : Fin 4) :
      clip (state t) i ≤ state t i :=
    clamp_le_of_nonnegative B hB (state t) i (positive t ht i)
  have reaction (t : ℝ) : 0 ≤ eta*clip (state t) 2*clip (state t) 3 :=
    mul_nonneg (mul_nonneg heta (clipped_pos t 2)) (clipped_pos t 3)
  have hz1 : ∀ t ∈ Set.Icc 0 T, state t 2 ≤ 2*t := by
    apply le_of_derivative_le _ _ _ (fun _ => 2) 0 T
      (fun t ht => derivative t ht 2)
    · intro t _
      simpa using! ((hasDerivAt_id t).const_mul 2).hasDerivWithinAt
    · simp [initial]
    · intro t _
      change 2 - eta*clip (state t) 2*clip (state t) 3 ≤ 2
      linarith [reaction t]
  have hx1 : ∀ t ∈ Set.Icc 0 T, state t 0 ≤ t^2 := by
    apply le_of_derivative_le _ _ _ (fun t => 2*t) 0 T
      (fun t ht => derivative t ht 0)
    · intro t _
      simpa using! ((hasDerivAt_id t).pow 2).hasDerivWithinAt
    · simp [initial]
    · intro t ht
      change clip (state t) 2 - clip (state t) 0 ≤ 2*t
      have ht' := Set.Ico_subset_Icc_self ht
      linarith [hz1 t ht', clipped_le t ht' 2, clipped_pos t 0]
  have hx2 : ∀ t ∈ Set.Icc 0 T, state t 1 ≤ t^3/3 := by
    apply le_of_derivative_le _ _ _ (fun t => t^2) 0 T
      (fun t ht => derivative t ht 1)
    · intro t _
      convert! (((hasDerivAt_id t).pow 3).div_const 3).hasDerivWithinAt using 1
      simp only [id_eq]
      ring
    · simp [initial]
    · intro t ht
      change clip (state t) 0 - clip (state t) 1 ≤ t^2
      have ht' := Set.Ico_subset_Icc_self ht
      linarith [hx1 t ht', clipped_le t ht' 0, clipped_pos t 1]
  have hz2 : ∀ t ∈ Set.Icc 0 T, state t 3 ≤ t^4/12 := by
    apply le_of_derivative_le _ _ _ (fun t => t^3/3) 0 T
      (fun t ht => derivative t ht 3)
    · intro t _
      convert! (((hasDerivAt_id t).pow 4).div_const 12).hasDerivWithinAt using 1
      simp only [id_eq]
      ring
    · simp [initial]
    · intro t ht
      change clip (state t) 1 - eta*clip (state t) 2*clip (state t) 3 ≤ t^3/3
      have ht' := Set.Ico_subset_Icc_self ht
      linarith [hx2 t ht', clipped_le t ht' 1, reaction t]
  exact fun t ht => ⟨hz1 t ht, hx1 t ht, hx2 t ht, hz2 t ht⟩

/-- One finite box containing all four polynomial bounds on [0,m]. -/
noncomputable def horizonBound (m : ℕ) : ℝ :=
  1 + 2*m + (m : ℝ)^2 + (m : ℝ)^3/3 + (m : ℝ)^4/12

theorem horizonBound_nonnegative (m : ℕ) : 0 ≤ horizonBound m := by
  unfold horizonBound
  positivity

theorem polynomials_le_horizon (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 (m : ℝ)) :
    2*t ≤ horizonBound m ∧ t^2 ≤ horizonBound m ∧
      t^3/3 ≤ horizonBound m ∧ t^4/12 ≤ horizonBound m := by
  have h2 : t^2 ≤ (m : ℝ)^2 := pow_le_pow_left₀ ht.1 ht.2 2
  have h3 : t^3 ≤ (m : ℝ)^3 := pow_le_pow_left₀ ht.1 ht.2 3
  have h4 : t^4 ≤ (m : ℝ)^4 := pow_le_pow_left₀ ht.1 ht.2 4
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hp2 := pow_nonneg hn 2
  have hp3 := pow_nonneg hn 3
  have hp4 := pow_nonneg hn 4
  unfold horizonBound
  constructor
  · linarith [ht.2]
  constructor
  · linarith
  constructor <;> linarith

/-- An original, unclamped zero-start physical solution exists on every [0,m].
The conclusion includes derivatives at both closed endpoints. -/
theorem finite_solution (eta : ℝ) (heta : 0 ≤ eta) (m : ℕ) :
    ∃ state : ℝ → Fin 4 → ℝ, state 0 = 0 ∧
      ∀ t ∈ Set.Icc 0 (m : ℝ), ∀ i,
        HasDerivWithinAt (fun s => state s i) (physicalField eta (state t) i)
          (Set.Icc 0 (m : ℝ)) t := by
  let B := horizonBound m
  have hB : 0 ≤ B := horizonBound_nonnegative m
  obtain ⟨state, initial, hd⟩ := (coordinateBox B hB).clamped_solution_on
    (physicalField eta) (physical_smooth eta) 0 0 m
  have derivative : ∀ t ∈ Set.Icc 0 (m : ℝ), ∀ i,
      HasDerivWithinAt (fun s => state s i)
        ((coordinateBox B hB).clamped (physicalField eta) (state t) i)
        (Set.Icc 0 (m : ℝ)) t := by
    intro t ht
    have h := hd t (by simpa using ht)
    simpa using hasDerivWithinAt_pi.mp h
  have pos := clamped_nonnegative eta B hB m state initial derivative
  have upper := clamped_polynomial_bounds eta heta B hB m state initial derivative
  refine ⟨state, initial, ?_⟩
  intro t ht i
  have inside : ∀ j, state t j ∈ Set.Icc 0 B := by
    intro j
    refine ⟨pos t ht j, ?_⟩
    obtain ⟨hz1, hx1, hx2, hz2⟩ := upper t ht
    obtain ⟨hbz1, hbx1, hbx2, hbz2⟩ := polynomials_le_horizon m t ht
    fin_cases j
    · exact hx1.trans hbx1
    · exact hx2.trans hbx2
    · exact hz1.trans hbz1
    · exact hz2.trans hbz2
  have hid := clamp_identity B hB (state t) inside
  simpa only [Trapping.clamped, hid] using derivative t ht i

#print axioms clamped_polynomial_bounds
#print axioms polynomials_le_horizon
#print axioms finite_solution

#print axioms physical_smooth
#print axioms clamped_nonnegative
end Gimle.Forseti.Examples.AIFFiniteExistence
