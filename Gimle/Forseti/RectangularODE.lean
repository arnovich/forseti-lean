module

public import Gimle.Forseti.Examples.AIFNonnegative
public import Gimle.Forseti.Nonlinear

/-! Finite-interval existence inside a closed coordinate rectangle.
Only Lipschitz continuity on the rectangle is required. Coordinate projection
provides a bounded globally Lipschitz auxiliary field; inward faces keep its
solution in the rectangle, where projection is the identity. Degenerate
coordinate intervals are permitted. -/

@[expose] public section

namespace Gimle.Forseti.RectangularODE

structure Rectangle (n : ℕ) where
  lower : Fin n → ℝ
  upper : Fin n → ℝ
  ordered : ∀ i, lower i ≤ upper i

namespace Rectangle
variable {n : ℕ} (R : Rectangle n)

def box : Set (Fin n → ℝ) := Set.Icc R.lower R.upper

noncomputable def clamp (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Set.projIcc (R.lower i) (R.upper i) (R.ordered i) (x i)

theorem clamp_mem (x : Fin n → ℝ) : R.clamp x ∈ R.box := by
  constructor
  · intro i
    exact (Set.projIcc (R.lower i) (R.upper i) (R.ordered i) (x i)).property.1
  · intro i
    exact (Set.projIcc (R.lower i) (R.upper i) (R.ordered i) (x i)).property.2

theorem clamp_eq {x : Fin n → ℝ} (hx : x ∈ R.box) : R.clamp x = x := by
  funext i
  simp [clamp, Set.projIcc_of_mem _ ⟨hx.1 i, hx.2 i⟩]

theorem clamp_lower {x : Fin n → ℝ} {i : Fin n} (h : x i ≤ R.lower i) :
    R.clamp x i = R.lower i := by
  simp only [clamp, Set.projIcc]
  exact max_eq_left ((min_le_right _ _).trans h)

theorem clamp_upper {x : Fin n → ℝ} {i : Fin n} (h : R.upper i ≤ x i) :
    R.clamp x i = R.upper i := by
  simp only [clamp, Set.projIcc]
  rw [min_eq_left h, max_eq_right (R.ordered i)]

theorem clamp_lipschitz : LipschitzWith 1 R.clamp := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  calc dist (R.clamp x i) (R.clamp y i) ≤ dist (x i) (y i) := by
        have h := (LipschitzWith.projIcc (R.ordered i)).dist_le_mul (x i) (y i)
        simpa [clamp, Subtype.dist_eq] using h
    _ ≤ dist x y := dist_le_pi_dist x y i

noncomputable def clamped (F : (Fin n → ℝ) → Fin n → ℝ) (x : Fin n → ℝ) :=
  F (R.clamp x)

/-- Inward-pointing lower and upper faces, including equality on a face. -/
def Inward (F : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ x ∈ R.box, ∀ i,
    (x i = R.lower i → 0 ≤ F x i) ∧ (x i = R.upper i → F x i ≤ 0)

theorem clamped_invariant (F : (Fin n → ℝ) → Fin n → ℝ) (hin : R.Inward F)
    (a b : ℝ) (state : ℝ → Fin n → ℝ) (h0 : state a ∈ R.box)
    (hd : ∀ t ∈ Set.Icc a b, ∀ i,
      HasDerivWithinAt (fun s => state s i) (R.clamped F (state t) i)
        (Set.Icc a b) t) : ∀ t ∈ Set.Icc a b, state t ∈ R.box := by
  have lower (i : Fin n) : ∀ t ∈ Set.Icc a b, R.lower i ≤ state t i := by
    have h := Examples.AIFNonnegative.nonnegative_of_derivative
      (fun t => state t i - R.lower i) (fun t => R.clamped F (state t) i) a b
      (fun t ht => (hd t ht i).sub_const _) (sub_nonneg.mpr (h0.1 i)) (by
        intro t ht hs
        exact (hin (R.clamp (state t)) (R.clamp_mem _) i).1
          (R.clamp_lower (by linarith)))
    exact fun t ht => sub_nonneg.mp (h t ht)
  have upper (i : Fin n) : ∀ t ∈ Set.Icc a b, state t i ≤ R.upper i := by
    have h := Examples.AIFNonnegative.nonnegative_of_derivative
      (fun t => R.upper i - state t i) (fun t => -R.clamped F (state t) i) a b
      (fun t ht => (hd t ht i).const_sub _) (sub_nonneg.mpr (h0.2 i)) (by
        intro t ht hs
        exact neg_nonneg.mpr ((hin (R.clamp (state t)) (R.clamp_mem _) i).2
          (R.clamp_upper (by linarith))))
    exact fun t ht => sub_nonneg.mp (h t ht)
  exact fun t ht => ⟨fun i => lower i t ht, fun i => upper i t ht⟩

theorem clamped_lipschitz {F : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}
    (hK : LipschitzOnWith K F R.box) : LipschitzWith K (R.clamped F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hc : dist (R.clamp x) (R.clamp y) ≤ dist x y := by
    simpa using R.clamp_lipschitz.dist_le_mul x y
  exact (hK.dist_le_mul _ (R.clamp_mem x) _ (R.clamp_mem y)).trans
    (mul_le_mul_of_nonneg_left hc K.coe_nonneg)

/-- The auxiliary field has a solution for any finite natural-number duration. -/
theorem clamped_exists {F : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}
    (hK : LipschitzOnWith K F R.box) (a : ℝ) (x0 : Fin n → ℝ) (m : ℕ) :
    ∃ state : ℝ → Fin n → ℝ, state a = x0 ∧
      ∀ t ∈ Set.Icc a (a + m),
        HasDerivWithinAt state (R.clamped F (state t)) (Set.Icc a (a + m)) t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact R.box).exists_bound_of_continuousOn
    hK.continuousOn
  let M' : NNReal := ⟨max M 0, le_max_right _ _⟩
  have hbound (x : Fin n → ℝ) : ‖R.clamped F x‖ ≤ M' :=
    (hM _ (R.clamp_mem x)).trans (le_max_left _ _)
  have endpoint : a ≤ a + m := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have pl : IsPicardLindelof (fun _ => R.clamped F)
      (tmin := a) (tmax := a + m) ⟨a, le_rfl, endpoint⟩ x0 (M' * m) 0 M' K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => hbound x)
      (R.clamped_lipschitz hK).lipschitzOnWith ?_
    simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_zero, sub_zero,
      add_sub_cancel_left, sub_self]
    rw [max_eq_left (Nat.cast_nonneg m)]
  exact pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Actual existence for the original field, with its invariant rectangle. -/
theorem exists_solution {F : (Fin n → ℝ) → Fin n → ℝ} {K : NNReal}
    (hK : LipschitzOnWith K F R.box) (hin : R.Inward F)
    (a : ℝ) (x0 : Fin n → ℝ) (h0 : x0 ∈ R.box) (m : ℕ) :
    ∃ state : ℝ → Fin n → ℝ, state a = x0 ∧
      (∀ t ∈ Set.Icc a (a + m), state t ∈ R.box) ∧
      ∀ t ∈ Set.Icc a (a + m), ∀ i,
        HasDerivWithinAt (fun s => state s i) (F (state t) i)
          (Set.Icc a (a + m)) t := by
  obtain ⟨state, hs, hd⟩ := R.clamped_exists hK a x0 m
  have hp := R.clamped_invariant F hin a (a + m) state (hs ▸ h0)
    (fun t ht => hasDerivWithinAt_pi.mp (hd t ht))
  refine ⟨state, hs, hp, ?_⟩
  intro t ht i
  have hh := hasDerivWithinAt_pi.mp (hd t ht) i
  simpa only [clamped, R.clamp_eq (hp t ht)] using hh

end Rectangle
end Gimle.Forseti.RectangularODE
