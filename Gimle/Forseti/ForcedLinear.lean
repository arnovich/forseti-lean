module

public import Gimle.Asgard.Dynamics.LinearAnalysis
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Well-posedness of continuously forced linear trajectories, for use in
trajectory contracts. Variation of constants proves existence; subtraction
reduces uniqueness to Asgard's homogeneous linear theorem. -/

@[expose] public section

namespace Gimle.Forseti.ForcedLinear

open Gimle.Asgard Gimle.Asgard.Dynamics
open scoped Interval

/-- Every continuous forcing has a global solution for every initial state. -/
theorem exists_solution {n : Nat} (L : Point n →L[ℝ] Point n)
    (forcing : Signal n) (continuous : Continuous forcing)
    (start : ℝ) (initial : Point n) :
    ∃ state : Signal n, state start = initial ∧
      ∀ t, HasDerivAt state (L (state t) + forcing t) t := by
  let : NormedAlgebra ℚ (Point n →L[ℝ] Point n) :=
    NormedAlgebra.restrictScalars ℚ ℝ (Point n →L[ℝ] Point n)
  let E : ℝ → (Point n →L[ℝ] Point n) := fun t => NormedSpace.exp (t • L)
  have dE (t : ℝ) : HasDerivAt E (L * E t) t :=
    hasDerivAt_exp_smul_const' L t
  have cE : Continuous E := continuous_iff_continuousAt.mpr
    (fun t => (dE t).continuousAt)
  let g : Signal n := fun t => E (-(t - start)) (forcing t)
  have cg : Continuous g := (cE.comp ((continuous_id.sub continuous_const).neg)).clm_apply
    continuous
  let J : Signal n := fun t => initial + ∫ s in start..t, g s
  have dJ (t : ℝ) : HasDerivAt J (g t) t := by
    simpa [J] using (intervalIntegral.integral_hasDerivAt_right
      (cg.intervalIntegrable start t)
      cg.aestronglyMeasurable.stronglyMeasurableAtFilter cg.continuousAt).const_add initial
  refine ⟨fun t => E (t - start) (J t), ?_, ?_⟩
  · simp [E, J, NormedSpace.exp_zero]
  · intro t
    have de : HasDerivAt (fun t => E (t - start)) (L * E (t - start)) t := by
      convert! (dE (t - start)).scomp t ((hasDerivAt_id t).sub_const start) using 1
      simp
    have cancel : E (t - start) * E (-(t - start)) = 1 := by
      dsimp [E]
      have neg : (-(t - start)) • L = -((t - start) • L) := by
        convert! neg_smul (t - start) L using 1
      rw [neg]
      have h := NormedSpace.exp_add_of_commute (Commute.refl ((t - start) • L)).neg_right
      convert! h.symm using 1
      simp [NormedSpace.exp_zero]
    convert! de.clm_apply (dJ t) using 1
    change L (E (t - start) (J t)) + forcing t =
      (L * E (t - start)) (J t) + E (t - start) (E (-(t - start)) (forcing t))
    have cancelled : E (t - start) (E (-(t - start)) (forcing t)) = forcing t := by
      change (E (t - start) * E (-(t - start))) (forcing t) = forcing t
      rw [cancel]
      rfl
    rw [cancelled]
    rfl

/-- A forcing continuous on the forward half-line has a solution there from any
initial value: the forcing is frozen at its start value for earlier times, which
makes it continuous on the whole line without changing it on the domain. -/
theorem exists_solution_on {n : Nat} (L : Point n →L[ℝ] Point n)
    (forcing : Signal n) (start : ℝ) (continuous : ContinuousOn forcing (Set.Ici start))
    (initial : Point n) :
    ∃ state : Signal n, state start = initial ∧
      ∀ t ∈ Set.Ici start, ∀ i, HasDerivWithinAt (fun t => state t i)
        ((L (state t) + forcing t) i) (Set.Ici start) t := by
  have frozen : Continuous fun t => forcing (max t start) :=
    continuous.comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t start)
  obtain ⟨state, hstart, hderiv⟩ := exists_solution L _ frozen start initial
  refine ⟨state, hstart, fun t ht i => ?_⟩
  have h := ((hasDerivAt_pi.mp (hderiv t)) i).hasDerivWithinAt (s := Set.Ici start)
  rwa [max_eq_left (Set.mem_Ici.1 ht)] at h

/-- The same input and initial value give the same state on the forward domain. -/
theorem unique_on {n : Nat} (L : Point n →L[ℝ] Point n)
    (forcing : Signal n) (start : ℝ) (x y : Signal n)
    (initial : x start = y start)
    (hx : ∀ t ∈ Set.Ici start, ∀ i, HasDerivWithinAt (fun t => x t i)
      ((L (x t) + forcing t) i) (Set.Ici start) t)
    (hy : ∀ t ∈ Set.Ici start, ∀ i, HasDerivWithinAt (fun t => y t i)
      ((L (y t) + forcing t) i) (Set.Ici start) t) :
    Set.EqOn x y (Set.Ici start) := by
  have equal := LinearAnalysis.unique_on L start (fun t => x t - y t) (fun _ => 0)
    (by simp [initial])
    (fun t ht i => by
      convert! (hx t ht i).sub (hy t ht i) using 1
      simp [map_sub])
    (fun t _ i => by simpa using (hasDerivWithinAt_const t (Set.Ici start) (0 : ℝ)))
  intro t ht
  exact sub_eq_zero.mp (equal ht)

#print axioms exists_solution
#print axioms exists_solution_on
#print axioms unique_on

end Gimle.Forseti.ForcedLinear
