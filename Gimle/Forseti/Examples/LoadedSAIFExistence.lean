module

public import Gimle.Forseti.Examples.LoadedSAIFModel
public import Gimle.Forseti.RectangularODE

/-! Physical-domain existence for the loaded rational feedback field. The coarse
rectangle supplies positivity and finite-time existence, not sharp tracking.
Each load phase is solved in physical time without multiplying the vector field
by its feedback denominator. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFExistence
open LoadedSAIFModel RectangularODE

noncomputable def physicalRectangle (L : ℝ) (hL : 0 ≤ L) : Rectangle 5 where
  lower := 0
  upper := upper L
  ordered := upper_nonnegative hL

theorem mem_rectangle {L : ℝ} {hL : 0 ≤ L} {x : State} :
    x ∈ (physicalRectangle L hL).box ↔ Physical L x := by
  exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

theorem physical_inward (L : ℝ) (hL : 0 ≤ L) :
    (physicalRectangle L hL).Inward (field L) := by
  intro x hx i
  have hp : Physical L x := mem_rectangle.mp hx
  have h0 := (hp 0).1
  have h1 := (hp 1).1
  have h2 := (hp 2).1
  have h3 := (hp 3).1
  have h4 := (hp 4).1
  have hu0 : x 0 ≤ alpha := (hp 0).2
  have hu1 : x 1 ≤ alpha + L := (hp 1).2
  have hu4 : x 4 ≤ L := (hp 4).2
  have hann : 0 ≤ 8 * x 2 * x 3 := by positivity
  constructor
  · intro hz
    change x i = 0 at hz
    fin_cases i
    · change x 0 = 0 at hz
      change 0 ≤ control x - x 0
      rw [hz, sub_zero]
      exact control_nonneg h3
    · change x 1 = 0 at hz
      change 0 ≤ x 0 - x 1 - (x 1 * (L - x 4) - x 4)
      rw [hz]
      linarith
    · change x 2 = 0 at hz
      change 0 ≤ 2 - 8 * x 2 * x 3 - dilution * x 2
      rw [hz]
      norm_num
    · change x 3 = 0 at hz
      change 0 ≤ x 1 - 8 * x 2 * x 3 - dilution * x 3
      rw [hz]
      simpa using h1
    · change x 4 = 0 at hz
      change 0 ≤ (x 1 * (L - x 4) - x 4) - x 4 / 5
      rw [hz]
      simpa using mul_nonneg h1 hL
  · intro hb
    change x i = upper L i at hb
    fin_cases i
    · change x 0 = alpha at hb
      change control x - x 0 ≤ 0
      rw [hb]
      exact sub_nonpos.mpr (control_le h3)
    · change x 1 = alpha + L at hb
      change x 0 - x 1 - (x 1 * (L - x 4) - x 4) ≤ 0
      have hh := mul_nonneg h1 (sub_nonneg.mpr hu4)
      linarith
    · change x 2 = 2 / dilution at hb
      change 2 - 8 * x 2 * x 3 - dilution * x 2 ≤ 0
      have hbalance : dilution * x 2 = 2 := by rw [hb]; norm_num [dilution]
      linarith
    · change x 3 = (alpha + L) / dilution at hb
      change x 1 - 8 * x 2 * x 3 - dilution * x 3 ≤ 0
      have hbalance : dilution * x 3 = alpha + L := by
        rw [hb]
        norm_num [dilution]
        ring
      linarith
    · change x 4 = L at hb
      change (x 1 * (L - x 4) - x 4) - x 4 / 5 ≤ 0
      rw [hb]
      nlinarith

/-- Smoothness is local to the positive feedback-denominator domain. -/
theorem field_smooth_on (L : ℝ) :
    ContDiffOn ℝ 1 (field L) {x : State | 0 < kappa + x 3} := by
  have coord (i : Fin 5) : ContDiffOn ℝ 1 (fun x : State => x i)
      {x : State | 0 < kappa + x 3} :=
    (contDiff_apply ℝ (fun _ => ℝ) i).contDiffOn
  have hc : ContDiffOn ℝ 1 control {x : State | 0 < kappa + x 3} := by
    exact contDiffOn_const.div (contDiffOn_const.add (coord 3))
      (fun x hx => ne_of_gt hx)
  have hb : ContDiffOn ℝ 1 (binding L) {x : State | 0 < kappa + x 3} :=
    ((coord 1).mul (contDiffOn_const.sub (coord 4))).sub (coord 4)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact hc.sub (coord 0)
  · exact ((coord 0).sub (coord 1)).sub hb
  · exact (contDiffOn_const.sub ((contDiffOn_const.mul (coord 2)).mul (coord 3))).sub
      (contDiffOn_const.mul (coord 2))
  · exact ((coord 1).sub ((contDiffOn_const.mul (coord 2)).mul (coord 3))).sub
      (contDiffOn_const.mul (coord 3))
  · exact hb.sub ((coord 4).div_const 5)

theorem physical_lipschitz (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : NNReal, LipschitzOnWith K (field L) (physicalRectangle L hL).box := by
  have hs : ContDiffOn ℝ 1 (field L) (physicalRectangle L hL).box :=
    (field_smooth_on L).mono (fun x hx => denominator_pos ((mem_rectangle.mp hx 3).1))
  exact hs.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _)
    (isCompact_Icc : IsCompact (physicalRectangle L hL).box)

/-- An original rational-field solution exists from every physical state for
every finite natural-number duration, and keeps the physical rectangle. -/
theorem finite_solution (L : ℝ) (hL : 0 ≤ L) (a : ℝ) (x0 : State)
    (h0 : Physical L x0) (m : ℕ) :
    ∃ state : ℝ → State, state a = x0 ∧
      (∀ t ∈ Set.Icc a (a + m), Physical L (state t)) ∧
      Solves L a (a + m) state := by
  obtain ⟨K, hK⟩ := physical_lipschitz L hL
  obtain ⟨state, hs, hp, hd⟩ := (physicalRectangle L hL).exists_solution hK
    (physical_inward L hL) a x0 (mem_rectangle.mpr h0) m
  exact ⟨state, hs, fun t ht => mem_rectangle.mp (hp t ht), hd⟩

private theorem interval_nhds_right {a b t : ℝ} (ha : a ≤ t) (hb : t < b) :
    Set.Icc a b ∈ nhdsWithin t (Set.Ici t) := by
  apply Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) (Iio_mem_nhds hb))
  intro s hs
  exact ⟨ha.trans hs.1, hs.2.le⟩

/-- Two supplied solutions with positive feedback denominators agree from the
same initial state. Compact trajectory images provide a common Lipschitz
rectangle entirely inside the denominator-positive domain. -/
theorem unique_on_positive (L a b : ℝ) (hab : a ≤ b)
    (state other : ℝ → State) (hs : Solves L a b state) (ho : Solves L a b other)
    (hsp : ∀ t ∈ Set.Icc a b, 0 < kappa + state t 3)
    (hop : ∀ t ∈ Set.Icc a b, 0 < kappa + other t 3)
    (h0 : state a = other a) : Set.EqOn state other (Set.Icc a b) := by
  classical
  have hsc : ContinuousOn state (Set.Icc a b) :=
    fun t ht => (hasDerivWithinAt_pi.mpr (hs t ht)).continuousWithinAt
  have hoc : ContinuousOn other (Set.Icc a b) :=
    fun t ht => (hasDerivWithinAt_pi.mpr (ho t ht)).continuousWithinAt
  let S : Set State := state '' Set.Icc a b ∪ other '' Set.Icc a b
  have hS : IsCompact S :=
    (isCompact_Icc.image_of_continuousOn hsc).union
      (isCompact_Icc.image_of_continuousOn hoc)
  have hne : S.Nonempty := ⟨state a, Or.inl ⟨a, ⟨le_rfl, hab⟩, rfl⟩⟩
  have hpos : ∀ x ∈ S, 0 < kappa + x 3 := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · exact hsp t ht
    · exact hop t ht
  have hlow (i : Fin 5) : ∃ x ∈ S, IsMinOn (fun y : State => y i) S x :=
    hS.exists_isMinOn hne (continuous_apply i).continuousOn
  have hhigh (i : Fin 5) : ∃ x ∈ S, IsMaxOn (fun y : State => y i) S x :=
    hS.exists_isMaxOn hne (continuous_apply i).continuousOn
  choose lower hlower lower_min using hlow
  choose upper hupper upper_max using hhigh
  let R : Rectangle 5 := {
    lower := fun i => lower i i
    upper := fun i => upper i i
    ordered := fun i => upper_max i (hlower i) }
  have hinside {x : State} (hx : x ∈ S) : x ∈ R.box :=
    ⟨fun i => lower_min i hx, fun i => upper_max i hx⟩
  have hdomain : R.box ⊆ {x : State | 0 < kappa + x 3} := by
    intro x hx
    have hlo : lower 3 3 ≤ x 3 := hx.1 3
    change 0 < kappa + x 3
    exact (hpos (lower 3) (hlower 3)).trans_le (add_le_add le_rfl hlo)
  obtain ⟨K, hK⟩ := ((field_smooth_on L).mono hdomain).exists_lipschitzOnWith
    one_ne_zero (convex_Icc _ _) (isCompact_Icc : IsCompact R.box)
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => field L)
    (s := fun _ => R.box) (fun _ _ => hK) hsc
  · intro t ht
    exact (hasDerivWithinAt_pi.mpr (hs t (Set.Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (interval_nhds_right ht.1 ht.2)
  · intro t ht
    exact hinside (Or.inl ⟨t, Set.Ico_subset_Icc_self ht, rfl⟩)
  · exact hoc
  · intro t ht
    exact (hasDerivWithinAt_pi.mpr (ho t (Set.Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
      (interval_nhds_right ht.1 ht.2)
  · intro t ht
    exact hinside (Or.inr ⟨t, Set.Ico_subset_Icc_self ht, rfl⟩)
  · exact h0

/-- Two physical load phases glued at their shared state, with no reset. -/
theorem switched_exists : ∃ state : ℝ → State, Switched state ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 30, Physical 0 (state t)) ∧
    (∀ t ∈ Set.Icc (30 : ℝ) 100, Physical 2 (state t)) := by
  obtain ⟨first, hf0, hfp, hfd⟩ := finite_solution 0 (by norm_num) 0 0
    (zero_physical (by norm_num)) 30
  have hf30 : Physical 2 (first 30) :=
    physical_mono_load (by norm_num : (0 : ℝ) ≤ 2)
      (hfp 30 (by norm_num))
  obtain ⟨second, hs0, hsp, hsd⟩ := finite_solution 2 (by norm_num) 30 (first 30) hf30 70
  have first_solves : Solves 0 0 30 first := by simpa using hfd
  have second_solves : Solves 2 30 100 second := by norm_num at hsd; exact hsd
  let state : ℝ → State := fun t => if t ≤ 30 then first t else second t
  have before (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 30) : state t = first t :=
    ite_eq_left ht.2
  have after (t : ℝ) (ht : t ∈ Set.Icc (30 : ℝ) 100) : state t = second t := by
    by_cases h : t ≤ 30
    · have heq : t = 30 := le_antisymm h ht.1
      subst t
      simp only [state, le_refl, ↓reduceIte]
      exact hs0.symm
    · exact ite_eq_right h
  have first_deriv : Solves 0 0 30 state := by
    intro t ht i
    have hh := first_solves t ht i
    have heq := before t ht
    rw [heq]
    exact hh.congr_of_mem (fun s hs => congrArg (fun x : State => x i)
      (before s (by simpa using hs))) (by simpa using ht)
  have second_deriv : Solves 2 30 100 state := by
    intro t ht i
    have hh := second_solves t ht i
    have heq := after t ht
    rw [heq]
    exact hh.congr_of_mem (fun s hs => congrArg (fun x : State => x i)
      (after s (by simpa using hs))) (by simpa using ht)
  refine ⟨state, ⟨?_, first_deriv, second_deriv⟩, ?_, ?_⟩
  · rw [before 0 (by norm_num)]
    exact hf0
  · intro t ht
    rw [before t ht]
    exact hfp t (by simpa using ht)
  · intro t ht
    rw [after t ht]
    exact hsp t (by convert ht using 1; norm_num)

/-- Uniqueness of the switched solution among trajectories in the physical
feedback domain. No differentiability through the load jump is required. -/
theorem switched_unique {state other : ℝ → State}
    (hs : Switched state) (ho : Switched other)
    (hsp : ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 < kappa + state t 3)
    (hop : ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 < kappa + other t 3) :
    Set.EqOn state other (Set.Icc (0 : ℝ) 100) := by
  have hb := unique_on_positive 0 0 30 (by norm_num) state other hs.before ho.before
    (fun t ht => hsp t ⟨ht.1, by linarith [ht.2]⟩)
    (fun t ht => hop t ⟨ht.1, by linarith [ht.2]⟩) (hs.initial.trans ho.initial.symm)
  have ha := unique_on_positive 2 30 100 (by norm_num) state other hs.after ho.after
    (fun t ht => hsp t ⟨by linarith [ht.1], ht.2⟩)
    (fun t ht => hop t ⟨by linarith [ht.1], ht.2⟩) (hb (by norm_num))
  intro t ht
  by_cases h : t ≤ 30
  · exact hb ⟨ht.1, h⟩
  · exact ha ⟨(lt_of_not_ge h).le, ht.2⟩

/-- Every admissible switched solution inherits the constructed physical bounds. -/
theorem physical_of_switched {state : ℝ → State} (hs : Switched state)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 < kappa + state t 3) :
    (∀ t ∈ Set.Icc (0 : ℝ) 30, Physical 0 (state t)) ∧
    (∀ t ∈ Set.Icc (30 : ℝ) 100, Physical 2 (state t)) := by
  obtain ⟨other, ho, hb, ha⟩ := switched_exists
  have hop : ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 < kappa + other t 3 := by
    intro t ht
    by_cases h : t ≤ 30
    · exact denominator_pos ((hb t ⟨ht.1, h⟩ 3).1)
    · exact denominator_pos ((ha t ⟨(lt_of_not_ge h).le, ht.2⟩ 3).1)
  have heq := switched_unique hs ho hp hop
  constructor
  · intro t ht
    rw [heq ⟨ht.1, by linarith [ht.2]⟩]
    exact hb t ht
  · intro t ht
    rw [heq ⟨by linarith [ht.1], ht.2⟩]
    exact ha t ht

#print axioms physical_inward
#print axioms finite_solution
#print axioms unique_on_positive
#print axioms switched_exists
#print axioms switched_unique
#print axioms physical_of_switched
end Gimle.Forseti.Examples.LoadedSAIFExistence
