module

public import Gimle.Forseti.Nonlinear

/-! A fixed five-species rational feedback model with finite binding capacity.
Coordinates are plant precursor, plant output, controller species one and two,
and occupied binding sites. The rational feedback retains physical time and its
denominator guard. A load switch changes the field, not the state. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFModel

abbrev State := Fin 5 → ℝ

noncomputable def alpha : ℝ := 316129 / 100000
noncomputable def kappa : ℝ := 147261 / 1000000
noncomputable def dilution : ℝ := 3 / 100

/-- Rational synthesis feedback; physical claims require a positive denominator. -/
noncomputable def control (x : State) : ℝ := alpha * kappa / (kappa + x 3)

/-- Net reversible binding before the occupied-site removal term. -/
noncomputable def binding (L : ℝ) (x : State) : ℝ := x 1 * (L - x 4) - x 4

/-- The physical-time field, including controller dilution and occupied-site loss. -/
noncomputable def field (L : ℝ) (x : State) : State :=
  ![control x - x 0,
    x 0 - x 1 - binding L x,
    2 - 8 * x 2 * x 3 - dilution * x 2,
    x 1 - 8 * x 2 * x 3 - dilution * x 3,
    binding L x - x 4 / 5]

/-- Coordinatewise closed-interval solution, with one-sided derivatives at endpoints. -/
def Solves (L a b : ℝ) (state : ℝ → State) : Prop :=
  ∀ t ∈ Set.Icc a b, ∀ i,
    HasDerivWithinAt (fun s => state s i) (field L (state t) i) (Set.Icc a b) t

/-- One continuous state across the two load phases; no derivative across the switch
is asserted. Each phase includes its own one-sided derivative at the join. -/
structure Switched (state : ℝ → State) : Prop where
  initial : state 0 = 0
  before : Solves 0 0 30 state
  after : Solves 2 30 100 state

/-- A coarse invariant physical rectangle, not the sharp response specification. -/
noncomputable def upper (L : ℝ) : State :=
  ![alpha, alpha + L, 2 / dilution, (alpha + L) / dilution, L]

def Physical (L : ℝ) (x : State) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ upper L i

theorem alpha_pos : 0 < alpha := by norm_num [alpha]
theorem kappa_pos : 0 < kappa := by norm_num [kappa]
theorem dilution_pos : 0 < dilution := by norm_num [dilution]

theorem denominator_lower {x : State} (h : 0 ≤ x 3) : kappa ≤ kappa + x 3 := by
  linarith

theorem denominator_pos {x : State} (h : 0 ≤ x 3) : 0 < kappa + x 3 :=
  kappa_pos.trans_le (denominator_lower h)

theorem control_nonneg {x : State} (h : 0 ≤ x 3) : 0 ≤ control x := by
  exact div_nonneg (mul_nonneg alpha_pos.le kappa_pos.le) (denominator_pos h).le

theorem control_le {x : State} (h : 0 ≤ x 3) : control x ≤ alpha := by
  rw [control, div_le_iff₀ (denominator_pos h)]
  nlinarith [mul_nonneg alpha_pos.le h]

theorem control_cap {x : State} (h : 0 ≤ x 3) : control x ≤ 4 :=
  (control_le h).trans (by norm_num [alpha])

/-- The rational feedback equals its original saturating expression on physical
states. This rewrites the feedback value, not the ODE's time variable. -/
theorem control_eq_saturating {x : State} (h : 0 ≤ x 3) :
    control x = alpha / (1 + x 3 / kappa) := by
  have hk : kappa ≠ 0 := ne_of_gt kappa_pos
  have hd : kappa + x 3 ≠ 0 := ne_of_gt (denominator_pos h)
  have hs : 1 + x 3 / kappa ≠ 0 := by
    have hh := div_nonneg h kappa_pos.le
    linarith
  unfold control
  field_simp [hk, hd, hs]

theorem output_balance (L : ℝ) (x : State) :
    field L x 1 + field L x 4 = x 0 - x 1 - x 4 / 5 := by
  change (x 0 - x 1 - binding L x) + (binding L x - x 4 / 5) = _
  ring

theorem precursor_balance (L : ℝ) (x : State) :
    field L x 0 = control x - x 0 := rfl

theorem upper_nonnegative {L : ℝ} (hL : 0 ≤ L) (i : Fin 5) : 0 ≤ upper L i := by
  fin_cases i <;> norm_num [upper, alpha, dilution] <;> linarith

theorem zero_physical {L : ℝ} (hL : 0 ≤ L) : Physical L 0 := by
  intro i
  exact ⟨le_rfl, upper_nonnegative hL i⟩

theorem capacity_zero {x : State} (h : Physical 0 x) : x 4 = 0 := by
  have hi := h 4
  simpa [upper] using le_antisymm hi.2 hi.1

theorem physical_mono_load {L K : ℝ} (hLK : L ≤ K) {x : State}
    (hx : Physical L x) : Physical K x := by
  intro i
  refine ⟨(hx i).1, (hx i).2.trans ?_⟩
  fin_cases i <;> norm_num [upper, dilution] <;> linarith

#print axioms control_le
#print axioms control_eq_saturating
#print axioms output_balance
end Gimle.Forseti.Examples.LoadedSAIFModel
