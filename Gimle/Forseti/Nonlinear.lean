import Gimle.Forseti.LinearEnergyContract
import Gimle.Forseti.Dissipative

/-! # Trapping contracts for compiled nonlinear models

A trajectory contract in the shape gimle-forseti's deciders cite needs, for one
compiled continuous model, existence and forward uniqueness of its realization,
a bound on an observed quantity, that bound lifted through the observation
circuit, and the declared input admitted. `LinearEnergyContract` derives all of
it when the field is linear. This module derives it for **any** compiled field
— every compiled field is polynomial, hence smooth (`contDiff_eval`) — from one
differential inequality on a weighted sum of squares:

`V(x) = Σ wᵢ (xᵢ − cᵢ)²` with `wᵢ > 0`, and at every state
`V' = Σ 2 wᵢ (xᵢ − cᵢ) Fᵢ(x) ≤ α (C' − V)` with `α > 0` and `C' < C`.

Then, from any start with `V ≤ C`:

* **invariance**: every realization keeps `V ≤ C` (`Dissipative.sublevel`);
* **existence for all `t ≥ start`**: Mathlib's Picard–Lindelöf is local, so the
  field is clamped coordinatewise to the sup-norm box that contains `{V ≤ C}`,
  which makes it bounded and globally Lipschitz; a solution exists on every
  `[start, start + n]`; those are glued by uniqueness; and Mathlib's fencing
  lemma keeps the glued solution inside `{V ≤ C}`, where the clamp is the
  identity, because at a contact point `V' ≤ α (C' − C) < 0` — the margin
  `C' < C` is what makes the fence strict;
* **forward uniqueness**: Lipschitz continuity on the compact box, which the
  invariant keeps every realization inside.

The data is a `Trapping`; the model-specific work is the inequality
`decrease` (an `nlinarith` or a checked certificate) and the observation's
closed form. `Examples/Lorenz.lean` is the first instance. -/

namespace Gimle.Forseti.Nonlinear

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Model
open Gimle.Asgard.Polynomial

/-! ## Every compiled field is smooth -/

/-- A polynomial expression evaluates to a `C¹` function of the point. -/
theorem contDiff_eval {n : Nat} (e : Expr n) : ContDiff ℝ 1 (fun x : Point n => e.eval x) := by
  induction e with
  | var i => exact contDiff_apply ℝ ℝ i
  | constant q => exact contDiff_const
  | add a b iha ihb => simp only [Expr.eval]; exact iha.add ihb
  | mul a b iha ihb => simp only [Expr.eval]; exact iha.mul ihb
  | neg a ih => simp only [Expr.eval]; exact ih.neg

variable {b : Body} {e : Evolution}

/-- The closed-form field of a compiled model: its rate expressions, evaluated. -/
noncomputable def field (M : ContinuousModel b e) (x : Point e.states.length) :
    Point e.states.length :=
  fun i => (M.rates.expressions i).eval x

theorem field_contDiff (M : ContinuousModel b e) : ContDiff ℝ 1 (field M) :=
  contDiff_pi.mpr fun i => contDiff_eval (M.rates.expressions i)

/-- A forward solution of a field from a point: the start value, and the
derivative within the forward domain at every point of it. -/
def Solves {n : Nat} (F : Point n → Point n) (time : TimeDomain) (x₀ : Point n)
    (state : Signal n) : Prop :=
  state time.start = x₀ ∧ ∀ t ∈ time.domain, ∀ i,
    HasDerivWithinAt (fun t => state t i) (F (state t) i) time.domain t

/-- A realization is a forward solution of the closed-form field from the
declared initial state. -/
theorem realizes_iff (M : ContinuousModel b e) (state : Signal e.states.length) :
    M.Realizes state ↔ Solves (field M) e.time M.initial state := by
  rw [← M.solves_iff_realizes, M.solves_iff_field]
  exact Iff.rfl

/-! ## The trapping data -/

/-- A weighted sum of squares `V = Σ wᵢ (xᵢ − cᵢ)²`, the rate `α` and inner level
`C'` of its differential inequality, the level `C` trapped, and the sup-norm
radius `R` about the centre that contains `{V ≤ C}`: `C ≤ wᵢ R²` for every `i`. -/
structure Trapping (n : Nat) where
  weights : Fin n → ℝ
  centre : Point n
  alpha : ℝ
  inner : ℝ
  bound : ℝ
  radius : ℝ
  weights_pos : ∀ i, 0 < weights i
  alpha_pos : 0 < alpha
  margin : inner < bound
  radius_nonneg : 0 ≤ radius
  covers : ∀ i, bound ≤ weights i * radius ^ 2

namespace Trapping

variable {n : Nat} (T : Trapping n)

/-- `V(x) = Σ wᵢ (xᵢ − cᵢ)²`. -/
noncomputable def energy (x : Point n) : ℝ := ∑ i, T.weights i * (x i - T.centre i) ^ 2

/-- `V'` along a field: `Σ 2 wᵢ (xᵢ − cᵢ) Fᵢ(x)`. -/
noncomputable def rate (F : Point n → Point n) (x : Point n) : ℝ :=
  ∑ i, 2 * T.weights i * (x i - T.centre i) * F x i

/-- The sup-norm box of radius `R` about the centre. -/
noncomputable def box : Set (Point n) := Metric.closedBall T.centre T.radius

theorem energy_nonneg (x : Point n) : 0 ≤ T.energy x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (T.weights_pos i).le (sq_nonneg _)

theorem mem_box_of_energy {x : Point n} (h : T.energy x ≤ T.bound) : x ∈ T.box := by
  rw [box, Metric.mem_closedBall, dist_pi_le_iff T.radius_nonneg]
  intro i
  rw [Real.dist_eq, abs_le]
  have term : T.weights i * (x i - T.centre i) ^ 2 ≤ T.energy x :=
    Finset.single_le_sum (f := fun j => T.weights j * (x j - T.centre j) ^ 2)
      (fun j _ => mul_nonneg (T.weights_pos j).le (sq_nonneg _)) (Finset.mem_univ i)
  have sq : (x i - T.centre i) ^ 2 ≤ T.radius ^ 2 :=
    le_of_mul_le_mul_left (term.trans (h.trans (T.covers i))) (T.weights_pos i)
  exact abs_le_of_sq_le_sq' sq T.radius_nonneg

/-- The chain rule for `V` along any differentiable signal. -/
theorem energy_hasDerivWithinAt (state : Signal n) (v : Point n) (s : Set ℝ) (t : ℝ)
    (derivative : ∀ i, HasDerivWithinAt (fun t => state t i) (v i) s t) :
    HasDerivWithinAt (fun t => T.energy (state t))
      (∑ i, 2 * T.weights i * (state t i - T.centre i) * v i) s t := by
  have d := HasDerivWithinAt.sum (u := Finset.univ)
    (A := fun i s => T.weights i * (state s i - T.centre i) ^ 2)
    (A' := fun i => T.weights i * (↑(2 : ℕ) * (state t i - T.centre i) ^ (2 - 1) * v i))
    (fun i _ => (((derivative i).sub_const (T.centre i)).pow 2).const_mul (T.weights i))
  refine (d.congr (fun s _ => ?_) ?_).congr_deriv ?_
  · simp [energy, Finset.sum_apply]
  · simp [energy, Finset.sum_apply]
  · refine Finset.sum_congr rfl fun i _ => ?_
    norm_num
    ring

/-- Along a forward solution, `V' = rate`. -/
theorem energy_derivative (F : Point n → Point n) (time : TimeDomain) (x₀ : Point n)
    (state : Signal n) (h : Solves F time x₀ state) (t : ℝ) (ht : t ∈ time.domain) :
    HasDerivWithinAt (fun t => T.energy (state t)) (T.rate F (state t)) time.domain t :=
  T.energy_hasDerivWithinAt state (F (state t)) time.domain t (h.2 t ht)

/-- Every forward solution from inside the level keeps `V ≤ C`. -/
theorem invariant (F : Point n → Point n)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (time : TimeDomain) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound)
    (state : Signal n) (h : Solves F time x₀ state) :
    ∀ t ∈ time.domain, T.energy (state t) ≤ T.bound := by
  apply Dissipative.sublevel time (fun t => T.energy (state t)) (fun t => T.rate F (state t))
    T.alpha T.bound (T.energy_derivative F time x₀ state h)
  · intro t _
    refine (decrease (state t)).trans (mul_le_mul_of_nonneg_left ?_ T.alpha_pos.le)
    linarith [T.margin]
  · rw [h.1]
    exact initial

/-! ## The clamped field: bounded and globally Lipschitz -/

/-- Each coordinate projected onto the box's interval; the identity on the box. -/
noncomputable def clamp (x : Point n) : Point n :=
  fun i => (Set.projIcc (T.centre i - T.radius) (T.centre i + T.radius)
    (by linarith [T.radius_nonneg]) (x i) : ℝ)

theorem clamp_mem_box (x : Point n) : T.clamp x ∈ T.box := by
  rw [box, Metric.mem_closedBall, dist_pi_le_iff T.radius_nonneg]
  intro i
  rw [Real.dist_eq, abs_le]
  obtain ⟨lo, hi⟩ := Set.mem_Icc.mp (Set.projIcc (T.centre i - T.radius) (T.centre i + T.radius)
    (by linarith [T.radius_nonneg]) (x i)).2
  simp only [clamp]
  constructor <;> linarith

theorem clamp_of_mem_box {x : Point n} (h : x ∈ T.box) : T.clamp x = x := by
  rw [box, Metric.mem_closedBall, dist_pi_le_iff T.radius_nonneg] at h
  funext i
  have hi := abs_le.mp ((Real.dist_eq _ _) ▸ h i)
  have inside : x i ∈ Set.Icc (T.centre i - T.radius) (T.centre i + T.radius) :=
    ⟨by linarith, by linarith⟩
  simp [clamp, Set.projIcc_of_mem _ inside]

theorem clamp_lipschitz : LipschitzWith 1 T.clamp := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  calc dist (T.clamp x i) (T.clamp y i) ≤ dist (x i) (y i) := by
        have := (LipschitzWith.projIcc (a := T.centre i - T.radius)
          (b := T.centre i + T.radius) (by linarith [T.radius_nonneg])).dist_le_mul (x i) (y i)
        simpa [clamp, Subtype.dist_eq] using this
    _ ≤ dist x y := dist_le_pi_dist x y i

/-- The field read through the clamp: the true field on the box. -/
noncomputable def clamped (F : Point n → Point n) (x : Point n) : Point n := F (T.clamp x)

theorem clamped_of_mem_box (F : Point n → Point n) {x : Point n} (h : x ∈ T.box) :
    T.clamped F x = F x := by
  simp [clamped, T.clamp_of_mem_box h]

theorem rate_clamped_of_mem_box (F : Point n → Point n) {x : Point n} (h : x ∈ T.box) :
    T.rate (T.clamped F) x = T.rate F x := by
  simp only [rate, T.clamped_of_mem_box F h]

theorem field_lipschitz (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) :
    ∃ K : NNReal, LipschitzOnWith K F T.box :=
  smooth.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
    (isCompact_closedBall _ _)

theorem clamped_lipschitz (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) :
    ∃ K : NNReal, LipschitzWith K (T.clamped F) := by
  obtain ⟨K, hK⟩ := T.field_lipschitz F smooth
  refine ⟨K * 1, ?_⟩
  rw [← lipschitzOnWith_univ]
  exact hK.comp T.clamp_lipschitz.lipschitzOnWith (fun x _ => T.clamp_mem_box x)

theorem clamped_bound (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) :
    ∃ L : ℝ, ∀ x, ‖T.clamped F x‖ ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_closedBall T.centre T.radius).exists_bound_of_continuousOn
    smooth.continuous.continuousOn
  exact ⟨L, fun x => hL _ (T.clamp_mem_box x)⟩

/-! ## Existence on every `[t₀, t₀ + n]`, glued -/

/-- Picard–Lindelöf for the clamped field on `[t₀, t₀ + n]`, from `x₀`. -/
theorem clamped_solution_on (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (t₀ : ℝ) (x₀ : Point n) (m : ℕ) : ∃ α : ℝ → Point n, α t₀ = x₀ ∧
      ∀ t ∈ Set.Icc t₀ (t₀ + m),
        HasDerivWithinAt α (T.clamped F (α t)) (Set.Icc t₀ (t₀ + m)) t := by
  obtain ⟨K, hK⟩ := T.clamped_lipschitz F smooth
  obtain ⟨L, hL⟩ := T.clamped_bound F smooth
  let L' : NNReal := ⟨max L 0, le_max_right _ _⟩
  let a : NNReal := L' * m
  have endpoint : t₀ ≤ t₀ + m := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have pl : IsPicardLindelof (fun _ => T.clamped F) (tmin := t₀) (tmax := t₀ + m)
      ⟨t₀, le_rfl, endpoint⟩ x₀ a 0 L' K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => (hL x).trans (le_max_left _ _))
      hK.lipschitzOnWith ?_
    simp only [a, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_zero, sub_zero,
      add_sub_cancel_left, sub_self]
    rw [max_eq_left (Nat.cast_nonneg m)]
  obtain ⟨α, h0, hd⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨α, h0, hd⟩

private theorem Icc_mem_nhdsWithin_Ici_of_lt {a c t b : ℝ} (ha : a ≤ c) (hb : t < b) :
    Set.Icc a b ∈ nhdsWithin t (Set.Ici c) := by
  apply Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici c) (Iio_mem_nhds hb))
  intro s hs
  exact ⟨ha.trans hs.1, hs.2.le⟩

/-- Two solutions of the clamped field from the same point agree on `[t₀, b]`. -/
theorem clamped_unique_on (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ b : ℝ)
    (α β : ℝ → Point n)
    (hα : ∀ t ∈ Set.Icc t₀ b, HasDerivWithinAt α (T.clamped F (α t)) (Set.Icc t₀ b) t)
    (hβ : ∀ t ∈ Set.Icc t₀ b, HasDerivWithinAt β (T.clamped F (β t)) (Set.Icc t₀ b) t)
    (h0 : α t₀ = β t₀) : Set.EqOn α β (Set.Icc t₀ b) := by
  obtain ⟨K, hK⟩ := T.clamped_lipschitz F smooth
  refine ODE_solution_unique (v := fun _ => T.clamped F) (fun _ => hK) ?_ ?_ ?_ ?_ h0
  · exact fun t ht => (hα t ht).continuousWithinAt
  · intro t ht
    exact (hα t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_of_lt ht.1 ht.2)
  · exact fun t ht => (hβ t ht).continuousWithinAt
  · intro t ht
    exact (hβ t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsWithin_Ici_of_lt ht.1 ht.2)

/-- The chosen solution on `[t₀, t₀ + m]`. -/
noncomputable def piece (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ)
    (x₀ : Point n) (m : ℕ) : ℝ → Point n :=
  Classical.choose (T.clamped_solution_on F smooth t₀ x₀ m)

theorem piece_start (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ) (x₀ : Point n)
    (m : ℕ) : T.piece F smooth t₀ x₀ m t₀ = x₀ :=
  (Classical.choose_spec (T.clamped_solution_on F smooth t₀ x₀ m)).1

theorem piece_deriv (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ) (x₀ : Point n)
    (m : ℕ) : ∀ t ∈ Set.Icc t₀ (t₀ + m), HasDerivWithinAt (T.piece F smooth t₀ x₀ m)
      (T.clamped F (T.piece F smooth t₀ x₀ m t)) (Set.Icc t₀ (t₀ + m)) t :=
  (Classical.choose_spec (T.clamped_solution_on F smooth t₀ x₀ m)).2

theorem piece_agree (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ) (x₀ : Point n)
    {k m : ℕ} (h : k ≤ m) :
    Set.EqOn (T.piece F smooth t₀ x₀ k) (T.piece F smooth t₀ x₀ m) (Set.Icc t₀ (t₀ + k)) := by
  have cast : (k : ℝ) ≤ m := by exact_mod_cast h
  refine T.clamped_unique_on F smooth t₀ (t₀ + k) _ _ (T.piece_deriv F smooth t₀ x₀ k) ?_
    (by rw [piece_start, piece_start])
  intro t ht
  exact (T.piece_deriv F smooth t₀ x₀ m t ⟨ht.1, ht.2.trans (by linarith)⟩).mono
    (Set.Icc_subset_Icc le_rfl (by linarith))

/-- The pieces glued: at `t`, the piece on `[t₀, t₀ + ⌈t − t₀⌉ + 1]`. -/
noncomputable def glued (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ)
    (x₀ : Point n) (t : ℝ) : Point n :=
  T.piece F smooth t₀ x₀ (⌈t - t₀⌉₊ + 1) t

private theorem lt_ceil_succ (t₀ t : ℝ) : t < t₀ + ((⌈t - t₀⌉₊ + 1 : ℕ) : ℝ) := by
  push_cast
  linarith [Nat.le_ceil (t - t₀)]

theorem glued_eq_piece (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ)
    (x₀ : Point n) {m : ℕ} {t : ℝ} (ht : t ∈ Set.Icc t₀ (t₀ + m)) :
    T.glued F smooth t₀ x₀ t = T.piece F smooth t₀ x₀ m t := by
  unfold glued
  rcases le_total (⌈t - t₀⌉₊ + 1) m with h | h
  · exact T.piece_agree F smooth t₀ x₀ h ⟨ht.1, (lt_ceil_succ t₀ t).le⟩
  · exact (T.piece_agree F smooth t₀ x₀ h ht).symm

theorem glued_start (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ)
    (x₀ : Point n) : T.glued F smooth t₀ x₀ t₀ = x₀ := by
  rw [T.glued_eq_piece F smooth t₀ x₀ (m := 1) ⟨le_rfl, by norm_num⟩, piece_start]

theorem glued_deriv (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (t₀ : ℝ)
    (x₀ : Point n) (t : ℝ) (ht : t₀ ≤ t) :
    HasDerivWithinAt (T.glued F smooth t₀ x₀) (T.clamped F (T.glued F smooth t₀ x₀ t))
      (Set.Ici t₀) t := by
  have tn := lt_ceil_succ t₀ t
  have mem : Set.Icc t₀ (t₀ + ((⌈t - t₀⌉₊ + 1 : ℕ) : ℝ)) ∈ nhdsWithin t (Set.Ici t₀) :=
    Icc_mem_nhdsWithin_Ici_of_lt le_rfl tn
  have h := (T.piece_deriv F smooth t₀ x₀ (⌈t - t₀⌉₊ + 1) t ⟨ht, tn.le⟩).mono_of_mem_nhdsWithin
    mem
  rw [← T.glued_eq_piece F smooth t₀ x₀ ⟨ht, tn.le⟩] at h
  exact h.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem mem fun s hs => T.glued_eq_piece F smooth t₀ x₀ hs)
    (T.glued_eq_piece F smooth t₀ x₀ ⟨ht, tn.le⟩)

/-- Fencing: the glued solution never leaves `{V ≤ C}`. At a contact point the
clamp is the identity, and there `V' ≤ α (C' − C) < 0`. -/
theorem glued_energy_le (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (t₀ : ℝ) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound) (t : ℝ) (ht : t₀ ≤ t) :
    T.energy (T.glued F smooth t₀ x₀ t) ≤ T.bound := by
  have deriv (s : ℝ) (hs : t₀ ≤ s) :
      HasDerivWithinAt (fun s => T.energy (T.glued F smooth t₀ x₀ s))
        (T.rate (T.clamped F) (T.glued F smooth t₀ x₀ s)) (Set.Ici t₀) s :=
    T.energy_hasDerivWithinAt _ _ _ s
      (hasDerivWithinAt_pi.mp (T.glued_deriv F smooth t₀ x₀ s hs))
  have fence := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => T.energy (T.glued F smooth t₀ x₀ s))
    (f' := fun s => T.rate (T.clamped F) (T.glued F smooth t₀ x₀ s)) (a := t₀) (b := t)
    (fun s hs => ((deriv s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self)
    (fun s hs => (deriv s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (B := fun _ => T.bound) (B' := fun _ => 0)
    (by simp only [T.glued_start]; exact initial)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro s _ (contact : T.energy (T.glued F smooth t₀ x₀ s) = T.bound)
      have inbox := T.mem_box_of_energy contact.le
      show T.rate (T.clamped F) (T.glued F smooth t₀ x₀ s) < 0
      rw [T.rate_clamped_of_mem_box F inbox]
      have := decrease (T.glued F smooth t₀ x₀ s)
      rw [contact] at this
      have := mul_pos T.alpha_pos (sub_pos.mpr T.margin)
      linarith)
  exact fence ⟨ht, le_rfl⟩

/-- A forward solution of `F` from inside the level exists: the glued solution
stays where the clamped and the true field agree. -/
theorem exists_solution (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (time : TimeDomain) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound) :
    ∃ state, Solves F time x₀ state := by
  refine ⟨T.glued F smooth time.start x₀, T.glued_start F smooth time.start x₀, ?_⟩
  intro t ht i
  have ht0 : time.start ≤ t := ht
  have d := T.glued_deriv F smooth time.start x₀ t ht0
  rw [T.clamped_of_mem_box F
    (T.mem_box_of_energy (T.glued_energy_le F smooth decrease time.start x₀ initial t ht0))] at d
  exact hasDerivWithinAt_pi.mp d i

/-! ## Forward uniqueness, on the compact box -/

theorem unique (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : ∀ x, T.rate F x ≤ T.alpha * (T.inner - T.energy x))
    (time : TimeDomain) (x₀ : Point n) (initial : T.energy x₀ ≤ T.bound)
    {x y : Signal n} (hx : Solves F time x₀ x) (hy : Solves F time x₀ y) :
    Set.EqOn x y time.domain := by
  obtain ⟨K, hK⟩ := T.field_lipschitz F smooth
  have vec (z : Signal n) (hz : Solves F time x₀ z) (s : ℝ) (hs : s ∈ time.domain) :
      HasDerivWithinAt z (F (z s)) time.domain s :=
    hasDerivWithinAt_pi.mpr fun i => hz.2 s hs i
  intro t ht
  have ht0 : time.start ≤ t := ht
  have within (s : ℝ) (hs : time.start ≤ s) : s ∈ time.domain := hs
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => T.box)
    (a := time.start) (b := t) (fun _ _ => hK) ?_ ?_ ?_ ?_ ?_ ?_ (hx.1.trans hy.1.symm)
    ⟨ht0, le_rfl⟩
  · exact fun s hs => (vec x hx s (within s hs.1)).continuousWithinAt.mono
      fun r hr => within r hr.1
  · exact fun s hs => (vec x hx s (within s hs.1)).mono fun r hr => within r (hs.1.trans hr)
  · exact fun s hs => T.mem_box_of_energy
      (T.invariant F decrease time x₀ initial x hx s (within s hs.1))
  · exact fun s hs => (vec y hy s (within s hs.1)).continuousWithinAt.mono
      fun r hr => within r hr.1
  · exact fun s hs => (vec y hy s (within s hs.1)).mono fun r hr => within r (hs.1.trans hr)
  · exact fun s hs => T.mem_box_of_energy
      (T.invariant F decrease time x₀ initial y hy s (within s hs.1))

end Trapping

/-! ## The contract of a compiled model, in the registry's interface shape -/

section Compiled

variable (M : ContinuousModel b e) (T : Trapping e.states.length)

theorem compiled_exists
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound) : ∃ state, M.Realizes state := by
  obtain ⟨state, solves⟩ :=
    T.exists_solution (field M) (field_contDiff M) decrease e.time M.initial initial
  exact ⟨state, (realizes_iff M state).mpr solves⟩

theorem compiled_unique
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound)
    {x y : Signal e.states.length} (hx : M.Realizes x) (hy : M.Realizes y) :
    Set.EqOn x y e.time.domain :=
  T.unique (field M) (field_contDiff M) decrease e.time M.initial initial
    ((realizes_iff M x).mp hx) ((realizes_iff M y).mp hy)

theorem compiled_invariant
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound)
    (state : Signal e.states.length) (realized : M.Realizes state) :
    ∀ t ∈ e.time.domain, T.energy (state t) ≤ T.bound :=
  T.invariant (field M) decrease e.time M.initial initial state ((realizes_iff M state).mp realized)

/-- The loop's contract: a trajectory exists, is unique forward, and keeps the
observation computing `V` in `[0, C]`. -/
theorem loop_contract (k : Fin b.observations.length)
    (energy_eq : ∀ x, M.outputs.circuit.run x k = T.energy x)
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound) :
    Contract M.feedback e.time (LinearEnergyContract.admitted M)
      (Always e.time fun x =>
        0 ≤ M.outputs.circuit.run x k ∧ M.outputs.circuit.run x k ≤ T.bound) where
  realizable input admit := by
    obtain ⟨state, realized⟩ := compiled_exists M T decrease initial
    exact ⟨state, (LinearEnergyContract.feedback_reads M input admit state).mpr realized⟩
  unique input admit x y hx hy :=
    compiled_unique M T decrease initial
      ((LinearEnergyContract.feedback_reads M input admit x).mp hx)
      ((LinearEnergyContract.feedback_reads M input admit y).mp hy)
  holds input admit state realized t ht := by
    dsimp only
    rw [energy_eq]
    exact ⟨T.energy_nonneg _, compiled_invariant M T decrease initial state
      ((LinearEnergyContract.feedback_reads M input admit state).mp realized) t ht⟩

/-- The observed contract: `0 ≤ V ≤ C` on the observation, for every admitted input. -/
theorem energy_contract (k : Fin b.observations.length)
    (energy_eq : ∀ x, M.outputs.circuit.run x k = T.energy x)
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => 0 ≤ observation k ∧ observation k ≤ T.bound) :=
  Contract.compose (loop_contract M T k energy_eq decrease initial)
    (Contract.lift M.outputs.circuit e.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

/-- A contract for any observation that every realization keeps in `[lo, hi]`,
with existence and uniqueness from a `Trapping` the field satisfies. The
invariance may come from anywhere: a second storage function that decays on
the trapping's ball, say. -/
theorem bounded_contract (k : Fin b.observations.length) (lo hi : ℝ)
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound)
    (bounded : ∀ state, M.Realizes state → ∀ t ∈ e.time.domain,
      lo ≤ M.outputs.circuit.run (state t) k ∧ M.outputs.circuit.run (state t) k ≤ hi) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => lo ≤ observation k ∧ observation k ≤ hi) :=
  have loop : Contract M.feedback e.time (LinearEnergyContract.admitted M)
      (Always e.time fun x =>
        lo ≤ M.outputs.circuit.run x k ∧ M.outputs.circuit.run x k ≤ hi) :=
    { realizable := fun input admit => by
        obtain ⟨state, realized⟩ := compiled_exists M T decrease initial
        exact ⟨state, (LinearEnergyContract.feedback_reads M input admit state).mpr realized⟩
      unique := fun input admit x y hx hy =>
        compiled_unique M T decrease initial
          ((LinearEnergyContract.feedback_reads M input admit x).mp hx)
          ((LinearEnergyContract.feedback_reads M input admit y).mp hy)
      holds := fun input admit state realized t ht =>
        bounded state ((LinearEnergyContract.feedback_reads M input admit state).mp realized)
          t ht }
  Contract.compose loop
    (Contract.lift M.outputs.circuit e.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

/-- A bound below the initial value of `V` is refuted by the declared input's
own realization at the start. -/
theorem refuted (k : Fin b.observations.length)
    (energy_eq : ∀ x, M.outputs.circuit.run x k = T.energy x)
    (decrease : ∀ x, T.rate (field M) x ≤ T.alpha * (T.inner - T.energy x))
    (initial : T.energy M.initial ≤ T.bound) (β : ℝ) (above : β < T.energy M.initial) :
    ¬ Holds (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => observation k ≤ β) := by
  intro claim
  obtain ⟨state, realized⟩ := compiled_exists M T decrease initial
  have start : state e.time.start = M.initial := ((realizes_iff M state).mp realized).1
  have bounded := claim _ (LinearEnergyContract.declared_input_admitted M) _
    ⟨state, (LinearEnergyContract.feedback_reads M _
      (LinearEnergyContract.declared_input_admitted M) state).mpr realized, rfl⟩
    e.time.start (by simp [TimeDomain.domain])
  simp only at bounded
  rw [start, energy_eq] at bounded
  exact absurd bounded (not_le.mpr above)

end Compiled

end Gimle.Forseti.Nonlinear
