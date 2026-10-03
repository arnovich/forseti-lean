import Gimle.Forseti.Nonlinear

/-! # Trapping with a decrease local to the sublevel set

`Nonlinear.Trapping` asks for `V' ≤ α (C' − V)` at **every** state. At an
equilibrium the rate is zero, so that hypothesis forces `V(x*) ≤ C'`: every set
it can trap contains every equilibrium of the field. For the Galerkin members
that is the laminar point, and no level below the laminar energy is reachable.

This module takes a general quadratic `V(x) = (x − c)ᵀ P (x − c)`, `P`
symmetric and coercive, and asks for the decrease only **on the set**:

`∀ x, V x ≤ C → V' x ≤ α (C' − V x)`, with `C' < C`.

Invariance then comes from Mathlib's barrier lemma rather than from the
integrating factor: at a first contact `V = C` the rate is `≤ α (C' − C) < 0`,
so the sublevel set is never left. Existence and uniqueness reuse the clamped
field of `Nonlinear.lean` through the diagonal ball `lower · Σ (xᵢ − cᵢ)²`,
which the quadratic dominates, so `{V ≤ C}` lies in that ball's box.

The decrease on the set is what a sum-of-squares certificate with an
S-procedure multiplier states: `α (C' − V) − V' + σ (V − C) ≥ 0` everywhere with
`σ ≥ 0`. gimle-forseti's spike 196 found such a certificate for the 3-mode
member at `ν = 1/10` inside `E ≤ 12`, below its laminar level; the example
`Examples/GalerkinNS/T3Below12.lean` is that instance. -/

namespace Gimle.Forseti.Nonlinear

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Model

/-! ## The data -/

/-- A quadratic `V = (x − c)ᵀ P (x − c)` with `P` symmetric and `P ≽ lower · I`,
the rate `α` and inner level `C'` of its differential inequality on the set, the
level `C` trapped, and a sup-norm radius `R` about the centre with `C ≤ lower · R²`,
so that `{V ≤ C}` lies in the box of radius `R`. -/
structure LocalTrapping (n : Nat) where
  matrix : Fin n → Fin n → ℝ
  centre : Point n
  alpha : ℝ
  inner : ℝ
  bound : ℝ
  radius : ℝ
  lower : ℝ
  symm : ∀ i j, matrix i j = matrix j i
  lower_pos : 0 < lower
  coercive : ∀ y : Point n, lower * ∑ i, y i ^ 2 ≤ ∑ i, ∑ j, matrix i j * y i * y j
  alpha_pos : 0 < alpha
  margin : inner < bound
  radius_nonneg : 0 ≤ radius
  covers : bound ≤ lower * radius ^ 2

namespace LocalTrapping

variable {n : Nat} (L : LocalTrapping n)

/-- `V(x) = Σᵢ Σⱼ Pᵢⱼ (xᵢ − cᵢ)(xⱼ − cⱼ)`. -/
noncomputable def energy (x : Point n) : ℝ :=
  ∑ i, ∑ j, L.matrix i j * (x i - L.centre i) * (x j - L.centre j)

/-- `V'` along a field: `Σᵢ 2 (P (x − c))ᵢ Fᵢ(x)`. -/
noncomputable def rate (F : Point n → Point n) (x : Point n) : ℝ :=
  ∑ i, (2 * ∑ j, L.matrix i j * (x j - L.centre j)) * F x i

/-- The diagonal ball `lower · Σ (xᵢ − cᵢ)²` the quadratic dominates, as a
`Trapping`: its clamp, box and glued solutions are reused. -/
noncomputable def ball : Trapping n where
  weights := fun _ => L.lower
  centre := L.centre
  alpha := L.alpha
  inner := L.inner
  bound := L.bound
  radius := L.radius
  weights_pos := fun _ => L.lower_pos
  alpha_pos := L.alpha_pos
  margin := L.margin
  radius_nonneg := L.radius_nonneg
  covers := fun _ => L.covers

theorem ball_energy_le (x : Point n) : L.ball.energy x ≤ L.energy x := by
  have h := L.coercive (fun i => x i - L.centre i)
  simp only [ball, Trapping.energy, energy]
  rw [Finset.mul_sum] at h
  exact h

theorem energy_nonneg (x : Point n) : 0 ≤ L.energy x :=
  (L.ball.energy_nonneg x).trans (L.ball_energy_le x)

theorem mem_box_of_energy {x : Point n} (h : L.energy x ≤ L.bound) : x ∈ L.ball.box :=
  L.ball.mem_box_of_energy ((L.ball_energy_le x).trans h)

/-! ## The chain rule -/

/-- The chain rule for `V` along any differentiable signal; the symmetry of `P`
folds the two halves of the product rule into one sum. -/
theorem energy_hasDerivWithinAt (state : Signal n) (v : Point n) (s : Set ℝ) (t : ℝ)
    (derivative : ∀ i, HasDerivWithinAt (fun t => state t i) (v i) s t) :
    HasDerivWithinAt (fun t => L.energy (state t))
      (∑ i, (2 * ∑ j, L.matrix i j * (state t j - L.centre j)) * v i) s t := by
  have inner (i : Fin n) : HasDerivWithinAt
      (fun s => ∑ j, L.matrix i j * (state s i - L.centre i) * (state s j - L.centre j))
      (∑ j, L.matrix i j * (v i * (state t j - L.centre j) + (state t i - L.centre i) * v j))
      s t := by
    have d := HasDerivWithinAt.sum (u := Finset.univ)
      (A := fun j s => L.matrix i j * (state s i - L.centre i) * (state s j - L.centre j))
      (A' := fun j => L.matrix i j * (v i * (state t j - L.centre j) + (state t i - L.centre i) * v j))
      (fun j _ => by
        have h := (((derivative i).sub_const (L.centre i)).const_mul (L.matrix i j)).mul
          ((derivative j).sub_const (L.centre j))
        exact h.congr_deriv (by ring))
    refine (d.congr (fun s _ => ?_) ?_)
    · simp [Finset.sum_apply]
    · simp [Finset.sum_apply]
  have d := HasDerivWithinAt.sum (u := Finset.univ)
    (A := fun i s => ∑ j, L.matrix i j * (state s i - L.centre i) * (state s j - L.centre j))
    (A' := fun i => ∑ j, L.matrix i j * (v i * (state t j - L.centre j) + (state t i - L.centre i) * v j))
    (fun i _ => inner i)
  refine (d.congr (fun s _ => ?_) ?_).congr_deriv ?_
  · simp [energy, Finset.sum_apply]
  · simp [energy, Finset.sum_apply]
  · -- Σᵢ Σⱼ Pᵢⱼ (vᵢ yⱼ + yᵢ vⱼ) = Σᵢ (2 Σⱼ Pᵢⱼ yⱼ) vᵢ, by symmetry of `P`.
    have swap : (∑ i, ∑ j, L.matrix i j * ((state t i - L.centre i) * v j)) =
        ∑ i, ∑ j, L.matrix i j * ((state t j - L.centre j) * v i) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [L.symm j i]
    calc (∑ i, ∑ j, L.matrix i j * (v i * (state t j - L.centre j) + (state t i - L.centre i) * v j))
        = (∑ i, ∑ j, L.matrix i j * ((state t j - L.centre j) * v i))
          + ∑ i, ∑ j, L.matrix i j * ((state t i - L.centre i) * v j) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 2 * ∑ i, ∑ j, L.matrix i j * ((state t j - L.centre j) * v i) := by
          rw [swap]; ring
      _ = ∑ i, (2 * ∑ j, L.matrix i j * (state t j - L.centre j)) * v i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring

/-- Along a forward solution, `V' = rate`. -/
theorem energy_derivative (F : Point n → Point n) (time : TimeDomain) (x₀ : Point n)
    (state : Signal n) (h : Solves F time x₀ state) (t : ℝ) (ht : t ∈ time.domain) :
    HasDerivWithinAt (fun t => L.energy (state t)) (L.rate F (state t)) time.domain t :=
  L.energy_hasDerivWithinAt state (F (state t)) time.domain t (h.2 t ht)

theorem rate_clamped_of_mem_box (F : Point n → Point n) {x : Point n} (h : x ∈ L.ball.box) :
    L.rate (L.ball.clamped F) x = L.rate F x := by
  simp only [rate, L.ball.clamped_of_mem_box F h]

/-! ## Invariance by the barrier lemma -/

/-- The decrease hypothesis, on the set only. -/
def Decreases (F : Point n → Point n) : Prop :=
  ∀ x, L.energy x ≤ L.bound → L.rate F x ≤ L.alpha * (L.inner - L.energy x)

/-- Every forward solution from inside the level keeps `V ≤ C`: at a contact
point `V' ≤ α (C' − C) < 0`, so the level is a barrier. -/
theorem invariant (F : Point n → Point n) (decrease : L.Decreases F)
    (time : TimeDomain) (x₀ : Point n) (initial : L.energy x₀ ≤ L.bound)
    (state : Signal n) (h : Solves F time x₀ state) :
    ∀ t ∈ time.domain, L.energy (state t) ≤ L.bound := by
  intro t ht
  have ht0 : time.start ≤ t := ht
  have deriv (s : ℝ) (hs : time.start ≤ s) :
      HasDerivWithinAt (fun s => L.energy (state s)) (L.rate F (state s)) (Set.Ici time.start) s :=
    L.energy_derivative F time x₀ state h s hs
  have fence := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => L.energy (state s)) (f' := fun s => L.rate F (state s))
    (a := time.start) (b := t)
    (fun s hs => ((deriv s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self)
    (fun s hs => (deriv s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (B := fun _ => L.bound) (B' := fun _ => 0)
    (by rw [h.1]; exact initial)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro s _ (contact : L.energy (state s) = L.bound)
      show L.rate F (state s) < 0
      have := decrease (state s) contact.le
      rw [contact] at this
      have := mul_pos L.alpha_pos (sub_pos.mpr L.margin)
      linarith)
  exact fence ⟨ht0, le_rfl⟩

/-! ## Existence on the forward half-line, and uniqueness -/

/-- Fencing the glued solution of the clamped field: at a contact point the clamp
is the identity and `V' ≤ α (C' − C) < 0`. -/
theorem glued_energy_le (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : L.Decreases F) (t₀ : ℝ) (x₀ : Point n) (initial : L.energy x₀ ≤ L.bound)
    (t : ℝ) (ht : t₀ ≤ t) : L.energy (L.ball.glued F smooth t₀ x₀ t) ≤ L.bound := by
  have deriv (s : ℝ) (hs : t₀ ≤ s) :
      HasDerivWithinAt (fun s => L.energy (L.ball.glued F smooth t₀ x₀ s))
        (L.rate (L.ball.clamped F) (L.ball.glued F smooth t₀ x₀ s)) (Set.Ici t₀) s :=
    L.energy_hasDerivWithinAt _ _ _ s
      (hasDerivWithinAt_pi.mp (L.ball.glued_deriv F smooth t₀ x₀ s hs))
  have fence := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => L.energy (L.ball.glued F smooth t₀ x₀ s))
    (f' := fun s => L.rate (L.ball.clamped F) (L.ball.glued F smooth t₀ x₀ s)) (a := t₀) (b := t)
    (fun s hs => ((deriv s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self)
    (fun s hs => (deriv s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (B := fun _ => L.bound) (B' := fun _ => 0)
    (by simp only [Trapping.glued_start]; exact initial)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro s _ (contact : L.energy (L.ball.glued F smooth t₀ x₀ s) = L.bound)
      have inbox := L.mem_box_of_energy contact.le
      show L.rate (L.ball.clamped F) (L.ball.glued F smooth t₀ x₀ s) < 0
      rw [L.rate_clamped_of_mem_box F inbox]
      have := decrease (L.ball.glued F smooth t₀ x₀ s) contact.le
      rw [contact] at this
      have := mul_pos L.alpha_pos (sub_pos.mpr L.margin)
      linarith)
  exact fence ⟨ht, le_rfl⟩

/-- A forward solution of `F` from inside the level exists: the glued solution of
the clamped field stays where the clamp is the identity. -/
theorem exists_solution (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : L.Decreases F) (time : TimeDomain) (x₀ : Point n)
    (initial : L.energy x₀ ≤ L.bound) : ∃ state, Solves F time x₀ state := by
  refine ⟨L.ball.glued F smooth time.start x₀, L.ball.glued_start F smooth time.start x₀, ?_⟩
  intro t ht i
  have ht0 : time.start ≤ t := ht
  have d := L.ball.glued_deriv F smooth time.start x₀ t ht0
  rw [L.ball.clamped_of_mem_box F
    (L.mem_box_of_energy (L.glued_energy_le F smooth decrease time.start x₀ initial t ht0))] at d
  exact hasDerivWithinAt_pi.mp d i

/-- Forward uniqueness: Lipschitz continuity on the compact box, which the
invariant keeps every realization inside. -/
theorem unique (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (decrease : L.Decreases F)
    (time : TimeDomain) (x₀ : Point n) (initial : L.energy x₀ ≤ L.bound)
    {x y : Signal n} (hx : Solves F time x₀ x) (hy : Solves F time x₀ y) :
    Set.EqOn x y time.domain := by
  obtain ⟨K, hK⟩ := L.ball.field_lipschitz F smooth
  have vec (z : Signal n) (hz : Solves F time x₀ z) (s : ℝ) (hs : s ∈ time.domain) :
      HasDerivWithinAt z (F (z s)) time.domain s :=
    hasDerivWithinAt_pi.mpr fun i => hz.2 s hs i
  intro t ht
  have ht0 : time.start ≤ t := ht
  have within (s : ℝ) (hs : time.start ≤ s) : s ∈ time.domain := hs
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => L.ball.box)
    (a := time.start) (b := t) (fun _ _ => hK) ?_ ?_ ?_ ?_ ?_ ?_ (hx.1.trans hy.1.symm)
    ⟨ht0, le_rfl⟩
  · exact fun s hs => (vec x hx s (within s hs.1)).continuousWithinAt.mono
      fun r hr => within r hr.1
  · exact fun s hs => (vec x hx s (within s hs.1)).mono fun r hr => within r (hs.1.trans hr)
  · exact fun s hs => L.mem_box_of_energy
      (L.invariant F decrease time x₀ initial x hx s (within s hs.1))
  · exact fun s hs => (vec y hy s (within s hs.1)).continuousWithinAt.mono
      fun r hr => within r hr.1
  · exact fun s hs => (vec y hy s (within s hs.1)).mono fun r hr => within r (hs.1.trans hr)
  · exact fun s hs => L.mem_box_of_energy
      (L.invariant F decrease time x₀ initial y hy s (within s hs.1))

end LocalTrapping

/-! ## The contracts of a compiled model -/

section Compiled

variable {b : Body} {e : Evolution}
variable (M : ContinuousModel b e) (L : LocalTrapping e.states.length)

theorem local_compiled_exists (decrease : L.Decreases (field M))
    (initial : L.energy M.initial ≤ L.bound) : ∃ state, M.Realizes state := by
  obtain ⟨state, solves⟩ :=
    L.exists_solution (field M) (field_contDiff M) decrease e.time M.initial initial
  exact ⟨state, (realizes_iff M state).mpr solves⟩

theorem local_compiled_unique (decrease : L.Decreases (field M))
    (initial : L.energy M.initial ≤ L.bound)
    {x y : Signal e.states.length} (hx : M.Realizes x) (hy : M.Realizes y) :
    Set.EqOn x y e.time.domain :=
  L.unique (field M) (field_contDiff M) decrease e.time M.initial initial
    ((realizes_iff M x).mp hx) ((realizes_iff M y).mp hy)

theorem local_compiled_invariant (decrease : L.Decreases (field M))
    (initial : L.energy M.initial ≤ L.bound)
    (state : Signal e.states.length) (realized : M.Realizes state) :
    ∀ t ∈ e.time.domain, L.energy (state t) ≤ L.bound :=
  L.invariant (field M) decrease e.time M.initial initial state
    ((realizes_iff M state).mp realized)

/-- A contract for any observation that every realization keeps in `[lo, hi]`,
with existence and uniqueness from a `LocalTrapping` the field satisfies on its
set. The bound typically comes from containment: `{V ≤ C}` inside `{E ≤ hi}`
by an S-lemma certificate. -/
theorem local_bounded_contract (k : Fin b.observations.length) (lo hi : ℝ)
    (decrease : L.Decreases (field M)) (initial : L.energy M.initial ≤ L.bound)
    (bounded : ∀ state, M.Realizes state → ∀ t ∈ e.time.domain,
      lo ≤ M.outputs.circuit.run (state t) k ∧ M.outputs.circuit.run (state t) k ≤ hi) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => lo ≤ observation k ∧ observation k ≤ hi) := by
  have loop : Contract M.feedback e.time (LinearEnergyContract.admitted M)
      (Always e.time fun x =>
        lo ≤ M.outputs.circuit.run x k ∧ M.outputs.circuit.run x k ≤ hi) :=
    { realizable := fun input admit => by
        obtain ⟨state, realized⟩ := local_compiled_exists M L decrease initial
        exact ⟨state, (LinearEnergyContract.feedback_reads M input admit state).mpr realized⟩
      unique := fun input admit x y hx hy =>
        local_compiled_unique M L decrease initial
          ((LinearEnergyContract.feedback_reads M input admit x).mp hx)
          ((LinearEnergyContract.feedback_reads M input admit y).mp hy)
      holds := fun input admit state realized t ht =>
        bounded state ((LinearEnergyContract.feedback_reads M input admit state).mp realized) t ht }
  exact Contract.compose loop
    (Contract.lift M.outputs.circuit e.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

end Compiled

#print axioms LocalTrapping.invariant
#print axioms LocalTrapping.exists_solution
#print axioms LocalTrapping.unique
#print axioms local_bounded_contract

end Gimle.Forseti.Nonlinear
