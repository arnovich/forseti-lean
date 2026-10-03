import Gimle.Forseti.LocalTrapping

/-! # Trapping for a polynomial `V` with a bounded sublevel set

`LocalTrapping` takes a quadratic form about a centre. The 5-mode Galerkin member's
below-laminar set (gimle-forseti's task 213) is a sublevel set of a degree-4
polynomial, a tube around what is, in simulation, a rotating wave; no quadratic
form about a centre was found below the laminar level there. This module takes
`V` as a polynomial expression (`Gimle.Asgard.Polynomial.Expr`), differentiates
it symbolically (`Expr.diff`), proves the chain rule for it along any
differentiable signal (`Expr.eval_hasDerivWithinAt`), and asks for:

* the decrease on the set, `∀ x, V x ≤ C → V' x ≤ α (C' − V x)` with `C' < C`;
* a sup-norm box about some point that contains `{V ≤ C}`, as a checkable
  hypothesis `boxed : ∀ x, V x ≤ C → ∀ i, |xᵢ − cᵢ| ≤ R` (for the tube it follows
  from the containment `V ≤ C → E ≤ 6`).

Invariance is the barrier lemma; existence and uniqueness reuse the clamped field
of `Nonlinear.lean` through a `Trapping` of radius `R` about the centre whose only
job is the box (`box`). The instance is `Examples/GalerkinNS/K5Below6.lean`. -/

namespace Gimle.Forseti.Nonlinear

open Gimle.Forseti
open Gimle.Forseti.Trajectory
open Gimle.Asgard
open Gimle.Asgard.Dynamics
open Gimle.Asgard.Model
open Gimle.Asgard.Polynomial

/-! ## Symbolic differentiation of a polynomial expression -/

/-- `∂/∂xₖ` of a polynomial expression, as an expression. It lives in this
namespace, not Asgard's, so it is written `Nonlinear.Expr.diff k e`. -/
def Expr.diff {n : Nat} (k : Fin n) : Expr n → Expr n
  | .var i => if i = k then .constant 1 else .constant 0
  | .constant _ => .constant 0
  | .add a b => .add (Expr.diff k a) (Expr.diff k b)
  | .mul a b => .add (.mul (Expr.diff k a) b) (.mul a (Expr.diff k b))
  | .neg a => .neg (Expr.diff k a)

/-- The chain rule: along a signal with derivative `v`, `e ∘ state` has derivative
`Σₖ (∂ₖe)(state t) · vₖ`. -/
theorem Expr.eval_hasDerivWithinAt {n : Nat} (e : Expr n) (state : Signal n) (v : Point n)
    (s : Set ℝ) (t : ℝ) (derivative : ∀ i, HasDerivWithinAt (fun t => state t i) (v i) s t) :
    HasDerivWithinAt (fun t => e.eval (state t)) (∑ k, (Expr.diff k e).eval (state t) * v k) s t := by
  induction e with
  | var i =>
    have h := derivative i
    refine h.congr_deriv ?_
    simp [Expr.eval, Expr.diff, apply_ite (Expr.eval (state t)), ite_mul, Finset.sum_ite_eq]
  | constant q =>
    refine (hasDerivWithinAt_const t s (q : ℝ)).congr_deriv ?_
    simp [Expr.eval, Expr.diff]
  | add a b iha ihb =>
    refine (iha.add ihb).congr_deriv ?_
    simp only [Expr.eval, Expr.diff, add_mul, Finset.sum_add_distrib]
  | mul a b iha ihb =>
    refine (iha.mul ihb).congr_deriv ?_
    simp only [Expr.eval, Expr.diff]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  | neg a ih =>
    refine ih.neg.congr_deriv ?_
    simp only [Expr.eval, Expr.diff, neg_mul, Finset.sum_neg_distrib]

/-! ## The data -/

/-- A polynomial `V`, the rate `α` and inner level `C'` of its differential
inequality on the set, the level `C` trapped, and a sup-norm box of radius `R`
about `centre` that `{V ≤ C}` lies in. -/
structure PolynomialTrapping (n : Nat) where
  poly : Expr n
  centre : Point n
  alpha : ℝ
  inner : ℝ
  bound : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  alpha_pos : 0 < alpha
  margin : inner < bound
  boxed : ∀ x : Point n, poly.eval x ≤ bound → ∀ i, |x i - centre i| ≤ radius

namespace PolynomialTrapping

variable {n : Nat} (P : PolynomialTrapping n)

/-- `V(x)`, the polynomial evaluated. -/
noncomputable def energy (x : Point n) : ℝ := P.poly.eval x

/-- `V'` along a field: `Σₖ (∂ₖV)(x) Fₖ(x)`. -/
noncomputable def rate (F : Point n → Point n) (x : Point n) : ℝ :=
  ∑ k, (Expr.diff k P.poly).eval x * F x k

/-- The box, as a `Trapping` of radius `R` about the centre whose clamp and glued
solutions are reused; its own level and rate play no role. -/
noncomputable def box : Trapping n where
  weights := fun _ => 1
  centre := P.centre
  alpha := 1
  inner := -1
  bound := P.radius ^ 2
  radius := P.radius
  weights_pos := fun _ => one_pos
  alpha_pos := one_pos
  margin := by linarith [sq_nonneg P.radius]
  radius_nonneg := P.radius_nonneg
  covers := fun _ => by simp

theorem mem_box_of_energy {x : Point n} (h : P.energy x ≤ P.bound) : x ∈ P.box.box := by
  rw [Trapping.box, Metric.mem_closedBall]
  change dist x P.centre ≤ P.radius
  rw [dist_pi_le_iff P.radius_nonneg]
  intro i
  rw [Real.dist_eq]
  exact P.boxed x h i

/-- Along a forward solution, `V' = rate`. -/
theorem energy_derivative (F : Point n → Point n) (time : TimeDomain) (x₀ : Point n)
    (state : Signal n) (h : Solves F time x₀ state) (t : ℝ) (ht : t ∈ time.domain) :
    HasDerivWithinAt (fun t => P.energy (state t)) (P.rate F (state t)) time.domain t :=
  Expr.eval_hasDerivWithinAt P.poly state (F (state t)) time.domain t (h.2 t ht)

theorem rate_clamped_of_mem_box (F : Point n → Point n) {x : Point n} (h : x ∈ P.box.box) :
    P.rate (P.box.clamped F) x = P.rate F x := by
  simp only [rate, P.box.clamped_of_mem_box F h]

/-- The decrease hypothesis, on the set only. -/
def Decreases (F : Point n → Point n) : Prop :=
  ∀ x, P.energy x ≤ P.bound → P.rate F x ≤ P.alpha * (P.inner - P.energy x)

/-! ## Invariance, existence, uniqueness -/

/-- Every forward solution from inside the level keeps `V ≤ C`: at a contact point
`V' ≤ α (C' − C) < 0`, so the level is a barrier. -/
theorem invariant (F : Point n → Point n) (decrease : P.Decreases F)
    (time : TimeDomain) (x₀ : Point n) (initial : P.energy x₀ ≤ P.bound)
    (state : Signal n) (h : Solves F time x₀ state) :
    ∀ t ∈ time.domain, P.energy (state t) ≤ P.bound := by
  intro t ht
  have ht0 : time.start ≤ t := ht
  have deriv (s : ℝ) (hs : time.start ≤ s) :
      HasDerivWithinAt (fun s => P.energy (state s)) (P.rate F (state s)) (Set.Ici time.start) s :=
    P.energy_derivative F time x₀ state h s hs
  have fence := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => P.energy (state s)) (f' := fun s => P.rate F (state s))
    (a := time.start) (b := t)
    (fun s hs => ((deriv s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self)
    (fun s hs => (deriv s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (B := fun _ => P.bound) (B' := fun _ => 0)
    (by rw [h.1]; exact initial)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro s _ (contact : P.energy (state s) = P.bound)
      show P.rate F (state s) < 0
      have := decrease (state s) contact.le
      rw [contact] at this
      have := mul_pos P.alpha_pos (sub_pos.mpr P.margin)
      linarith)
  exact fence ⟨ht0, le_rfl⟩

/-- Fencing the glued solution of the clamped field. -/
theorem glued_energy_le (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : P.Decreases F) (t₀ : ℝ) (x₀ : Point n) (initial : P.energy x₀ ≤ P.bound)
    (t : ℝ) (ht : t₀ ≤ t) : P.energy (P.box.glued F smooth t₀ x₀ t) ≤ P.bound := by
  have deriv (s : ℝ) (hs : t₀ ≤ s) :
      HasDerivWithinAt (fun s => P.energy (P.box.glued F smooth t₀ x₀ s))
        (P.rate (P.box.clamped F) (P.box.glued F smooth t₀ x₀ s)) (Set.Ici t₀) s :=
    Expr.eval_hasDerivWithinAt P.poly _ _ _ s
      (hasDerivWithinAt_pi.mp (P.box.glued_deriv F smooth t₀ x₀ s hs))
  have fence := image_le_of_deriv_right_lt_deriv_boundary'
    (f := fun s => P.energy (P.box.glued F smooth t₀ x₀ s))
    (f' := fun s => P.rate (P.box.clamped F) (P.box.glued F smooth t₀ x₀ s)) (a := t₀) (b := t)
    (fun s hs => ((deriv s hs.1).continuousWithinAt).mono Set.Icc_subset_Ici_self)
    (fun s hs => (deriv s hs.1).mono (Set.Ici_subset_Ici.mpr hs.1))
    (B := fun _ => P.bound) (B' := fun _ => 0)
    (by simp only [Trapping.glued_start]; exact initial)
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
    (by
      intro s _ (contact : P.energy (P.box.glued F smooth t₀ x₀ s) = P.bound)
      have inbox := P.mem_box_of_energy contact.le
      show P.rate (P.box.clamped F) (P.box.glued F smooth t₀ x₀ s) < 0
      rw [P.rate_clamped_of_mem_box F inbox]
      have := decrease (P.box.glued F smooth t₀ x₀ s) contact.le
      rw [contact] at this
      have := mul_pos P.alpha_pos (sub_pos.mpr P.margin)
      linarith)
  exact fence ⟨ht, le_rfl⟩

/-- A forward solution of `F` from inside the level exists. -/
theorem exists_solution (F : Point n → Point n) (smooth : ContDiff ℝ 1 F)
    (decrease : P.Decreases F) (time : TimeDomain) (x₀ : Point n)
    (initial : P.energy x₀ ≤ P.bound) : ∃ state, Solves F time x₀ state := by
  refine ⟨P.box.glued F smooth time.start x₀, P.box.glued_start F smooth time.start x₀, ?_⟩
  intro t ht i
  have ht0 : time.start ≤ t := ht
  have d := P.box.glued_deriv F smooth time.start x₀ t ht0
  rw [P.box.clamped_of_mem_box F
    (P.mem_box_of_energy (P.glued_energy_le F smooth decrease time.start x₀ initial t ht0))] at d
  exact hasDerivWithinAt_pi.mp d i

/-- Forward uniqueness, on the compact box the invariant keeps every realization in. -/
theorem unique (F : Point n → Point n) (smooth : ContDiff ℝ 1 F) (decrease : P.Decreases F)
    (time : TimeDomain) (x₀ : Point n) (initial : P.energy x₀ ≤ P.bound)
    {x y : Signal n} (hx : Solves F time x₀ x) (hy : Solves F time x₀ y) :
    Set.EqOn x y time.domain := by
  obtain ⟨K, hK⟩ := P.box.field_lipschitz F smooth
  have vec (z : Signal n) (hz : Solves F time x₀ z) (s : ℝ) (hs : s ∈ time.domain) :
      HasDerivWithinAt z (F (z s)) time.domain s :=
    hasDerivWithinAt_pi.mpr fun i => hz.2 s hs i
  intro t ht
  have ht0 : time.start ≤ t := ht
  have within (s : ℝ) (hs : time.start ≤ s) : s ∈ time.domain := hs
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => P.box.box)
    (a := time.start) (b := t) (fun _ _ => hK) ?_ ?_ ?_ ?_ ?_ ?_ (hx.1.trans hy.1.symm)
    ⟨ht0, le_rfl⟩
  · exact fun s hs => (vec x hx s (within s hs.1)).continuousWithinAt.mono
      fun r hr => within r hr.1
  · exact fun s hs => (vec x hx s (within s hs.1)).mono fun r hr => within r (hs.1.trans hr)
  · exact fun s hs => P.mem_box_of_energy
      (P.invariant F decrease time x₀ initial x hx s (within s hs.1))
  · exact fun s hs => (vec y hy s (within s hs.1)).continuousWithinAt.mono
      fun r hr => within r hr.1
  · exact fun s hs => (vec y hy s (within s hs.1)).mono fun r hr => within r (hs.1.trans hr)
  · exact fun s hs => P.mem_box_of_energy
      (P.invariant F decrease time x₀ initial y hy s (within s hs.1))

end PolynomialTrapping

/-! ## The contracts of a compiled model -/

section Compiled

variable {b : Body} {e : Evolution}
variable (M : ContinuousModel b e) (P : PolynomialTrapping e.states.length)

theorem poly_compiled_exists (decrease : P.Decreases (field M))
    (initial : P.energy M.initial ≤ P.bound) : ∃ state, M.Realizes state := by
  obtain ⟨state, solves⟩ :=
    P.exists_solution (field M) (field_contDiff M) decrease e.time M.initial initial
  exact ⟨state, (realizes_iff M state).mpr solves⟩

theorem poly_compiled_unique (decrease : P.Decreases (field M))
    (initial : P.energy M.initial ≤ P.bound)
    {x y : Signal e.states.length} (hx : M.Realizes x) (hy : M.Realizes y) :
    Set.EqOn x y e.time.domain :=
  P.unique (field M) (field_contDiff M) decrease e.time M.initial initial
    ((realizes_iff M x).mp hx) ((realizes_iff M y).mp hy)

theorem poly_compiled_invariant (decrease : P.Decreases (field M))
    (initial : P.energy M.initial ≤ P.bound)
    (state : Signal e.states.length) (realized : M.Realizes state) :
    ∀ t ∈ e.time.domain, P.energy (state t) ≤ P.bound :=
  P.invariant (field M) decrease e.time M.initial initial state
    ((realizes_iff M state).mp realized)

/-- A contract for any observation that every realization keeps in `[lo, hi]`,
with existence and uniqueness from a `PolynomialTrapping` the field satisfies on
its set; the bound typically comes from containment by an S-lemma certificate. -/
theorem poly_bounded_contract (k : Fin b.observations.length) (lo hi : ℝ)
    (decrease : P.Decreases (field M)) (initial : P.energy M.initial ≤ P.bound)
    (bounded : ∀ state, M.Realizes state → ∀ t ∈ e.time.domain,
      lo ≤ M.outputs.circuit.run (state t) k ∧ M.outputs.circuit.run (state t) k ≤ hi) :
    Contract (LinearEnergyContract.observed M) e.time (LinearEnergyContract.admitted M)
      (Always e.time fun observation => lo ≤ observation k ∧ observation k ≤ hi) := by
  have loop : Contract M.feedback e.time (LinearEnergyContract.admitted M)
      (Always e.time fun x =>
        lo ≤ M.outputs.circuit.run x k ∧ M.outputs.circuit.run x k ≤ hi) :=
    { realizable := fun input admit => by
        obtain ⟨state, realized⟩ := poly_compiled_exists M P decrease initial
        exact ⟨state, (LinearEnergyContract.feedback_reads M input admit state).mpr realized⟩
      unique := fun input admit x y hx hy =>
        poly_compiled_unique M P decrease initial
          ((LinearEnergyContract.feedback_reads M input admit x).mp hx)
          ((LinearEnergyContract.feedback_reads M input admit y).mp hy)
      holds := fun input admit state realized t ht =>
        bounded state ((LinearEnergyContract.feedback_reads M input admit state).mp realized) t ht }
  exact Contract.compose loop
    (Contract.lift M.outputs.circuit e.time (fun _ bounded => bounded))
    (DomainRespecting.lift _ _ _)

end Compiled

#print axioms Expr.eval_hasDerivWithinAt
#print axioms PolynomialTrapping.invariant
#print axioms PolynomialTrapping.exists_solution
#print axioms PolynomialTrapping.unique
#print axioms poly_bounded_contract

end Gimle.Forseti.Nonlinear
