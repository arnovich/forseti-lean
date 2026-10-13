import Gimle.Forseti.LinearEnergy

/-! Derivative-to-trajectory rules for exact storage certificates. These rules
prove properties of supplied trajectories; existence and uniqueness remain
separate obligations of any total circuit contract. -/

namespace Gimle.Forseti.Dissipative

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.LinearEnergy

/-- The full quadratic derivative, retaining both matrix factors. -/
noncomputable def quadraticRate {n : Nat} (p : QMatrix n) (s v : Point n) : ℝ :=
  dotProduct v (p.eval s) + dotProduct s (p.eval v)

/-- A quadratic storage derivative from the component-wise derivative contract. -/
theorem quadratic_derivative {n : Nat} (p : QMatrix n) (state : Signal n)
    (velocity : Point n) (domain : Set ℝ) (t : ℝ)
    (derivative : ∀ i, HasDerivWithinAt (fun t => state t i) (velocity i) domain t) :
    HasDerivWithinAt (fun t => quadratic p (state t))
      (quadraticRate p (state t) velocity) domain t := by
  have hs : HasDerivWithinAt state velocity domain t := hasDerivWithinAt_pi.mpr derivative
  have hp := (LinearAnalysis.rationalOperator p).hasFDerivAt.comp_hasDerivWithinAt t hs
  have hp' : ∀ i, HasDerivWithinAt (fun t => p.eval (state t) i)
      (p.eval velocity i) domain t := by
    intro i
    convert! hasDerivWithinAt_pi.mp hp i using 1 <;> simp [Linear.Matrix.eval]
  exact dotProduct_derivative state (fun t => p.eval (state t)) velocity (p.eval velocity)
    domain t derivative hp'

/-- A checked differential inequality `V' ≤ −γ V` on the forward half-line gives
exponential decay, `V(t) ≤ V(start) e^{−γ (t − start)}`: the integrating factor
`e^{γ t} V` is antitone. For `γ = 0` this is monotone decrease. -/
theorem decay (time : TimeDomain) (value rate : ℝ → ℝ) (gamma : ℝ)
    (derivative : ∀ t ∈ time.domain, HasDerivWithinAt value (rate t) time.domain t)
    (decrease : ∀ t ∈ time.domain, rate t ≤ -gamma * value t) :
    ∀ t ∈ time.domain, value t ≤ value time.start * Real.exp (-gamma * (t - time.start)) := by
  have factor (t : ℝ) (ht : t ∈ time.domain) :
      HasDerivWithinAt (fun t => Real.exp (gamma * t) * value t)
        (Real.exp (gamma * t) * (gamma * value t + rate t)) time.domain t := by
    have he := (Real.hasDerivAt_exp (gamma * t)).comp t
      ((hasDerivAt_id t).const_mul gamma)
    convert! he.hasDerivWithinAt.mul (derivative t ht) using 1
    simp only [Function.comp_apply]
    ring
  have anti : AntitoneOn (fun t => Real.exp (gamma * t) * value t) time.domain := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun t => Real.exp (gamma * t) * (gamma * value t + rate t))
      (convex_Ici time.start)
    · intro t ht
      exact (factor t ht).continuousWithinAt
    · intro t ht
      exact (factor t (interior_subset ht)).mono interior_subset
    · intro t ht
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have := decrease t (interior_subset ht)
      linarith
  intro t ht
  have h := anti (show time.start ∈ time.domain by simp [TimeDomain.domain]) ht ht
  have e : Real.exp (-gamma * (t - time.start)) * Real.exp (gamma * t) =
      Real.exp (gamma * time.start) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have pos := Real.exp_pos (gamma * t)
  have step : value t * Real.exp (gamma * t) ≤
      value time.start * Real.exp (-gamma * (t - time.start)) * Real.exp (gamma * t) := by
    rw [mul_assoc, e]
    linarith [h, mul_comm (Real.exp (gamma * t)) (value t),
      mul_comm (Real.exp (gamma * time.start)) (value time.start)]
  exact le_of_mul_le_mul_right step pos

/-- A checked differential inequality preserves a sublevel on the forward
half-line. No invariant is assumed on the unknown feedback trajectory. -/
theorem sublevel (time : TimeDomain) (value rate : ℝ → ℝ) (alpha bound : ℝ)
    (derivative : ∀ t ∈ time.domain, HasDerivWithinAt value (rate t) time.domain t)
    (decrease : ∀ t ∈ time.domain, rate t ≤ alpha * (bound - value t))
    (initial : value time.start ≤ bound) :
    ∀ t ∈ time.domain, value t ≤ bound := by
  have factor (t : ℝ) (ht : t ∈ time.domain) :
      HasDerivWithinAt (fun t => Real.exp (alpha * t) * (value t - bound))
        (Real.exp (alpha * t) * (alpha * (value t - bound) + rate t)) time.domain t := by
    have he := (Real.hasDerivAt_exp (alpha * t)).comp t
      ((hasDerivAt_id t).const_mul alpha)
    convert! he.hasDerivWithinAt.mul ((derivative t ht).sub_const bound) using 1
    simp only [Function.comp_apply]
    ring
  have anti : AntitoneOn (fun t => Real.exp (alpha * t) * (value t - bound)) time.domain := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun t => Real.exp (alpha * t) * (alpha * (value t - bound) + rate t))
      (convex_Ici time.start)
    · intro t ht
      exact (factor t ht).continuousWithinAt
    · intro t ht
      exact (factor t (interior_subset ht)).mono interior_subset
    · intro t ht
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have := decrease t (interior_subset ht)
      linarith
  intro t ht
  have h := anti (show time.start ∈ time.domain by simp [TimeDomain.domain]) ht ht
  have atStart : Real.exp (alpha * time.start) * (value time.start - bound) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have := h.trans atStart
  nlinarith [Real.exp_pos (alpha * t)]

#print axioms quadratic_derivative
#print axioms sublevel

end Gimle.Forseti.Dissipative
