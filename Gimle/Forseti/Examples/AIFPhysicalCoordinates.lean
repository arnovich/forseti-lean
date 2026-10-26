module

public import Gimle.Forseti.Examples.AIFTrajectory

/-! Exact physical/shifted coordinate identities for the antithetic integral
feedback (AIF) model `x₁' = z₁ − x₁`, `x₂' = x₁ − x₂`, `z₁' = 2 − η z₁ z₂`,
`z₂' = x₂ − η z₁ z₂`. This is an algebraic specification of the field; no Asgard
circuit is bound to it here. Trajectory results transform supplied derivatives;
they do not assert existence. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFPhysicalCoordinates

/-- Physical species order: x1, x2, z1, z2; fixed plant gain one and reference two. -/
noncomputable def physicalField (eta : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 2 - x 0, x 0 - x 1, 2 - eta*x 2*x 3, x 1 - eta*x 2*x 3]

/-- The fourth shifted coordinate includes the fixed parameter's scale. -/
noncomputable def shift (eta : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0 - 2, x 1 - 2, x 2 - 2, eta*x 3 - 1]

noncomputable def unshift (eta : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![y 0 + 2, y 1 + 2, y 2 + 2, (y 3 + 1)/eta]

/-- The linear part of the affine coordinate change, acting on velocities. -/
noncomputable def tangent (eta : ℝ) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![v 0, v 1, v 2, eta*v 3]

theorem shift_zero (eta : ℝ) : shift eta 0 = ![-2,-2,-2,-1] := by
  ext i
  fin_cases i <;> simp [shift]

theorem unshift_shift (eta : ℝ) (h : eta ≠ 0) (x : Fin 4 → ℝ) :
    unshift eta (shift eta x) = x := by
  ext i
  fin_cases i <;> simp [shift, unshift, h]

theorem shift_unshift (eta : ℝ) (h : eta ≠ 0) (y : Fin 4 → ℝ) :
    shift eta (unshift eta y) = y := by
  ext i
  fin_cases i <;> simp [shift, unshift]
  field_simp [h]
  ring

/-- No division is used in the forward field identity, so it holds at eta zero too. -/
theorem field_conjugacy (eta : ℝ) (x : Fin 4 → ℝ) :
    tangent eta (physicalField eta x) = AIFDriftModel.field eta (shift eta x) := by
  ext i
  fin_cases i
  · change x 2 - x 0 = -(x 0 - 2) + (x 2 - 2)
    ring
  · change x 0 - x 1 = (x 0 - 2) - (x 1 - 2)
    ring
  · change 2 - eta*x 2*x 3 = -(x 2 - 2) - (2 + (x 2 - 2))*(eta*x 3 - 1)
    ring
  · change eta*(x 1 - eta*x 2*x 3) =
      eta*((x 1 - 2) - (x 2 - 2) - (2 + (x 2 - 2))*(eta*x 3 - 1))
    ring

/-- Fixed eta is essential: the fourth derivative is eta times the physical one. -/
theorem shift_derivative (eta : ℝ) (state : ℝ → Fin 4 → ℝ)
    (domain : Set ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun s => state s i)
      (physicalField eta (state t) i) domain t) (i : Fin 4) :
    HasDerivWithinAt (fun s => shift eta (state s) i)
      (AIFDriftModel.field eta (shift eta (state t)) i) domain t := by
  rw [← field_conjugacy]
  fin_cases i
  · simpa [shift, tangent] using (hx 0).sub_const 2
  · simpa [shift, tangent] using (hx 1).sub_const 2
  · simpa [shift, tangent] using (hx 2).sub_const 2
  · simpa [shift, tangent] using ((hx 3).const_mul eta).sub_const 1

/-- The inverse carries supplied shifted derivatives back to physical species. -/
theorem unshift_derivative (eta : ℝ) (h : eta ≠ 0) (state : ℝ → Fin 4 → ℝ)
    (domain : Set ℝ) (t : ℝ)
    (hy : ∀ i, HasDerivWithinAt (fun s => state s i)
      (AIFDriftModel.field eta (state t) i) domain t) (i : Fin 4) :
    HasDerivWithinAt (fun s => unshift eta (state s) i)
      (physicalField eta (unshift eta (state t)) i) domain t := by
  have hf := field_conjugacy eta (unshift eta (state t))
  rw [shift_unshift eta h] at hf
  rw [← hf] at hy
  fin_cases i
  · simpa [unshift, tangent] using (hy 0).add_const 2
  · simpa [unshift, tangent] using (hy 1).add_const 2
  · simpa [unshift, tangent] using (hy 2).add_const 2
  · simpa [unshift, tangent, h] using ((hy 3).add_const 1).div_const eta

/-- Moving-energy differentiation now applies to a physical trajectory after shifting. -/
theorem physical_tubeEnergy_derivative (d : AIFSlabModel.Slab)
    (hh : d.step ≠ 0) (hp : d.etaLo < d.etaHi) (eta : ℝ)
    (state : ℝ → Fin 4 → ℝ) (domain : Set ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivWithinAt (fun s => state s i)
      (physicalField eta (state t) i) domain t) :
    HasDerivWithinAt (fun s => AIFMesh.tubeEnergy d s eta (shift eta (state s)))
      (AIFSlabModel.energyRate d (AIFSlabModel.timeCoordinate d t)
        (AIFSlabModel.etaCoordinate d eta)
        (shift eta (state t) - AIFSlabModel.center d (AIFSlabModel.timeCoordinate d t)
          (AIFSlabModel.etaCoordinate d eta))) domain t :=
  AIFTrajectory.tubeEnergy_derivative d hh hp eta (fun s => shift eta (state s))
    domain t (shift_derivative eta state domain t hx)

/-- The physical bound `x₂ ≤ 16/5` is exactly the shifted bound `y₂ ≤ 6/5`. -/
theorem output_bound_iff (eta : ℝ) (x : Fin 4 → ℝ) :
    x 1 ≤ 16/5 ↔ shift eta x 1 ≤ 6/5 := by
  simp only [shift, Matrix.cons_val_one, Matrix.cons_val_zero]
  constructor <;> intro h <;> linarith

#print axioms shift_zero
#print axioms unshift_shift
#print axioms shift_unshift
#print axioms field_conjugacy
#print axioms shift_derivative
#print axioms unshift_derivative
#print axioms physical_tubeEnergy_derivative
#print axioms output_bound_iff
end Gimle.Forseti.Examples.AIFPhysicalCoordinates
