module

public import Gimle.Forseti.Examples.AIFSlabContainment

/-! An output bound on one AIF slab from its moving metric tube and cubic center
bounds: when the margin matrices have checked certificates, every error vector in
the tube has its output coordinate `e₁` within `±gap` of the center. The certificates
are hypotheses here. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFOutputEnclosure
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFSlabModel AIFSlabContainment

/-- Scale by gap squared to avoid division in rational certificate targets. -/
def outputConstant (d : Slab) (gap : ℚ) : QMatrix 4 := fun i j =>
  gap^2 * d.startMetric i j - if i = 1 ∧ j = 1 then 1/40000 else 0

def outputCoefficients (d : Slab) (gap : ℚ) : Fin 4 → Fin 1 → QMatrix 4 :=
  cubicCoefficients (outputConstant d gap) (scale (gap^2) (linearMetric d))
    (scale (gap^2) (quadraticMetric d)) (scale (gap^2) (cubicMetric d))

noncomputable def outputMargin (d : Slab) (gap : ℚ) (s : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => (gap : ℝ)^2 * metric d s i j - if i = 1 ∧ j = 1 then 1/40000 else 0

theorem output_binding (d : Slab) (gap : ℚ) (s u : ℝ) :
    outputMargin d gap s = tensorMatrix (outputCoefficients d gap) s u := by
  ext i j
  simp [outputMargin, metric, hermite, tensorMatrix, outputCoefficients,
    cubicCoefficients, outputConstant, linearMetric, quadraticMetric, cubicMetric,
    scale, basis, Fin.sum_univ_succ, Nat.choose]
  split_ifs <;> ring

theorem output_energy_identity (d : Slab) (gap : ℚ) (s : ℝ) (e : Fin 4 → ℝ) :
    matrixForm (outputMargin d gap s) e =
      (gap : ℝ)^2 * matrixForm (metric d s) e - (e 1)^2/40000 := by
  simp [matrixForm, outputMargin, Fin.sum_univ_succ]
  ring

/-- Closed tube membership controls both signs of the output-coordinate error. -/
theorem output_error_contained (d : Slab) (gap : ℚ) (hg : 0 ≤ gap)
    (s : ℝ) (e : Fin 4 → ℝ)
    (hm : 0 ≤ matrixForm (outputMargin d gap s) e)
    (he : matrixForm (metric d s) e ≤ 1/40000) :
    e 1 ∈ Set.Icc (-(gap : ℝ)) (gap : ℝ) := by
  rw [output_energy_identity] at hm
  have hscaled := mul_le_mul_of_nonneg_left he (sq_nonneg (gap : ℝ))
  have hs : (e 1)^2 ≤ (gap : ℝ)^2 := by nlinarith
  exact abs_le_of_sq_le_sq' hs (by exact_mod_cast hg)

theorem output_error_contained_of_certificates (d : Slab) (gap : ℚ) (hg : 0 ≤ gap)
    (certificates : Fin 4 → Fin 1 → WeightedSquares 4)
    (valid : ∀ i j, (certificates i j).Represents (outputCoefficients d gap i j))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (e : Fin 4 → ℝ)
    (he : matrixForm (metric d s) e ≤ 1/40000) :
    e 1 ∈ Set.Icc (-(gap : ℝ)) (gap : ℝ) :=
  output_error_contained d gap hg s e
    (target_nonnegative certificates valid (output_binding d gap s 0) hs (by norm_num) e) he

/-- The two interior Bernstein controls include physical endpoint slopes. -/
def hermiteControls (h a b c d : ℚ) : Fin 4 → ℚ := ![a, a+h*c/3, b-h*d/3, b]

theorem hermite_controls_binding (h a b c d : ℚ) (s : ℝ) :
    hermite h a b c d s =
      ∑ i : Fin 4, basis 3 i s * (hermiteControls h a b c d i : ℝ) := by
  simp [hermite, hermiteControls, basis, Fin.sum_univ_succ, Nat.choose]
  ring

theorem cubic_partition (s : ℝ) : (∑ i : Fin 4, basis 3 i s) = 1 := by
  simp [basis, Fin.sum_univ_succ, Nat.choose]
  ring

/-- Bounds on all four controls bound the cubic throughout the closed interval. -/
theorem hermite_upper (h a b c d bound : ℚ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (controls : ∀ i, hermiteControls h a b c d i ≤ bound) :
    hermite h a b c d s ≤ (bound : ℝ) := by
  rw [hermite_controls_binding]
  calc
    (∑ i : Fin 4, basis 3 i s * (hermiteControls h a b c d i : ℝ)) ≤
        ∑ i : Fin 4, basis 3 i s * (bound : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast controls i)
        (basis_nonnegative 3 i hs)
    _ = (bound : ℝ) := by rw [← Finset.sum_mul, cubic_partition, one_mul]

/-- Both parameter-edge cubics bound their affine parameter interpolation. -/
theorem center_upper (d : Slab) (bound : ℚ) (s u : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (lo : ∀ i, hermiteControls d.step (d.loStart 1) (d.loEnd 1)
      (d.loStartSlope 1) (d.loEndSlope 1) i ≤ bound)
    (hi : ∀ i, hermiteControls d.step (d.hiStart 1) (d.hiEnd 1)
      (d.hiStartSlope 1) (d.hiEndSlope 1) i ≤ bound) :
    center d s u 1 ≤ (bound : ℝ) := by
  have hlo := hermite_upper _ _ _ _ _ bound s hs lo
  have hhi := hermite_upper _ _ _ _ _ bound s hs hi
  have hl := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hu.2)
  have hh := mul_le_mul_of_nonneg_left hhi hu.1
  unfold center
  linarith

/-- The center bound and scaled metric margin imply the shifted x2 threshold. -/
theorem shifted_output_bound (d : Slab) (bound : ℚ) (hg : 0 ≤ 6/5 - bound)
    (certificates : Fin 4 → Fin 1 → WeightedSquares 4)
    (valid : ∀ i j, (certificates i j).Represents (outputCoefficients d (6/5-bound) i j))
    (lo : ∀ i, hermiteControls d.step (d.loStart 1) (d.loEnd 1)
      (d.loStartSlope 1) (d.loEndSlope 1) i ≤ bound)
    (hi : ∀ i, hermiteControls d.step (d.hiStart 1) (d.hiEnd 1)
      (d.hiStartSlope 1) (d.hiEndSlope 1) i ≤ bound)
    (s u : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin 4 → ℝ) (he : matrixForm (metric d s) (x - center d s u) ≤ 1/40000) :
    x 1 ≤ 6/5 := by
  have hc := center_upper d bound s u hs hu lo hi
  have herr := output_error_contained_of_certificates d (6/5-bound) hg
    certificates valid s hs (x - center d s u) he
  have he1 : x 1 - center d s u 1 ≤ (6/5 : ℝ) - (bound : ℝ) := by
    simpa using herr.2
  linarith

#print axioms output_binding
#print axioms output_energy_identity
#print axioms output_error_contained_of_certificates
#print axioms hermite_controls_binding
#print axioms cubic_partition
#print axioms hermite_upper
#print axioms center_upper
#print axioms shifted_output_bound
end Gimle.Forseti.Examples.AIFOutputEnclosure
