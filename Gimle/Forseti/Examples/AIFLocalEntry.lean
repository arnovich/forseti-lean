import Gimle.Forseti.Examples.AIFLocalStability

/-! Entry from a terminal moving tube into the fixed local Lyapunov region.
The endpoint metric and both parameter-edge centers require exact certificates. -/
namespace Gimle.Forseti.Examples.AIFLocalEntry
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open AIFLocalStability AIFSlabModel

noncomputable def value (x : Fin 4 → ℝ) : ℝ := energy (x 0) (x 1) (x 2) (x 3)

/-- The local quadratic is nonnegative for every shifted state. -/
theorem value_nonnegative (x : Fin 4 → ℝ) : 0 ≤ value x := by
  have h := positive_0 (x 0) (x 1) (x 2) (x 3)
  have hn : 0 ≤ normSq (x 0) (x 1) (x 2) (x 3) := by unfold normSq; positivity
  unfold value
  linarith

/-- A quadratic triangle estimate, with the exact factor two. -/
theorem value_add_le (x y : Fin 4 → ℝ) : value (x+y) ≤ 2*value x+2*value y := by
  have h := value_nonnegative (x-y)
  have hi : value (x+y)+value (x-y)=2*value x+2*value y := by
    simp only [value, energy, Pi.add_apply, Pi.sub_apply]
    ring
  linarith

/-- Convex interpolation between endpoint centers preserves an energy upper bound. -/
theorem value_convex_le (x y : Fin 4 → ℝ) (u bound : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (hx : value x ≤ bound) (hy : value y ≤ bound) :
    value (fun i => (1-u)*x i+u*y i) ≤ bound := by
  have hn := mul_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2))
    (value_nonnegative (x-y))
  have hi : (1-u)*value x+u*value y-value (fun i => (1-u)*x i+u*y i) =
      u*(1-u)*value (x-y) := by
    simp only [value, energy, Pi.sub_apply]
    ring
  have hxl := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hu.2)
  have hyl := mul_le_mul_of_nonneg_left hy hu.1
  nlinarith only [hn,hi,hxl,hyl]

/-- Subtract I/50 from the exact rational endpoint metric. -/
def coercivityMargin (p : QMatrix 4) : QMatrix 4 :=
  fun i j => p i j - if i=j then 1/50 else 0

theorem norm_bound_of_certificate (p : QMatrix 4) (certificate : WeightedSquares 4)
    (valid : certificate.Represents (coercivityMargin p)) (x : Fin 4 → ℝ) :
    normSq (x 0) (x 1) (x 2) (x 3)/50 ≤ matrixForm (realMatrix p) x := by
  have h := certificate.nonnegative _ valid x
  have hi : quadratic (coercivityMargin p) x = matrixForm (realMatrix p) x -
      normSq (x 0) (x 1) (x 2) (x 3)/50 := by
    rw [← matrixForm_rat]
    simp [coercivityMargin, matrixForm, realMatrix, normSq, Fin.sum_univ_succ]
    ring
  rw [hi] at h
  linarith

/-- The cubic center at the right endpoint is affine in the parameter. -/
theorem center_end_bound (d : Slab) (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (lo : value (fun i => (d.loEnd i : ℝ)) ≤ 1/400)
    (hi : value (fun i => (d.hiEnd i : ℝ)) ≤ 1/400) :
    value (center d 1 u) ≤ 1/400 := by
  have hc : center d 1 u = (fun i => (1-u)*(d.loEnd i : ℝ)+u*(d.hiEnd i : ℝ)) := by
    ext i
    simp [AIFSlabModel.center]
    ring
  rw [hc]
  exact value_convex_le (fun i => (d.loEnd i : ℝ))
    (fun i => (d.hiEnd i : ℝ)) u (1/400) hu lo hi

/-- Terminal tube membership and exact endpoint checks give a strict local entry. -/
theorem terminal_entry (d : Slab) (certificate : WeightedSquares 4)
    (valid : certificate.Represents (coercivityMargin d.endMetric))
    (lo : value (fun i => (d.loEnd i : ℝ)) ≤ 1/400)
    (hi : value (fun i => (d.hiEnd i : ℝ)) ≤ 1/400)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) (x : Fin 4 → ℝ)
    (tube : matrixForm (metric d 1) (x-center d 1 u) ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  have hc := center_end_bound d u hu lo hi
  have hn := norm_bound_of_certificate d.endMetric certificate valid (x-center d 1 u)
  have hm : metric d 1 = realMatrix d.endMetric := by ext i j; simp [metric, realMatrix]
  rw [hm] at tube
  have he := energy_le_normSq ((x-center d 1 u) 0) ((x-center d 1 u) 1)
    ((x-center d 1 u) 2) ((x-center d 1 u) 3)
  change value (x-center d 1 u) ≤ _ at he
  have ha := value_add_le (center d 1 u) (x-center d 1 u)
  have hs : center d 1 u+(x-center d 1 u)=x := by ext i; simp
  rw [hs] at ha
  constructor <;> linarith

/-- Physical time and parameter coordinates are preserved at the closed endpoint. -/
theorem terminal_entry_physical (d : Slab) (hh : d.step ≠ 0)
    (hp : d.etaLo < d.etaHi) (certificate : WeightedSquares 4)
    (valid : certificate.Represents (coercivityMargin d.endMetric))
    (lo : value (fun i => (d.loEnd i : ℝ)) ≤ 1/400)
    (hi : value (fun i => (d.hiEnd i : ℝ)) ≤ 1/400)
    (eta : ℝ) (heta : eta ∈ Set.Icc (d.etaLo : ℝ) (d.etaHi : ℝ))
    (x : Fin 4 → ℝ)
    (tube : AIFMesh.tubeEnergy d ((d.tStart : ℝ)+d.step) eta x ≤ 1/40000) :
    value x ≤ 3/400 ∧ value x < 1/100 := by
  have hr : (d.step : ℝ) ≠ 0 := by exact_mod_cast hh
  have ht : timeCoordinate d ((d.tStart : ℝ)+d.step)=1 := by simp [timeCoordinate,hr]
  simp only [AIFMesh.tubeEnergy,ht] at tube
  exact terminal_entry d certificate valid lo hi _ (etaCoordinate_mem d hp eta heta) x tube

#print axioms value_nonnegative
#print axioms value_add_le
#print axioms value_convex_le
#print axioms norm_bound_of_certificate
#print axioms center_end_bound
#print axioms terminal_entry
#print axioms terminal_entry_physical
end Gimle.Forseti.Examples.AIFLocalEntry
