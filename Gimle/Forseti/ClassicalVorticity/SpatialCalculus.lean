import Gimle.Forseti.ClassicalVorticity
import Gimle.Forseti.ClassicalVorticity.SquareCalculus
import Mathlib.Algebra.Order.ToIntervalMod

/-! Spatial calculus for the independent solution class. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set Real

/-- Joint continuity on the time strip gives continuity of each spatial slice. -/
theorem continuous_slice {f : Field} {T t : ℝ}
    (hf : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2) {z | z.1 ∈ Icc 0 T})
    (ht : t ∈ Icc 0 T) : Continuous (f t) :=
  hf.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ht)

/-- Differentiating a periodic scalar function preserves its period. -/
theorem periodic_derivative {f f' : ℝ → ℝ} {L : ℝ}
    (hp : Function.Periodic f L) (hd : ∀ x, HasDerivAt f (f' x) x) :
    Function.Periodic f' L := by
  intro x
  have h := (hd (x + L)).comp x ((hasDerivAt_id x).add_const L)
  have he : (fun s => f (s + L)) = f := funext hp
  change HasDerivAt (fun s => f (s + L)) (f' (x + L) * 1) x at h
  rw [he] at h
  simpa using h.unique (hd x)

/-- Periodicity of the first derivative is derived from the value field. -/
theorem Periodic.dx {f : SpatialJet} {T : ℝ} (hp : Periodic f.value T)
    (hr : Regular f T) : Periodic f.dx T := by
  intro t ht p
  constructor
  · exact periodic_derivative (f := fun x => f.value t (x,p.2))
      (f' := fun x => f.dx t (x,p.2)) (fun x => (hp t ht (x,p.2)).1)
      (fun x => hr.deriv_x t ht (x,p.2)) p.1
  · have h := hr.deriv_x t ht (p.1,p.2 + 2 * π)
    have he : (fun s => f.value t (s,p.2 + 2 * π)) =
        (fun s => f.value t (s,p.2)) := funext (fun s => (hp t ht (s,p.2)).2)
    rw [he] at h
    exact h.unique (hr.deriv_x t ht p)

/-- Periodicity of the derivative in the second coordinate, in both directions. -/
theorem Periodic.dy {f : SpatialJet} {T : ℝ} (hp : Periodic f.value T)
    (hr : Regular f T) : Periodic f.dy T := by
  intro t ht p
  constructor
  · have h := hr.deriv_y t ht (p.1 + 2 * π,p.2)
    have he : (fun s => f.value t (p.1 + 2 * π,s)) =
        (fun s => f.value t (p.1,s)) := funext (fun s => (hp t ht (p.1,s)).1)
    rw [he] at h
    exact h.unique (hr.deriv_y t ht p)
  · exact periodic_derivative (f := fun y => f.value t (p.1,y))
      (f' := fun y => f.dy t (p.1,y)) (fun y => (hp t ht (p.1,y)).2)
      (fun y => hr.deriv_y t ht (p.1,y)) p.2

/-- The difference of two spatial jets. -/
def SpatialJet.sub (f g : SpatialJet) : SpatialJet where
  value := fun t p => f.value t p - g.value t p
  dx := fun t p => f.dx t p - g.dx t p
  dy := fun t p => f.dy t p - g.dy t p
  dxx := fun t p => f.dxx t p - g.dxx t p
  dyy := fun t p => f.dyy t p - g.dyy t p
  dxy := fun t p => f.dxy t p - g.dxy t p

/-- Spatial regularity is stable under subtraction. -/
theorem Regular.sub {f g : SpatialJet} {T : ℝ} (hf : Regular f T) (hg : Regular g T) :
    Regular (f.sub g) T where
  deriv_x := fun t ht p => (hf.deriv_x t ht p).sub (hg.deriv_x t ht p)
  deriv_y := fun t ht p => (hf.deriv_y t ht p).sub (hg.deriv_y t ht p)
  deriv_xx := fun t ht p => (hf.deriv_xx t ht p).sub (hg.deriv_xx t ht p)
  deriv_yy := fun t ht p => (hf.deriv_yy t ht p).sub (hg.deriv_yy t ht p)
  deriv_yx := fun t ht p => (hf.deriv_yx t ht p).sub (hg.deriv_yx t ht p)
  deriv_xy := fun t ht p => (hf.deriv_xy t ht p).sub (hg.deriv_xy t ht p)
  continuous_value := hf.continuous_value.sub hg.continuous_value
  continuous_dx := hf.continuous_dx.sub hg.continuous_dx
  continuous_dy := hf.continuous_dy.sub hg.continuous_dy
  continuous_dxx := hf.continuous_dxx.sub hg.continuous_dxx
  continuous_dyy := hf.continuous_dyy.sub hg.continuous_dyy
  continuous_dxy := hf.continuous_dxy.sub hg.continuous_dxy

/-- Spatial periodicity is stable under subtraction. -/
theorem Periodic.sub {f g : Field} {T : ℝ} (hf : Periodic f T) (hg : Periodic g T) :
    Periodic (fun t p => f t p - g t p) T := by
  intro t ht p
  exact ⟨congrArg₂ (· - ·) (hf t ht p).1 (hg t ht p).1,
    congrArg₂ (· - ·) (hf t ht p).2 (hg t ht p).2⟩

/-- The spatial elliptic bound holds on every closed-interval slice. -/
theorem Regular.elliptic_estimate {f : SpatialJet} {T t : ℝ} (hr : Regular f T)
    (hp : Periodic f.value T) (ht : t ∈ Icc 0 T) :
    squareAverage (2 * π) (fun p => f.dx t p ^ 2 + f.dy t p ^ 2) ≤
      2 * (2 * π) ^ 2 * squareAverage (2 * π) (fun p => (f.dxx t p + f.dyy t p) ^ 2) := by
  apply periodic_elliptic_estimate (mul_pos (by norm_num) pi_pos)
    (continuous_slice hr.continuous_value ht) (continuous_slice hr.continuous_dx ht)
    (continuous_slice hr.continuous_dy ht) (continuous_slice hr.continuous_dxx ht)
    (continuous_slice hr.continuous_dyy ht)
    (fun x y => hr.deriv_x t ht (x,y)) (fun x y => hr.deriv_y t ht (x,y))
    (fun x y => hr.deriv_xx t ht (x,y)) (fun x y => hr.deriv_yy t ht (x,y))
  · intro y; simpa using (hp t ht (0,y)).1
  · intro x; simpa using (hp t ht (x,0)).2
  · intro y; simpa using (hp.dx hr t ht (0,y)).1
  · intro x; simpa using (hp.dy hr t ht (x,0)).2

/-- For arbitrary classical solutions, squared velocity difference is controlled
by squared vorticity difference, with no spectral or energy hypothesis. -/
theorem Solves.velocity_difference_sq_le {ν T : ℝ} {initial₁ initial₂ : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T initial₁ ω₁ ψ₁ dt₁) (h₂ : Solves ν T initial₂ ω₂ ψ₂ dt₂)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    squareAverage (2 * π) (fun p =>
      (ψ₁.dx t p - ψ₂.dx t p) ^ 2 + (ψ₁.dy t p - ψ₂.dy t p) ^ 2) ≤
      2 * (2 * π) ^ 2 * squareAverage (2 * π) (fun p => (ω₁.value t p - ω₂.value t p) ^ 2) := by
  have h := (h₁.stream_regular.sub h₂.stream_regular).elliptic_estimate
    (h₁.stream_periodic.sub h₂.stream_periodic) ht
  have he : ∀ p, (ψ₁.sub ψ₂).dxx t p + (ψ₁.sub ψ₂).dyy t p =
      ω₁.value t p - ω₂.value t p := by
    intro p
    dsimp [SpatialJet.sub]
    linarith [h₁.laplacian t ht p, h₂.laplacian t ht p]
  simp_rw [he] at h
  exact h

/-- A periodic field with zero squared average vanishes on the whole covering space. -/
theorem Periodic.eq_zero_of_squareAverage_sq_eq_zero {f : Field} {T t : ℝ}
    (hp : Periodic f T) (ht : t ∈ Icc 0 T) (hc : Continuous (f t))
    (hzero : squareAverage (2 * π) (fun p => f t p ^ 2) = 0) (p : ℝ × ℝ) :
    f t p = 0 := by
  have hL : 0 < 2 * π := mul_pos (by norm_num) pi_pos
  let x := toIcoMod hL 0 p.1
  let y := toIcoMod hL 0 p.2
  have hx : x ∈ Icc 0 (2 * π) := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL p.1)
  have hy : y ∈ Icc 0 (2 * π) := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL p.2)
  have hpx : Function.Periodic (fun s => f t (s,p.2)) (2 * π) :=
    fun s => (hp t ht (s,p.2)).1
  have hpy : Function.Periodic (fun s => f t (x,s)) (2 * π) :=
    fun s => (hp t ht (x,s)).2
  have hex : f t (x,p.2) = f t p := hpx.sub_zsmul_eq (toIcoDiv hL 0 p.1)
  have hey : f t (x,y) = f t (x,p.2) := hpy.sub_zsmul_eq (toIcoDiv hL 0 p.2)
  rw [← hex, ← hey]
  exact Gimle.Forseti.ClassicalVorticity.eq_zero_of_squareAverage_sq_eq_zero hL hc hzero hx hy

#print axioms Periodic.dx
#print axioms Solves.velocity_difference_sq_le
end Gimle.Forseti.ClassicalVorticity
