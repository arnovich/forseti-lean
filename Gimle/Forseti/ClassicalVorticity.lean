import Gimle.Asgard.Streams.MildSolution
import Gimle.Forseti.ClassicalVorticity.Comparison

/-!
# Independent classical vorticity fields

The comparison class contains ordinary periodic fields and their derivative
witnesses. It makes no reference to circuit outputs, Fourier representations,
even symmetry, energy estimates, or an intended solution. The mild realization
inhabits this class. The imported scalar comparison lemmas are conditional on a
proved differential inequality; they are not PDE uniqueness theorems.
-/
namespace Gimle.Forseti.ClassicalVorticity

open Set Real
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild

/-- A physical scalar field on time and the periodic square's covering space. -/
abbrev Field := ℝ → ℝ × ℝ → ℝ

/-- A scalar field and its spatial derivative witnesses, independent of streams. -/
structure SpatialJet where
  value : Field
  dx : Field
  dy : Field
  dxx : Field
  dyy : Field
  dxy : Field

/-- Spatial derivatives and joint continuity on the closed time strip. -/
structure Regular (f : SpatialJet) (T : ℝ) : Prop where
  deriv_x : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => f.value t (s, x.2)) (f.dx t x) x.1
  deriv_y : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => f.value t (x.1, s)) (f.dy t x) x.2
  deriv_xx : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => f.dx t (s, x.2)) (f.dxx t x) x.1
  deriv_yy : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => f.dy t (x.1, s)) (f.dyy t x) x.2
  deriv_yx : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => f.dy t (s, x.2)) (f.dxy t x) x.1
  deriv_xy : ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    HasDerivAt (fun s => f.dx t (x.1, s)) (f.dxy t x) x.2
  continuous_value : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f.value z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dx : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f.dx z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dy : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f.dy z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dxx : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f.dxx z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dyy : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f.dyy z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  continuous_dxy : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f.dxy z.1 z.2)
    {z | z.1 ∈ Icc 0 T}

/-- Separate spatial periodicity, required only on the comparison interval. -/
def Periodic (f : Field) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ x : ℝ × ℝ,
    f t (x.1 + 2 * π, x.2) = f t x ∧
    f t (x.1, x.2 + 2 * π) = f t x

/-- Classical periodic vorticity with velocity `(-ψ_y, ψ_x)`.
Only vorticity has a time-derivative witness; the stream-function gauge is free.
The PDE and time derivative are required on the open time interval. -/
structure Solves (ν T : ℝ) (initial : ℝ × ℝ → ℝ)
    (ω ψ : SpatialJet) (dt : Field) : Prop where
  vorticity_regular : Regular ω T
  stream_regular : Regular ψ T
  vorticity_periodic : Periodic ω.value T
  stream_periodic : Periodic ψ.value T
  deriv_time : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => ω.value s x) (dt t x) t
  continuous_dt : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => dt z.1 z.2)
    {z | z.1 ∈ Icc 0 T}
  initial_value : ∀ x, ω.value 0 x = initial x
  laplacian : ∀ t ∈ Icc 0 T, ∀ x, ψ.dxx t x + ψ.dyy t x = ω.value t x
  equation : ∀ t ∈ Ioo 0 T, ∀ x,
    dt t x + (-ψ.dy t x * ω.dx t x + ψ.dx t x * ω.dy t x) =
      ν * (ω.dxx t x + ω.dyy t x)

/-- Add an arbitrary time-dependent spatial constant to the stream function. -/
def SpatialJet.addGauge (ψ : SpatialJet) (c : ℝ → ℝ) : SpatialJet :=
  { ψ with value := fun t x => ψ.value t x + c t }

/-- The stream-function gauge changes neither the velocity nor the equation.
Continuity of the gauge is sufficient; no time derivative of it is needed. -/
theorem Solves.addGauge {ν T : ℝ} {initial : ℝ × ℝ → ℝ}
    {ω ψ : SpatialJet} {dt : Field} (h : Solves ν T initial ω ψ dt)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Icc 0 T)) :
    Solves ν T initial ω (ψ.addGauge c) dt := by
  refine ⟨h.vorticity_regular, ?_, h.vorticity_periodic, ?_, h.deriv_time,
    h.continuous_dt, h.initial_value, h.laplacian, h.equation⟩
  · refine { h.stream_regular with
      deriv_x := fun t ht x => (h.stream_regular.deriv_x t ht x).add_const (c t)
      deriv_y := fun t ht x => (h.stream_regular.deriv_y t ht x).add_const (c t)
      continuous_value := ?_ }
    exact h.stream_regular.continuous_value.add
      (hc.comp continuous_fst.continuousOn (fun _ hz => hz))
  · intro t ht x
    exact ⟨congrArg (fun a => a + c t) (h.stream_periodic t ht x).1,
      congrArg (fun a => a + c t) (h.stream_periodic t ht x).2⟩

/-- Subtract the actual PDEs before estimating the difference. The transport
by the first velocity is separated from the velocity-difference forcing. -/
theorem Solves.difference_equation {ν T : ℝ} {p₁ p₂ : ℝ × ℝ → ℝ}
    {ω₁ ψ₁ ω₂ ψ₂ : SpatialJet} {dt₁ dt₂ : Field}
    (h₁ : Solves ν T p₁ ω₁ ψ₁ dt₁) (h₂ : Solves ν T p₂ ω₂ ψ₂ dt₂)
    (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ × ℝ) :
    dt₁ t x - dt₂ t x +
      (-ψ₁.dy t x * (ω₁.dx t x - ω₂.dx t x) +
        ψ₁.dx t x * (ω₁.dy t x - ω₂.dy t x)) =
    ν * ((ω₁.dxx t x - ω₂.dxx t x) + (ω₁.dyy t x - ω₂.dyy t x)) -
      (-(ψ₁.dy t x - ψ₂.dy t x) * ω₂.dx t x +
        (ψ₁.dx t x - ψ₂.dx t x) * ω₂.dy t x) := by
  linear_combination h₁.equation t ht x - h₂.equation t ht x

/-- Read the already proved derivatives of a mild field as an ordinary jet. -/
noncomputable def mildJet (ν : ℚ) (ω : Stream) : SpatialJet where
  value := analyticField ν ω
  dx := seriesD₁ ν ω
  dy := seriesD₂ ν ω
  dxx := seriesD₁₁ ν ω
  dyy := seriesD₂₂ ν ω
  dxy := seriesD₁₂ ν ω

/-- Reuse the existing spatial derivative proofs without extra assumptions. -/
theorem regular_mild {ν : ℚ} {ω : Stream} {T : ℝ}
    (h : SpatialRegularity ν ω T) : Regular (mildJet ν ω) T :=
  ⟨h.derivX₁, h.derivX₂, h.derivX₁X₁, h.derivX₂X₂, h.derivX₂X₁, h.derivX₁X₂,
    h.continuous_field, h.continuous_derivX₁, h.continuous_derivX₂,
    h.continuous_derivX₁X₁, h.continuous_derivX₂X₂, h.continuous_derivX₁X₂⟩

private theorem field_periodic_x (P : RealPoly) (x : ℝ × ℝ) :
    RealPoly.field P (x.1 + 2 * π, x.2) = RealPoly.field P x := by
  unfold RealPoly.field Finsupp.sum
  apply Finset.sum_congr rfl
  intro k _
  change P k * cos ((k.1 : ℝ) * (x.1 + 2 * π) + (k.2 : ℝ) * x.2) = _
  have he : (k.1 : ℝ) * (x.1 + 2 * π) + (k.2 : ℝ) * x.2 =
      ((k.1 : ℝ) * x.1 + (k.2 : ℝ) * x.2) + (k.1 : ℝ) * (2 * π) := by ring
  rw [he, cos_add_int_mul_two_pi]

private theorem field_periodic_y (P : RealPoly) (x : ℝ × ℝ) :
    RealPoly.field P (x.1, x.2 + 2 * π) = RealPoly.field P x := by
  unfold RealPoly.field Finsupp.sum
  apply Finset.sum_congr rfl
  intro k _
  change P k * cos ((k.1 : ℝ) * x.1 + (k.2 : ℝ) * (x.2 + 2 * π)) = _
  have he : (k.1 : ℝ) * x.1 + (k.2 : ℝ) * (x.2 + 2 * π) =
      ((k.1 : ℝ) * x.1 + (k.2 : ℝ) * x.2) + (k.2 : ℝ) * (2 * π) := by ring
  rw [he, cos_add_int_mul_two_pi]

/-- Spatial periodicity follows termwise even before a convergence certificate. -/
theorem periodic_mild (ν : ℚ) (ω : Stream) (T : ℝ) :
    Periodic (analyticField ν ω) T := by
  intro t _ x
  constructor
  · apply tsum_congr
    intro n
    exact field_periodic_x (eval ν t (ω n)) x
  · apply tsum_congr
    intro n
    exact field_periodic_y (eval ν t (ω n)) x

/-- The existing mild realization satisfies the independent classical PDE class. -/
theorem of_mild {ν : ℚ} {ω : Stream} {P : Torus.TrigPoly} {T : ℝ}
    (h : IsMildClassicalSolution ν ω P T) :
    Solves (ν : ℝ) T (RealPoly.field (realEmbed P))
      (mildJet ν ω) (mildJet ν (psi ω)) (seriesDt ν ω) :=
  ⟨regular_mild h.spatial, regular_mild h.streamFunction,
    periodic_mild ν ω T, periodic_mild ν (psi ω) T,
    h.derivT, h.continuous_derivT, h.initial, h.laplacian, h.equation⟩

#print axioms of_mild
#print axioms Solves.addGauge
#print axioms Solves.difference_equation
end Gimle.Forseti.ClassicalVorticity
