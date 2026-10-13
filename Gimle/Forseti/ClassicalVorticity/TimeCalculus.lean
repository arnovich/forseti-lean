import Gimle.Forseti.ClassicalVorticity.SpatialCalculus
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Continuity and time differentiation of the spatial square average. -/
namespace Gimle.Forseti.ClassicalVorticity
open Set MeasureTheory Filter
open scoped Topology Interval

/-- The iterated normalized average is the normalized area integral. -/
theorem squareAverage_eq_integral {L : ℝ} (hL : 0 < L) {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) :
    squareAverage L f = (∫ p in Icc 0 L ×ˢ Icc 0 L, f p) / L ^ 2 := by
  have hi : IntegrableOn f (Icc 0 L ×ˢ Icc 0 L) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h := setIntegral_prod f (μ := volume) (ν := volume)
    (by simpa only [Measure.volume_eq_prod] using hi)
  simp only [← Measure.volume_eq_prod] at h
  unfold squareAverage average
  rw [intervalIntegral.integral_div]
  simp_rw [intervalIntegral.integral_of_le hL.le, ← integral_Icc_eq_integral_Ioc]
  rw [← h, div_div, pow_two]

/-- Continuous parameter dependence survives averaging over the square. -/
theorem continuous_squareAverage {X : Type*} [TopologicalSpace X]
    {f : X × (ℝ × ℝ) → ℝ} (hf : Continuous f) (L : ℝ) :
    Continuous (fun t => squareAverage L (fun p => f (t,p))) := by
  have hc : Continuous (fun p : (X × ℝ) × ℝ => f (p.1.1,(p.1.2,p.2))) := by
    exact hf.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  exact continuous_average (continuous_average hc L) L

/-- Closed-strip continuity gives closed-interval continuity of the average. -/
theorem continuousOn_squareAverage {f : Field} {T : ℝ}
    (hf : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2) {z | z.1 ∈ Icc 0 T})
    (L : ℝ) : ContinuousOn (fun t => squareAverage L (f t)) (Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (fun z : (Icc 0 T) × (ℝ × ℝ) => f z.1 z.2) :=
    hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun z => z.1.property)
  exact continuous_squareAverage hc L

/-- Differentiation under the area integral, using joint continuity to obtain
an integrable uniform bound on the derivative. -/
theorem hasDerivAt_squareAverage {f dt : Field} {T L t : ℝ} (hL : 0 < L)
    (hf : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2) {z | z.1 ∈ Icc 0 T})
    (hc : ContinuousOn (fun z : ℝ × (ℝ × ℝ) => dt z.1 z.2) {z | z.1 ∈ Icc 0 T})
    (hd : ∀ s ∈ Ioo 0 T, ∀ p, HasDerivAt (fun r => f r p) (dt s p) s)
    (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => squareAverage L (f s)) (squareAverage L (dt t)) t := by
  let K := Icc (0 : ℝ) L ×ˢ Icc (0 : ℝ) L
  let μ := volume.restrict K
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hbound := (isCompact_Icc.prod hK).bddAbove_image
    (hc.norm.mono (fun _ hz => hz.1))
  obtain ⟨B, hB⟩ := hbound
  have hn : Ioo 0 T ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := f) (F' := dt) (bound := fun _ => B) hn
    (by filter_upwards [hn] with s hs
        exact (continuous_slice hf ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable)
    ((continuous_slice hf ⟨ht.1.le, ht.2.le⟩).continuousOn.integrableOn_compact hK)
    ((continuous_slice hc ⟨ht.1.le, ht.2.le⟩).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      intro s hs
      apply hB
      exact ⟨(s,p), ⟨⟨hs.1.le, hs.2.le⟩, hp⟩, rfl⟩)
    (integrableOn_const hK.measure_ne_top)
    (Eventually.of_forall (fun p s hs => hd s hs p))
  have hscaled := hder.2.div_const (L ^ 2)
  rw [← squareAverage_eq_integral hL (continuous_slice hc ⟨ht.1.le, ht.2.le⟩)] at hscaled
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [hn] with s hs
  exact squareAverage_eq_integral hL (continuous_slice hf ⟨hs.1.le, hs.2.le⟩)

#print axioms hasDerivAt_squareAverage
end Gimle.Forseti.ClassicalVorticity
