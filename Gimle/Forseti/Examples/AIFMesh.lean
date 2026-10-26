module

public import Gimle.Forseti.Examples.AIFSlabModel

/-! A finite time-by-parameter mesh of AIF slabs whose adjacent slabs share exact
endpoint centers, slopes and metrics, and whose time intervals cover the mesh span.
Coverage and joins do not imply any matrix positivity or trajectory theorem. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFMesh
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix AIFSlabModel

/-- One shared time node, with physical slopes rather than normalized slopes. -/
structure Knot where
  lo : Fin 4 → ℚ
  hi : Fin 4 → ℚ
  loSlope : Fin 4 → ℚ
  hiSlope : Fin 4 → ℚ
  value : QMatrix 4
  slope : QMatrix 4

/-- Dimensions count intervals; every endpoint is stored, including the last. -/
structure Mesh (nt nb : Nat) where
  times : Fin (nt + 1) → ℚ
  edges : Fin (nb + 1) → ℚ
  nodes : Fin nb → Fin (nt + 1) → Knot

def Mesh.slab {nt nb : Nat} (m : Mesh nt nb) (b : Fin nb) (i : Fin nt) : Slab where
  tStart := m.times i.castSucc
  step := m.times i.succ - m.times i.castSucc
  etaLo := m.edges b.castSucc
  etaHi := m.edges b.succ
  loStart := (m.nodes b i.castSucc).lo
  loEnd := (m.nodes b i.succ).lo
  loStartSlope := (m.nodes b i.castSucc).loSlope
  loEndSlope := (m.nodes b i.succ).loSlope
  hiStart := (m.nodes b i.castSucc).hi
  hiEnd := (m.nodes b i.succ).hi
  hiStartSlope := (m.nodes b i.castSucc).hiSlope
  hiEndSlope := (m.nodes b i.succ).hiSlope
  startMetric := (m.nodes b i.castSucc).value
  endMetric := (m.nodes b i.succ).value
  startMetricSlope := (m.nodes b i.castSucc).slope
  endMetricSlope := (m.nodes b i.succ).slope

/-- Exact endpoint compatibility, including slopes and parameter coordinates. -/
structure Joins (a b : Slab) : Prop where
  time : a.tStart + a.step = b.tStart
  etaLo : a.etaLo = b.etaLo
  etaHi : a.etaHi = b.etaHi
  lo : a.loEnd = b.loStart
  hi : a.hiEnd = b.hiStart
  loSlope : a.loEndSlope = b.loStartSlope
  hiSlope : a.hiEndSlope = b.hiStartSlope
  metric : a.endMetric = b.startMetric
  metricSlope : a.endMetricSlope = b.startMetricSlope

theorem Mesh.joins {nt nb : Nat} (m : Mesh nt nb) (b : Fin nb) (i j : Fin nt)
    (h : i.succ = j.castSucc) : Joins (m.slab b i) (m.slab b j) := by
  constructor <;> simp [Mesh.slab, h]

@[simp] theorem hermite_zero (h a b c d : ℚ) : hermite h a b c d 0 = (a : ℝ) := by
  simp [hermite]

@[simp] theorem hermite_one (h a b c d : ℚ) : hermite h a b c d 1 = (b : ℝ) := by
  simp [hermite]
  ring

@[simp] theorem hermiteRate_zero (h a b c d : ℚ) (hh : h ≠ 0) :
    hermiteRate h a b c d 0 = (c : ℝ) := by
  have hr : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  simp [hermiteRate, hr]

@[simp] theorem hermiteRate_one (h a b c d : ℚ) (hh : h ≠ 0) :
    hermiteRate h a b c d 1 = (d : ℝ) := by
  have hr : (h : ℝ) ≠ 0 := by exact_mod_cast hh
  simp [hermiteRate]
  field_simp [hr]
  ring

theorem Joins.center_eq {a b : Slab} (h : Joins a b) (u : ℝ) :
    center a 1 u = center b 0 u := by
  ext i
  simp [center, h.lo, h.hi]

theorem Joins.metric_eq {a b : Slab} (h : Joins a b) : AIFSlabModel.metric a 1 = AIFSlabModel.metric b 0 := by
  ext i j
  simp [AIFSlabModel.metric, h.metric]

theorem Joins.centerRate_eq {a b : Slab} (h : Joins a b)
    (ha : a.step ≠ 0) (hb : b.step ≠ 0) (u : ℝ) :
    centerRate a 1 u = centerRate b 0 u := by
  ext i
  simp [centerRate, ha, hb, h.loSlope, h.hiSlope]

theorem Joins.metricRate_eq {a b : Slab} (h : Joins a b)
    (ha : a.step ≠ 0) (hb : b.step ≠ 0) : metricRate a 1 = metricRate b 0 := by
  ext i j
  simp [metricRate, ha, hb, h.metricSlope]

theorem Joins.coordinates {a b : Slab} (h : Joins a b)
    (ha : a.step ≠ 0) (p : ℝ) :
    timeCoordinate a b.tStart = 1 ∧ timeCoordinate b b.tStart = 0 ∧
      etaCoordinate a p = etaCoordinate b p := by
  have hr : (a.step : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht : (b.tStart : ℝ) = (a.tStart : ℝ) + a.step := by exact_mod_cast h.time.symm
  exact ⟨by simp [timeCoordinate, ht, hr], by simp [timeCoordinate],
    by simp [etaCoordinate, h.etaLo, h.etaHi]⟩

/-- Energy of a fixed state in the physical-time, moving-center metric. -/
noncomputable def tubeEnergy (d : Slab) (t p : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  matrixForm (metric d (timeCoordinate d t))
    (x - center d (timeCoordinate d t) (etaCoordinate d p))

/-- The same state has exactly the same energy from either side of a time join. -/
theorem Joins.tubeEnergy_eq {a b : Slab} (h : Joins a b)
    (ha : a.step ≠ 0) (_hb : b.step ≠ 0) (p : ℝ) (x : Fin 4 → ℝ) :
    tubeEnergy a b.tStart p x = tubeEnergy b b.tStart p x := by
  obtain ⟨ht, hz, hp⟩ := h.coordinates ha p
  simp only [tubeEnergy, ht, hz, hp, h.center_eq, h.metric_eq]

/-- A finite chain of closed intervals covers its endpoint span.
No monotonicity is needed for existence; positive mesh widths are checked separately. -/
theorem interval_covered (n : Nat) (f : Fin (n + 2) → ℝ) (x : ℝ)
    (hx : x ∈ Set.Icc (f 0) (f (Fin.last (n + 1)))) :
    ∃ i : Fin (n + 1), x ∈ Set.Icc (f i.castSucc) (f i.succ) := by
  induction n with
  | zero => exact ⟨0, hx⟩
  | succ n ih =>
    by_cases h : x ≤ f (Fin.last (n + 1)).castSucc
    · obtain ⟨i, hi⟩ := ih (fun j => f j.castSucc) ⟨hx.1, h⟩
      exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last (n + 1), ⟨le_of_lt (lt_of_not_ge h), hx.2⟩⟩

/-- Complete geometric coverage, independent of any dynamics certificates. -/
theorem Mesh.covers {nt nb : Nat} (m : Mesh (nt + 1) (nb + 1)) (t p : ℝ)
    (ht : t ∈ Set.Icc (m.times 0 : ℝ) (m.times (Fin.last (nt + 1)) : ℝ))
    (hp : p ∈ Set.Icc (m.edges 0 : ℝ) (m.edges (Fin.last (nb + 1)) : ℝ)) :
    ∃ b : Fin (nb + 1), ∃ i : Fin (nt + 1),
      t ∈ Set.Icc ((m.slab b i).tStart : ℝ)
        (((m.slab b i).tStart : ℝ) + (m.slab b i).step) ∧
      p ∈ Set.Icc ((m.slab b i).etaLo : ℝ) ((m.slab b i).etaHi : ℝ) := by
  obtain ⟨i, hi⟩ := interval_covered nt (fun j => (m.times j : ℝ)) t ht
  obtain ⟨b, hb⟩ := interval_covered nb (fun j => (m.edges j : ℝ)) p hp
  refine ⟨b, i, ?_, hb⟩
  simpa [Mesh.slab] using hi

#print axioms Mesh.covers
#print axioms Mesh.joins
#print axioms Joins.tubeEnergy_eq
#print axioms Joins.centerRate_eq
#print axioms Joins.metricRate_eq
end Gimle.Forseti.Examples.AIFMesh
