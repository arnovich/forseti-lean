import Gimle.Forseti.Examples.AIFSlabModel

/-! Symmetric rational endpoint metrics and slopes give symmetric interpolated AIF
slab metrics and metric rates at every time. -/
namespace Gimle.Forseti.Examples.AIFSlabData
open AIFSlabModel (Slab)

/-- Every independent Hermite matrix input is checked, including both slopes. -/
def SymmetricData (d : Slab) : Prop := ∀ i j,
  d.startMetric i j = d.startMetric j i ∧
  d.endMetric i j = d.endMetric j i ∧
  d.startMetricSlope i j = d.startMetricSlope j i ∧
  d.endMetricSlope i j = d.endMetricSlope j i

theorem metric_symmetric (d : Slab) (symmetric : SymmetricData d)
    (s : ℝ) (i j : Fin 4) :
    AIFSlabModel.metric d s i j = AIFSlabModel.metric d s j i := by
  simp only [AIFSlabModel.metric, (symmetric i j).1,
    (symmetric i j).2.1, (symmetric i j).2.2.1, (symmetric i j).2.2.2]

theorem metricRate_symmetric (d : Slab) (symmetric : SymmetricData d)
    (s : ℝ) (i j : Fin 4) :
    AIFSlabModel.metricRate d s i j = AIFSlabModel.metricRate d s j i := by
  simp only [AIFSlabModel.metricRate, (symmetric i j).1,
    (symmetric i j).2.1, (symmetric i j).2.2.1, (symmetric i j).2.2.2]

#print axioms metric_symmetric
#print axioms metricRate_symmetric
end Gimle.Forseti.Examples.AIFSlabData
