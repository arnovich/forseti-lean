module

public import Gimle.Forseti.Examples.LoadedSAIFPolynomial
public import Gimle.Forseti.Examples.LoadedSAIFTransfer

/-! Guard and exact-identity regressions for the rational feedback certificates. -/

@[expose] public section

namespace Gimle.Forseti.Tests.LoadedSAIFCertificates
open Gimle.Forseti.Examples.LoadedSAIFModel
open Gimle.Forseti.Examples.LoadedSAIFCertificates

example (p : State) : denominator p (-(kappa + p 3)) = 0 := by
  simp [denominator]

example (p : State) : ¬ 0 < denominator p (-(kappa + p 3)) := by
  simp [denominator]

example (L : ℝ) (p v e : State) (h : kappa + p 3 + e 3 ≠ 0) (i : Fin 5) :
    denominator p (e 3) * (field L (p + e) i - v i) =
      (∑ j, clearedMatrix L p (e 4) (e 3) i j * e j) +
        clearedResidual L p v (e 3) i :=
  cleared_velocity L p v e h i

def poleData : StationaryData where
  load := 0
  center := ![0, 0, 0, -147261/1000000, 0]
  metric := 0
  radiusSq := 1
  decay := 1
  margin := 1
  cBound := 1/100
  feedbackBound := 1/100

example : ¬ Nonempty (StationaryCertificate poleData) := by
  rintro ⟨certificate⟩
  have h := certificate.feedback_guard
  norm_num [poleData, kappa] at h

example : ¬ Nonempty (StationaryCertificate { poleData with radiusSq := 0 }) := by
  rintro ⟨certificate⟩
  have h := certificate.radius_positive
  norm_num at h

def linearData : MovingData where
  load := 0
  tStart := 0
  step := 2
  centerStart := 0
  centerEnd := ![2, 0, 0, 0, 0]
  centerStartSlope := ![1, 0, 0, 0, 0]
  centerEndSlope := ![1, 0, 0, 0, 0]
  metricStart := 0
  metricEnd := 0
  metricStartSlope := 0
  metricEndSlope := 0
  radiusSq := 1
  decay := 1
  margin := 1
  cBound := 1
  feedbackBound := 1

/-- A non-unit normalized time step still produces the physical slope one. -/
example (t : ℝ) :
    HasDerivAt (fun s => movingCenter linearData (movingTime linearData s) 0) 1 t := by
  have h := movingCenter_derivative linearData (by norm_num [linearData]) t 0
  norm_num [movingCenterRate, linearData, Gimle.Forseti.Examples.AIFSlabModel.hermiteRate] at h
  exact h

end Gimle.Forseti.Tests.LoadedSAIFCertificates
