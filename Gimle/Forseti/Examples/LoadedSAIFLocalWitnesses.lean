import Gimle.Forseti.Examples.LoadedSAIFStationary
import Gimle.Forseti.Examples.LoadedSAIFLocalMatrices

/-! Fixed rational local-region certificates, bound to the original field. -/
namespace Gimle.Forseti.Examples.LoadedSAIFLocalWitnesses
open Gimle.Forseti.LinearEnergy Gimle.Forseti.BernsteinMatrix
open LoadedSAIFCertificates LoadedSAIFLocalMatrices
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def region0 : StationaryData where
  load := 0
  center := ![(192641627/100000000), (192641627/100000000), (5094377/2000000), (9439743/100000000), 0]
  metric := region0Metric
  radiusSq := (1/50000)
  decay := (1/1000)
  margin := (1/200000000)
  cBound := (1/500)
  feedbackBound := (1/1000)

def region0NegativeCoefficients : Fin 1 → Fin 3 → QMatrix 6 :=
  fun _ => ![region0Drift0, region0Drift1, region0Drift2]

def region0NegativeSquares : Fin 1 → Fin 3 → WeightedSquares 6 :=
  fun _ => ![region0Drift0Squares, region0Drift1Squares, region0Drift2Squares]

theorem region0NegativeValid : ∀ i j,
    (region0NegativeSquares i j).Represents (region0NegativeCoefficients i j) := by
  intro i j
  fin_cases i
  fin_cases j
  · exact region0Drift0Valid
  · exact region0Drift1Valid
  · exact region0Drift2Valid

theorem region0NegativeBinding (u : ℝ) :
    stationaryBlock region0 (-1/500) u =
      tensorMatrix region0NegativeCoefficients 0 u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryBlock, driftBlock, driftMatrix, residualProduct,
      clearedMatrix, clearedResidual, denominator, feedbackError,
      StationaryData.realCenter, region0, region0Metric, realMatrix,
      LoadedSAIFModel.binding, LoadedSAIFModel.alpha, LoadedSAIFModel.kappa,
      LoadedSAIFModel.dilution, tensorMatrix, basis, region0NegativeCoefficients,
      region0Drift0, region0Drift1, region0Drift2, Fin.sum_univ_succ]
  all_goals ring

noncomputable def region0Negative :
    StationaryBlockCertificate region0 (-1/500) where
  coefficients := region0NegativeCoefficients
  squares := region0NegativeSquares
  valid := region0NegativeValid
  binding := region0NegativeBinding

def region0PositiveCoefficients : Fin 1 → Fin 3 → QMatrix 6 :=
  fun _ => ![region0Drift3, region0Drift4, region0Drift5]

def region0PositiveSquares : Fin 1 → Fin 3 → WeightedSquares 6 :=
  fun _ => ![region0Drift3Squares, region0Drift4Squares, region0Drift5Squares]

theorem region0PositiveValid : ∀ i j,
    (region0PositiveSquares i j).Represents (region0PositiveCoefficients i j) := by
  intro i j
  fin_cases i
  fin_cases j
  · exact region0Drift3Valid
  · exact region0Drift4Valid
  · exact region0Drift5Valid

theorem region0PositiveBinding (u : ℝ) :
    stationaryBlock region0 (1/500) u =
      tensorMatrix region0PositiveCoefficients 0 u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryBlock, driftBlock, driftMatrix, residualProduct,
      clearedMatrix, clearedResidual, denominator, feedbackError,
      StationaryData.realCenter, region0, region0Metric, realMatrix,
      LoadedSAIFModel.binding, LoadedSAIFModel.alpha, LoadedSAIFModel.kappa,
      LoadedSAIFModel.dilution, tensorMatrix, basis, region0PositiveCoefficients,
      region0Drift3, region0Drift4, region0Drift5, Fin.sum_univ_succ]
  all_goals ring

noncomputable def region0Positive :
    StationaryBlockCertificate region0 (1/500) where
  coefficients := region0PositiveCoefficients
  squares := region0PositiveSquares
  valid := region0PositiveValid
  binding := region0PositiveBinding

theorem region0OutputBinding :
    stationaryMargin region0 ![0, 1, 0, 0, 0] (1/200) = region0OutputMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region0, region0Metric, region0OutputMargin]

theorem region0FeedbackBinding :
    stationaryMargin region0 ![0, 0, 0, 1, 0] (1/1000) = region0FeedbackMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region0, region0Metric, region0FeedbackMargin]

theorem region0CBinding :
    stationaryMargin region0 ![0, 0, 0, 0, 1] (1/500) = region0CMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region0, region0Metric, region0CMargin]

theorem region0PoolBinding :
    stationaryMargin region0 ![0, 0, 1, 1, 0] 1 = region0PoolMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region0, region0Metric, region0PoolMargin]

noncomputable def region0Certificate : StationaryCertificate region0 where
  radius_positive := by norm_num [region0]
  c_positive := by norm_num [region0]
  feedback_positive := by norm_num [region0]
  margin_positive := by norm_num [region0]
  feedback_guard := by norm_num [region0, LoadedSAIFModel.kappa]
  symmetric := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [region0, region0Metric]
  capacity := region0CMarginSquares
  capacity_valid := by
    have coord : coordinate 4 = ![0, 0, 0, 0, 1] := by
      ext i
      fin_cases i <;> norm_num [coordinate]
    rw [coord]
    change region0CMarginSquares.Represents
      (stationaryMargin region0 ![0, 0, 0, 0, 1] (1/500))
    rw [region0CBinding]
    exact region0CMarginValid
  feedback := region0FeedbackMarginSquares
  feedback_valid := by
    have coord : coordinate 3 = ![0, 0, 0, 1, 0] := by
      ext i
      fin_cases i <;> norm_num [coordinate]
    rw [coord]
    change region0FeedbackMarginSquares.Represents
      (stationaryMargin region0 ![0, 0, 0, 1, 0]
        (1/1000))
    rw [region0FeedbackBinding]
    exact region0FeedbackMarginValid
  negative := by
    have endpoint : (-region0.cBound : ℚ) = (-1/500) := by
      norm_num [region0]
    rw [endpoint]
    exact region0Negative
  positive := region0Positive

#print axioms region0Certificate
theorem region0Bounds (x : LoadedSAIFModel.State)
    (hx : region0.energy x ≤ region0.radiusSq) :
    x 1 ≤ (13/5 : ℝ) ∧ x 2+x 3 ≤ 8 ∧ x 1 ∈ Set.Icc (9/5 : ℝ) (11/5) := by
  have hout := stationary_observable region0 ![0, 1, 0, 0, 0] (1/200)
    region0OutputMarginSquares (by
      rw [region0OutputBinding]
      exact region0OutputMarginValid)
    (by norm_num [region0]) (by norm_num) x hx
  have hpool := stationary_observable region0 ![0, 0, 1, 1, 0] 1
    region0PoolMarginSquares (by
      rw [region0PoolBinding]
      exact region0PoolMarginValid)
    (by norm_num [region0]) (by norm_num) x hx
  norm_num [StationaryData.realCenter, region0, Fin.sum_univ_succ] at hout hpool
  rcases abs_le.mp hout with ⟨hlo, hhi⟩
  have hp := (abs_le.mp hpool).2
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

#print axioms region0Bounds


def region1 : StationaryData where
  load := 2
  center := ![(214521517/100000000), (190005131/100000000), (170068633/50000000), (3487487/50000000), (122581927/100000000)]
  metric := region1Metric
  radiusSq := (1/1500)
  decay := (1/1000)
  margin := (1/6000000)
  cBound := (13/1000)
  feedbackBound := (1/250)

def region1NegativeCoefficients : Fin 1 → Fin 3 → QMatrix 6 :=
  fun _ => ![region1Drift0, region1Drift1, region1Drift2]

def region1NegativeSquares : Fin 1 → Fin 3 → WeightedSquares 6 :=
  fun _ => ![region1Drift0Squares, region1Drift1Squares, region1Drift2Squares]

theorem region1NegativeValid : ∀ i j,
    (region1NegativeSquares i j).Represents (region1NegativeCoefficients i j) := by
  intro i j
  fin_cases i
  fin_cases j
  · exact region1Drift0Valid
  · exact region1Drift1Valid
  · exact region1Drift2Valid

theorem region1NegativeBinding (u : ℝ) :
    stationaryBlock region1 (-13/1000) u =
      tensorMatrix region1NegativeCoefficients 0 u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryBlock, driftBlock, driftMatrix, residualProduct,
      clearedMatrix, clearedResidual, denominator, feedbackError,
      StationaryData.realCenter, region1, region1Metric, realMatrix,
      LoadedSAIFModel.binding, LoadedSAIFModel.alpha, LoadedSAIFModel.kappa,
      LoadedSAIFModel.dilution, tensorMatrix, basis, region1NegativeCoefficients,
      region1Drift0, region1Drift1, region1Drift2, Fin.sum_univ_succ]
  all_goals ring

noncomputable def region1Negative :
    StationaryBlockCertificate region1 (-13/1000) where
  coefficients := region1NegativeCoefficients
  squares := region1NegativeSquares
  valid := region1NegativeValid
  binding := region1NegativeBinding

def region1PositiveCoefficients : Fin 1 → Fin 3 → QMatrix 6 :=
  fun _ => ![region1Drift3, region1Drift4, region1Drift5]

def region1PositiveSquares : Fin 1 → Fin 3 → WeightedSquares 6 :=
  fun _ => ![region1Drift3Squares, region1Drift4Squares, region1Drift5Squares]

theorem region1PositiveValid : ∀ i j,
    (region1PositiveSquares i j).Represents (region1PositiveCoefficients i j) := by
  intro i j
  fin_cases i
  fin_cases j
  · exact region1Drift3Valid
  · exact region1Drift4Valid
  · exact region1Drift5Valid

theorem region1PositiveBinding (u : ℝ) :
    stationaryBlock region1 (13/1000) u =
      tensorMatrix region1PositiveCoefficients 0 u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryBlock, driftBlock, driftMatrix, residualProduct,
      clearedMatrix, clearedResidual, denominator, feedbackError,
      StationaryData.realCenter, region1, region1Metric, realMatrix,
      LoadedSAIFModel.binding, LoadedSAIFModel.alpha, LoadedSAIFModel.kappa,
      LoadedSAIFModel.dilution, tensorMatrix, basis, region1PositiveCoefficients,
      region1Drift3, region1Drift4, region1Drift5, Fin.sum_univ_succ]
  all_goals ring

noncomputable def region1Positive :
    StationaryBlockCertificate region1 (13/1000) where
  coefficients := region1PositiveCoefficients
  squares := region1PositiveSquares
  valid := region1PositiveValid
  binding := region1PositiveBinding

theorem region1OutputBinding :
    stationaryMargin region1 ![0, 1, 0, 0, 0] (1/40) = region1OutputMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region1, region1Metric, region1OutputMargin]

theorem region1FeedbackBinding :
    stationaryMargin region1 ![0, 0, 0, 1, 0] (1/250) = region1FeedbackMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region1, region1Metric, region1FeedbackMargin]

theorem region1CBinding :
    stationaryMargin region1 ![0, 0, 0, 0, 1] (13/1000) = region1CMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region1, region1Metric, region1CMargin]

theorem region1PoolBinding :
    stationaryMargin region1 ![0, 0, 1, 1, 0] 1 = region1PoolMargin := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stationaryMargin, region1, region1Metric, region1PoolMargin]

noncomputable def region1Certificate : StationaryCertificate region1 where
  radius_positive := by norm_num [region1]
  c_positive := by norm_num [region1]
  feedback_positive := by norm_num [region1]
  margin_positive := by norm_num [region1]
  feedback_guard := by norm_num [region1, LoadedSAIFModel.kappa]
  symmetric := by
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [region1, region1Metric]
  capacity := region1CMarginSquares
  capacity_valid := by
    have coord : coordinate 4 = ![0, 0, 0, 0, 1] := by
      ext i
      fin_cases i <;> norm_num [coordinate]
    rw [coord]
    change region1CMarginSquares.Represents
      (stationaryMargin region1 ![0, 0, 0, 0, 1] (13/1000))
    rw [region1CBinding]
    exact region1CMarginValid
  feedback := region1FeedbackMarginSquares
  feedback_valid := by
    have coord : coordinate 3 = ![0, 0, 0, 1, 0] := by
      ext i
      fin_cases i <;> norm_num [coordinate]
    rw [coord]
    change region1FeedbackMarginSquares.Represents
      (stationaryMargin region1 ![0, 0, 0, 1, 0]
        (1/250))
    rw [region1FeedbackBinding]
    exact region1FeedbackMarginValid
  negative := by
    have endpoint : (-region1.cBound : ℚ) = (-13/1000) := by
      norm_num [region1]
    rw [endpoint]
    exact region1Negative
  positive := region1Positive

#print axioms region1Certificate
theorem region1Bounds (x : LoadedSAIFModel.State)
    (hx : region1.energy x ≤ region1.radiusSq) :
    x 1 ≤ (13/5 : ℝ) ∧ x 2+x 3 ≤ 8 ∧ x 1 ∈ Set.Icc (9/5 : ℝ) (11/5) ∧ |x 1-2| ≤ (3/20 : ℝ) := by
  have hout := stationary_observable region1 ![0, 1, 0, 0, 0] (1/40)
    region1OutputMarginSquares (by
      rw [region1OutputBinding]
      exact region1OutputMarginValid)
    (by norm_num [region1]) (by norm_num) x hx
  have hpool := stationary_observable region1 ![0, 0, 1, 1, 0] 1
    region1PoolMarginSquares (by
      rw [region1PoolBinding]
      exact region1PoolMarginValid)
    (by norm_num [region1]) (by norm_num) x hx
  norm_num [StationaryData.realCenter, region1, Fin.sum_univ_succ] at hout hpool
  rcases abs_le.mp hout with ⟨hlo, hhi⟩
  have hp := (abs_le.mp hpool).2
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · constructor <;> linarith
  apply abs_le.mpr
  constructor <;> linarith

#print axioms region1Bounds


end Gimle.Forseti.Examples.LoadedSAIFLocalWitnesses
