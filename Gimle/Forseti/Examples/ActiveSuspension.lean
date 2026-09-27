import Gimle.Forseti.Examples.SuspensionCertificateData
import Gimle.Forseti.ForcedLinear

/-! Total safety for a nested active suspension, from a searched common storage.
The outer theorem consumes a component behavior contract; neither concrete
actuator implementation is unfolded there. Local storage identities and the
cross-term derivative are retained when assembling the invariant proof. -/

namespace Gimle.Forseti.Examples.ActiveSuspension

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open Gimle.Forseti.LinearEnergy Gimle.Forseti.Dissipative CertificateData

/-- Mechanical coordinates retained at the component boundary. -/
def plantState (s : Point 5) : Point 4 := ![s 0, s 1, s 2, s 3]

/-- The certificate includes physical component energies and an additional
quadratic form containing the coupling terms discovered by the search. -/
def coupling : QMatrix 5 := fun i j => storage i j -
  (![![1, -1, 0, 0, 0], ![-1, 3, 0, 0, 0], ![0, 0, 1, 0, 0],
    ![0, 0, 0, 1 / 2, 0], ![0, 0, 0, 0, 1]] : QMatrix 5) i j

/-- The common quadratic storage found by exact search. -/
noncomputable def storageValue (s : Point 5) : ℝ := quadratic storage s

theorem storage_decomposition (s : Point 5) :
    storageValue s = plantEnergy (plantState s) + s 4^2 + quadratic coupling s := by
  simp [storageValue, plantEnergy, plantState, coupling, quadratic, realMatrix,
    dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem rate_decomposition (s v : Point 5) :
    quadraticRate storage s v = plantEnergyRate (plantState s) (plantState v) +
      2 * s 4 * v 4 + quadraticRate coupling s v := by
  simp [quadraticRate, plantEnergyRate, plantState, coupling, Linear.Matrix.eval,
    dotProduct, Fin.sum_univ_succ]
  ring

theorem rhs_plant (rate : ℚ) (road : ℝ) (s : Point 5) :
    plantState (rhs rate road s) = plantRhs road (s 4) (plantState s) := by
  funext i
  fin_cases i <;> rfl

/-- The combined rate keeps local dissipations and port exchanges visible;
the extra quadratic rate handles the searched cross terms. -/
noncomputable def storageRate (rate : ℚ) (road : ℝ) (s : Point 5) : ℝ :=
  (-2 * (s 2 - s 3)^2 + s 4 * (s 2 - s 3) + 4 * road * s 3) +
    2 * (rate : ℝ) * (s 4 * command (plantState s) - s 4^2) +
    quadraticRate coupling s (rhs rate road s)

/-- Assemble the plant and actuator storage identities at their connected ports. -/
theorem combined_storage (rate : ℚ) (road : ℝ) (s : Point 5) :
    quadraticRate storage s (rhs rate road s) = storageRate rate road s := by
  rw [rate_decomposition, rhs_plant, plant_storage]
  change _ + 2 * s 4 * ((rate : ℝ) * (command (plantState s) - s 4)) + _ = _
  rw [actuator_storage]
  rfl

/-- The analytic operator is a derived representation of the component equations. -/
noncomputable def operator (rate : ℚ) : Point 5 →L[ℝ] Point 5 :=
  LinearAnalysis.rationalOperator (stateMatrix rate)

theorem rhs_linear (rate : ℚ) (road : ℝ) (s : Point 5) :
    rhs rate road s = operator rate s + fun i => (roadVector i : ℝ) * road := by
  funext i
  fin_cases i <;>
    simp [rhs, operator, LinearAnalysis.rationalOperator_apply, stateMatrix,
      roadVector, Fin.sum_univ_succ] <;> ring

/-- Every admitted road and initial state has a trajectory through all three traces. -/
theorem system_exists (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (time : TimeDomain) (input : Signal 6)
    (continuous : Continuous (signalLeft (n := 1) (m := 5) input : Signal 1)) :
    ∃ state, (system implementation time.axis).Rel time input state := by
  let forcing : Signal 5 := fun t i => (roadVector i : ℝ) * input t 0
  have cf : Continuous forcing := by
    apply continuous_pi
    intro i
    convert! continuous_const.mul ((continuous_apply 0).comp continuous) using 1
  obtain ⟨state, initial, derivative⟩ := ForcedLinear.exists_solution (operator rate)
    forcing cf time.start (signalRight (n := 1) (m := 5) input time.start)
  refine ⟨state, (system_law implementation rate law time input state).mpr ⟨initial, ?_⟩⟩
  intro t _ i
  rw [rhs_linear]
  exact ((hasDerivAt_pi.mp (derivative t)) i).hasDerivWithinAt

/-- Independent forward uniqueness for the exact component interface. -/
theorem system_unique (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (time : TimeDomain) (input : Signal 6)
    (x y : Signal 5) (hx : (system implementation time.axis).Rel time input x)
    (hy : (system implementation time.axis).Rel time input y) : Set.EqOn x y time.domain := by
  obtain ⟨ix, dx⟩ := (system_law implementation rate law time input x).mp hx
  obtain ⟨iy, dy⟩ := (system_law implementation rate law time input y).mp hy
  apply ForcedLinear.unique_on (operator rate)
    (fun t i => (roadVector i : ℝ) * input t 0) time.start x y (ix.trans iy.symm)
  · intro t ht i
    simpa only [rhs_linear, TimeDomain.domain] using dx t ht i
  · intro t ht i
    simpa only [rhs_linear, TimeDomain.domain] using dy t ht i

set_option maxRecDepth 10000 in
/-- The generated supply matrix is checked against the component-derived rate. -/
theorem supply_identity (rate : ℚ) (s : Point 5) (road : ℝ) :
    quadratic (supplyMatrix storage alpha beta rate) (pointAppend s ![road]) =
      (beta : ℝ) * road^2 - (alpha : ℝ) * storageValue s - storageRate rate road s := by
  let remainder : QMatrix 6 := fun i j => -alpha * embed storage i j +
    if i = 5 ∧ j = 5 then beta else 0
  have split : supplyMatrix storage alpha beta rate =
      dissipation (extendedMatrix rate) (embed storage) + remainder := by
    ext i j
    simp [supplyMatrix, remainder]
    ring
  have diss (x : Point 6) :
      quadratic (dissipation (extendedMatrix rate) (embed storage)) x =
        -quadraticRate (embed storage) x ((extendedMatrix rate).eval x) := by
    have h := derivative_identity (extendedMatrix rate) (embed storage) x
    change quadraticRate _ _ _ = _ at h
    linarith
  rw [split, quadratic_add, diss, ← combined_storage]
  simp [remainder, extendedMatrix, embed, quadratic, realMatrix,
    quadraticRate, Linear.Matrix.eval, storageValue, storage, stateMatrix, roadVector,
    rhs, alpha, beta, pointAppend, dotProduct, Matrix.mulVec, Fin.sum_univ_succ,
    Fin.addCases]
  ring

/-- Exact replay of the same dissipation certificate for both actuator rates. -/
theorem supply_nonnegative (rate : ℚ) (supported : SupportedRate rate) (x : Point 6) :
    0 ≤ quadratic (supplyMatrix storage alpha beta rate) x := by
  rcases supported with rfl | rfl
  · exact slowSupply.nonnegative _ slowSupply_valid x
  · exact fastSupply.nonnegative _ fastSupply_valid x

/-- The disturbance budget closes the differential inequality globally in state. -/
theorem rate_bound (rate : ℚ) (supported : SupportedRate rate) (s : Point 5)
    (road : ℝ) (bounded : |road| ≤ 1 / 1000) :
    storageRate rate road s ≤ (alpha : ℝ) * (1 - storageValue s) := by
  have h := supply_nonnegative rate supported (pointAppend s ![road])
  rw [supply_identity] at h
  have bounds := abs_le.mp bounded
  have square : road^2 ≤ 1 / 1000000 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 1000 - road)
      (by linarith : 0 ≤ 1 / 1000 + road)]
  norm_num [alpha, beta] at h ⊢
  linarith

/-- The independent initial ball lies inside the discovered invariant. -/
theorem initial_inclusion (s : Point 5) (inside : initialSize s ≤ 1 / 100) :
    storageValue s ≤ 1 := by
  have h := CertificateData.initial.nonnegative _ initial_valid s
  have identity : quadratic (initialMatrix storage) s = 100 * initialSize s - storageValue s := by
    simp [initialMatrix, initialSize, storageValue, quadratic, realMatrix,
      dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    ring
  rw [identity] at h
  linarith

/-- Observable containment is checked separately for each requested output. -/
theorem output_inclusion (s : Point 5) (inside : storageValue s ≤ 1) :
    safeOutputs (observations.run s) := by
  intro i
  have h : 0 ≤ quadratic (outputMatrix storage i) s := by
    fin_cases i
    · exact output0.nonnegative _ output0_valid s
    · exact output1.nonnegative _ output1_valid s
    · exact output2.nonnegative _ output2_valid s
  have identity : quadratic (outputMatrix storage i) s =
      storageValue s - (observations.run s i)^2 := by
    fin_cases i <;>
      simp [outputMatrix, outputRows, observations, Polynomial.Expr.eval,
        storageValue, quadratic, realMatrix, dotProduct, Matrix.mulVec,
        Fin.sum_univ_succ] <;> ring
  rw [identity] at h
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (observations.run s i + 1),
    sq_nonneg (observations.run s i - 1)]

/-- Derivative of the common storage assembled from the component contracts. -/
theorem storage_derivative (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (time : TimeDomain) (input : Signal 6)
    (state : Signal 5) (realized : (system implementation time.axis).Rel time input state)
    (t : ℝ) (within : t ∈ time.domain) :
    HasDerivWithinAt (fun t => storageValue (state t))
      (storageRate rate (input t 0) (state t)) time.domain t := by
  have derivative := ((system_law implementation rate law time input state).mp realized).2 t within
  have h := Dissipative.quadratic_derivative storage state _ time.domain t derivative
  rw [combined_storage] at h
  exact h

/-- The outer feedback theorem consumes an actuator interface and one common
certificate. Existence and uniqueness do not follow from assuming the invariant. -/
theorem system_contract (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (supported : SupportedRate rate)
    (time : TimeDomain) :
    Contract (system implementation time.axis) time (admitted time)
      (Always time fun s => storageValue s ≤ 1) where
  realizable input admit := system_exists implementation rate law time input admit.1.1
  unique input _ x y hx hy := system_unique implementation rate law time input x y hx hy
  holds input admit state realized := by
    apply Dissipative.sublevel time (fun t => storageValue (state t))
      (fun t => storageRate rate (input t 0) (state t)) alpha 1
    · exact storage_derivative implementation rate law time input state realized
    · intro t ht
      exact rate_bound rate supported _ _ (admit.1.2 t ht)
    · rw [((system_law implementation rate law time input state).mp realized).1]
      exact initial_inclusion _ admit.2

/-- The third observation is the derivative of body velocity along the circuit. -/
theorem body_acceleration (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (time : TimeDomain) (input : Signal 6)
    (state : Signal 5) (realized : (system implementation time.axis).Rel time input state)
    (t : ℝ) (within : t ∈ time.domain) :
    HasDerivWithinAt (fun t => state t 2) (observations.run (state t) 2) time.domain t := by
  have h := ((system_law implementation rate law time input state).mp realized).2 t within 2
  convert! h using 1
  simp [observations, Polynomial.Expr.eval, rhs]
  ring

/-- One reusable outer theorem gives all three visible bounds. -/
theorem output_contract (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (supported : SupportedRate rate)
    (time : TimeDomain) :
    Contract (observed implementation time.axis) time (admitted time)
      (Always time safeOutputs) :=
  Contract.compose (system_contract implementation rate law supported time)
    (Contract.lift observations time output_inclusion) (DomainRespecting.lift _ _ _)

/-- Original actuator: rate 2. -/
theorem standard_contract (time : TimeDomain) :
    Contract (observed (actuator 2) time.axis) time (admitted time)
      (Always time safeOutputs) :=
  output_contract _ 2 (actuator_law 2) (Or.inl rfl) time

/-- A faster actuator reuses the outer theorem and the same storage certificate. -/
theorem replacement_contract (time : TimeDomain) :
    Contract (observed (actuator (5 / 2)) time.axis) time (admitted time)
      (Always time safeOutputs) :=
  output_contract _ (5 / 2) (actuator_law (5 / 2)) (Or.inr rfl) time

#print axioms combined_storage
#print axioms output_contract
#print axioms replacement_contract

end Gimle.Forseti.Examples.ActiveSuspension
