import Gimle.Forseti.Trajectory

/-! A normalized two-mass active suspension, with road displacement as input.
Masses are 2 and 1, suspension stiffness/damping are both 2, tire stiffness is
4, and there is no tire damper. State order is [qb, qw, vb, vw, force].
This is an exact mathematical benchmark, not a calibrated vehicle model.
-/

namespace Gimle.Forseti.Examples.ActiveSuspension

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open Polynomial

/-- Plant ports: [road displacement, applied force, qb, qw, vb, vw]. -/
def plantField : Gimle.Asgard.Circuit (2 + 4) 4 :=
  compileOutputs ![.var 4, .var 5,
    .add (.add (.add (.neg (.var 2)) (.var 3)) (.add (.neg (.var 4)) (.var 5)))
      (.mul (.constant (1 / 2)) (.var 1)),
    .add (.add (.add (.mul (.constant 2) (.var 2)) (.mul (.constant (-6)) (.var 3)))
      (.add (.mul (.constant 2) (.var 4)) (.mul (.constant (-2)) (.var 5))))
      (.add (.neg (.var 1)) (.mul (.constant 4) (.var 0)))]

/-- The mechanical component has its own four-state trace. -/
def plant (axis : String) : Dynamics.Circuit (2 + 4) 4 := close axis plantField

/-- The controller observes the plant state and commands an opposing force. -/
def controller : Gimle.Asgard.Circuit 4 1 :=
  (Expr.add (.add (.neg (.var 0)) (.var 1)) (.add (.neg (.var 2)) (.var 3))).compile

/-- Actuator field: first-order response to command, with explicit force state. -/
def actuatorField (rate : ℚ) : Gimle.Asgard.Circuit (1 + 1) 1 :=
  (Expr.mul (.constant rate) (.add (.var 0) (.neg (.var 1)))).compile

/-- The actuator has its own one-state trace. -/
def actuator (rate : ℚ) (axis : String) : Dynamics.Circuit (1 + 1) 1 :=
  close axis (actuatorField rate)

/-- Algebraic command, checked against the original controller below. -/
noncomputable def command (s : Point 4) : ℝ := -s 0 + s 1 - s 2 + s 3

/-- Plant derivative at an open input port. -/
noncomputable def plantRhs (road force : ℝ) (s : Point 4) : Point 4 :=
  ![s 2, s 3, -s 0 + s 1 - s 2 + s 3 + force / 2,
    2 * s 0 - 6 * s 1 + 2 * s 2 - 2 * s 3 - force + 4 * road]

@[simp] theorem controller_run (s : Point 4) : controller.run s 0 = command s := by
  simp [controller, command, Expr.eval]
  ring

@[simp] theorem plantField_run (d : Point 2) (s : Point 4) :
    plantField.run (pointAppend d s) = plantRhs (d 0) (d 1) s := by
  funext i
  fin_cases i <;>
    simp [plantField, plantRhs, Expr.eval, pointAppend] <;> ring

@[simp] theorem actuatorField_run (rate : ℚ) (d s : Point 1) :
    (actuatorField rate).run (pointAppend d s) 0 = (rate : ℝ) * (d 0 - s 0) := by
  simp [actuatorField, Expr.eval, pointAppend, sub_eq_add_neg]

/-- An unrestricted behavioral interface: no continuity assumption on hidden
commands, which may be arbitrary before the forward time domain. -/
def ActuatorLaw (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ) : Prop :=
  ∀ (time : TimeDomain) (input : Signal 2) (force : Signal 1),
    (implementation time.axis).Rel time input force ↔
      force time.start 0 = input time.start 1 ∧
      ∀ t ∈ time.domain, HasDerivWithinAt (fun t => force t 0)
        ((rate : ℝ) * (input t 0 - force t 0)) time.domain t

/-- Each concrete actuator implements the same parameterized port interface. -/
theorem actuator_law (rate : ℚ) : ActuatorLaw (actuator rate) rate := by
  intro time input force
  unfold actuator
  conv_lhs => rw [← signalAppend_parts (n := 1) (m := 1) input]
  rw [close_rel]
  simp only [true_and]
  constructor
  · rintro ⟨initial, derivative⟩
    refine ⟨congrFun initial 0, ?_⟩
    intro t ht
    simpa [signalLeft, pointLeft] using derivative t ht 0
  · rintro ⟨initial, derivative⟩
    refine ⟨?_, ?_⟩
    · funext i
      fin_cases i
      exact initial
    · intro t ht i
      fin_cases i
      simpa [signalLeft, pointLeft] using derivative t ht

/-- Mechanical component contract, including its actual initial wires. -/
theorem plant_law (time : TimeDomain) (input : Signal (2 + 4)) (state : Signal 4) :
    (plant time.axis).Rel time input state ↔
      state time.start = signalRight input time.start ∧
      ∀ t ∈ time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        (plantRhs (input t 0) (input t 1) (state t) i) time.domain t := by
  unfold plant
  conv_lhs => rw [← signalAppend_parts (n := 2) (m := 4) input]
  rw [close_rel]
  simp [signalLeft, pointLeft]

/-- Mechanical storage combines both masses and both springs. -/
noncomputable def plantEnergy (s : Point 4) : ℝ :=
  (s 0 - s 1)^2 + 2 * s 1^2 + s 2^2 + s 3^2 / 2

/-- The derivative functional of the plant's storage. -/
noncomputable def plantEnergyRate (s v : Point 4) : ℝ :=
  2 * (s 0 - s 1) * (v 0 - v 1) + 4 * s 1 * v 1 +
    2 * s 2 * v 2 + s 3 * v 3

/-- Open-port storage identity retains the force/velocity and road/velocity exchanges. -/
theorem plant_storage (road force : ℝ) (s : Point 4) :
    plantEnergyRate s (plantRhs road force s) =
      -2 * (s 2 - s 3)^2 + force * (s 2 - s 3) + 4 * road * s 3 := by
  simp [plantEnergyRate, plantRhs]
  ring

/-- Actuator storage retains the command/force exchange and its damping. -/
theorem actuator_storage (rate : ℚ) (command force : ℝ) :
    2 * force * ((rate : ℝ) * (command - force)) =
      2 * (rate : ℝ) * (force * command - force^2) := by ring

/-- Route [road, initial5, feedback5] to [plant drivers, plant initial4,
actuator command, actuator initial]. The controller is a typed subcircuit. -/
def connection : Gimle.Asgard.Circuit ((1 + 5) + 5) ((2 + 4) + (1 + 1)) :=
  .compose
    (Polynomial.route ![0, 10, 1, 2, 3, 4, 6, 7, 8, 9, 5])
    (.parallel (Wiring.identity 6) (.parallel controller (.id)))

/-- External input and state sent to the two open component interfaces. -/
noncomputable def componentInputs (input : Point 6) (s : Point 5) : Point 8 :=
  ![input 0, s 4, input 1, input 2, input 3, input 4,
    command ![s 0, s 1, s 2, s 3], input 5]

@[simp] theorem connection_run (input : Point 6) (s : Point 5) :
    connection.run (pointAppend input s) = componentInputs input s := by
  funext i
  fin_cases i <;>
    simp [connection, componentInputs, Gimle.Asgard.Circuit.run,
      controller, Expr.eval, pointLeft, pointRight, pointAppend, command]
  ring

/-- Outer feedback around two already closed components: three real traces. -/
def system (implementation : String → Dynamics.Circuit 2 1) (axis : String) :
    Dynamics.Circuit (1 + 5) 5 :=
  .trace 5 (.compose (.lift connection)
    (.compose (.parallel (plant axis) (implementation axis)) (.lift (duplicate 5))))

/-- The open-loop connection identifies the feedback witnesses with the output.
Both directions construct/check the actual circuit relation. -/
theorem system_ports (implementation : String → Dynamics.Circuit 2 1)
    (time : TimeDomain) (input : Signal 6) (state : Signal 5) :
    (system implementation time.axis).Rel time input state ↔
      (plant time.axis).Rel time
        (signalLeft (n := 6) (m := 2) (fun t => componentInputs (input t) (state t)))
        (signalLeft (n := 4) (m := 1) state) ∧
      (implementation time.axis).Rel time
        (signalRight (n := 6) (m := 2) (fun t => componentInputs (input t) (state t)))
        (signalRight (n := 4) (m := 1) state) := by
  simp only [system, Dynamics.Circuit.Rel]
  constructor
  · rintro ⟨feedback, routed, hr, output, ho, hd⟩
    subst routed
    have both : signalAppend state feedback = signalAppend output output := by
      convert! hd using 1
      funext t
      exact (duplicate_run (output t)).symm
    have hs : state = output := by simpa using congrArg signalLeft both
    have hf : feedback = output := by simpa using congrArg signalRight both
    subst output
    subst feedback
    simpa only [signalAppend, connection_run] using ho
  · intro h
    refine ⟨state, _, rfl, state, ?_, ?_⟩
    · simpa only [signalAppend, connection_run] using h
    · funext t
      exact (duplicate_run (state t)).symm

/-- The shared actuator interface accepts these two fixed response rates. -/
def SupportedRate (rate : ℚ) : Prop := rate = 2 ∨ rate = 5 / 2

/-- Whole derivative assembled from the component ports; all state positions are explicit. -/
noncomputable def rhs (rate : ℚ) (road : ℝ) (s : Point 5) : Point 5 :=
  ![s 2, s 3, -s 0 + s 1 - s 2 + s 3 + s 4 / 2,
    2 * s 0 - 6 * s 1 + 2 * s 2 - 2 * s 3 - s 4 + 4 * road,
    (rate : ℝ) * (-s 0 + s 1 - s 2 + s 3 - s 4)]

/-- Exact source coefficients, independently bound to the original typed components. -/
def stateMatrix (rate : ℚ) : LinearEnergy.QMatrix 5 :=
  ![![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-1, 1, -1, 1, 1 / 2],
    ![2, -6, 2, -2, -1], ![-rate, rate, -rate, rate, -rate]]

/-- Road displacement enters wheel acceleration only. -/
def roadVector : Fin 5 → ℚ := ![0, 0, 0, 4, 0]

/-- A component interface implementation induces precisely the assembled ODE. -/
theorem system_law (implementation : String → Dynamics.Circuit 2 1) (rate : ℚ)
    (law : ActuatorLaw implementation rate) (time : TimeDomain)
    (input : Signal 6) (state : Signal 5) :
    (system implementation time.axis).Rel time input state ↔
      state time.start = signalRight input time.start ∧
      ∀ t ∈ time.domain, ∀ i, HasDerivWithinAt (fun t => state t i)
        (rhs rate (input t 0) (state t) i) time.domain t := by
  rw [system_ports, plant_law, law]
  constructor
  · rintro ⟨⟨pi, pd⟩, ⟨ai, ad⟩⟩
    refine ⟨?_, ?_⟩
    · funext i
      fin_cases i
      all_goals first
        | exact congrFun pi 0
        | exact congrFun pi 1
        | exact congrFun pi 2
        | exact congrFun pi 3
        | exact ai
    · intro t ht i
      fin_cases i
      all_goals first
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs, command] using pd t ht 0
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs, command] using pd t ht 1
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs, command] using pd t ht 2
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs, command] using pd t ht 3
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs, command] using ad t ht
  · rintro ⟨initial, derivative⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · funext i
      fin_cases i <;> convert! congrFun initial _ using 1
    · intro t ht i
      fin_cases i
      all_goals first
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs] using derivative t ht 0
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs] using derivative t ht 1
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs] using derivative t ht 2
        | simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
            plantRhs, rhs] using derivative t ht 3
    · exact congrFun initial 4
    · intro t ht
      simpa [componentInputs, signalLeft, signalRight, pointLeft, pointRight,
        rhs, command] using derivative t ht 4

/-- Exact observation circuit: suspension travel, actuator force, body acceleration. -/
def observations : Gimle.Asgard.Circuit 5 3 :=
  compileOutputs ![.add (.var 0) (.neg (.var 1)), .var 4,
    .add (.add (.add (.neg (.var 0)) (.var 1)) (.add (.neg (.var 2)) (.var 3)))
      (.mul (.constant (1 / 2)) (.var 4))]

/-- State rows of the three observed linear quantities. -/
def outputRows : Fin 3 → Fin 5 → ℚ :=
  ![![1, -1, 0, 0, 0], ![0, 0, 0, 0, 1], ![-1, 1, -1, 1, 1 / 2]]

/-- Outputs of the whole nested circuit. -/
def observed (implementation : String → Dynamics.Circuit 2 1) (axis : String) :=
  Dynamics.Circuit.compose (system implementation axis) (.lift observations)

/-- The initial region is fixed independently of the searched storage matrix. -/
noncomputable def initialSize (s : Point 5) : ℝ := ∑ i, s i ^ 2

/-- Continuous road displacement of amplitude at most 1/1000, from an initial
Euclidean ball of radius 1/10. Initialization wires are read only at the start. -/
def admitted (time : TimeDomain) : SignalPredicate 6 :=
  Initialized time (fun road => Continuous road ∧
    ∀ t ∈ time.domain, |road t 0| ≤ 1 / 1000)
    (fun initial => initialSize initial ≤ 1 / 100)

/-- Fixed output limits, independent of the certificate search. -/
def safeOutputs (y : Point 3) : Prop := ∀ i, |y i| ≤ 1

#print axioms system_law

end Gimle.Forseti.Examples.ActiveSuspension
