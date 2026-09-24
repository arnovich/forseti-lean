import Gimle.Forseti.LinearEnergy
import Gimle.Asgard.Examples.LinearOscillator
import Gimle.Asgard.Examples.EnergyDemo

namespace Gimle.Forseti.Tests.LinearEnergy
open Gimle.Asgard Dynamics Gimle.Forseti.LinearEnergy

def oscillatorP : QMatrix 2 := ![![2, 0], ![0, 2]]

def oscillatorCertificate : Certificate 2 where
  positive := { count := 2, weight := ![2, 2], vector := ![![1, 0], ![0, 1]] }
  decrease := { count := 1, weight := ![8], vector := ![![0, 1]] }

theorem oscillator_valid :
    oscillatorCertificate.Valid Examples.LinearOscillator.matrix oscillatorP := by
  simp only [Certificate.Valid, WeightedSquares.Represents]
  decide +kernel

-- Full entry recomputation recovers D=diag(0,8), hence V'=-8y².
example : dissipation Examples.LinearOscillator.matrix oscillatorP = ![![0, 0], ![0, 8]] := by
  decide +kernel

theorem oscillator_energy (x : Point 2) : EnergyDemo.energy.run x 0 = quadratic oscillatorP x := by
  rw [EnergyDemo.energyIdentity]
  simp [quadratic, realMatrix, oscillatorP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem oscillator_rhs (x : Point 2) :
    Oscillator.vectorField.run x = Examples.LinearOscillator.matrix.eval x := by
  rw [← Examples.LinearOscillator.field_eq, Linear.Matrix.field_correct]

/-- A certificate for the original typed RHS and energy circuits bounds every
actual realization, not only the canonical explicit trajectory. -/
theorem oscillator_bound (state : Signal 2)
    (realized : Realizes Oscillator.vectorField
      (Examples.LinearOscillator.problem 0 1 0).time ![1, 0] state)
    (t : ℝ) (forward : 0 ≤ t) :
    0 ≤ EnergyDemo.energy.run (state t) 0 ∧ EnergyDemo.energy.run (state t) 0 ≤ 4 := by
  apply circuit_energy_bound (Examples.LinearOscillator.problem 0 1 0)
    Oscillator.vectorField EnergyDemo.energy oscillatorP oscillatorCertificate
    oscillator_rhs oscillator_energy oscillator_valid state realized 4 _ t _
  · norm_num [Examples.LinearOscillator.problem, EnergyDemo.energyIdentity]
  · simpa [Examples.LinearOscillator.problem, TimeDomain.domain] using forward

-- The initial sublevel is nonempty, and its nonzero point has an actual realization.
example : EnergyDemo.energy.run ![1, 0] 0 ≤ 4 := by norm_num [EnergyDemo.energyIdentity]
example : ∃ state, Realizes Oscillator.vectorField
    (Examples.LinearOscillator.problem 0 1 0).time ![1, 0] state :=
  exists_realization (Examples.LinearOscillator.problem 0 1 0) Oscillator.vectorField oscillator_rhs

-- A changed damping sign invalidates the stored decrease decomposition.
def changedDamping : QMatrix 2 := ![![0, 1], ![-1, 2]]
example : ¬ oscillatorCertificate.Valid changedDamping oscillatorP := by
  simp only [Certificate.Valid, WeightedSquares.Represents]
  decide +kernel

-- Off-diagonal entries contribute TWICE to a symmetric quadratic's cross term.
def sharedSquare : WeightedSquares 2 where
  count := 1
  weight := ![1]
  vector := ![![1, 1]]

example : sharedSquare.Represents ![![1, 1], ![1, 1]] := by
  simp only [WeightedSquares.Represents]
  decide +kernel
example (x : Point 2) : quadratic sharedSquare.matrix x = (x 0 + x 1)^2 := by
  simp [quadratic, realMatrix, Matrix.mulVec, dotProduct,
    WeightedSquares.matrix, termMatrix, sharedSquare, Fin.sum_univ_two]
  ring

-- Asymmetric A and nonuniform P expose mistaken transposes in AᵀP+PA.
def asymmetricA : QMatrix 2 := ![![-1, 1], ![-2, -2]]
def asymmetricP : QMatrix 2 := ![![2, 0], ![0, 1]]
def asymmetricCertificate : Certificate 2 where
  positive := { count := 2, weight := ![2, 1], vector := ![![1, 0], ![0, 1]] }
  decrease := { count := 2, weight := ![4, 4], vector := ![![1, 0], ![0, 1]] }
example : asymmetricCertificate.Valid asymmetricA asymmetricP := by
  simp only [Certificate.Valid, WeightedSquares.Represents]
  decide +kernel

-- Three dimensions, noncommuting A/P and a fractional weighted-square factor.
def threeA : QMatrix 3 := ![![-1, 1, 0], ![0, -2, 0], ![0, 0, -3]]
def threeP : QMatrix 3 := ![![2, 1, 0], ![1, 1, 0], ![0, 0, 1]]
def threeCertificate : Certificate 3 where
  positive :=
    { count := 3
      weight := ![1, 1, 1]
      vector := ![![1, 0, 0], ![1, 1, 0], ![0, 0, 1]] }
  decrease :=
    { count := 3
      weight := ![4, 7/4, 6]
      vector := ![![1, 1/4, 0], ![0, 1, 0], ![0, 0, 1]] }
example : threeCertificate.Valid threeA threeP := by
  simp only [Certificate.Valid, WeightedSquares.Represents]
  decide +kernel
example : dissipation threeA threeP = ![![4, 1, 0], ![1, 2, 0], ![0, 0, 6]] := by
  decide +kernel

-- A semidefinite energy certificate does not control the unobserved unstable state.
def partialA : QMatrix 2 := ![![-1, 0], ![0, 1]]
def partialP : QMatrix 2 := ![![1, 0], ![0, 0]]
def partialCertificate : Certificate 2 where
  positive := { count := 1, weight := ![1], vector := ![![1, 0]] }
  decrease := { count := 1, weight := ![2], vector := ![![1, 0]] }
example : partialCertificate.Valid partialA partialP := by
  simp only [Certificate.Valid, WeightedSquares.Represents]
  decide +kernel
example (y : ℝ) : quadratic partialP ![0, y] = 0 := by
  simp [quadratic, realMatrix, partialP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- Empty square families certify zero energy, including zero-dimensional systems.
def noSquares (n : Nat) : WeightedSquares n where
  count := 0
  weight := Fin.elim0
  vector := Fin.elim0

example {n : Nat} (a : QMatrix n) :
    (Certificate.mk (noSquares n) (noSquares n)).Valid a 0 := by
  simp [Certificate.Valid, WeightedSquares.Represents, noSquares,
    WeightedSquares.matrix, dissipation]

-- Negative weights fail even when a zero vector makes the entry sums vanish.
def negativeZero : WeightedSquares 1 where
  count := 1
  weight := ![-1]
  vector := ![![0]]
example : ¬ negativeZero.Represents 0 := by
  simp only [WeightedSquares.Represents]
  decide +kernel

theorem oscillator_full_contract :
    SublevelSafety Oscillator.vectorField EnergyDemo.energy
      (Examples.LinearOscillator.problem 0 1 0).time 4 :=
  certificate_sound (Examples.LinearOscillator.problem 0 1 0) Oscillator.vectorField
    EnergyDemo.energy oscillatorP oscillatorCertificate oscillator_rhs oscillator_energy oscillator_valid 4

#print axioms oscillator_bound
#print axioms oscillator_full_contract
end Gimle.Forseti.Tests.LinearEnergy
