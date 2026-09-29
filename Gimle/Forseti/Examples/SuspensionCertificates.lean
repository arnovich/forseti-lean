import Gimle.Forseti.Examples.SuspensionModel
import Gimle.Forseti.Dissipative

/-! Certificate targets recomputed from the independent suspension model.
The optional search tool emits data for these targets; it does not define them. -/

namespace Gimle.Forseti.Examples.ActiveSuspension

open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.LinearEnergy

/-- Embed state storage into [state, road], with no storage on the road input. -/
def embed (p : QMatrix 5) : QMatrix (5 + 1) := fun i j =>
  Fin.addCases (fun i => Fin.addCases (p i) (fun _ => 0) j) (fun _ => 0) i

/-- Extend the source dynamics for the algebraic derivative calculation only.
The final row is zero because no road derivative is used or assumed. -/
def extendedMatrix (rate : ℚ) : QMatrix (5 + 1) := fun i j =>
  Fin.addCases (fun i => Fin.addCases (stateMatrix rate i) (fun _ => roadVector i) j)
    (fun _ => 0) i

/-- The square certificate must prove V' + alpha V ≤ beta road². -/
def supplyMatrix (p : QMatrix 5) (alpha beta rate : ℚ) : QMatrix (5 + 1) := fun i j =>
  dissipation (extendedMatrix rate) (embed p) i j - alpha * embed p i j +
    if i = 5 ∧ j = 5 then beta else 0

/-- Containment of the independently specified Euclidean initial ball. -/
def initialMatrix (p : QMatrix 5) : QMatrix 5 := fun i j =>
  (if i = j then 100 else 0) - p i j

/-- The requested output square must be bounded by V. -/
def outputMatrix (p : QMatrix 5) (output : Fin 3) : QMatrix 5 := fun i j =>
  p i j - outputRows output i * outputRows output j

end Gimle.Forseti.Examples.ActiveSuspension
