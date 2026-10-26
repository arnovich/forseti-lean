module

public import Gimle.Asgard.Examples.AIF
public import Gimle.Forseti.Examples.AIFGlobalSolution
public import Gimle.Forseti.Examples.AIFPhysicalCoordinates

/-! The compiled Asgard antithetic integral feedback (AIF) circuit bound to the
physical-coordinate model used by the AIF tube results. The source-compiled field
equals the hand-written physical field, and a realization of the zero-initialized
feedback is exactly a zero-start solution of the physical ODE for `t ≥ 0`. The
compiled observation reads `x₂`, and the bound `x₂ ≤ 16/5` on it is exactly
`y₂ ≤ 6/5` in the equilibrium-shifted coordinates `y = x − (2, 2, 2, ·)` of
`AIFPhysicalCoordinates`. For every fixed `η ≥ 0` a realization exists, any two
agree for `t ≥ 0`, and every species and the observation stay nonnegative. The
shifted start and moving-tube energy derivative are restated for realizations so
local tube results can take one directly. No tube, drift or upper output bound is
claimed here. -/

@[expose] public section

namespace Gimle.Forseti.Examples.AIFCircuitBinding
open Gimle.Asgard AIFPhysicalCoordinates

/-- The source-compiled feedback field equals the hand-written `physicalField`. -/
theorem compiled_field (eta : ℝ) (x : Point 4) :
    Gimle.Asgard.Examples.AIF.field.run (pointAppend ![eta] x) = physicalField eta x :=
  Gimle.Asgard.Examples.AIF.field_appended eta x

/-- The compiled feedback's zero initialization and component ODEs. -/
theorem realizes_iff_physical (eta : ℝ) (state : Dynamics.Signal 4) :
    Gimle.Asgard.Examples.AIF.Realizes eta state ↔ state 0 = 0 ∧
      ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
        HasDerivWithinAt (fun s => state s i)
          (physicalField eta (state t) i) (Set.Ici 0) t :=
  Gimle.Asgard.Examples.AIF.realizes_iff eta state

/-- A realization starts at the shifted point `(-2, -2, -2, -1)`. -/
theorem shifted_initial (eta : ℝ) (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state) :
    shift eta (state 0) = ![-2,-2,-2,-1] := by
  rw [((realizes_iff_physical eta state).mp realized).1]
  exact shift_zero eta

/-- The closed-interval derivative interface used by local tube invariance. -/
theorem shifted_derivative_on (eta : ℝ) (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (a b : ℝ) (ha : 0 ≤ a) (t : ℝ) (ht : t ∈ Set.Icc a b) (i : Fin 4) :
    HasDerivWithinAt (fun s => shift eta (state s) i)
      (AIFDriftModel.field eta (shift eta (state t)) i) (Set.Icc a b) t := by
  have hx := ((realizes_iff_physical eta state).mp realized).2 t (ha.trans ht.1)
  exact (shift_derivative eta state (Set.Ici 0) t hx i).mono
    (fun _ hs => ha.trans hs.1)

/-- The moving-tube energy derivative along a realization of the compiled circuit. -/
theorem compiled_energy_derivative (d : AIFSlabModel.Slab)
    (hh : d.step ≠ 0) (hp : d.etaLo < d.etaHi) (eta : ℝ)
    (state : Dynamics.Signal 4)
    (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => AIFMesh.tubeEnergy d s eta (shift eta (state s)))
      (AIFSlabModel.energyRate d (AIFSlabModel.timeCoordinate d t)
        (AIFSlabModel.etaCoordinate d eta)
        (shift eta (state t) - AIFSlabModel.center d (AIFSlabModel.timeCoordinate d t)
          (AIFSlabModel.etaCoordinate d eta))) (Set.Ici 0) t :=
  physical_tubeEnergy_derivative d hh hp eta state (Set.Ici 0) t
    (((realizes_iff_physical eta state).mp realized).2 t ht)

/-- On the compiled `x₂` observation, `x₂ ≤ 16/5` is exactly the shifted bound `y₂ ≤ 6/5`. -/
theorem compiled_output_bound_iff (eta : ℝ) (x : Point 4) :
    Gimle.Asgard.Examples.AIF.output.run x 0 ≤ 16/5 ↔ shift eta x 1 ≤ 6/5 := by
  rw [Gimle.Asgard.Examples.AIF.output_correct]
  exact output_bound_iff eta x

/-- The constructed physical solution realizes the compiled feedback. -/
theorem solution_realizes (eta : ℝ) (heta : 0 ≤ eta) :
    Gimle.Asgard.Examples.AIF.Realizes eta (AIFGlobalSolution.solution eta heta) :=
  (realizes_iff_physical eta _).mpr
    ⟨AIFGlobalSolution.solution_start eta heta, AIFGlobalSolution.solution_derivative eta heta⟩

/-- Every fixed `η ≥ 0` has a realization. -/
theorem exists_realization (eta : ℝ) (heta : 0 ≤ eta) :
    ∃ state : Dynamics.Signal 4, Gimle.Asgard.Examples.AIF.Realizes eta state :=
  ⟨AIFGlobalSolution.solution eta heta, solution_realizes eta heta⟩

/-- Any two realizations of the compiled feedback agree for all `t ≥ 0`. -/
theorem realization_unique (eta : ℝ) (heta : 0 ≤ eta) (x y : Dynamics.Signal 4)
    (hx : Gimle.Asgard.Examples.AIF.Realizes eta x)
    (hy : Gimle.Asgard.Examples.AIF.Realizes eta y) : Set.EqOn x y (Set.Ici 0) := by
  have px := (realizes_iff_physical eta x).mp hx
  have py := (realizes_iff_physical eta y).mp hy
  intro t ht
  exact (AIFGlobalSolution.solution_unique eta heta x px.1 px.2 ht).trans
    (AIFGlobalSolution.solution_unique eta heta y py.1 py.2 ht).symm

/-- Every species of a realization is nonnegative for `t ≥ 0`. -/
theorem realization_nonnegative (eta : ℝ) (heta : 0 ≤ eta)
    (state : Dynamics.Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 4) : 0 ≤ state t i := by
  have physical := (realizes_iff_physical eta state).mp realized
  have eq := AIFGlobalSolution.solution_unique eta heta state physical.1 physical.2 ht
  rw [eq]
  exact AIFGlobalSolution.solution_nonnegative eta heta t ht i

/-- The compiled observation reads a nonnegative physical species. -/
theorem realization_output_nonnegative (eta : ℝ) (heta : 0 ≤ eta)
    (state : Dynamics.Signal 4) (realized : Gimle.Asgard.Examples.AIF.Realizes eta state)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Gimle.Asgard.Examples.AIF.output.run (state t) 0 := by
  rw [Gimle.Asgard.Examples.AIF.output_correct]
  exact realization_nonnegative eta heta state realized t ht 1

#print axioms compiled_field
#print axioms realizes_iff_physical
#print axioms shifted_initial
#print axioms shifted_derivative_on
#print axioms compiled_energy_derivative
#print axioms compiled_output_bound_iff
#print axioms solution_realizes
#print axioms exists_realization
#print axioms realization_unique
#print axioms realization_nonnegative
#print axioms realization_output_nonnegative
end Gimle.Forseti.Examples.AIFCircuitBinding
