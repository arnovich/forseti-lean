import Gimle.Forseti.ClassicalVorticity.Uniqueness
import Gimle.Forseti.MildVorticity

/-! Classical uniqueness as a consequence of the certified mild Hoare contract. -/
namespace Gimle.Forseti.MildVorticity
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Mild
open Gimle.Forseti.ClassicalVorticity

/-- Every independent classical solution agrees with the certified output's
vorticity field on the certified interval. -/
theorem Certified.unique_classical {ν : ℚ} {P : Torus.TrigPoly} {T : ℝ} {output : Point 1}
    (hc : Certified ν P T output) (hν : 0 ≤ ν) (hT : 0 ≤ T)
    {ω ψ : SpatialJet} {dt : Field}
    (h : Solves (ν : ℝ) T (RealPoly.field (realEmbed P)) ω ψ dt) :
    ∀ t ∈ Set.Icc 0 T, ∀ p, ω.value t p = analyticField ν (output 0) t p :=
  h.vorticity_unique (of_mild hc.classical) (by exact_mod_cast hν) hT

/-- The mild circuit's total Hoare contract can expose uniqueness among the
independent classical fields as part of its output guarantee. -/
theorem contract_with_classical_uniqueness {ν : ℚ} {P : Torus.TrigPoly} {T : ℝ}
    (hc : Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed P) (Certified ν P T))
    (hν : 0 ≤ ν) (hT : 0 ≤ T) :
    Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed P)
      (fun output => Certified ν P T output ∧ ∀ (ω ψ : SpatialJet) (dt : Field),
        Solves (ν : ℝ) T (RealPoly.field (realEmbed P)) ω ψ dt →
          ∀ t ∈ Set.Icc 0 T, ∀ p, ω.value t p = analyticField ν (output 0) t p) := by
  apply hc.consequence (fun _ h => h)
  intro output h
  exact ⟨h, fun _ _ _ hs => h.unique_classical hν hT hs⟩

#print axioms Certified.unique_classical
#print axioms contract_with_classical_uniqueness
end Gimle.Forseti.MildVorticity
