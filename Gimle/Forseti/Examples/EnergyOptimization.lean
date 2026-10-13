import Gimle.Forseti.Examples.EnergyDemo
import Gimle.Forseti.Examples.EnergyOptimizationData
import Gimle.Asgard.Examples.EnergyOptimization

/-! Transfer the original energy property through Asgard's exact circuit rewrite. -/
namespace Gimle.Forseti.EnergyOptimization

export Gimle.Asgard.EnergyOptimization (optimized optimizedIdentity equivalence
  wrongMultiplier counterexample wrongIsNotEquivalent)

theorem sourceMatchesAsgard : EnergyDemo.energy = EnergyOptimizationData.source := rfl

theorem targetMatchesAsgard : optimized = EnergyOptimizationData.target := rfl

-- This theorem is about precisely the two exported Asgard circuits.
theorem exportedEquivalence :
    GlobalCircuitEquivalence EnergyOptimizationData.source EnergyOptimizationData.target :=
  equivalence

-- Reuse the original [0,4] guarantee on [-1,1]² through exact substitution.
theorem optimizedBound :
    ExactHoare EnergyDemoData.precondition optimized EnergyDemoData.postcondition :=
  exactCircuitSubstitution EnergyDemo.energyBound equivalence

theorem wrongMatchesAsgard : wrongMultiplier = EnergyOptimizationData.Wrong.target := rfl

theorem wrongViolatesBound :
    ¬ ExactHoare EnergyDemoData.precondition wrongMultiplier EnergyDemoData.postcondition := by
  intro claim
  have bound := claim ![1, 1] EnergyDemo.maximumAttained.1
  norm_num [EnergyDemoData.postcondition, counterexample.2] at bound

#print axioms exportedEquivalence
#print axioms optimizedBound
#print axioms wrongIsNotEquivalent
#print axioms wrongViolatesBound

end Gimle.Forseti.EnergyOptimization
