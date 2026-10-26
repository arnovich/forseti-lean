module

public import Gimle.Forseti.Examples.LoadedSAIFExistence
public import Gimle.Forseti.Examples.LoadedSAIFResources

/-! The fixed physical-time response and resource contract. The five continuous
response bounds are explicit proof obligations. Existence, physical bounds,
uniqueness and the integral budgets then follow without sampled trajectories or
numerical quadrature. A concrete certificate must discharge ContinuousBounds;
this composition theorem alone does not assert those response bounds. -/

@[expose] public section

namespace Gimle.Forseti.Examples.LoadedSAIFContract
open Set LoadedSAIFModel LoadedSAIFExistence LoadedSAIFResources

/-- Continuous response obligations for the unchanged loaded model. -/
structure ContinuousBounds (state : ℝ → State) : Prop where
  peak : ∀ t ∈ Icc (0 : ℝ) 100, state t 1 ≤ 13 / 5
  pool : ∀ t ∈ Icc (0 : ℝ) 100, state t 2 + state t 3 ≤ 8
  startup : ∀ t ∈ Icc (3 : ℝ) 30, state t 1 ∈ Icc (9 / 5) (11 / 5)
  recovery : ∀ t ∈ Icc (33 : ℝ) 100, state t 1 ∈ Icc (9 / 5) (11 / 5)
  tail : ∀ t ∈ Icc (80 : ℝ) 100, |state t 1 - 2| ≤ 3 / 20

/-- Full finite-horizon contract, with uniqueness restricted to its stated
positive-denominator domain and interval. -/
structure Contract (state : ℝ → State) : Prop extends ContinuousBounds state where
  model : Switched state
  physical_before : ∀ t ∈ Icc (0 : ℝ) 30, Physical 0 (state t)
  physical_after : ∀ t ∈ Icc (30 : ℝ) 100, Physical 2 (state t)
  nonnegative : ∀ t ∈ Icc (0 : ℝ) 100, ∀ i, 0 ≤ state t i
  denominator : ∀ t ∈ Icc (0 : ℝ) 100, kappa ≤ kappa + state t 3
  actuation_cap : ∀ t ∈ Icc (0 : ℝ) 100, control (state t) ≤ 4
  actuation_budget : (∫ t in (0 : ℝ)..100, control (state t)) ≤ 270
  synthesis_budget : (∫ t in (0 : ℝ)..100, (2 + state t 1)) ≤ 500
  unique : ∀ other : ℝ → State, Switched other →
    (∀ t ∈ Icc (0 : ℝ) 100, 0 < kappa + other t 3) →
    EqOn state other (Icc (0 : ℝ) 100)

/-- All additional contract clauses follow from physical solutions and the
five continuous response obligations. -/
theorem contract_of_bounds {state : ℝ → State} (hs : Switched state)
    (hb : ∀ t ∈ Icc (0 : ℝ) 30, Physical 0 (state t))
    (ha : ∀ t ∈ Icc (30 : ℝ) 100, Physical 2 (state t))
    (bounds : ContinuousBounds state) : Contract state := by
  have hn : ∀ t ∈ Icc (0 : ℝ) 100, ∀ i, 0 ≤ state t i := by
    intro t ht i
    by_cases h : t ≤ 30
    · exact (hb t ⟨ht.1, h⟩ i).1
    · exact (ha t ⟨(lt_of_not_ge h).le, ht.2⟩ i).1
  have resources := resource_budgets hs (fun t ht => hn t ht 3)
    (by simpa [upper] using (ha 100 (by norm_num) 0).2)
    (fun t ht => capacity_zero (hb t ht))
    (fun t ht => by simpa [upper] using (ha t ht 4).2)
    bounds.peak (fun t ht => (bounds.startup t ht).2)
    (fun t ht => (bounds.recovery t ht).2)
  exact {
    toContinuousBounds := bounds
    model := hs
    physical_before := hb
    physical_after := ha
    nonnegative := hn
    denominator := fun t ht => denominator_lower (hn t ht 3)
    actuation_cap := fun t ht => control_cap (hn t ht 3)
    actuation_budget := le_trans resources.1 (by norm_num)
    synthesis_budget := le_trans resources.2 (by norm_num)
    unique := fun other ho hp => switched_unique hs ho
      (fun t ht => denominator_pos (hn t ht 3)) hp }

/-- A checked response enclosure for physical solutions closes existence of the
full contract. The enclosure remains an explicit premise here. -/
theorem exists_contract_of_bounds
    (checked : ∀ state : ℝ → State, Switched state →
      (∀ t ∈ Icc (0 : ℝ) 30, Physical 0 (state t)) →
      (∀ t ∈ Icc (30 : ℝ) 100, Physical 2 (state t)) →
      ContinuousBounds state) :
    ∃ state : ℝ → State, Contract state := by
  obtain ⟨state, hs, hb, ha⟩ := switched_exists
  exact ⟨state, contract_of_bounds hs hb ha (checked state hs hb ha)⟩

#print axioms contract_of_bounds
#print axioms exists_contract_of_bounds
end Gimle.Forseti.Examples.LoadedSAIFContract
