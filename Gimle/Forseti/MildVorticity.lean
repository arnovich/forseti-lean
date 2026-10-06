import Gimle.Forseti.Euler
import Gimle.Forseti.Mild
import Gimle.Asgard.Streams.MildDissipation

/-! Classical, dissipative total contracts of Asgard's typed mild circuit.
Admission fixes only the embedded initial slice. Convergence constants and
numerical certificate choices are theorem premises, not admission tests. -/
namespace Gimle.Forseti.MildVorticity
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.Mild

/-- The canonical boundary representative; only its zero slice matters. -/
noncomputable def boundary (P : TrigPoly) : Gimle.Asgard.Streams.Mild.Stream := fun _ => embed P

/-- Guarantees on the actual output throughout the requested forward interval. -/
structure Certified (ν : ℚ) (P : TrigPoly) (T : ℝ)
    (output : Gimle.Asgard.Streams.Mild.Point 1) : Prop where
  formal_eq : output 0 = wild ν (boundary P)
  mean_zero : ∀ n, Gimle.Asgard.Streams.Mild.MeanZero (output 0 n)
  even : ∀ n, Gimle.Asgard.Streams.Mild.IsEven (output 0 n)
  initial : ∀ x, analyticField ν (output 0) 0 x = RealPoly.field (realEmbed P) x
  converges : ∀ t ∈ Set.Icc 0 T, ∀ x,
    HasSum (seriesTerm ν (output 0) t x) (analyticField ν (output 0) t x)
  reconstruction : ∀ t ∈ Set.Icc 0 T, ∀ x,
    analyticField ν (output 0) t x = ∑' k, fourierCoeff ν (output 0) t k * Real.cos (phase k x)
  classical : IsMildClassicalSolution ν (output 0) P T
  dissipation : HasDissipation ν (output 0) T

/-- Package the proved properties of the canonical actual output. -/
theorem certified {ν : ℚ} (hν : 0 ≤ ν) (P : TrigPoly)
    (hz : Torus.MeanZero P) (he : Torus.IsEven P) {K : ℕ} (hK : Torus.SizeLE K P)
    {T M q : ℝ} (hT : 0 ≤ T) (hg : GeometricBound ν (wild ν (boundary P)) T M q)
    (hq : 0 ≤ q) (hq1 : q < 1) : Certified ν P T ![wild ν (boundary P)] := by
  have hc := mild_classical hν (boundary P) P rfl hz he hK hT hg hq hq1
  have hd := mild_dissipation hν (boundary P) P rfl hz he hK hT hg hq hq1
  have hM : 0 ≤ M := by
    have hh := (RealPoly.l1_nonneg (eval ν 0 (wild ν (boundary P) 0))).trans (hg 0 ⟨le_rfl, hT⟩ 0)
    simpa using hh
  refine ⟨rfl, wild_meanZero ν (boundary P) (meanZero_embed hz),
    wild_isEven ν (boundary P) (isEven_embed he), hc.initial, ?_, ?_, hc, hd⟩
  · intro t ht x
    exact (hc.summable t ht x).of_norm.hasSum
  · intro t ht x
    exact analyticField_eq_fourier (wild_sizeLE ν (boundary P) K (sizeLE_embed hK)) hM hq hq1 (hg t ht) x

/-- A total contract for every input with the prescribed initial slice. -/
theorem contract {ν : ℚ} (hν : 0 ≤ ν) (P : TrigPoly)
    (hz : Torus.MeanZero P) (he : Torus.IsEven P) {K : ℕ} (hK : Torus.SizeLE K P)
    {T M q : ℝ} (hT : 0 ≤ T) (hg : GeometricBound ν (wild ν (boundary P)) T M q)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed P) (Certified ν P T) := by
  apply (Mild.solution_contract ν (boundary P)).consequence (fun _ h => h)
  intro output ho
  subst output
  exact certified hν P hz he hK hT hg hq hq1

/-- A requested numerical postcondition preserves all classical guarantees. -/
theorem contract_with {ν : ℚ} (P : TrigPoly) {T : ℝ}
    (hc : Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed P) (Certified ν P T))
    (post : Mild.Predicate 1) (hp : post ![wild ν (boundary P)]) :
    Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed P)
      (fun output => Certified ν P T output ∧ post output) := by
  apply hc.consequence (fun _ h => h)
  intro output h
  refine ⟨h, ?_⟩
  have ho : output = ![wild ν (boundary P)] := by
    funext i
    fin_cases i
    exact h.formal_eq
  rwa [ho]

namespace Table

/-- The Euler-scale certificate includes every nonnegative viscosity and zero data. -/
theorem euler_contract (table : Torus.Table) (hz : Euler.Table.ZeroMean table)
    (he : Euler.Table.Symmetric table) {ν : ℚ} (hν : 0 ≤ ν)
    {K : ℕ} (hK : 1 ≤ K) (hs : ∀ e ∈ table, size e.1 ≤ K)
    {L : ℚ} (hL : Torus.Table.absSum table ≤ L) {T : ℝ} (hT : 0 ≤ T)
    (hq : (72 : ℝ) * L * K * T < 1) :
    Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed (Torus.Table.toTrig table))
      (Certified ν (Torus.Table.toTrig table) T) := by
  have hl := (Torus.Table.l1_le_absSum table).trans hL
  have hl0 : (0 : ℝ) ≤ L := by exact_mod_cast (Torus.l1_nonneg _).trans hl
  exact contract hν _ (Euler.Table.meanZero hz) (Euler.Table.isEven he)
    (Torus.Table.sizeLE_toTrig hs) hT
    (wild_euler_geometric hν (boundary _) _ rfl hK (Torus.Table.sizeLE_toTrig hs) hl T)
    (by positivity) hq

/-- The viscosity-dependent certificate is an alternative proof of the same contract. -/
theorem catalan_contract (table : Torus.Table) (hz : Euler.Table.ZeroMean table)
    (he : Euler.Table.Symmetric table) {ν r : ℚ} (hν : 0 < ν)
    {K : ℕ} (hs : ∀ e ∈ table, size e.1 ≤ K)
    {L : ℚ} (hL : Torus.Table.absSum table ≤ L) {T : ℝ} (hT : 0 ≤ T)
    (hr : 0 ≤ r) (hTr : T ≤ (ν : ℝ) * (r : ℝ) ^ 2) (hq : 4 * r * L < 1) :
    Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed (Torus.Table.toTrig table))
      (Certified ν (Torus.Table.toTrig table) T) := by
  have hl := (Torus.Table.l1_le_absSum table).trans hL
  have hl0 : (0 : ℚ) ≤ L := (Torus.l1_nonneg _).trans hl
  exact contract hν.le _ (Euler.Table.meanZero hz) (Euler.Table.isEven he)
    (Torus.Table.sizeLE_toTrig hs) hT
    (wild_geometric hν hT hr hTr (boundary _) _ rfl hl)
    (by exact_mod_cast (show 0 ≤ 4 * r * L by positivity)) (by exact_mod_cast hq)

/-- Semantic cancellation admits an arbitrary nonnegative horizon, independently
of the unreduced table's absolute coefficient sum. -/
theorem zero_contract (table : Torus.Table) (hz : Euler.Table.IsZero table)
    {ν : ℚ} (hν : 0 ≤ ν) {T : ℝ} (hT : 0 ≤ T) :
    Mild.Contract (mildCircuit ν) (fun input => input 0 0 = embed (Torus.Table.toTrig table))
      (Certified ν (Torus.Table.toTrig table) T) := by
  rw [Euler.Table.toTrig_zero hz]
  have hg := wild_euler_geometric hν (boundary 0) 0 rfl (K := 1) (by norm_num)
    (by simp [Torus.SizeLE]) (L := 0) (by simp [Torus.l1]) T
  have hg' : GeometricBound ν (wild ν (boundary 0)) T 0 0 := by simpa using hg
  exact contract hν 0 (by simp [Torus.MeanZero]) (by simp [Torus.IsEven])
    (K := 1) (by simp [Torus.SizeLE]) hT hg' le_rfl (by norm_num)

end Table
#print axioms contract
#print axioms Table.euler_contract
#print axioms Table.catalan_contract
#print axioms Table.zero_contract
end Gimle.Forseti.MildVorticity
