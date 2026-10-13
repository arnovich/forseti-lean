import Gimle.Forseti.Fourier
import Gimle.Asgard.Streams.EulerRadius
import Gimle.Asgard.Streams.EulerSolution
import Gimle.Asgard.Streams.VorticityTable

/-! Classical Euler properties of Asgard's Fourier feedback circuit.

Only the initial slice is admitted. The formal circuit has a unique output;
its real field is a classical solution on the explicitly certified interval.
This does not assert uniqueness among arbitrary classical fields or a maximal
existence interval. Certificate constants are premises, never part of admission.
-/
namespace Gimle.Forseti.Euler

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.TrigStream

/-- Properties of the actual output on a caller-specified closed interval. -/
structure Certified (boundary : TrigStream) (radius : ℝ)
    (output : Gimle.Asgard.Streams.Fourier.Point 1) : Prop where
  /-- Equality of whole formal streams, not only a finite window. -/
  formal_eq : output 0 = NS.stream .ogf 0 boundary
  /-- The spatial mean vanishes at every formal degree. -/
  mean_zero : ∀ n, MeanZero (output 0 n)
  /-- Real cosine symmetry holds at every formal degree. -/
  even : ∀ n, IsEven (output 0 n)
  /-- The evaluated initial field is the declared initial field. -/
  initial : ∀ x, analyticField (output 0) 0 x = field (boundary 0) x
  /-- The field is a convergent series throughout the requested interval. -/
  converges : ∀ t x, |t| ≤ radius →
    HasSum (seriesTerm (output 0) t x) (analyticField (output 0) t x)
  /-- All derivatives, continuity and the Euler PDE hold, including endpoints. -/
  classical : ∀ t x, |t| ≤ radius → NS.IsClassicalSolution (output 0) t x

/-- The closed requested interval lies strictly inside the proved open disc. -/
theorem inside_radius {ρ r t : ℝ} (hρ : 0 < ρ) (hr : ρ * r < 1)
    (ht : |t| ≤ r) : |t| < 1 / ρ := by
  apply (lt_div_iff₀ hρ).mpr
  calc |t| * ρ ≤ r * ρ := mul_le_mul_of_nonneg_right ht hρ.le
    _ < 1 := by simpa [mul_comm] using hr

/-- Semantic realization, with all analytical hypotheses explicit. -/
theorem certified (b : TrigStream) (hz : MeanZero (b 0)) (he : IsEven (b 0))
    {K : ℕ} (hs : SizeLE K (b 0)) {M ρ r : ℝ}
    (hg : GeometricBound (NS.stream .ogf 0 b) M ρ)
    (hp : 0 < ρ) (hq : ρ * r < 1) : Certified b r ![NS.stream .ogf 0 b] where
  formal_eq := rfl
  mean_zero := NS.stream_meanZero .ogf 0 hz
  even := NS.stream_isEven .ogf 0 he
  initial := NS.analyticField_zero b
  converges := fun _ _ ht => hasSum_analyticField hg hp.le hq ht
  classical := fun _ x ht => NS.euler_classical b hz he hs hg hp (inside_radius hp hq ht) x

/-- A total contract: every admitted boundary produces the certified output. -/
theorem contract (b : TrigStream) (hz : MeanZero (b 0)) (he : IsEven (b 0))
    {K : ℕ} (hs : SizeLE K (b 0)) {M ρ r : ℝ}
    (hg : GeometricBound (NS.stream .ogf 0 b) M ρ)
    (hp : 0 < ρ) (_hr : 0 ≤ r) (hq : ρ * r < 1) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = b 0) (Certified b r) := by
  apply (Fourier.solution_contract .ogf 0 b).consequence (fun _ h => h)
  intro output h
  subst output
  exact certified b hz he hs hg hp hq

/-- Conjoin a requested bound without weakening the classical output guarantee. -/
theorem contract_with (b : TrigStream) {r : ℝ}
    (h : Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = b 0) (Certified b r))
    (post : Fourier.Predicate 1) (hp : post ![NS.stream .ogf 0 b]) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = b 0) (fun output => Certified b r output ∧ post output) := by
  apply h.consequence (fun _ h => h)
  intro output hc
  refine ⟨hc, ?_⟩
  have same : output = ![NS.stream .ogf 0 b] := by
    funext i
    fin_cases i
    exact hc.formal_eq
  rwa [same]

/-- Zero initial data have a zero norm bound at any chosen positive growth rate. -/
theorem zero_geometric (b : TrigStream) (hz : b 0 = 0) (ρ : ℝ) :
    GeometricBound (NS.stream .ogf 0 b) 0 ρ := by
  have hs : SizeLE 1 (b 0) := by rw [hz]; exact sizeLE_zero 1
  have hl : l1 (b 0) ≤ (0 : ℚ) := by simp [hz, l1]
  have h := NS.euler_geometricBound b (by decide : 1 ≤ (1 : ℕ)) hs hl
  intro n
  simpa using h n

/-- Zero data are covered at every finite radius, without a zero divisor. -/
theorem zero_contract (b : TrigStream) (hz : b 0 = 0) {r : ℝ} (hr : 0 ≤ r) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = b 0) (Certified b r) := by
  have hs : SizeLE 1 (b 0) := by rw [hz]; exact sizeLE_zero 1
  have hp : 0 < 1 / (r + 1) := by positivity
  apply contract b (by simp [hz, MeanZero]) (by simp [hz, IsEven]) hs
    (zero_geometric b hz (1 / (r + 1))) hp hr
  rw [one_div_mul_eq_div]
  exact (div_lt_one (by positivity)).mpr (by linarith)

namespace Table

/-- The zero Fourier coefficient, after summing duplicate entries, vanishes. -/
def ZeroMean (table : Torus.Table) : Prop := Torus.Table.coeff 0 table = 0

instance (table : Torus.Table) : Decidable (ZeroMean table) := inferInstanceAs
  (Decidable (Torus.Table.coeff 0 table = 0))

/-- A finite symmetry certificate, checking every listed mode and its reflection. -/
def Symmetric (table : Torus.Table) : Prop :=
  ∀ e ∈ table, Torus.Table.coeff (-e.1) table = Torus.Table.coeff e.1 table

instance (table : Torus.Table) : Decidable (Symmetric table) := by
  unfold Symmetric
  infer_instance

/-- Absence from the table implies a zero aggregate coefficient. -/
theorem coeff_zero_of_absent (table : Torus.Table) (k : Wave)
    (h : ∀ e ∈ table, e.1 ≠ k) : Torus.Table.coeff k table = 0 := by
  induction table with
  | nil => rfl
  | cons e tail ih =>
    rw [Torus.Table.coeff, if_neg (h e List.mem_cons_self), zero_add]
    exact ih (fun f hf => h f (List.mem_cons_of_mem _ hf))

/-- The finite zero-mean certificate implies semantic zero mean. -/
theorem meanZero {table : Torus.Table} (h : ZeroMean table) :
    MeanZero (Torus.Table.toTrig table) := by
  exact (Torus.Table.toTrig_apply table 0).trans h

/-- The finite symmetry certificate controls every Fourier mode, listed or not. -/
theorem isEven {table : Torus.Table} (h : Symmetric table) :
    IsEven (Torus.Table.toTrig table) := by
  intro k
  simp only [Torus.Table.toTrig_apply]
  by_cases hk : ∃ e ∈ table, e.1 = k
  · obtain ⟨e, he, rfl⟩ := hk
    exact h e he
  · have zero_k : Torus.Table.coeff k table = 0 :=
      coeff_zero_of_absent table k (fun e he eq => hk ⟨e, he, eq⟩)
    by_cases hn : ∃ e ∈ table, e.1 = -k
    · obtain ⟨e, he, eq⟩ := hn
      have cert := h e he
      rw [eq, neg_neg] at cert
      exact cert.symm
    · rw [zero_k, coeff_zero_of_absent table (-k) (fun e he eq => hn ⟨e, he, eq⟩)]

/-- Every aggregate coefficient represented by the table vanishes. -/
def IsZero (table : Torus.Table) : Prop :=
  ∀ e ∈ table, Torus.Table.coeff e.1 table = 0

instance (table : Torus.Table) : Decidable (IsZero table) := by
  unfold IsZero
  infer_instance

/-- A zero-table certificate denotes the zero polynomial, even with cancellation. -/
theorem toTrig_zero {table : Torus.Table} (h : IsZero table) :
    Torus.Table.toTrig table = 0 := by
  ext k
  rw [Torus.Table.toTrig_apply, Finsupp.zero_apply]
  by_cases hk : ∃ e ∈ table, e.1 = k
  · obtain ⟨e, he, rfl⟩ := hk
    exact h e he
  · exact coeff_zero_of_absent table k (fun e he eq => hk ⟨e, he, eq⟩)

/-- Finite certificates instantiate the semantic circuit contract. -/
theorem contract (table : Torus.Table) (hz : ZeroMean table) (he : Symmetric table)
    {K : ℕ} (hK : 1 ≤ K) (hs : ∀ e ∈ table, size e.1 ≤ K)
    {L : ℚ} (hL : Torus.Table.absSum table ≤ L) {r : ℝ} (hr : 0 ≤ r)
    (hp : 0 < (72 : ℝ) * L * K) (hq : (72 : ℝ) * L * K * r < 1) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Torus.Table.toTrig table)
      (Certified (fun _ => Torus.Table.toTrig table) r) :=
  Euler.contract (fun _ => Torus.Table.toTrig table) (meanZero hz) (isEven he) (Torus.Table.sizeLE_toTrig hs)
    (NS.euler_geometricBound (fun _ => Torus.Table.toTrig table) hK (Torus.Table.sizeLE_toTrig hs)
      ((Torus.Table.l1_le_absSum table).trans hL)) hp hr hq

/-- Semantic cancellation gives a classical circuit contract at every finite radius. -/
theorem zero_contract (table : Torus.Table) (hz : IsZero table) {r : ℝ} (hr : 0 ≤ r) :
    Fourier.Contract (NS.vorticityCircuit .ogf 0)
      (fun input => input 0 0 = Torus.Table.toTrig table)
      (Certified (fun _ => Torus.Table.toTrig table) r) :=
  Euler.zero_contract (fun _ => Torus.Table.toTrig table) (toTrig_zero hz) hr

end Table

#print axioms contract
#print axioms zero_contract
#print axioms Table.isEven

end Gimle.Forseti.Euler
