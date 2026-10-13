import Gimle.Forseti.MildVorticity
import Gimle.Asgard.Examples.MildBand

/-! Total mild circuit contracts bind every guarantee to the admitted initial
slice and actual whole output, including both numerical certificate routes. -/
namespace Gimle.Forseti.Tests.MildVorticity
open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus
open Gimle.Asgard.Streams.Mild Gimle.Forseti

/-- A different finite start from the three-mode example. -/
def table : Torus.Table :=
  [((1, 0), 1 / 2), ((-1, 0), 1 / 2), ((0, 2), 1 / 4), ((0, -2), 1 / 4)]

noncomputable def P : TrigPoly := Torus.Table.toTrig table

/-- Both bounds prove exactly the same postcondition, over the same circuit. -/
theorem euler : Mild.Contract (mildCircuit (1 / 10)) (fun input => input 0 0 = embed P)
    (MildVorticity.Certified (1 / 10) P (1 / 2160)) :=
  MildVorticity.Table.euler_contract table (by decide +kernel) (by decide +kernel)
    (by norm_num) (K := 2) (by decide) (by decide) (L := 3 / 2) (by decide +kernel)
    (by norm_num) (by norm_num)

theorem catalan : Mild.Contract (mildCircuit (1 / 10)) (fun input => input 0 0 = embed P)
    (MildVorticity.Certified (1 / 10) P (1 / 2160)) :=
  MildVorticity.Table.catalan_contract table (by decide +kernel) (by decide +kernel)
    (r := 1 / 12) (by norm_num) (K := 2) (by decide) (L := 3 / 2) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

noncomputable def noisy : Gimle.Asgard.Streams.Mild.Stream :=
  fun n => if n = 0 then embed P else embed (Finsupp.single 0 1)

-- Higher boundary data do not prevent realization or change the output.
example : ∃ output, (mildCircuit (1 / 10)).Rel ![noisy] output ∧
    MildVorticity.Certified (1 / 10) P (1 / 2160) output := euler.exists_safe _ rfl

-- A nonexistent safe output cannot make a contract true.
example : ¬ Mild.Contract (mildCircuit (1 / 10))
    (fun input => input 0 0 = embed P) (fun _ => False) := by
  intro h
  obtain ⟨_, _, hf⟩ := h.exists_safe ![MildVorticity.boundary P] rfl
  exact hf

-- Replacing feedback by an identity wire cannot preserve the guarantee.
example : ¬ Mild.Contract (Gimle.Asgard.Streams.Mild.Circuit.route (ν := 1 / 10) (n := 1) id)
    (fun input => input 0 0 = embed P) (MildVorticity.Certified (1 / 10) P (1 / 2160)) := by
  intro h
  have hc := h.holds ![noisy] rfl ![noisy] rfl
  have hm := hc.mean_zero 1
  have he := congrArg (ExpPoly.eval (1 / 10) 0) hm
  norm_num [noisy, Gimle.Asgard.Streams.Mild.MeanZero, embed] at he

-- A different initial slice cannot acquire this postcondition.
example : ¬ ∃ output, (mildCircuit (1 / 10)).Rel ![fun _ => embed 0] output ∧
    MildVorticity.Certified (1 / 10) P (1 / 2160) output := by
  rintro ⟨output, related, hc⟩
  have ho := (mildCircuit_rel_iff _ _ _).mp related
  have hh := congrArg (fun s => eval (1 / 10) 0 (s 0) (1, 0)) hc.formal_eq
  rw [ho] at hh
  simp only [Matrix.cons_val_zero, wild_initial (1 / 10) (fun _ => embed 0) 0 rfl,
    wild_initial (1 / 10) (MildVorticity.boundary P) P rfl, ite_true] at hh
  norm_num [realEmbed, P, table, Torus.Table.toTrig_apply, Torus.Table.coeff] at hh

-- Admissible finite-table certificates exclude asymmetric or nonzero-mean data.
example : ¬ Euler.Table.Symmetric [((1, 0), 1)] := by decide +kernel
example : ¬ Euler.Table.ZeroMean [((0, 0), 1)] := by decide +kernel

-- Exact cancellation, including the mean mode, supports arbitrarily large times
-- through the zero-data constructor. ν=0 is also covered.
example : Mild.Contract (mildCircuit 0)
    (fun input => input 0 0 = embed (Torus.Table.toTrig
      [((0, 0), 1), ((0, 0), -1), ((2, 1), 3), ((2, 1), -3)]))
    (MildVorticity.Certified 0 (Torus.Table.toTrig
      [((0, 0), 1), ((0, 0), -1), ((2, 1), 3), ((2, 1), -3)]) 1000000) :=
  MildVorticity.Table.zero_contract _ (by decide +kernel) le_rfl (by norm_num)

-- A numerical band remains conjoined with convergence, PDE and dissipation.
example : Mild.Contract (mildCircuit (1 / 10))
    (fun input => input 0 0 = embed Gimle.Asgard.Examples.EulerThreeMode.ω₀)
    (fun output => MildVorticity.Certified (1 / 10) Gimle.Asgard.Examples.EulerThreeMode.ω₀ (1 / 5760) output ∧
      MildBandBound (1 / 10) (output 0) (1 / 5760) (3519 / 1000)) := by
  have hg := wild_geometric (ν := 1 / 10) (r := 1 / 24) (T := 1 / 5760)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (MildVorticity.boundary Gimle.Asgard.Examples.EulerThreeMode.ω₀) Gimle.Asgard.Examples.EulerThreeMode.ω₀ rfl Gimle.Asgard.Examples.EulerBand.start_l1
  apply MildVorticity.contract_with _ (MildVorticity.contract (by norm_num) _
    Gimle.Asgard.Examples.EulerThreeMode.ω₀_meanZero Gimle.Asgard.Examples.EulerThreeMode.ω₀_isEven Gimle.Asgard.Examples.EulerBand.start_sizeLE
    (by norm_num) hg (by norm_num) (by norm_num))
  exact Gimle.Asgard.Examples.MildBand.band

-- Truncation also preserves the entire certified postcondition.
example : Mild.Contract (mildCircuit (1 / 10)) (fun input => input 0 0 = embed P)
    (fun output => MildVorticity.Certified (1 / 10) P (1 / 2160) output ∧
      MildTruncationBound (1 / 10) (output 0) (1 / 2160) 3 (1 / 200)) := by
  apply MildVorticity.contract_with P euler
  have h := wild_euler_truncation (ν := 1 / 10) (T := 1 / 2160)
    (by norm_num) (by norm_num) (MildVorticity.boundary P) P rfl
    (K := 2) (by decide) (Torus.Table.sizeLE_toTrig (by decide : ∀ e ∈ table, size e.1 ≤ 2))
    (L := 3 / 2) ((Torus.Table.l1_le_absSum table).trans (by decide +kernel)) (by norm_num) 3
  norm_num [eulerTail] at h
  exact h

example : Mild.Contract (mildCircuit 0) (fun input => input 0 0 = embed (Torus.Table.toTrig []))
    (MildVorticity.Certified 0 (Torus.Table.toTrig []) 0) :=
  MildVorticity.Table.zero_contract [] (by decide) le_rfl le_rfl
example : ¬ (0 : ℝ) ≤ -1 := by norm_num
example : ¬ (4 * (1 / 6 : ℚ) * (3 / 2) < 1) := by norm_num

-- The total postcondition exposes closed-endpoint energy control directly.
example (output : Gimle.Asgard.Streams.Mild.Point 1)
    (hc : MildVorticity.Certified (1 / 10) P (1 / 2160) output) :
    energy (fourierCoeff (1 / 10) (output 0) (1 / 2160)) ≤
      energy (fourierCoeff (1 / 10) (output 0) 0) :=
  hc.dissipation.energy_le_initial ⟨by norm_num, le_rfl⟩

#print axioms MildVorticity.contract
#print axioms MildVorticity.Table.zero_contract
end Gimle.Forseti.Tests.MildVorticity
