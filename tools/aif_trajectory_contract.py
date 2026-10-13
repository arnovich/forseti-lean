#!/usr/bin/env python3
"""Emit typed, well-posed AIF trajectory contracts and hostile regressions."""

from __future__ import annotations

import argparse
from pathlib import Path


def generate() -> dict[str, str]:
    """Generate research contracts; only successful Lean replay grants authority."""
    source = """import Gimle.Forseti.Examples.AIFUniformPrefix
import Gimle.Forseti.Trajectory

/-! Typed contracts for the original compiled feedback followed by its output.
Startup safety is discharged. Larger-horizon contracts retain both complete
certificate families explicitly until all cells have been supplied. -/
namespace Gimle.Forseti.Examples.AIFTrajectoryContract
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory

/-- The original compiled feedback followed by the original x2 observer. -/
def observed : Dynamics.Circuit 5 1 :=
  .compose Gimle.Asgard.Examples.AIF.feedback (.lift Gimle.Asgard.Examples.AIF.output)

/-- Eta is fixed as a driver; only the initial-wire value at time zero is read. -/
def admitted (eta : ℝ) : SignalPredicate 5 :=
  Initialized Gimle.Asgard.Examples.AIF.time
    (fun driver => driver = Gimle.Asgard.Examples.AIF.drivers eta)
    (fun initial => initial = (0 : Point 4))

theorem feedback_reads (eta : ℝ) (input : Signal 5) (hi : admitted eta input)
    (state : Signal 4) :
    Gimle.Asgard.Examples.AIF.feedback.Rel Gimle.Asgard.Examples.AIF.time input state ↔
      Gimle.Asgard.Examples.AIF.Realizes eta state := by
  rw [Gimle.Asgard.Examples.AIF.feedback, close_rel_reads_start, hi.1, hi.2]
  rfl

theorem declared_input_admitted (eta : ℝ) : admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun _ => (0 : Point 4))) := by
  constructor <;> simp [signalLeft_append, signalRight_append]

theorem observed_rel (input : Signal 5) (output : Signal 1) :
    observed.Rel Gimle.Asgard.Examples.AIF.time input output ↔
      ∃ state, Gimle.Asgard.Examples.AIF.feedback.Rel
        Gimle.Asgard.Examples.AIF.time input state ∧
        output = fun t => Gimle.Asgard.Examples.AIF.output.run (state t) := Iff.rfl

/-- Lift a bound on every realization into the existing total typed contract. -/
theorem contract_of_realizations (eta : ℝ) (heta : 0 ≤ eta)
    (post : SignalPredicate 1)
    (safe : ∀ state, Gimle.Asgard.Examples.AIF.Realizes eta state →
      post (fun t => Gimle.Asgard.Examples.AIF.output.run (state t))) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta) post where
  realizable input hi := by
    obtain ⟨state, realized⟩ := AIFCircuitSolution.exists_realization eta heta
    refine ⟨fun t => Gimle.Asgard.Examples.AIF.output.run (state t), ?_⟩
    exact (observed_rel input _).mpr ⟨state, (feedback_reads eta input hi state).mpr realized, rfl⟩
  unique input hi first second hfirst hsecond := by
    obtain ⟨x, hx, rfl⟩ := (observed_rel input first).mp hfirst
    obtain ⟨y, hy, rfl⟩ := (observed_rel input second).mp hsecond
    have same := AIFCircuitSolution.realization_unique eta heta x y
      ((feedback_reads eta input hi x).mp hx) ((feedback_reads eta input hi y).mp hy)
    intro t ht
    exact congrArg Gimle.Asgard.Examples.AIF.output.run (same ht)
  holds input hi output related := by
    obtain ⟨state, hs, rfl⟩ := (observed_rel input output).mp related
    exact safe state ((feedback_reads eta input hi state).mp hs)

/-- No missing-certificate or trajectory assumptions remain on this prefix. -/
theorem startup_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ output t 0 ∧ output t 0 ≤ 16/5) := by
  apply contract_of_realizations eta (by linarith [hp.1])
  exact (AIFUniformPrefix.all_parameter_safety eta hp).2

/-- Conditional all-forward contract: both full-mesh families are still premises. -/
theorem forward_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (output : ∀ b i, AIFSafetyComposition.CellOutput b i) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta)
      (Always Gimle.Asgard.Examples.AIF.time fun y => 0 ≤ y 0 ∧ y 0 ≤ 16/5) := by
  apply contract_of_realizations eta (by linarith [hp.1])
  exact (AIFSafetyComposition.forward_safety_of_certificates drift output eta hp).2

/-- The requested time-100 contract; still conditional on full certificate coverage. -/
theorem hundred_contract (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12)
    (drift : ∀ b i, AIFStartupPrefix.CellDrift b i)
    (output : ∀ b i, AIFSafetyComposition.CellOutput b i) :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted eta)
      (fun y => ∀ t ∈ Set.Icc (0 : ℝ) 100, 0 ≤ y t 0 ∧ y t 0 ≤ 16/5) := by
  apply (forward_contract eta hp drift output).consequence (fun _ h => h)
  intro y hy t ht
  exact hy t ht.1

#print axioms feedback_reads
#print axioms declared_input_admitted
#print axioms observed_rel
#print axioms contract_of_realizations
#print axioms startup_contract
#print axioms forward_contract
#print axioms hundred_contract
end Gimle.Forseti.Examples.AIFTrajectoryContract
"""
    regressions = """import Gimle.Forseti.Examples.AIFTrajectoryContract

/-! Hostile and boundary regressions for the typed AIF input contract. -/
namespace Gimle.Forseti.Examples.AIFTrajectoryContractRegressions
open Gimle.Asgard Gimle.Asgard.Dynamics Gimle.Forseti.Trajectory
open AIFTrajectoryContract

theorem changed_initial_rejected (eta : ℝ) : ¬ admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta)
      (fun _ => (![1,0,0,0] : Point 4))) := by
  intro h
  have wrong := congrFun h.2 0
  norm_num [signalRight_append] at wrong

theorem varying_eta_rejected (eta : ℝ) : ¬ admitted eta
    (signalAppend (fun t => (![eta+t] : Point 1)) (fun _ => (0 : Point 4))) := by
  intro h
  have wrong := congrFun (congrFun h.1 1) 0
  norm_num [signalLeft_append, Gimle.Asgard.Examples.AIF.drivers] at wrong

theorem initial_wires_read_only_at_start (eta : ℝ) : admitted eta
    (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta)
      (fun t => (![t,t,t,t] : Point 4))) := by
  constructor
  · simp [signalLeft_append]
  · ext i
    fin_cases i <;> simp [signalRight_append, Gimle.Asgard.Examples.AIF.time]

theorem lower_endpoint_contract :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted 8)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ output t 0 ∧ output t 0 ≤ 16/5) :=
  startup_contract 8 (by norm_num)

theorem upper_endpoint_contract :
    Contract observed Gimle.Asgard.Examples.AIF.time (admitted 12)
      (fun output => ∀ t ∈ Set.Icc (0 : ℝ) (21/200),
        0 ≤ output t 0 ∧ output t 0 ≤ 16/5) :=
  startup_contract 12 (by norm_num)

/-- The admitted-input predicate has a witness with an actual safe observed behavior. -/
theorem safe_behavior_exists (eta : ℝ) (hp : eta ∈ Set.Icc (8 : ℝ) 12) :
    ∃ output, observed.Rel Gimle.Asgard.Examples.AIF.time
      (signalAppend (Gimle.Asgard.Examples.AIF.drivers eta) (fun _ => (0 : Point 4))) output ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (21/200), 0 ≤ output t 0 ∧ output t 0 ≤ 16/5 :=
  (startup_contract eta hp).exists_safe _ (declared_input_admitted eta)

#print axioms changed_initial_rejected
#print axioms varying_eta_rejected
#print axioms initial_wires_read_only_at_start
#print axioms lower_endpoint_contract
#print axioms upper_endpoint_contract
#print axioms safe_behavior_exists
end Gimle.Forseti.Examples.AIFTrajectoryContractRegressions
"""
    return {
        "AIFTrajectoryContract.lean": source,
        "AIFTrajectoryContractRegressions.lean": regressions,
    }


def main() -> None:
    """Write proposed proof modules or check exact bytes without mutation."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.check:
        args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, source in generate().items():
        path = args.output_directory / name
        if args.check:
            if not path.is_file() or path.read_bytes() != source.encode():
                raise SystemExit(f"generated {name} differs")
        else:
            path.write_bytes(source.encode())


if __name__ == "__main__":
    main()
