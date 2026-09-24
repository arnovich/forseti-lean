import Gimle.Forseti.Examples.EquationWorkflow
import Gimle.Asgard.Simulation.Client
import Gimle.Asgard.Simulation.EquationRequests

/-! Explicit execution of the circuits used in EquationWorkflow's theorems.
Building or opening the proof module never starts a Python process. -/
open Gimle.Asgard Gimle.Asgard.Simulation Lean

/-- Display data for the exact model; not a trusted interchange or proof certificate. -/
private def exactModel {n : Nat} (p : Dynamics.Linear.RationalProblem n) : Json :=
  Json.mkObj [
    ("schema", .str "asgard.linear-ode-diagram/v1"),
    ("axis", .str p.axis), ("start", .str (toString p.start)),
    ("states", .arr (List.ofFn (fun i => Json.mkObj [
      ("name", .str (p.names i)), ("initial", .str (toString (p.initial i)))])).toArray),
    ("matrix", .arr (List.ofFn (fun i => Json.arr
      (List.ofFn (fun j => Json.str (toString (p.matrix i j)))).toArray)).toArray)]

/-- Retain the owned request and lossless observations; this JSON is not a proof. -/
private def record {n m : Nat} (request : Request n m) (observation : Observation request) :
    IO Json := do
  let .ok original := request.toJson | throw (IO.userError "invalid original request")
  return Json.mkObj [
    ("request", original), ("trajectory", encodeRows observation.trajectory),
    ("times", match observation.times with
      | none => Json.null
      | some times => toJson (times.map encodeFloat)),
    ("provenance", observation.provenance), ("diagnostics", observation.diagnostics)]

def main (args : List String) : IO UInt32 := do
  let [python] := args | throw (IO.userError "Usage: equation_demo /absolute/venv/bin/python")
  let cancel ← IO.mkRef false
  let energy ← run EquationRequests.energy {python := python} cancel
  let oscillator ← run EquationRequests.oscillator {python := python} cancel
  let rhs ← run EquationRequests.oscillatorPoint {python := python} cancel
  let step ← run EquationRequests.oscillatorStep {python := python} cancel
  let energyJson ← record EquationRequests.energy energy
  let oscillatorJson ← record EquationRequests.oscillator oscillator
  let rhsJson ← record EquationRequests.oscillatorPoint rhs
  let stepJson ← record EquationRequests.oscillatorStep step
  IO.println (Json.mkObj ([
    ("schema", toJson "asgard.equation-workflow-observations/v1"),
    ("authority", toJson "none"),
    ("exactModel", exactModel Examples.EquationModels.model),
    ("energy", energyJson), ("oscillator", oscillatorJson),
    ("oscillatorRhs", rhsJson), ("oscillatorStep", stepJson)])).compress
  return 0
