import Lean.Replay
import Lean.Data.Json.Printer

open Lean

/- The checker never runs candidate source, initializers, or environment extensions.
   Candidate object files are produced locally in a separate restricted process. -/

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

unsafe def readEnv (name : Name) : IO Environment :=
  importModules #[{ module := name }] {} (trustLevel := 0) (loadExts := false) (level := .private)

partial def auditAxioms (env : Environment) (pending : List Name)
    (seen : NameSet := {}) (axioms : NameSet := {}) : IO NameSet := do
  match pending with
  | [] => pure axioms
  | name :: rest =>
    if seen.contains name then return ← auditAxioms env rest seen axioms
    let some info := env.toKernelEnv.find? name | throw (IO.userError s!"missing constant {name}")
    require (!info.isUnsafe && !info.isPartial) s!"unsafe dependency {name}"
    let axioms := match info with
      | .axiomInfo _ => axioms.insert name
      | _ => axioms
    auditAxioms env (info.getUsedConstantsAsSet.toArray.toList ++ rest) (seen.insert name) axioms

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [imports, core, expectedPath, candidatePath, rootName] := args
      | throw (IO.userError "invalid checker arguments")
    -- Avoid initSearchPath: it includes ambient LEAN_PATH.
    searchPathRef.set [⟨imports⟩, ⟨core⟩, ⟨expectedPath⟩, ⟨candidatePath⟩]
    let expected ← readEnv `Expected
    -- Expected is independently generated with only the support import. Reuse
    -- its closure instead of loading a third copy of the support environment.
    let some expectedIndex := expected.header.moduleNames.findIdx? (· == `Expected)
      | throw (IO.userError "missing independent expected module")
    for item in expected.header.moduleData[expectedIndex]!.imports do
      require (item.module == `Gimle.Forseti || item.module == `Init)
        s!"unexpected independent statement import {item.module}"
    let raw ← readEnv `Candidate
    for name in raw.header.moduleNames do
      require (name == `Candidate ||
        (name != `Expected && expected.header.moduleNames.contains name))
        s!"undeclared import {name}"
    let some index := raw.header.moduleNames.findIdx? (· == `Candidate)
      | throw (IO.userError "missing candidate module")
    let data := raw.header.moduleData[index]!
    for item in data.imports do
      require (item.module == `Gimle.Forseti || item.module == `Init)
        s!"undeclared direct import {item.module}"
    require (data.constants.size <= 10000) "candidate declaration limit"
    let mut owned : Std.HashMap Name ConstantInfo := {}
    for info in data.constants do
      let name := info.name
      require ((expected.toKernelEnv.find? name).isNone && !owned.contains name)
        s!"shadowed declaration {name}"
      require (!info.isUnsafe && !info.isPartial) s!"unsafe candidate declaration {name}"
      match info with
      | .defnInfo value => require (value.safety == .safe) s!"partial definition {name}"
      | _ => pure ()
      owned := owned.insert name info
    let root := rootName.toName
    require (owned.contains root) "root is not owned by the candidate"
    let checked ← expected.replay owned
    let some (.thmInfo proofInfo) := checked.toKernelEnv.find? root
      | throw (IO.userError "root must be a theorem")
    require proofInfo.levelParams.isEmpty "polymorphic root is unsupported"
    let some (.defnInfo statement) := checked.toKernelEnv.find? `forsetiExpected
      | throw (IO.userError "missing independent expected statement")
    match Kernel.check checked {} proofInfo.value with
    | .error _ => throw (IO.userError "invalid root proof")
    | .ok inferred =>
      match Kernel.isDefEq checked {} inferred proofInfo.type with
      | .ok equal => require equal "proof and theorem type differ"
      | .error _ => throw (IO.userError "invalid inferred proof type")
    match Kernel.isDefEq checked {} proofInfo.type statement.value with
    | .error _ => throw (IO.userError "kernel type check failed")
    | .ok equal => require equal "candidate theorem differs from original obligation"
    let axioms ← auditAxioms checked [root, `forsetiExpected]
    for name in axioms.toArray do
      require ([`Classical.choice, `Quot.sound, `propext].contains name)
        s!"forbidden transitive axiom {name}"
    let names := axioms.toArray.toList.map Name.toString |>.mergeSort (· ≤ ·)
    IO.println (Json.compress (Json.arr (names.toArray.map Json.str)))
    return 0
  catch error =>
    IO.eprintln error.toString
    return 1
