import Lean

/-!
# Axiom audit of every declaration

Imports the modules named on the command line and checks that every declaration they define
depends on no axiom other than `propext`, `Classical.choice` and `Quot.sound`. `sorry`
(`sorryAx`), native evaluation (`Lean.ofReduceBool`, `Lean.trustCompiler` and the auxiliary
axioms of `native_decide`) and declared axioms all show up here, however they are written.
Run by `scripts/check-axioms.sh`.
-/

open Lean

/-- The accepted axioms. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Components whose declarations may use `sorryAx`. Each is a DSL diagnostic that checks an
elaboration error with `#guard_msgs`; after the error Lean still adds the generated
declarations, with `sorryAx` in place of the part that failed. -/
def mayUseSorry : List Name :=
  [`DSLTests.Diagnostics.Infinite, `DSLTests.Diagnostics.Growing,
    `DSLTests.Diagnostics.Uninitialized, `DSLTests.Diagnostics.WrongReply]

/-- Whether declaration `c` may depend on axiom `a`. -/
def accepted (c a : Name) : Bool :=
  allowed.contains a || (a == ``sorryAx && mayUseSorry.any (·.isPrefixOf c))

unsafe def main (args : List String) : IO UInt32 := do
  let modules := args.toArray.map String.toName
  if modules.isEmpty then
    IO.eprintln "error: no modules to audit"
    return 1
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let audited : NameSet := modules.foldl (·.insert ·) {}
  -- The declarations defined in the audited modules, not in their imports.
  let ours (c : Name) : Bool :=
    match env.getModuleIdxFor? c with
    | some idx => audited.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let names := env.constants.fold (init := #[]) fun acc c _ => if ours c then acc.push c else acc
  let ctx : Core.Context := { fileName := "<axiom audit>", fileMap := default }
  let (bad, _) ← (names.filterMapM fun c => do
      let axs ← collectAxioms c
      let outside := axs.filter fun a => !accepted c a
      return if outside.isEmpty then none else some (c, outside)
    : CoreM _).toIO ctx { env }
  for (c, axs) in bad do
    IO.println s!"error: {c} depends on {axs.toList}"
  IO.println s!"axioms: {names.size} declarations in {modules.size} modules, \
    {bad.size} outside the envelope"
  return if bad.isEmpty then 0 else 1
