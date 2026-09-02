/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller.InfoTree
import Informalization.Semantics.CBC
import Informalization.Semantics.Plan
import Informalization.Semantics.Registry

/-!
# Genuine CBC source gate

This test elaborates `CBCMAC/Main.lean` in its owning downstream project. It
validates the executable CBC profile against the live
declaration telescopes, decodes the theorem statement, and checks that the
registered mathematical spine is recovered from the checked proof.

By default the project is the sibling `cbc-mac-cc` checkout; the
`INFORMALIZATION_CBC_ROOT` environment variable may override that path. A
source that no longer matches the profile fails closed with an invalid-selector
or missing-declaration error.
-/

namespace Tests.CBCExternal

open Lean Meta
open Informalization.MassotMiller.InfoTree
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.Plan

def assertIO (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def projectRoot : IO System.FilePath := do
  if let some configured ← IO.getEnv "INFORMALIZATION_CBC_ROOT" then
    let path : System.FilePath := configured
    if ← (path / "CBCMAC" / "Main.lean").pathExists then
      return path
    throw (IO.userError
      "INFORMALIZATION_CBC_ROOT does not contain CBCMAC/Main.lean")
  let path : System.FilePath := "../../cbc-mac-cc"
  if ← (path / "CBCMAC" / "Main.lean").pathExists then return path
  throw (IO.userError "the sibling cbc-mac-cc/CBCMAC/Main.lean was not found")

def lakeSetupFor (lakeRoot path : System.FilePath) : IO ModuleSetup := do
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["setup-file", path.toString]
    cwd := some lakeRoot
  }
  unless output.exitCode == 0 do
    throw (IO.userError s!"lake setup-file failed:\n{output.stderr}")
  match Json.parse output.stdout >>= fromJson? with
  | .ok setup => return setup
  | .error message =>
      throw (IO.userError s!"could not parse Lake module setup: {message}")

def requiredProofRoles : Array ProofRuleRole := #[
  .collisionConditionalEquivalence,
  .conditionalEquivalenceUnderRestriction,
  .blindWinningBound,
  .commonDomainDataProcessing,
  .restrictionApplicationEquation,
  .ignoreGameMBO,
  .conditionalEquivalenceToBlindWinning,
  .blindWinningToNonadaptive,
  .collisionMassBound
]

/-- Validate the frontend against the actual downstream CBC distance theorem. -/
unsafe def check : IO Unit := do
  initSearchPath (← findSysroot)
  let root ← projectRoot
  let source := root / "CBCMAC" / "Main.lean"
  let setup ← lakeSetupFor root ("CBCMAC/Main.lean" : System.FilePath)
  let some module ← elaborateFile source `CBCSemanticSourceFixture (some setup) #[]
    | throw (IO.userError "could not elaborate the genuine CBC source")
  let declaration := `CBCMAC.cbc_randomness_expander
  let catalog := Informalization.Semantics.CBC.catalog
  let visibleCatalog := catalog.filter fun entry =>
    (module.environment.find? entry.declaration).isSome
  let issues := Registry.validateCatalog module.environment visibleCatalog
  assertIO issues.isEmpty
    s!"CBC semantic catalog does not match the live source: {repr issues}"
  let some context := module.contextFor declaration
    | throw (IO.userError "missing elaboration context for the CBC theorem")
  context.runMetaM {} do
    let information ← getConstInfo declaration
    forallTelescope information.type fun _ conclusion => do
      let some claim ← Canonical.decodeClaim?
          Informalization.Semantics.CBC.profile conclusion
        | throwError "the genuine CBC theorem has no canonical claim"
      match claim with
      | .distanceBound .. => pure ()
      | _ => throwError "the genuine CBC theorem is not a distance bound"

    let some plan ← Plan.fromDeclarationWithProfile? module.environment catalog
        Informalization.Semantics.CBC.profile declaration
      | throwError "the genuine CBC theorem has no checked proof plan"
    let roles := plan.steps.map (·.application.role)
    unless requiredProofRoles.all roles.contains do
      throwError "CBC semantic support is incomplete: {repr roles}"

end Tests.CBCExternal
