import Tests.Rendering.Automatic
import Tests.Rendering.Proofs

/-! Real info-tree tests cover proof cursor activation and elaborated calculation justifications. -/

open Lean Elab CCWidget ProofWidgets

namespace Rendering.ProofAutomaticTests

/-- The marker selects a real calculation statement after complete frontend elaboration. -/
def calculation := "open CategoryTheory ConstructiveCryptography
open ConstructiveCryptography.CryptographicAlgebra
variable {C : Type} [Category C] {Phi : C → Type} [ResourceTheory C Phi]
variable {A : C} (R : Phi A)
example : (𝟙 A ≫ 𝟙 A) • R = R := by
  calc
    §(𝟙 A ≫ 𝟙 A) • R = (𝟙 A) • ((𝟙 A) • R) := attach_serial _ _ R
    _ = (𝟙 A) • R := attach_identity _
    _ = R := attach_identity _"

/-- The H method justifies one supplied calc step; the following bound is independent. -/
def hCalculation := "open SystemAlgebra ConstructiveCryptography.CryptographicAlgebra
variable {A : Interface} (R S : TypedSystem A) (ε δ : NNReal)
variable (argument : RandomSystem.HCoefficient R.1 S.1 ε)
example (widen : (ε : ENNReal) ≤ δ) : distance R S ≤ δ := by
  calc
    §distance R S ≤ ε := Interface.distance_le_of_hCoefficient argument
    _ ≤ δ := widen"

/-- Preserve the actual command syntax and contexts, as the server does for a snapshot. -/
def calculationRungs (env : Environment) (opts : Options) (source : String)
    (expectErrors := false) : IO (Array Rung) := do
  let parts := source.splitOn "§"
  unless parts.length == 2 do throw (IO.userError "expected one cursor")
  let pos : String.Pos.Raw := ⟨parts[0]!.utf8ByteSize⟩
  let input := Parser.mkInputContext (String.join parts) "calculation.lean"
  let state ← IO.processCommands input {} (Command.mkState env {} opts)
  unless state.commandState.messages.hasErrors == expectErrors do
    throw (IO.userError "unexpected calculation diagnostics")
  for tree in state.commandState.infoState.substituteLazy.get.trees do
    let commands := tree.foldInfo (init := #[]) fun _ info acc =>
      match info with
      | .ofCommandInfo info => acc.push info.stx
      | _ => acc
    for command in commands do
      if let some rungs ← calcLadderFromTree? command tree input.fileMap pos #[] false then
        return rungs
  throw (IO.userError "no calculation at cursor")

run_cmd do
  let env ← getEnv
  let opts ← getOptions
  let rungs ← calculationRungs env opts calculation
  unless rungs.size == 3 && rungs.all (·.jv?.isSome) do
    throwError "a calculation lost its elaborated relations"
  unless rungs.all (·.justification?.isSome) do throwError "a calculation lost a justification"
  let first := AutomaticTests.textOf rungs[0]!.justification?.get!
  unless (first.splitOn "attach_serial").length > 1 do throwError "wrong first justification"
  -- A proof with an unfinished tactic keeps its goal and never looks completed.
  let incomplete := calculation.replace "attach_serial _ _ R" "by skip"
  let pending ← calculationRungs env opts incomplete true
  let some unfinished := pending[0]!.justification?
    | throwError "missing unfinished proof information"
  unless (AutomaticTests.textOf unfinished |>.splitOn "Unfinished").length > 1 do
    throwError "an unfinished calculation lost its obligation"
  let hRungs ← calculationRungs env opts hCalculation
  unless hRungs.size == 2 && hRungs[0]!.jv?.isSome && hRungs[1]!.code?.isSome do
    throwError "the H method changed the recorded calculation"
  let some first := hRungs[0]!.justification? | throwError "missing H justification"
  let .ok first := staticHtml first | throwError "H justification was not exportable"
  unless (first.splitOn "cc-proof-method").length == 2 do
    throwError "the H step lost its method inspector"
  let some second := hRungs[1]!.justification? | throwError "missing next justification"
  unless (AutomaticTests.textOf second |>.splitOn "widen").length > 1 do
    throwError "the H method replaced the next step's justification"
  let unfinishedH := hCalculation.replace "Interface.distance_le_of_hCoefficient argument" "by skip"
  let pendingH ← calculationRungs env opts unfinishedH true
  let some unfinished := pendingH[0]!.justification? | throwError "missing H-step obligations"
  unless (AutomaticTests.textOf unfinished |>.splitOn "Unfinished").length > 1 do
    throwError "an unfinished H step looked established"

run_cmd do
  let env ← getEnv
  let opts ← getOptions
  let source := "#check §SystemAlgebra.Tests.RevealedHCoefficient.halfBadReveal
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3)
  (Counter (budget := 3))"
  AutomaticTests.checkCursor env opts source "Proof"
  AutomaticTests.checkCursor env opts ("set_option cc.diagram.auto false\n" ++ source) "Proof" false
  AutomaticTests.checkCursor env opts (source.replace "#check" "#cc_proof_show") "Proof" true true
  AutomaticTests.checkCursor env opts "variable {A : Interface} (R S : TypedSystem A)\n\
    variable (w : RandomSystem.HCoefficient R.1 S.1 3)\n\
    #check §w" "Proof"
  AutomaticTests.checkCursor env opts "variable {A : Interface} (R S : TypedSystem A)\n\
    variable (w : RandomSystem.HCoefficient R.1 S.1 3)\n\
    example : ConstructiveCryptography.CryptographicAlgebra.distance R S ≤ (3 : NNReal) :=\n\
      §Interface.distance_le_of_hCoefficient w" "Proof"
  AutomaticTests.checkCursor env opts "variable {A : Interface} (R S : TypedSystem A)\n\
    variable (ε : NNReal) (w : RandomSystem.HCoefficient R.1 S.1 ε)\n\
    example : ConstructiveCryptography.CryptographicAlgebra.distance R S ≤ ε :=\n\
      Interface.§distance_le_of_hCoefficient w" "Proof"

end Rendering.ProofAutomaticTests
