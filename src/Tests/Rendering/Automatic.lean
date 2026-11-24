import Rendering
import Examples.DSL.Components
import Lean.Elab.Frontend

/-! Cursor views use the elaborator's actual info trees, including local contexts and options. -/

open Lean Elab Meta CCWidget ProofWidgets

namespace Rendering.AutomaticTests

/-- Inspect visible text without forcing RPC references outside a server session. -/
partial def textOf : Html → String
  | .text text => text
  | .element "style" _ _ => ""
  | .element _ _ children | .component _ _ _ children =>
    String.join (children.toList.map textOf)

/-- `§` marks the cursor; it is removed before Lean parses and elaborates the fixture. -/
def checkCursor (env : Environment) (options : Options) (fixture : String)
    (expected : String) (enabled := true) (explicit := false) (errors := false) : IO Unit := do
  let parts := fixture.splitOn "§"
  unless parts.length == 2 do throw (IO.userError "fixture needs one cursor marker")
  let preamble := "open SystemAlgebra DSLExamples CategoryTheory\n"
  let source := preamble ++ String.join parts
  let pos : String.Pos.Raw := ⟨preamble.utf8ByteSize + parts[0]!.utf8ByteSize⟩
  let input := Parser.mkInputContext source "cursor-test.lean"
  let st ← IO.processCommands input {} (Command.mkState env {} options)
  unless st.commandState.messages.hasErrors == errors do
    throw (IO.userError s!"unexpected elaboration diagnostics in {fixture}")
  let mut found := false
  let mut hasExplicit := false
  for tree in st.commandState.infoState.substituteLazy.get.trees do
    if (tree.hoverableInfoAtM? (m := Id) pos (includeStop := true)).isNone then continue
    found := true
    hasExplicit := hasExplicit || tree.foldInfo (init := false) fun _ i acc =>
      acc || explicitViewAt i.stx pos
    unless automaticEnabledAt tree pos options == enabled do
      throw (IO.userError s!"wrong automatic option in {fixture}")
    let view? ← cursorView? tree pos
    if expected.isEmpty then
      unless view?.isNone do throw (IO.userError s!"unexpected cursor view in {fixture}")
    else
      let some view := view? | throw (IO.userError s!"missing {expected} view in {fixture}")
      unless (textOf view).startsWith expected do
        throw (IO.userError s!"wrong view in {fixture}: {textOf view}")
  unless found || expected.isEmpty do throw (IO.userError s!"no info at cursor in {fixture}")
  unless hasExplicit == explicit do
    throw (IO.userError s!"wrong explicit-panel suppression in {fixture}")

run_cmd do
  let env ← getEnv
  let opts ← getOptions
  -- Imported systems, converters and interfaces need no display command or display-name attribute.
  checkCursor env opts "#check §Counter (budget := 3)" "Diagram"
  checkCursor env opts "#check §WriteThrough (budget := 3)" "Diagram"
  checkCursor env opts "#check §Cache 3" "Diagram"
  checkCursor env opts "#check §𝟙 (Cache 3)" "Diagram"
  checkCursor env opts "#check §@Counter" "Pseudocode"
  checkCursor env opts
    "open scoped SystemAlgebra.DSL\nsystem §AutoBits\n  on bit() → Bool\n    return true"
    "Pseudocode"
  -- Ordinary definitions and local variables keep their actual elaboration context.
  checkCursor env opts "noncomputable def exampleSystem := §Counter (budget := 3)" "Diagram"
  checkCursor env opts "noncomputable def §exampleSystem := Counter (budget := 3)" "Diagram"
  checkCursor env opts
    "example (R : TypedSystem (Cache 3)) : R = R := by exact Eq.refl §R" "Diagram"
  checkCursor env opts
    "theorem §exampleEquality : Counter (budget := 3) = Counter (budget := 3) := rfl"
    "Diagram"
  -- Both file options and command-local options are read at the cursor, not at end of file.
  checkCursor env opts
    "set_option cc.diagram.auto false\n#check §Counter (budget := 3)" "Diagram" false
  checkCursor env opts
    "set_option cc.diagram.auto false in\n#check §Counter (budget := 3)" "Diagram" false
  checkCursor env opts
    "set_option cc.diagram.auto false in\n#check Counter (budget := 3)\n\
    #check §Counter (budget := 4)"
    "Diagram"
  checkCursor env opts
    "section\nset_option cc.diagram.auto false\nend\n#check §Counter (budget := 3)" "Diagram"
  -- Explicit views still work when automatic views are off, and must never be duplicated.
  checkCursor env opts "#cc_diagram_show §Counter (budget := 3)" "Diagram" true true
  checkCursor env opts
    "set_option cc.diagram.auto false in\n#cc_diagram_show §Counter (budget := 3)"
    "Diagram" false true
  checkCursor env opts "#cc_pseudocode_show §Counter" "Pseudocode" true true
  -- No inferred CC semantics for unrelated values, and no invented parameter instantiation.
  checkCursor env opts "#check §(7 : Nat)" ""
  checkCursor env opts "#check §Nat.succ" ""
  checkCursor env opts "#check §TypedConverter.comp" ""
  checkCursor env opts "#check §Counter (budget := _)" ""
  checkCursor env opts "#check §Counter (budget := true)" "" true false true
  checkCursor env opts "#check (Counter (budget := 3))\n\n§\n" ""
  checkCursor env opts "-- §Counter is mentioned in prose.\n#check (0 : Nat)" ""

end Rendering.AutomaticTests
