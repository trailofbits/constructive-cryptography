import Rendering.Export

/-!
# Viewing recorded DSL declarations

`#cc_pseudocode_show Name` shows the declaration's original pseudocode in the infoview.
`#cc_pseudocode_export Name to "pseudocode.html"` exports the same view. Both resolve an exact
declaration name and refuse declarations without recorded source. Applied terms are viewed
through their expandable diagram leaf, which retains the application and labels the source
as the original declaration, with parameters as declared.
-/

namespace CCWidget
open Lean Server Elab Command ProofWidgets SystemAlgebra.DSL

/-- Resolve source metadata without unfolding a definition or opening a source file. -/
def elabPseudocode (name : Ident) : CoreM SourceDocument := do
  let name ← Elab.realizeGlobalConstNoOverloadWithInfo name
  let some doc := (sourceDocuments.getState (← getEnv)).find? name
    | throwError "cc_pseudocode: no recorded DSL source for {name}"
  return doc


elab (name := ccPseudocodeShow) stx:"#cc_pseudocode_show " name:ident : command => do
  let doc ← liftCoreM (elabPseudocode name)
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← rpcEncode (pseudocodePanel doc)) }) stx

elab "#cc_pseudocode_export " name:ident " to " path:str : command => do
  let doc ← liftCoreM (elabPseudocode name)
  match htmlDocument "DSL pseudocode" (pseudocodePanel doc) with
  | .ok html => IO.FS.writeFile path.getString html
  | .error error => throwError "{error}"

end CCWidget
