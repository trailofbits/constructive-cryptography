import Rendering.CCWidget

/-!
# Static export of the same system diagram

`#cc_diagram_export t to "diagram.html"` exports the same expression tree and CSS
as the infoview, with selectable Lean text in place of RPC-backed hover widgets.
A small bundled controller provides the same hover, pin and dismiss behavior as the infoview.
No network resources, downloaded fonts, or rendering service are required. Without scripting,
interface information remains available through native disclosures.
-/

namespace CCWidget
open Lean ProofWidgets

/-- Escape text and attribute values; display labels are never interpreted as HTML. -/
def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;" |>.replace "'" "&#39;"

/-- Serialize static HTML only. An RPC-backed component cannot silently disappear
from an export: callers must use the renderer's ordinary text fallback. -/
partial def staticHtml : Html → Except String String
  | .text s => pure (escapeHtml s)
  | .component .. => throw "static export cannot contain RPC components"
  -- Style is an HTML raw-text element: entity escaping would corrupt selectors.
  -- A CSS escape for '<' prevents an embedded closing tag from ending the element.
  | .element "style" #[] #[.text css] =>
      pure ("<style>" ++ css.replace "<" "\\3c " ++ "</style>")
  | .element tag attrs children => do
    let mut result := "<" ++ tag
    for (key, val) in attrs do
      let key := if key == "className" then "class" else key
      match val with
      | .str value => result := result ++ " " ++ key ++ "=\"" ++ escapeHtml value ++ "\""
      | .bool true => result := result ++ " " ++ key
      | .bool false => pure ()
      | _ => throw s!"unsupported static attribute: {key}"
    result := result ++ ">"
    for child in children do result := result ++ (← staticHtml child)
    return result ++ "</" ++ tag ++ ">"

/-- Fixed controller code only; source expressions are serialized as escaped HTML elsewhere. -/
def exportedInspectorScript : String :=
  "<script type=\"module\" data-cc-inspectors>" ++ exportedInspectorJavascript ++ "</script>"

/-- A standalone document, including native mathematical typography and the
complete original Lean expression. -/
def htmlDocument (title : String) (body : Html) : Except String String := do
  return "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">" ++
    "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">" ++
    "<meta name=\"color-scheme\" content=\"light dark\"><title>" ++ escapeHtml title ++
    "</title><style>body{margin:0;padding:24px;box-sizing:border-box;}" ++
    "main{max-width:1280px;margin:auto;}" ++
    "@media(max-width:480px){body{padding:12px;}}</style></head><body><main>" ++
    (← staticHtml body) ++ "</main>" ++ exportedInspectorScript ++ "</body></html>"

elab "#cc_diagram_export " t:term " to " path:str : command => do
  let document ← Elab.Command.runTermElabM fun _ => do
    let some j ← elabView t | throwError "cc_diagram: expression not recognized"
    match htmlDocument "System diagram" (panel (renderJudgment j #[])) with
    | .ok document => pure document
    | .error error => throwError "{error}"
  IO.FS.writeFile path.getString document

elab "#cc_proof_export " t:term " to " path:str : command => do
  let document ← Elab.Command.runTermElabM fun _ => do
    let html ← elabProofView t false
    match htmlDocument "Proof view" html with
    | .ok document => pure document
    | .error error => throwError "{error}"
  IO.FS.writeFile path.getString document

end CCWidget
