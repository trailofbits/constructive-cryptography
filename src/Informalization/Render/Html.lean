/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Rendering.CCWidget
import Rendering.Export
import Informalization.Core.Explanation
import Informalization.Core.ProofGraph
import Informalization.Render.Json

/-!
# Standalone Interactive ETH CADMO HTML Renderer

Bundles:
* ETH CADMO `memoir` + Palatino CSS (`cadmo-reader.css`),
* Interactive `⊕`/`⊖`, Paper/Auditor toggle, and Margin Inspector JS (`cadmo-reader.js`),
* `Rendering`'s deterministic CC box-and-wire CSS & inspector controller,
* The canonical `Explanation.Document` JSON (safely escaped for `<script>`).

Works 100% offline with zero external network dependencies (while automatically upgrading
LaTeX formulas via KaTeX if loaded in an environment that provides it).
-/

namespace Informalization.Render.Html

open Lean Meta
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph
open Informalization.Render.Json

/-- Bundled ETH CADMO monograph stylesheet. -/
def cadmoStylesheet : String := include_str "cadmo-reader.css"

/-- Bundled interactive CADMO reader script. -/
def cadmoScript : String := include_str "cadmo-reader.js"

/-- Safely embed JSON inside a `<script type="application/json">` tag without allowing
`</script>` or HTML comment breakouts. -/
def escapeJsonForScript (s : String) : String :=
  s.replace "<" "\\u003c" |>.replace ">" "\\u003e" |>.replace "&" "\\u0026"

/-- Render a canonical `Document` as a complete, standalone, offline-ready ETH CADMO HTML file. -/
def renderDocumentHtml (doc : Document) : String :=
  let titleEsc := CCWidget.escapeHtml doc.title
  let ccCss := CCWidget.stylesheet.replace "<" "\\3c "
  let cadmoCss := cadmoStylesheet.replace "<" "\\3c "
  let jsonPayload := escapeJsonForScript (toJson doc).compress
  "<!doctype html>\n" ++
  "<html lang=\"en\">\n" ++
  "<head>\n" ++
  "  <meta charset=\"utf-8\">\n" ++
  "  <meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\n" ++
  "  <meta name=\"color-scheme\" content=\"light dark\">\n" ++
  s!"  <title>{titleEsc}</title>\n" ++
  s!"  <style data-cc-diagram>{ccCss}</style>\n" ++
  s!"  <style data-cadmo-reader>{cadmoCss}</style>\n" ++
  "</head>\n" ++
  "<body>\n" ++
  "  <div id=\"cadmo-root\"></div>\n" ++
  s!"  <script id=\"cadmo-document-data\" type=\"application/json\">{jsonPayload}</script>\n" ++
  s!"  <script data-cadmo-controller>{cadmoScript}</script>\n" ++
  CCWidget.exportedInspectorScript ++ "\n" ++
  "</body>\n" ++
  "</html>\n"

/-- Export a single declaration as standalone CADMO HTML directly from Lean. -/
elab "#informalize_export " decl:ident " to " path:str : command => do
  let html ← Elab.Command.runTermElabM fun _ => do
    let declName ← Elab.realizeGlobalConstNoOverloadWithInfo decl
    let doc ← buildDocument (humanLemmaLabel (← getEnv) declName) none #[declName]
    return renderDocumentHtml doc
  IO.FS.writeFile path.getString html

end Informalization.Render.Html
