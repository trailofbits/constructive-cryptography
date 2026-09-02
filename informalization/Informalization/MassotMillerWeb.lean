/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller

/-!
# Paper-style web reader for the public InformalLean document schema

The renderer exposes one mount contract used by both the standalone page and
native host applications. The generated shell deliberately contains no
editorial header, footer, kicker, or proof summary. The theorem records are the
complete authored document; the bundled stylesheet also keeps mathematical
text at the surrounding prose scale.
The web application supplies only the interaction described by Massot and Miller:
zero-text goal markers select a human-rendered state in the side inspector,
hidden-branch selections are cleared on collapse, and the inspector is omitted
when the document has no goal-state nodes or no state is currently selected.
Hover affordances use a light dotted underline, darkening only on hover or
keyboard focus, and semantic-depth controls sit immediately before the passage
whose detail they reveal. A
small right-edge disclosure
switches between the semantic proof and the complete concrete proof tree; the
renderer applies no additional depth limit. The global expansion control
selects the complete proof tree and opens it recursively; global collapse
closes both trees and restores the semantic paper view. Global proof controls form an ordinary footer after
the proof rather than floating over its prose, and use a reader-owned class so
presentation frameworks cannot capture them. Their dimensions are relative to
the reader text, so embedded and standalone views retain the same proportions.
Lean-derived hover descriptions use a viewport-level
floating layer: they are neither clipped by the theorem pane nor given their
own scrollport. Expressions outside the notation registry use the conservative
structural LaTeX printer rather than a raw source fragment. When served on
localhost by the development watcher, a successful build stamp reloads the
page; static and `file://` readers perform no live-reload request.
-/

namespace Informalization.MassotMiller

private def rendererCss : String := include_str "../web/massot-miller.css"
/-- The bundled renderer, including structural mathematical fallbacks,
sanitized context labels, inline-safe interactive references, and opt-in
localhost reload detection, is embedded so local files need no script
sidecar. -/
private def rendererJs : String := include_str "../web/massot-miller.js"

structure WebPage where
  title : String
  declarations : Document
  deriving Inhabited

private def escapeHtml (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '&' => "&amp;"
      | '<' => "&lt;"
      | '>' => "&gt;"
      | '"' => "&quot;"
      | '\'' => "&#39;"
      | _ => c.toString

/-- Protect JSON embedded in an HTML script-data element. -/
def jsonForScriptData (json : String) : String :=
  (json.replace "&" "\\u0026").replace "<" "\\u003c" |>.replace ">" "\\u003e"

def WebPage.toHtml (page : WebPage) : String :=
  let payload := jsonForScriptData (documentToJson page.declarations).pretty
  "<!DOCTYPE html>\n" ++
  "<html lang=\"en\"><head><meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\n" ++
  "<title>" ++ escapeHtml page.title ++ "</title>\n" ++
  "<style>\n" ++ rendererCss ++ "\n</style>\n" ++
  "<link rel=\"stylesheet\" href=\"https://cdn.jsdelivr.net/npm/katex@0.17.0/dist/katex.min.css\" crossorigin=\"anonymous\">\n" ++
  "<script src=\"https://cdn.jsdelivr.net/npm/katex@0.17.0/dist/katex.min.js\" crossorigin=\"anonymous\"></script>\n" ++
  "</head><body><div id=\"main\"></div>\n" ++
  "<script id=\"informalization-data\" type=\"application/json\">\n" ++ payload ++
  "\n</script>\n" ++
  "<script>\n" ++ rendererJs ++ "\n</script>\n" ++
  "</body></html>\n"

def WebPage.write (page : WebPage) (jsonPath htmlPath : System.FilePath) : IO Unit := do
  IO.FS.writeFile jsonPath ((documentToJson page.declarations).pretty ++ "\n")
  IO.FS.writeFile htmlPath page.toHtml

/-- Write a standalone HTML entry point.  CSS, renderer code, and the public
JSON document are embedded so the page also works when opened through
`file://`; KaTeX is only a progressive network-loaded enhancement.  The two
sidecar assets are retained for consumers that want to extract them. -/
def WebPage.writeHtmlBundle (page : WebPage) (htmlPath : System.FilePath) : IO Unit := do
  let directory := htmlPath.parent.getD "."
  IO.FS.createDirAll directory
  IO.FS.writeFile htmlPath page.toHtml
  IO.FS.writeFile (directory / "massot-miller.css") rendererCss
  IO.FS.writeFile (directory / "massot-miller.js") rendererJs

#guard jsonForScriptData "{\"x\":\"</script>\"}" ==
  "{\"x\":\"\\u003c/script\\u003e\"}"

end Informalization.MassotMiller
