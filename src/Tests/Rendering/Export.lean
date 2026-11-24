import Rendering.Export

/-! Static export preserves renderer CSS and escapes all term-derived text.
An interactive component must be rendered with its text fallback before export. -/

open Lean Elab Command CCWidget ProofWidgets

run_cmd do
  if (exportedInspectorJavascript.toLower.splitOn "</script").length != 1 then
    throwError "controller contains a closing HTML script tag"
  unless exportedInspectorJavascript == inspectorController ++ "\nenhanceExportedInspectors();\n" do
    throwError "export and native inspector controllers differ"
  unless escapeHtml "<img a='x' b=\"y\">&" ==
      "&lt;img a=&#39;x&#39; b=&quot;y&quot;&gt;&amp;" do
    throwError "HTML text escaping failed"
  let .ok css := staticHtml (.element "style" #[] #[.text "a > b { color: red }"])
    | throwError "stylesheet serialization failed"
  unless css == "<style>a > b { color: red }</style>" do
    throwError "CSS selectors were changed by HTML entity escaping"
  let .ok escapedCss := staticHtml (.element "style" #[] #[.text "</style><script>"])
    | throwError "raw-text serialization failed"
  unless escapedCss == "<style>\\3c /style>\\3c script></style>" do
    throwError "raw-text element can be closed by its contents"
  let interactive := Html.ofComponent CalcStepper { initialIndex := 0 } #[]
  match staticHtml interactive with
  | .error _ => pure ()
  | .ok _ => throwError "an RPC component silently disappeared during export"
