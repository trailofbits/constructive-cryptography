import RandomSystems.Typed.DSL.Source
import ProofWidgets.Component.HtmlDisplay

/-!
# Source-backed pseudocode cards

The Penpot layout uses a declaration heading and whitespace-separated procedure blocks.
Every displayed character comes from the compiler's original source partition. There is no
decompilation, parameter substitution, keyword translation, or invented interface attribution.
-/

namespace CCWidget
open Lean ProofWidgets SystemAlgebra.DSL

/-- Render the original DSL declaration. Procedures remain in source order and share one
card, including initialization; a multi-port component is not split into independent systems. -/
def renderPseudocode (doc : SourceDocument) : Html := Id.run do
  let mut parts := #[]
  for part in doc.sections do
    let code := Html.element "pre" #[]
      #[.element "strong" #[] #[.text part.header], .text part.body]
    if part.proof then
      parts := parts.push <| .element "details" #[("className", .str "cc-pseudocode-proof")]
        #[.element "summary" #[] #[.text "by"], code]
    else
      parts := parts.push <| .element "section"
        #[("className", .str (if part.block then "cc-pseudocode-block"
          else "cc-pseudocode-clause"))] #[code]
  return .element "article"
    #[("className", .str "cc-pseudocode"), ("data-declaration", .str doc.declaration.toString)]
    #[.element "header" #[]
        #[.element "span" #[("className", .str "cc-pseudocode-origin"),
            ("title", .str doc.declaration.toString)] #[.text "Declaration"],
          .element "pre" #[("className", .str "cc-pseudocode-heading")]
            #[.text doc.header]],
      .element "div" #[("className", .str "cc-pseudocode-sections")] parts,
      .element "details" #[("className", .str "cc-source-toggle")]
        #[.element "summary" #[("title", .str "Exact original DSL declaration")] #[.text "Lean"],
          .element "pre" #[("className", .str "cc-pseudocode-source")] #[.text doc.source]]]

end CCWidget
