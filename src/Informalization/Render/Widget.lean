/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import ProofWidgets.Component.HtmlDisplay
import Informalization.Core.Explanation
import Informalization.Core.ProofGraph
import Informalization.Render.Json

/-!
# Lean 4 Infoview Renderer (`ProofWidgets`)

Renders the exact same canonical `Explanation.Document` IR live inside the VS Code Lean 4
Infoview via `#informalize_show Decl`, using native `<details>` interactive `⊕` disclosure,
ETH CADMO Palatino styling, clickable symbol definitions, and Kyle Miller goal checkpoints.
-/

namespace Informalization.Render.Widget

open Lean Meta ProofWidgets Server
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph
open Informalization.Render.Json

/-- Clean readable math string for native Infoview rendering. -/
private def prettyInfoviewMath (tex : String) : String :=
  tex
    |>.replace "\\varepsilon" "ε"
    |>.replace "\\epsilon" "ε"
    |>.replace "\\Delta" "Δ"
    |>.replace "\\Pi" "Π"
    |>.replace "\\pi" "π"
    |>.replace "\\sigma" "σ"
    |>.replace "\\kappa" "κ"
    |>.replace "\\alpha" "α"
    |>.replace "\\beta" "β"
    |>.replace "\\parallel" "∥"
    |>.replace "\\le" "≤"
    |>.replace "\\ge" "≥"
    |>.replace "\\neq" "≠"
    |>.replace "\\in" "∈"
    |>.replace "\\subseteq" "⊆"
    |>.replace "\\times" "×"
    |>.replace "\\cdot" "·"
    |>.replace "\\circ" "∘"
    |>.replace "\\to" "→"
    |>.replace "\\forall" "∀"
    |>.replace "\\exists" "∃"
    |>.replace "\\mathbb{R}_{\\ge 0}" "ℝ≥0"
    |>.replace "\\mathbb{R}" "ℝ"
    |>.replace "\\mathbb{N}" "ℕ"
    |>.replace "\\," " "
    |>.replace "\\;" " "

private def renderInlineHtml : Inline → Html
  | .text s => .text s
  | .emph s => .element "em" #[] #[.text s]
  | .inlineMath tex =>
      .element "span" #[("className", "cadmo-iv-math")] #[.text (prettyInfoviewMath tex)]
  | .displayMath tex punct =>
      .element "div" #[("className", "cadmo-iv-display")] #[.text (prettyInfoviewMath tex ++ punct)]
  | .symbol _ disp isMath =>
      let label := if isMath then prettyInfoviewMath disp else disp
      .element "span" #[("className", "cadmo-iv-sym")] #[.text label]
  | .citation l _ =>
      .element "span" #[("className", "cadmo-iv-cite")] #[.text s!"[{l}]"]

private def renderInlinesHtml (xs : Array Inline) : Array Html :=
  xs.map renderInlineHtml

private def renderGoalHtml (g : GoalState) : Html :=
  let ctxItems := g.context.map fun c =>
    let prefixStr := match c.name? with | some n => s!"{n}: " | none => ""
    .element "li" #[] #[.text (prefixStr ++ c.description)]
  .element "details" #[("className", "cadmo-iv-goal")] #[
    .element "summary" #[] #[.text "⊢ goal"],
    .element "div" #[("className", "cadmo-iv-goal-body")] #[
      .element "ul" #[] ctxItems,
      .element "div" #[("className", "cadmo-iv-goal-target")] #[
        .text ("⊢ " ++ prettyInfoviewMath g.targetLatex)
      ]
    ]
  ]

private partial def renderProofNodeHtml : ProofNode → Html
  | .flowNote _ txt _ =>
      .element "div" #[("className", "cadmo-iv-note")] #[
        .element "strong" #[] #[.text "Note. "],
        .text txt
      ]
  | .figure _ cap _ =>
      .element "div" #[("className", "cadmo-iv-note")] (renderInlinesHtml cap)
  | .routineReceipt _ summary count _ goal? =>
      let extra := match goal? with | some g => #[renderGoalHtml g] | none => #[]
      .element "div" #[("className", "cadmo-iv-routine")] (
        #[.text s!"[{summary} ({count} checked)]"] ++ extra
      )
  | .calcChain _ intro steps goal? _ =>
      let rows := steps.mapIdx fun idx (cs, sub) =>
        let lhs := if idx == 0 then prettyInfoviewMath cs.lhsLatex else ""
        let rel := prettyInfoviewMath cs.relationLatex
        let rhs := prettyInfoviewMath cs.rhsLatex
        let line := .element "div" #[("className", "cadmo-iv-calc-line")] (
          #[.text s!"{lhs}  {rel}  {rhs}   — "] ++ renderInlinesHtml cs.reason
        )
        if sub.isEmpty then line
        else
          .element "details" #[("className", "cadmo-iv-step")] #[
            .element "summary" #[] #[line],
            .element "div" #[("className", "cadmo-iv-children")] (sub.map renderProofNodeHtml)
          ]
      let extra := match goal? with | some g => #[renderGoalHtml g] | none => #[]
      .element "div" #[("className", "cadmo-iv-calc")] (
        #[.element "div" #[] (renderInlinesHtml intro)] ++ rows ++ extra
      )
  | .step _ content children goal? _ _ isWrapper _ =>
      if isWrapper && !children.isEmpty then
        .element "div" #[] (children.map renderProofNodeHtml)
      else
        let body := renderInlinesHtml content
        let extra := match goal? with | some g => #[renderGoalHtml g] | none => #[]
        if children.isEmpty then
          .element "div" #[("className", "cadmo-iv-leaf")] (body ++ extra)
        else
          .element "details" #[("className", "cadmo-iv-step")] #[
            .element "summary" #[] (body ++ extra),
            .element "div" #[("className", "cadmo-iv-children")] (children.map renderProofNodeHtml)
          ]

private def infoviewCss : String :=
  ".cadmo-iv { font-family: 'Palatino Linotype', 'TeX Gyre Pagella', Palatino, Georgia, serif; line-height: 1.55; padding: 8px 10px; max-width: 52rem; }\n" ++
  ".cadmo-iv-head { font-variant-caps: small-caps; font-weight: 600; font-size: 1.08em; margin-bottom: 6px; }\n" ++
  ".cadmo-iv-ambient { border-left: 2px solid #888; padding: 4px 8px; margin-bottom: 8px; opacity: 0.9; font-size: 0.92em; }\n" ++
  ".cadmo-iv-stmt { border-left: 3px solid #2b6cb0; padding: 6px 10px; margin-bottom: 10px; }\n" ++
  ".cadmo-iv-step { margin: 4px 0; }\n" ++
  ".cadmo-iv-step > summary { cursor: pointer; }\n" ++
  ".cadmo-iv-children { margin-left: 14px; padding-left: 10px; border-left: 1px solid rgba(128,128,128,0.35); }\n" ++
  ".cadmo-iv-leaf { margin: 4px 0 4px 14px; }\n" ++
  ".cadmo-iv-routine { margin: 3px 0 3px 14px; font-style: italic; opacity: 0.78; font-size: 0.9em; }\n" ++
  ".cadmo-iv-note { border-left: 2px solid rgba(128,128,128,0.5); padding: 4px 8px; margin: 6px 0; font-style: italic; font-size: 0.92em; }\n" ++
  ".cadmo-iv-sym { border-bottom: 1px dotted currentColor; }\n" ++
  ".cadmo-iv-math { font-style: italic; }\n" ++
  ".cadmo-iv-display { text-align: center; margin: 6px 0; font-style: italic; }\n" ++
  ".cadmo-iv-goal { display: inline-block; margin-left: 6px; font-size: 0.82em; opacity: 0.8; }\n" ++
  ".cadmo-iv-goal-body { padding: 4px 8px; border-left: 2px solid #2b6cb0; margin-top: 4px; }\n" ++
  ".cadmo-iv-calc-line { font-family: inherit; margin: 2px 0; }\n"

/-- Convert a canonical `Document` into `ProofWidgets.Html` for live Infoview display. -/
def renderDocumentInfoview (doc : Document) : Html :=
  let entryEls := doc.entries.map fun e =>
    let titleStr := match e.title? with
      | some t => s!"{e.header} ({t})."
      | none => s!"{e.header}."
    let sectionCtxEl := match e.sectionContext? with
      | some sc =>
          let secParas := sc.paragraphs.map fun p => .element "p" #[] (renderInlinesHtml p)
          #[.element "div" #[("className", "cadmo-iv-ambient")] secParas]
      | none => #[]
    let ambientEl := match e.ambient? with
      | some amb =>
          #[.element "div" #[("className", "cadmo-iv-ambient")]
            (#[.element "strong" #[] #[.text "Setting. "]] ++ renderInlinesHtml amb.summary)]
      | none => #[]
    let stmtEls := e.statement.map fun p => .element "p" #[] (renderInlinesHtml p)
    let proofEls :=
      if e.proof.isEmpty then #[]
      else
        #[.element "div" #[] (
          #[.element "em" #[] #[.text "Proof. "]] ++ e.proof.map renderProofNodeHtml
        )]
    .element "section" #[] (
      #[.element "div" #[("className", "cadmo-iv-head")] #[.text titleStr]] ++
      sectionCtxEl ++
      ambientEl ++
      #[.element "div" #[("className", "cadmo-iv-stmt")] stmtEls] ++
      proofEls
    )
  .element "div" #[("className", "cadmo-iv")] (
    #[.element "style" #[] #[.text infoviewCss]] ++ entryEls
  )

/-- Show a live interactive CADMO informalization directly in the Lean 4 Infoview. -/
elab (name := informalizeShowCmd) stx:"#informalize_show " decl:ident : command => do
  let html ← Elab.Command.runTermElabM fun _ => do
    let declName ← Elab.realizeGlobalConstNoOverloadWithInfo decl
    let doc ← buildDocument (humanLemmaLabel (← getEnv) declName) none #[declName]
    return renderDocumentInfoview doc
  Elab.Command.liftCoreM <| Lean.Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript) (return json% { html: $(← rpcEncode html) }) stx

end Informalization.Render.Widget
