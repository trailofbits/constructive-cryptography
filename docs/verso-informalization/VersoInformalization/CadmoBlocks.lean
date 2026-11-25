/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoInformalization.Schema

/-!
# ETH CADMO Verso & HTML Block Builders

Reusable block builders that project any decoded `Schema.Document` into:
1. **ETH CADMO Palatino HTML fragments** (`renderEntryHtml`, `renderProofNodeHtml`,
   `renderCalcStepRowsHtml`, `renderInspectorCardHtml`, `renderDocumentHtml`),
   suitable both for Verso `Block`/`Inline` HTML extensions and static monograph pages;
2. **Verso literate chapter source stubs** (`renderVersoChapterStub`) so authors can
   embed checked CC theorems into Verso manuals, papers, and slides while keeping
   100% of mathematical claims mechanically sourced from the exported JSON.
-/

namespace VersoInformalization.CadmoBlocks

open Lean
open VersoInformalization.Schema

/-- Escape HTML special characters for safe text & attribute emission. -/
def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;"
    |>.replace "<" "&lt;"
    |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;"
    |>.replace "'" "&#39;"

/-- Safely escape JSON for inclusion inside `<script type="application/json">`. -/
def escapeJsonForScript (s : String) : String :=
  s.replace "<" "\\u003c"
    |>.replace ">" "\\u003e"
    |>.replace "&" "\\u0026"

/-- Lightweight offline LaTeX-to-Unicode pretty formatter matching `cadmo-reader.js`. -/
def prettyFallbackMath (tex : String) : String :=
  tex
    |>.replace "\\varepsilon" "ε"
    |>.replace "\\epsilon" "ε"
    |>.replace "\\Delta" "Δ"
    |>.replace "\\Pi" "Π"
    |>.replace "\\Sigma" "Σ"
    |>.replace "\\pi" "π"
    |>.replace "\\sigma" "σ"
    |>.replace "\\kappa" "κ"
    |>.replace "\\alpha" "α"
    |>.replace "\\beta" "β"
    |>.replace "\\gamma" "γ"
    |>.replace "\\delta" "δ"
    |>.replace "\\rho" "ρ"
    |>.replace "\\tau" "τ"
    |>.replace "\\phi" "φ"
    |>.replace "\\psi" "ψ"
    |>.replace "\\parallel" "∥"
    |>.replace "\\le" "≤"
    |>.replace "\\ge" "≥"
    |>.replace "\\neq" "≠"
    |>.replace "\\subseteq" "⊆"
    |>.replace "\\times" "×"
    |>.replace "\\cdot" "·"
    |>.replace "\\circ" "∘"
    |>.replace "\\to" "→"
    |>.replace "\\mapsto" "↦"
    |>.replace "\\forall" "∀"
    |>.replace "\\exists" "∃"
    |>.replace "\\land" "∧"
    |>.replace "\\lor" "∨"
    |>.replace "\\neg" "¬"
    |>.replace "\\infty" "∞"
    |>.replace "\\," " "
    |>.replace "\\;" " "
    |>.replace "\\!" ""
    |>.replace "\\_" "_"

/-- Render a math span (`displayMode = false`) or display block (`displayMode = true`). -/
def renderMathHtml (latex : String) (displayMode : Bool := false) : String :=
  let cls := if displayMode then "cadmo-display-math" else "cadmo-math"
  let tag := if displayMode then "div" else "span"
  let body := escapeHtml (prettyFallbackMath latex)
  s!"<{tag} class=\"{cls}\" data-latex=\"{escapeHtml latex}\">{body}</{tag}>"

/-- Render a single `Inline` element. Underlined `symbol` buttons bind to `SymbolInspector` by key. -/
def renderInlineHtml (doc : Document) : Inline → String
  | .text value => escapeHtml value
  | .emph value => s!"<em>{escapeHtml value}</em>"
  | .inlineMath latex => renderMathHtml latex false
  | .displayMath latex punct =>
      let full := if punct.isEmpty then latex else s!"{latex}\\,{punct}"
      renderMathHtml full true
  | .symbol key display isMath =>
      let titleAttr := match doc.findInspector? key with
        | some _ => s!"Inspect {display}"
        | none => display
      let inner := if isMath then renderMathHtml display false else escapeHtml display
      s!"<button type=\"button\" class=\"cadmo-sym\" data-symbol-key=\"{escapeHtml key}\" " ++
      s!"aria-pressed=\"false\" title=\"{escapeHtml titleAttr}\">{inner}</button>"
  | .citation label detail =>
      s!"<span class=\"cadmo-citation\" title=\"{escapeHtml detail}\">[{escapeHtml label}]</span>"

/-- Render an array of `Inline` elements. -/
def renderInlinesHtml (doc : Document) (xs : Array Inline) : String :=
  String.join (xs.toList.map (renderInlineHtml doc))

/-- Render an embedded `Rendering` CC diagram container. -/
def renderDiagramFigureHtml (html : String) (caption? : Option String := none) : String :=
  let cap := match caption? with
    | some c => s!"<figcaption class=\"cadmo-figure-caption\">{c}</figcaption>"
    | none => ""
  s!"<figure class=\"cadmo-figure\"><div>{html}</div>{cap}</figure>"

/-- Render a Kyle Miller `GoalState` card (hygienized context + target). -/
def renderGoalStateCardHtml (goal : GoalState) (label : String := "Proof step") : String :=
  let ctxItems := String.join <| goal.context.toList.map fun (c : ContextEntry) =>
    let nameHtml := match c.name? with
      | some nm => s!"<strong>{escapeHtml nm}: </strong>"
      | none => ""
    s!"<li>{nameHtml}{escapeHtml c.description}</li>"
  let ctxSection :=
    if goal.context.isEmpty then ""
    else
      s!"<div class=\"cadmo-inspector-kicker\">Context</div>" ++
      s!"<ul class=\"cadmo-goal-ctx\">{ctxItems}</ul>"
  let rawDetails := match goal.rawLeanGoal? with
    | some raw =>
        s!"<details class=\"cadmo-lean-details\"><summary>Raw Lean goal</summary>" ++
        s!"<div class=\"cadmo-lean-code\">{escapeHtml raw}</div></details>"
    | none => ""
  s!"<section class=\"cadmo-inspector-card\">" ++
  s!"<div class=\"cadmo-inspector-head\"><div>" ++
  s!"<div class=\"cadmo-inspector-kicker\">Checked Proof State</div>" ++
  s!"<h3 class=\"cadmo-inspector-title\">{escapeHtml label}</h3>" ++
  s!"</div></div>" ++
  ctxSection ++
  s!"<div class=\"cadmo-inspector-kicker\">Goal</div>" ++
  s!"<div class=\"cadmo-goal-target\">{renderMathHtml goal.targetLatex false}</div>" ++
  rawDetails ++
  "</section>"

/-- Render a type-aware `SymbolInspector` card (Interface table, DSL card, CC assembly,
math definition, witness card, or parameter). -/
def renderInspectorCardHtml (ins : SymbolInspector) : String :=
  let (kicker, bodyHtml) := match ins.kind with
    | .interfaceTable ports domainLatex budgetNote =>
        let dom := if domainLatex.isEmpty then ""
          else s!"<p>Domain: {renderMathHtml domainLatex false}</p>"
        let rows := String.join <| ports.toList.map fun (p : PortRow) =>
          s!"<tr><td>{escapeHtml p.port}</td><td>{renderMathHtml p.queryLatex false}</td>" ++
          s!"<td>{renderMathHtml p.replyLatex false}</td></tr>"
        let tbl := if ports.isEmpty then ""
          else
            "<table class=\"cadmo-inspector-table\"><thead><tr>" ++
            "<th>Port</th><th>Query</th><th>Reply</th></tr></thead>" ++
            s!"<tbody>{rows}</tbody></table>"
        let budget := if budgetNote.isEmpty then "" else s!"<p>{escapeHtml budgetNote}</p>"
        ("Interface", dom ++ tbl ++ budget)
    | .dslPseudocode header body fullSource =>
        let hd := if header.isEmpty then "" else s!"<p><strong>{escapeHtml header}</strong></p>"
        let code := if body.isEmpty then fullSource else body
        ("System / Converter", hd ++ s!"<pre class=\"cadmo-pseudocode\">{escapeHtml code}</pre>")
    | .ccDiagram svgOrHtml summaryLatex =>
        let sum := if summaryLatex.isEmpty then "" else renderMathHtml summaryLatex true
        let fig := if svgOrHtml.isEmpty then "" else renderDiagramFigureHtml svgOrHtml
        ("CC Assembly", sum ++ fig)
    | .mathDefinition equationLatex proseSummary =>
        let prose := if proseSummary.isEmpty then "" else s!"<p>{escapeHtml proseSummary}</p>"
        let eq := if equationLatex.isEmpty then "" else renderMathHtml equationLatex true
        ("Definition", prose ++ eq)
    | .witnessCard title rows =>
        let hd := if title.isEmpty then "" else s!"<p><strong>{escapeHtml title}</strong></p>"
        let rowHtml := String.join <| rows.toList.map fun (k, v) =>
          s!"<tr><th>{escapeHtml k}</th><td>{renderMathHtml v false}</td></tr>"
        ("Witness", hd ++ s!"<table class=\"cadmo-inspector-table\"><tbody>{rowHtml}</tbody></table>")
    | .parameter roleDescription =>
        ("Parameter", s!"<p>{escapeHtml roleDescription}</p>")
    | .localShorthand equationLatex roleDescription =>
        let prose := if roleDescription.isEmpty then "" else s!"<p>{escapeHtml roleDescription}</p>"
        let eq := if equationLatex.isEmpty then "" else renderMathHtml equationLatex true
        ("Local shorthand", prose ++ eq)
  let finalKicker := ins.roleBadge?.getD kicker
  let docHtml := match ins.docString? with
    | some d => if d.isEmpty then "" else s!"<p class=\"cadmo-sidenote-doc\">{escapeHtml d}</p>"
    | none => ""
  let clausesHtml :=
    if ins.clauses.isEmpty then ""
    else
      let items := String.join <| ins.clauses.toList.map fun c =>
        s!"<li>{renderMathHtml c false}</li>"
      s!"<ul class=\"cadmo-sidenote-clauses\">{items}</ul>"
  let leanSig :=
    (match ins.leanName? with | some nm => s!"{nm} :\n" | none => "") ++ ins.leanType
  let leanDetails :=
    "<details class=\"cadmo-lean-details\"><summary>Exact Lean signature</summary>" ++
    s!"<div class=\"cadmo-lean-code\">{escapeHtml leanSig}</div></details>"
  s!"<section class=\"cadmo-inspector-card\" data-inspector-key=\"{escapeHtml ins.key}\">" ++
  s!"<div class=\"cadmo-inspector-head\"><div>" ++
  s!"<div class=\"cadmo-inspector-kicker\">{escapeHtml finalKicker}</div>" ++
  s!"<h3 class=\"cadmo-inspector-title\">{renderMathHtml ins.display false}</h3>" ++
  s!"</div></div>{bodyHtml}{docHtml}{clausesHtml}{leanDetails}</section>"

/-- Project proof nodes according to `ViewMode`: in `paper` mode, transparent `isWrapper`
steps with children are stepped through so Level 0 lands on genuine mathematical joints. -/
partial def projectNodes (mode : ViewMode) (nodes : Array ProofNode) : Array ProofNode :=
  match mode with
  | .auditor => nodes
  | .paper =>
      nodes.foldl (init := #[]) fun acc n =>
        match n with
        | .step _ _ children _ _ _ true _ =>
            if children.isEmpty then acc.push n
            else acc ++ projectNodes mode children
        | _ => acc.push n

/-- Render a recursive `ProofNode` in ETH CADMO style with quiet `⊕`/`⊖` disclosure controls. -/
partial def renderProofNodeHtml (doc : Document) (mode : ViewMode := .paper) : ProofNode → String
  | .flowNote id text _ =>
      s!"<aside class=\"cadmo-flow-note\" data-node-id=\"{escapeHtml id}\">" ++
      s!"<span class=\"cadmo-flow-badge\">Note</span>{escapeHtml text}</aside>"
  | .figure id caption html =>
      let cap? := if caption.isEmpty then none else some (renderInlinesHtml doc caption)
      s!"<div data-node-id=\"{escapeHtml id}\">{renderDiagramFigureHtml html cap?}</div>"
  | .routineReceipt id summary stepCount details _ =>
      let projected := projectNodes mode details
      let hasDetails := !projected.isEmpty
      let toggle :=
        if hasDetails then
          s!"<button type=\"button\" class=\"cadmo-toggle\" aria-expanded=\"false\" " ++
          s!"data-toggle-target=\"{escapeHtml id}\">⊕</button>"
        else ""
      let childrenHtml :=
        if hasDetails then
          let inner := String.join (projected.toList.map (renderProofNodeHtml doc mode))
          s!"<div class=\"cadmo-children\" id=\"children-{escapeHtml id}\" hidden>{inner}</div>"
        else ""
      s!"<div class=\"cadmo-node\" data-node-id=\"{escapeHtml id}\">" ++
      s!"<div class=\"cadmo-routine\">{toggle}" ++
      s!"<span class=\"cadmo-routine-chip\">{escapeHtml summary} ({stepCount} checked)</span>" ++
      s!"</div>{childrenHtml}</div>"
  | .calcChain id intro steps _ _ =>
      let introHtml :=
        if intro.isEmpty then ""
        else s!"<p class=\"cadmo-calc-intro\">{renderInlinesHtml doc intro}</p>"
      let rows := String.join <| (steps.toList.zipIdx).map fun (((st : CalcStep), ch), idx) =>
        let projected := projectNodes mode ch
        let sid := s!"{id}-s{idx}"
        let lhs := if idx == 0 then renderMathHtml st.lhsLatex false else ""
        let toggle :=
          if projected.isEmpty then ""
          else
            s!"<button type=\"button\" class=\"cadmo-toggle\" aria-expanded=\"false\" " ++
            s!"data-toggle-target=\"{escapeHtml sid}\">⊕</button> "
        let mainRow :=
          s!"<tr><td class=\"cadmo-calc-lhs\">{lhs}</td>" ++
          s!"<td class=\"cadmo-calc-rel\">{renderMathHtml st.relationLatex false}</td>" ++
          s!"<td class=\"cadmo-calc-rhs\">{renderMathHtml st.rhsLatex false}</td>" ++
          s!"<td class=\"cadmo-calc-reason\">{toggle}{renderInlinesHtml doc st.reason}</td></tr>"
        let expandRow :=
          if projected.isEmpty then ""
          else
            let diag := match st.diagramHtml? with
              | some d => renderDiagramFigureHtml d
              | none => ""
            let sub := String.join (projected.toList.map (renderProofNodeHtml doc mode))
            s!"<tr class=\"cadmo-calc-expand-row\" id=\"children-{escapeHtml sid}\" hidden>" ++
            s!"<td colspan=\"4\">{diag}<div class=\"cadmo-children\">{sub}</div></td></tr>"
        mainRow ++ expandRow
      s!"<div class=\"cadmo-calc\" data-node-id=\"{escapeHtml id}\">{introHtml}" ++
      s!"<table class=\"cadmo-calc-table\"><tbody>{rows}</tbody></table></div>"
  | .step id content children goal? diagramHtml? originDecl? isWrapper defaultExpanded =>
      let projected := projectNodes mode children
      let hasChildren := !projected.isEmpty
      let expandedAttr := if defaultExpanded then "true" else "false"
      let glyph := if defaultExpanded then "⊖" else "⊕"
      let toggle :=
        if hasChildren then
          s!"<button type=\"button\" class=\"cadmo-toggle\" aria-expanded=\"{expandedAttr}\" " ++
          s!"data-toggle-target=\"{escapeHtml id}\">{glyph}</button>"
        else
          "<span class=\"cadmo-toggle-spacer\" aria-hidden=\"true\"></span>"
      let wrapperTag :=
        if isWrapper then "<span class=\"cadmo-wrapper-tag\">wrapper</span>" else ""
      let originTag := match originDecl? with
        | some d => s!"<span class=\"cadmo-origin-tag\">{escapeHtml d}</span>"
        | none => ""
      let goalBtn := match goal? with
        | some _ => "<button type=\"button\" class=\"cadmo-goal-btn\" title=\"Inspect checked Lean goal state\">⊢</button>"
        | none => ""
      let diagHtml := match diagramHtml? with
        | some d => renderDiagramFigureHtml d
        | none => ""
      let childrenHtml :=
        if hasChildren then
          let hiddenAttr := if defaultExpanded then "" else " hidden"
          let inner := String.join (projected.toList.map (renderProofNodeHtml doc mode))
          s!"<div class=\"cadmo-children\" id=\"children-{escapeHtml id}\"{hiddenAttr}>{inner}</div>"
        else ""
      let cls := if isWrapper then "cadmo-node is-wrapper" else "cadmo-node"
      s!"<div class=\"{cls}\" data-node-id=\"{escapeHtml id}\">" ++
      s!"<div class=\"cadmo-node-row\">{toggle}" ++
      s!"<div class=\"cadmo-node-body\">{renderInlinesHtml doc content}{wrapperTag}{originTag}{goalBtn}</div>" ++
      s!"</div>{diagHtml}{childrenHtml}</div>"

/-- Render one `Entry` (Theorem, Lemma, Proposition, Definition) in ETH CADMO style. -/
def renderEntryHtml (doc : Document) (entry : Entry) (mode : ViewMode := .paper) : String :=
  let titleSpan := match entry.title? with
    | some t => s!"<span class=\"cadmo-entry-title\">({escapeHtml t}).</span>"
    | none => ""
  let axiomClass := if entry.axioms.hasSorry then "cadmo-axiom-pill has-sorry" else "cadmo-axiom-pill"
  let axiomLabel :=
    if entry.axioms.hasSorry then "⚠ sorry"
    else s!"✓ {entry.axioms.axioms.size} axioms"
  let ambientHtml := match entry.ambient? with
    | some amb =>
        s!"<div class=\"cadmo-ambient\"><span class=\"cadmo-ambient-label\">Setting.</span>" ++
        s!"{renderInlinesHtml doc amb.summary}</div>"
    | none => ""
  let statementHtml := String.join <| entry.statement.toList.map fun para =>
    s!"<p>{renderInlinesHtml doc para}</p>"
  let diagramHtml := match entry.diagramHtml? with
    | some d => renderDiagramFigureHtml d
    | none => ""
  let projectedProof := projectNodes mode entry.proof
  let proofHtml :=
    if projectedProof.isEmpty then ""
    else
      let nodesHtml := String.join (projectedProof.toList.map (renderProofNodeHtml doc mode))
      "<section class=\"cadmo-proof\"><span class=\"cadmo-proof-lead\">Proof.</span>" ++
      nodesHtml ++
      "<div class=\"cadmo-qed\" aria-hidden=\"true\">□</div></section>"
  let sectionHtml := match entry.sectionTitle? with
    | some st =>
        let secIntro := match entry.sectionIntro? with
          | some si => s!"<p class=\"cadmo-section-intro\">{escapeHtml si}</p>"
          | none => ""
        let secCtx := match entry.sectionContext? with
          | some sc =>
              let paras := String.join <| sc.paragraphs.toList.map fun p =>
                s!"<p>{renderInlinesHtml doc p}</p>"
              s!"<div class=\"cadmo-section-context\" id=\"{escapeHtml sc.sectionId}-context\">" ++
              s!"<span class=\"cadmo-section-context-label\">Section Context.</span>{paras}</div>"
          | none => ""
        let secNumHtml := match entry.sectionContext? with
          | some sc => s!"<span class=\"cadmo-section-num\">{sc.sectionNumber}.</span>"
          | none => ""
        "<div class=\"cadmo-section-head\">" ++
        s!"<h2 class=\"cadmo-section-title\">{secNumHtml}{escapeHtml st}</h2>" ++
        s!"{secIntro}{secCtx}</div>"
    | none => ""
  s!"{sectionHtml}<article class=\"cadmo-entry\" id=\"decl-{escapeHtml entry.declaration}\">" ++
  s!"<header class=\"cadmo-entry-head\">" ++
  s!"<h2 class=\"cadmo-entry-heading\"><span class=\"cadmo-entry-kind\">{escapeHtml entry.header}</span>{titleSpan}</h2>" ++
  s!"<div class=\"cadmo-entry-meta\"><span class=\"{axiomClass}\">{axiomLabel}</span></div>" ++
  s!"</header>{ambientHtml}" ++
  s!"<div class=\"cadmo-statement\">{statementHtml}</div>" ++
  s!"{diagramHtml}{proofHtml}</article>"

/-- Render a complete static ETH CADMO `<main>` + `<aside>` document body. -/
def renderDocumentBodyHtml (doc : Document) (mode : ViewMode := doc.defaultMode) : String :=
  let subtitleHtml := match doc.subtitle? with
    | some s => s!"<p class=\"cadmo-doc-subtitle\">{escapeHtml s}</p>"
    | none => ""
  let entriesHtml := String.join (doc.entries.toList.map (renderEntryHtml doc · mode))
  let inspectorsHtml := String.join (doc.inspectors.toList.map renderInspectorCardHtml)
  "<div class=\"cadmo-shell\"><main class=\"cadmo-main\">" ++
  "<header class=\"cadmo-doc-header\">" ++
  "<div class=\"cadmo-kicker\">Constructive Cryptography · Verso Informalization</div>" ++
  s!"<h1 class=\"cadmo-doc-title\">{escapeHtml doc.title}</h1>{subtitleHtml}</header>" ++
  entriesHtml ++
  "</main>" ++
  s!"<aside class=\"cadmo-margin\" aria-label=\"Symbol & Definition Index\">{inspectorsHtml}</aside>" ++
  "</div>"

/-- Render a Verso literate `.lean` chapter stub referencing a canonical `Document` JSON.
Authors can extend this stub with narrative Verso sections while every theorem statement,
equation, diagram, and recursive proof step stays mechanically synced with the JSON IR. -/
def renderVersoChapterStub (doc : Document) (jsonRelPath : String) (moduleName : String := "Chapter") : String :=
  let subtitleComment := match doc.subtitle? with
    | some s => s!"\n> *{s}*\n"
    | none => ""
  let entryBlocks := String.join <| doc.entries.toList.map fun (e : Entry) =>
    let label := match e.title? with
      | some t => s!"{e.header} ({t})"
      | none => s!"{e.header}: {e.declaration}"
    let axNote :=
      if e.axioms.hasSorry then "WARNING: contains sorryAx"
      else s!"axioms: {", ".intercalate e.axioms.axioms.toList}"
    s!"\n## {label}\n\n" ++
    s!"-- Checked declaration: `{e.declaration}` ({axNote})\n" ++
    s!"-- Verso directive (when Verso Manual/Blog backend is enabled):\n" ++
    s!":::cadmoEntry \"{jsonRelPath}\" \"{e.declaration}\"\n:::\n"
  s!"/-\n" ++
  s!"Generated Verso chapter stub for: {doc.title}\n" ++
  s!"Canonical IR source: {jsonRelPath}\n" ++
  s!"-/\n" ++
  s!"import VersoInformalization.Schema\n" ++
  s!"import VersoInformalization.CadmoBlocks\n\n" ++
  s!"namespace VersoChapters.{moduleName}\n\n" ++
  s!"/-- Path to the canonical checked `Explanation.Document` JSON for this chapter. -/\n" ++
  s!"def documentJsonPath : System.FilePath := \"{jsonRelPath}\"\n\n" ++
  s!"/-- Render this chapter's ETH CADMO HTML body directly from the canonical JSON. -/\n" ++
  s!"def renderChapterBody : IO String := do\n" ++
  s!"  let doc ← VersoInformalization.Schema.loadDocumentFile documentJsonPath\n" ++
  s!"  return VersoInformalization.CadmoBlocks.renderDocumentBodyHtml doc\n\n" ++
  s!"/-!\n" ++
  s!"# {doc.title}\n" ++
  subtitleComment ++
  entryBlocks ++
  s!"-/\n\n" ++
  s!"end VersoChapters.{moduleName}\n"

end VersoInformalization.CadmoBlocks
