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
    |>.replace "\\left(" "("
    |>.replace "\\right)" ")"
    |>.replace "\\left[" "["
    |>.replace "\\right]" "]"
    |>.replace "^{-}" "⁻"
    |>.replace "\\," " "
    |>.replace "\\;" " "
    |>.replace "\\!" ""
    |>.replace "\\_" "_"

private def takeScriptGroup (cs : List Char) (depth : Nat) (inner : List Char) :
    Option (List Char × List Char) :=
  match cs with
  | [] => none
  | '{' :: more => takeScriptGroup more (depth + 1) ('{' :: inner)
  | '}' :: more =>
      if depth == 0 then some (inner.reverse, more)
      else takeScriptGroup more (depth - 1) ('}' :: inner)
  | x :: more => takeScriptGroup more depth (x :: inner)

private partial def convertScriptGroupsGo (chars : List Char) (acc : List Char) : List Char :=
  match chars with
  | [] => acc
  | c :: '{' :: rest =>
      if c == '^' || c == '_' then
        let tag := if c == '^' then "sup" else "sub"
        match takeScriptGroup rest 0 [] with
        | some (inner, tail) =>
            let openTag := s!"<{tag}>".toList.reverse
            let closeTag := s!"</{tag}>".toList.reverse
            let renderedInner := (convertScriptGroupsGo inner []).reverse
            convertScriptGroupsGo tail (closeTag ++ renderedInner ++ openTag ++ acc)
        | none => convertScriptGroupsGo ('{' :: rest) (c :: acc)
      else
        convertScriptGroupsGo ('{' :: rest) (c :: acc)
  | c :: rest => convertScriptGroupsGo rest (c :: acc)

/-- Convert simple TeX `^{...}` / `_{...}` groups in already-escaped text into HTML `<sup>`/`<sub>`
tags for crisp fallback math rendering before JS hydration. -/
private def convertScriptGroupsHtml (escaped : String) : String :=
  String.ofList (convertScriptGroupsGo escaped.toList []).reverse

/-- Render a math span (`displayMode = false`) or display block (`displayMode = true`). -/
def renderMathHtml (latex : String) (displayMode : Bool := false) (dataKey? : Option String := none) : String :=
  let cls := if displayMode then "cadmo-display-math" else "cadmo-math"
  let tag := if displayMode then "div" else "span"
  let body := convertScriptGroupsHtml (escapeHtml (prettyFallbackMath latex))
  let keyAttr := match dataKey? with
    | some k => s!" data-cadmo-key=\"{escapeHtml k}\""
    | none => ""
  s!"<{tag} class=\"{cls}\" data-latex=\"{escapeHtml latex}\"{keyAttr}>{body}</{tag}>"

private def trustClassAttr? (mode : ViewMode) : Option ProseTrust → Option (String × String × String)
  | none => none
  | some .intuitionGloss =>
      let title := if mode == .auditor then "Authorial gloss (intuition)" else ""
      some ("cadmo-trust-gloss", "intuitionGloss", title)
  | some .kernelFormula =>
      let title := if mode == .auditor then "Kernel-verified formula" else ""
      some ("cadmo-trust-kernel", "kernelFormula", title)
  | some .kernelProvedClaim =>
      let title := if mode == .auditor then "Kernel-verified claim" else ""
      some ("cadmo-trust-kernel", "kernelProvedClaim", title)
  | some .typedRef =>
      let title := if mode == .auditor then "Kernel-verified typed reference" else ""
      some ("cadmo-trust-kernel", "typedRef", title)

private def wrapTrustHtml (mode : ViewMode) (trust? : Option ProseTrust) (inner : String) : String :=
  match trustClassAttr? mode trust? with
  | none => inner
  | some (cls, tag, title) =>
      let titleAttr := if title.isEmpty then "" else s!" title=\"{escapeHtml title}\""
      s!"<span class=\"{cls}\" data-trust=\"{tag}\"{titleAttr}>{inner}</span>"

/-- Render a single `Inline` element. Underlined `symbol` buttons bind to `SymbolInspector` by key. -/
def renderInlineHtml (doc : Document) (mode : ViewMode := .paper) : Inline → String
  | .text value trust? => wrapTrustHtml mode trust? (escapeHtml value)
  | .emph value trust? => wrapTrustHtml mode trust? s!"<em>{escapeHtml value}</em>"
  | .inlineMath latex trust? dataKey? =>
      wrapTrustHtml mode trust? (renderMathHtml latex false dataKey?)
  | .displayMath latex punct trust? dataKey? =>
      let full := if punct.isEmpty then latex else s!"{latex}\\,{punct}"
      wrapTrustHtml mode trust? (renderMathHtml full true dataKey?)
  | .symbol key display isMath trust? dataKey? =>
      let pinnedKey := dataKey?.getD key
      let titleAttr := match doc.findInspector? pinnedKey <|> doc.findInspector? key with
        | some _ => s!"Inspect {display}"
        | none => display
      let inner := if isMath then renderMathHtml display false none else escapeHtml display
      let trustCls := match trustClassAttr? mode trust? with
        | some (cls, _, _) => s!" {cls}"
        | none => ""
      let trustAttr := match trustClassAttr? mode trust? with
        | some (_, tag, _) => s!" data-trust=\"{tag}\""
        | none => ""
      s!"<button type=\"button\" class=\"cadmo-sym{trustCls}\" data-symbol-key=\"{escapeHtml key}\" " ++
      s!"data-cadmo-key=\"{escapeHtml pinnedKey}\"{trustAttr} " ++
      s!"aria-pressed=\"false\" title=\"{escapeHtml titleAttr}\">{inner}</button>"
  | .citation label detail trust? =>
      wrapTrustHtml mode trust?
        s!"<span class=\"cadmo-citation\" title=\"{escapeHtml detail}\">[{escapeHtml label}]</span>"

/-- Render an array of `Inline` elements. -/
def renderInlinesHtml (doc : Document) (xs : Array Inline) (mode : ViewMode := .paper) : String :=
  String.join (xs.toList.map (renderInlineHtml doc mode))

/-- Parse inline/display math delimiters (`$...$`, `\(...\)`) inside prose strings for static HTML. -/
partial def renderMixedTextHtml (s : String) : String :=
  let chars := s.toList
  let arr := chars.toArray
  let n := arr.size
  let rec findClose (idx : Nat) (c1 : Char) (c2? : Option Char) (acc : List Char) : Option (String × Nat) :=
    if h : idx < n then
      let c := arr[idx]
      if c == '\\' && idx + 1 < n && c2?.isNone && arr[idx + 1]! == '$' then
        findClose (idx + 2) c1 c2? ('$' :: '\\' :: acc)
      else if c2?.isSome && c == c1 && idx + 1 < n && arr[idx + 1]! == c2?.get! then
        some ((String.ofList acc.reverse).trimAscii.toString, idx + 2)
      else if c2?.isNone && c == c1 then
        some ((String.ofList acc.reverse).trimAscii.toString, idx + 1)
      else
        findClose (idx + 1) c1 c2? (c :: acc)
    else none
  let rec go (i : Nat) (buf : List Char) (out : String) : String :=
    if h : i < n then
      let c := arr[i]
      if c == '\\' && i + 1 < n then
        let nxt := arr[i + 1]!
        if nxt == '$' then
          go (i + 2) ('$' :: buf) out
        else if nxt == '(' then
          match findClose (i + 2) '\\' (some ')') [] with
          | some (m, j) => go j [] (out ++ escapeHtml (String.ofList buf.reverse) ++ renderMathHtml m false)
          | none => go (i + 1) (c :: buf) out
        else
          go (i + 1) (c :: buf) out
      else if c == '$' then
        if i + 1 < n && arr[i + 1]! == '$' then
          match findClose (i + 2) '$' (some '$') [] with
          | some (m, j) => go j [] (out ++ escapeHtml (String.ofList buf.reverse) ++ renderMathHtml m true)
          | none => go (i + 1) (c :: buf) out
        else
          match findClose (i + 1) '$' none [] with
          | some (m, j) => go j [] (out ++ escapeHtml (String.ofList buf.reverse) ++ renderMathHtml m false)
          | none => go (i + 1) (c :: buf) out
      else
        go (i + 1) (c :: buf) out
    else
      out ++ escapeHtml (String.ofList buf.reverse)
  go 0 [] ""

private def matchesSubArray (arr : Array Char) (idx : Nat) (pat : Array Char) : Bool :=
  if idx + pat.size > arr.size then false
  else Id.run do
    for k in [:pat.size] do
      if arr[idx + k]! != pat[k]! then
        return false
    return true

/-- Strip any residual `<style>...</style>` blocks defensively from embedded diagram HTML. -/
def stripEmbeddedStyles (s : String) : String :=
  let arr := s.toList.toArray
  let lowerArr := arr.map Char.toLower
  let openPat := "<style".toList.toArray
  let closePat := "</style>".toList.toArray
  let n := arr.size
  Id.run do
    let mut i := 0
    let mut out : List Char := []
    while i < n do
      if matchesSubArray lowerArr i openPat then
        let nextIdx := i + openPat.size
        let isStyleTag :=
          nextIdx >= n ||
          lowerArr[nextIdx]! == '>' ||
          lowerArr[nextIdx]!.isWhitespace
        if isStyleTag then
          let mut j := nextIdx
          let mut foundClose := false
          while j + closePat.size <= n do
            if matchesSubArray lowerArr j closePat then
              i := j + closePat.size
              foundClose := true
              break
            j := j + 1
          if !foundClose then
            break
          continue
      out := arr[i]! :: out
      i := i + 1
    return String.ofList out.reverse

/-- Render an embedded `Rendering` CC diagram container (stripping any residual `<style>` tags). -/
def renderDiagramFigureHtml (html : String) (caption? : Option String := none) : String :=
  let cleanHtml := stripEmbeddedStyles html
  let cap := match caption? with
    | some c => s!"<figcaption class=\"cadmo-figure-caption\">{c}</figcaption>"
    | none => ""
  s!"<figure class=\"cadmo-figure\"><div>{cleanHtml}</div>{cap}</figure>"

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
steps with children are stepped through so Level 0 lands on genuine mathematical joints,
and leaf `isWrapper` nodes (such as bare hypothesis passthroughs) are hidden. -/
partial def projectNodes (mode : ViewMode) (nodes : Array ProofNode) : Array ProofNode :=
  match mode with
  | .auditor => nodes
  | .paper =>
      nodes.foldl (init := #[]) fun acc n =>
        match n with
        | .step _ _ children _ _ _ true _ _ _ _ =>
            if children.isEmpty then acc
            else acc ++ projectNodes mode children
        | _ => acc.push n

/-- Filter children visible in `mode`: in `paper` mode, omit a disclosure toggle when the
visible children are empty or consist of a single `routineReceipt`. -/
def visibleChildren (mode : ViewMode) (nodes : Array ProofNode) : Array ProofNode :=
  let vis := projectNodes mode nodes
  match mode with
  | .auditor => vis
  | .paper =>
      if vis.isEmpty then #[]
      else if vis.size == 1 then
        match vis[0]! with
        | .routineReceipt .. => #[]
        | _ => vis
      else vis

/-- Render a proof node in ETH CADMO style with quiet `⊕`/`⊖` disclosure controls. -/
partial def renderProofNodeHtml (doc : Document) (mode : ViewMode := .paper) : ProofNode → String
  | .flowNote id text placement =>
      if placement == "paragraph" then
        if text.isEmpty then
          s!"<div class=\"cadmo-para-break\" data-node-id=\"{escapeHtml id}\"></div>"
        else
          s!"<p class=\"cadmo-proof-para\" data-node-id=\"{escapeHtml id}\"><span class=\"cadmo-para-heading\">{renderMixedTextHtml text}</span></p>"
      else
        s!"<aside class=\"cadmo-flow-note\" data-node-id=\"{escapeHtml id}\">" ++
        s!"<span class=\"cadmo-flow-badge\">Note</span>{renderMixedTextHtml text}</aside>"
  | .figure id caption html =>
      let cap? := if caption.isEmpty then none else some (renderInlinesHtml doc caption mode)
      s!"<div data-node-id=\"{escapeHtml id}\">{renderDiagramFigureHtml html cap?}</div>"
  | .routineReceipt id summary stepCount details _ =>
      let projected := visibleChildren mode details
      let hasDetails := !projected.isEmpty
      let toggle :=
        if hasDetails then
          s!"<button type=\"button\" class=\"cadmo-toggle\" aria-expanded=\"false\" " ++
          s!"data-toggle-target=\"{escapeHtml id}\">⊕</button>"
        else ""
      let childrenHtml :=
        if hasDetails then
          let inner := String.join (projected.toList.map (renderProofNodeHtml doc mode))
          s!"<div class=\"cadmo-children cadmo-expanded-children\" id=\"children-{escapeHtml id}\" hidden>{inner}</div>"
        else ""
      s!"<div class=\"cadmo-node\" data-node-id=\"{escapeHtml id}\">" ++
      s!"<div class=\"cadmo-routine\">" ++
      s!"<span class=\"cadmo-routine-chip\">{escapeHtml summary} ({stepCount} checked)</span>" ++
      s!"{toggle}</div>{childrenHtml}</div>"
  | .calcChain id intro steps _ _ =>
      let introHtml :=
        if intro.isEmpty then ""
        else s!"<p class=\"cadmo-calc-intro\">{renderInlinesHtml doc intro mode}</p>"
      let rows := String.join <| (steps.toList.zipIdx).map fun (((st : CalcStep), ch), idx) =>
        let projected := visibleChildren mode ch
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
          s!"<td class=\"cadmo-calc-reason\">{toggle}{renderInlinesHtml doc st.reason mode}</td></tr>"
        let expandRow :=
          if projected.isEmpty then ""
          else
            let diag := match st.diagramHtml? with
              | some d => renderDiagramFigureHtml d
              | none => ""
            let sub := String.join (projected.toList.map (renderProofNodeHtml doc mode))
            s!"<tr class=\"cadmo-calc-expand-row\" id=\"children-{escapeHtml sid}\" hidden>" ++
            s!"<td colspan=\"4\">{diag}<div class=\"cadmo-children cadmo-expanded-children\">{sub}</div></td></tr>"
        mainRow ++ expandRow
      s!"<div class=\"cadmo-calc\" data-node-id=\"{escapeHtml id}\">{introHtml}" ++
      s!"<table class=\"cadmo-calc-table\"><tbody>{rows}</tbody></table></div>"
  | .step id content children goal? diagramHtml? originDecl? isWrapper defaultExpanded
      startsParagraph leadHeading? trust? =>
      let projected := visibleChildren mode children
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
          s!"<div class=\"cadmo-children cadmo-expanded-children\" id=\"children-{escapeHtml id}\"{hiddenAttr}>{inner}</div>"
        else ""
      let paraBreak := if startsParagraph then "<div class=\"cadmo-para-break\"></div>" else ""
      let leadHeadHtml := match leadHeading? with
        | some hd =>
            let trimmed := hd.trimAscii.toString
            if trimmed.isEmpty then ""
            else s!"<span class=\"cadmo-para-heading\">{renderMixedTextHtml (trimmed ++ " ")}</span>"
        | none => ""
      let trustCls := match trustClassAttr? mode trust? with
        | some (c, _, _) => s!" {c}"
        | none => ""
      let trustAttr := match trustClassAttr? mode trust? with
        | some (_, tag, tTitle) =>
            let tAttr := if tTitle.isEmpty then "" else s!" title=\"{escapeHtml tTitle}\""
            s!" data-trust=\"{tag}\"{tAttr}"
        | none => ""
      let trustBadge :=
        if trust? == some .intuitionGloss then "<span class=\"cadmo-trust-badge\">[gloss]</span>" else ""
      let cls := (if isWrapper then "cadmo-node is-wrapper" else "cadmo-node") ++ trustCls
      s!"{paraBreak}<div class=\"{cls}\" data-node-id=\"{escapeHtml id}\"{trustAttr}>" ++
      s!"<div class=\"cadmo-node-row\">{toggle}" ++
      s!"<div class=\"cadmo-node-body\">{leadHeadHtml}{renderInlinesHtml doc content mode}{trustBadge}{wrapperTag}{originTag}{goalBtn}</div>" ++
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
        let rawTxt := String.join (amb.summary.toList.map fun (inl : Schema.Inline) =>
          match inl with
          | .text s _ | .emph s _ => s
          | .inlineMath s _ _ | .displayMath s _ _ _ => s
          | .symbol _ d _ _ _ => d
          | .citation l _ _ => l)
        if (rawTxt.splitOn "We work in the Constructive Cryptography framework").length > 1 then ""
        else
          s!"<div class=\"cadmo-ambient\"><span class=\"cadmo-ambient-label\">Setting.</span>" ++
          s!"{renderInlinesHtml doc amb.summary mode}</div>"
    | none => ""
  let statementHtml := String.join <| entry.statement.toList.map fun para =>
    s!"<p>{renderInlinesHtml doc para mode}</p>"
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
                s!"<p>{renderInlinesHtml doc p mode}</p>"
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
