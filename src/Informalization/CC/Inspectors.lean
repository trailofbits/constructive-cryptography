/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Rendering.CCWidget
import Rendering.Export
import Rendering.Widget
import Rendering.Instances
import Rendering.Proofs
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.ProofGraph
import Informalization.Core.Overlay
import Informalization.Core.Routine
import Informalization.Core.Explanation
import Informalization.CC.Registry
import Informalization.CC.Ontology

/-!
# Type-Aware CC Symbol Inspectors & Live `Rendering` Diagram Hooks

Connects `Rendering`'s deterministic box-and-wire diagrams, interface port tables,
and parser-recorded DSL pseudocode cards into `Informalization.Core.ProofGraph`:

1. **`ccDiagramHook`** (`ProofGraph.registerDiagramHook`): projects CC expressions,
   judgments, and proof witnesses via `CCWidget.viewExprCore` / `CCWidget.renderJudgment` /
   `CCWidget.panel` / `CCWidget.staticHtml` into static HTML embedded directly inside
   `Entry.diagramHtml?` and `ProofNode.diagramHtml?`.
2. **`collectCCInspectors`** (`ProofGraph.registerInspectorCollector`): inspects every
   named symbol (free variables and project constants) appearing in a theorem statement
   and dispatches by type to the best human-first `SymbolInspector`:
   * **`Interface`** → `InspectorKind.interfaceTable` (Port / Query / Reply / Domain via
     `CCWidget.interfacePorts` and `CCWidget.interfaceProjections`);
   * **DSL `converter` / `system`** → `InspectorKind.dslPseudocode` (exact parser-recorded
     slices from `SystemAlgebra.DSL.sourceDocuments`);
   * **CC assembly** → `InspectorKind.ccDiagram` (static `Rendering` box-and-wire HTML);
   * **`HCoefficient` / `Implication` witness** → `InspectorKind.witnessCard`;
   * **Project mathematical definition** → ambient-suppressed `InspectorKind.mathDefinition`;
   * **Named parameter** → `InspectorKind.parameter`.
-/

namespace Informalization.CC.Inspectors

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.ProofGraph
open Informalization.Core.Overlay
open Informalization.Core.Routine
open Informalization.Core.Explanation
open Informalization.Core.Presentation
open Informalization.CC.Registry

cc_diagram_substitution
  ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin 1 0 2 "≃"
cc_diagram_whisker_right CategoryTheory.MonoidalCategoryStruct.whiskerRight 1 0
cc_diagram_whisker_left CategoryTheory.MonoidalCategoryStruct.whiskerLeft 3 0

/-! ## 1. Static Box-and-Wire Diagram Hook (`Rendering` Integration) -/

/-- Strip embedded `<style>...</style>` blocks from `CCWidget.staticHtml` output (since `Html.lean`
hoists the shared CC stylesheet once into `<head>`). Uses Unicode-safe character arrays. -/
private def stripEmbeddedStyles (html : String) : String := Id.run do
  let arr := html.toList.toArray
  let lower := arr.map Char.toLower
  let n := arr.size
  let matchAt (pos : Nat) (pat : Array Char) : Bool := Id.run do
    if pos + pat.size > n then return false
    for j in [:pat.size] do
      if lower[pos + j]! != pat[j]! then return false
    return true
  let openTag := "<style".toList.toArray
  let closeTag := "</style>".toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  while i < n do
    if matchAt i openTag then
      let nxt := if i + 6 < n then some lower[i + 6]! else none
      let isTagStart := match nxt with
        | some '>' | some ' ' | some '\t' | some '\n' | some '\r' => true
        | _ => false
      if isTagStart then
        let mut j := i + 6
        while j < n && !matchAt j closeTag do
          j := j + 1
        if j < n then
          i := j + closeTag.size
          continue
    out := out.push arr[i]!
    i := i + 1
  return String.ofList out.toList

/-- Convert a LaTeX alias from `SymbolTable` into readable HTML/MathML-safe Unicode text
so exported box-and-wire diagrams never leak raw backslashes or TeX commands. -/
private def latexToDiagramUnicode (s : String) : String := Id.run do
  let mut out := s
  -- Preserve escaped literal braces `\{` and `\}` during TeX group stripping.
  out := out.replace "\\{" "\uE001"
  out := out.replace "\\}" "\uE002"
  for (pat, rep) in [
    ("\\llbracket", "⟦"), ("\\rrbracket", "⟧"),
    ("\\langle", "⟨"), ("\\rangle", "⟩"),
    ("\\mathcal{U}", "𝒰"), ("\\mathbb{N}", "ℕ"), ("\\mathbb{Z}", "ℤ"),
    ("\\mathbb{R}", "ℝ"), ("\\mathbb{B}", "𝔹"), ("\\mathbb{1}", "𝟙"), ("\\mathbf{1}", "𝟙"),
    ("\\$", "$"), ("\\_", "_"), ("\\%", "%"), ("\\&", "&"),
    ("\\!", ""), ("\\,", ""), ("\\;", " "), ("\\:", " "),
    ("\\quad", " "), ("\\qquad", " "),
    ("\\left", ""), ("\\right", ""), ("\\mathbin", "")
  ] do
    out := out.replace pat rep
  let rec stripFracOnce (chars : List Char) : Option String :=
    let rec findFrac : List Char → List Char → Option String
      | acc, '\\' :: 'f' :: 'r' :: 'a' :: 'c' :: '{' :: rest =>
        let rec readGroup (depth : Nat) (grp : List Char) : List Char → Option (String × List Char)
          | [] => none
          | '}' :: rs =>
            if depth == 0 then some (String.ofList grp.reverse, rs)
            else readGroup (depth - 1) ('}' :: grp) rs
          | '{' :: rs => readGroup (depth + 1) ('{' :: grp) rs
          | c :: rs => readGroup depth (c :: grp) rs
        match readGroup 0 [] rest with
        | some (num, '{' :: afterNum) =>
          match readGroup 0 [] afterNum with
          | some (den, tail) =>
            some (String.ofList acc.reverse ++ "(" ++ num ++ ")/(" ++ den ++ ")" ++ String.ofList tail)
          | none => none
        | _ => none
      | acc, c :: rs => findFrac (c :: acc) rs
      | _, [] => none
    findFrac [] chars
  for _ in [:8] do
    match stripFracOnce out.toList with
    | some next => out := next
    | none => break
  for w in [
    "\\operatorname{", "\\mathrm{", "\\mathsf{", "\\mathbf{",
    "\\mathit{", "\\mathcal{", "\\boldsymbol{", "\\mathbb{", "\\text{"
  ] do
    out := out.replace w ""
  for (pat, rep) in [
    ("\\varepsilon", "ε"), ("\\epsilon", "ε"),
    ("\\varphi", "φ"), ("\\phi", "φ"), ("\\Phi", "Φ"),
    ("\\psi", "ψ"), ("\\Psi", "Ψ"),
    ("\\pi", "π"), ("\\Pi", "Π"),
    ("\\rho", "ρ"), ("\\sigma", "σ"), ("\\Sigma", "Σ"),
    ("\\delta", "δ"), ("\\Delta", "Δ"),
    ("\\alpha", "α"), ("\\beta", "β"),
    ("\\gamma", "γ"), ("\\Gamma", "Γ"),
    ("\\lambda", "λ"), ("\\Lambda", "Λ"),
    ("\\tau", "τ"), ("\\eta", "η"),
    ("\\theta", "θ"), ("\\Theta", "Θ"),
    ("\\mu", "μ"), ("\\nu", "ν"), ("\\kappa", "κ"),
    ("\\omega", "ω"), ("\\Omega", "Ω"),
    ("\\chi", "χ"), ("\\xi", "ξ"), ("\\zeta", "ζ"),
    ("\\ell", "ℓ"), ("\\infty", "∞"),
    ("\\pm", "±"), ("\\mp", "∓"), ("\\perp", "⊥"), ("\\top", "⊤"),
    ("\\times", "×"), ("\\cdot", "·"), ("\\circ", "∘"), ("\\bullet", "•"),
    ("\\otimes", "⊗"), ("\\parallel", "∥"), ("\\Vert", "∥"), ("\\mid", "|"),
    ("\\longrightarrow", "⟶"), ("\\rightarrow", "→"), ("\\to", "→"), ("\\mapsto", "↦"),
    ("\\simeq", "≃"), ("\\approx", "≈"), ("\\equiv", "≡"),
    ("\\leq", "≤"), ("\\le", "≤"), ("\\geq", "≥"), ("\\ge", "≥"), ("\\neq", "≠"), ("\\ne", "≠"),
    ("\\notin", "∉"), ("\\in", "∈"), ("\\subseteq", "⊆"),
    ("\\cup", "∪"), ("\\cap", "∩"), ("\\emptyset", "∅"),
    ("\\wedge", "∧"), ("\\vee", "∨"), ("\\neg", "¬"),
    ("\\forall", "∀"), ("\\exists", "∃"),
    ("\\sum", "∑"), ("\\prod", "∏")
  ] do
    out := out.replace pat rep
  out := out.replace "{" ""
  out := out.replace "}" ""
  out := out.replace "\uE001" "{"
  out := out.replace "\uE002" "}"
  while (out.splitOn "  ").length > 1 do
    out := out.replace "  " " "
  return out.trimAscii.toString

private def toDiagramAliases (tbl : SymbolTable) : CCWidget.DiagramAliases := {
  active := true
  constAliases := tbl.constAliases.toList.foldl (init := {}) fun acc (k, v) =>
    acc.insert k (latexToDiagramUnicode v)
  shortAliases := tbl.shortAliases.toList.foldl (init := {}) fun acc (k, v) =>
    acc.insert k (latexToDiagramUnicode v)
  binderAliases := tbl.binderAliases.toList.foldl (init := {}) fun acc (k, v) =>
    acc.insert k (latexToDiagramUnicode v)
  exprAliases := tbl.exprAliases.map fun (pat, v) => (pat, latexToDiagramUnicode v)
  hiddenArgs := tbl.hiddenArgs
  zeroArgConsts := tbl.zeroArgConsts
  constTemplates := tbl.constTemplates.toList.foldl (init := {}) fun acc (k, v) =>
    acc.insert k (latexToDiagramUnicode v)
}

private def symbolTableFingerprint (tbl : SymbolTable) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for (k, v) in tbl.constAliases.toList do
    h := mixHash h (mixHash (hash k) (hash v))
  for (k, v) in tbl.shortAliases.toList do
    h := mixHash h (mixHash (hash k) (hash v))
  for (k, v) in tbl.binderAliases.toList do
    h := mixHash h (mixHash (hash k) (hash v))
  for (pat, v) in tbl.exprAliases do
    h := mixHash h (mixHash (hash pat) (hash v))
  for (k, idxs) in tbl.hiddenArgs.toList do
    h := mixHash h (mixHash (hash k) (hash idxs))
  for n in tbl.zeroArgConsts.toList do
    h := mixHash h (hash n)
  for (k, v) in tbl.constTemplates.toList do
    h := mixHash h (mixHash (hash k) (hash v))
  return h

/-- Render a checked Lean expression or CC judgment to self-contained static HTML using
`Rendering`'s deterministic projection (`CCWidget.viewExprCore`, `CCWidget.renderJudgment`,
`CCWidget.panel`, `CCWidget.staticHtml`). Returns `none` for non-CC expressions. -/
private initialize diagHtmlCacheRef : IO.Ref (Std.HashMap (UInt64 × Expr) (Option String)) ← IO.mkRef {}

private def withDiagHeartbeats {α : Type} (maxUserHB : Nat := 2500)
    (x : MetaM (Option α)) : MetaM (Option α) := do
  try
    Lean.Core.withCurrHeartbeats <|
      withTheReader Core.Context (fun c =>
        let limit := maxUserHB * 1000
        { c with maxHeartbeats := if c.maxHeartbeats == 0 then 0 else max c.maxHeartbeats limit }) do
        controlAt CoreM fun runInBase =>
          Lean.Core.tryCatchRuntimeEx (runInBase x) fun ex =>
            runInBase do
              if ex.isMaxHeartbeat then return none
              else throw ex
  catch _ =>
    return none

private def isPureMathStdNamespace (n : Name) : Bool :=
  let root := n.getRoot.toString
  root == "Init" || root == "Lean" || root == "Std" || root == "Batteries" ||
  root == "Mathlib" || root == "Core" || root == "Logic" ||
  root == "Nat" || root == "Int" || root == "Bool" || root == "Prop" ||
  root == "Real" || root == "NNReal" || root == "ENNReal" ||
  root == "Fin" || root == "Finset" || root == "Set" || root == "List" ||
  root == "Option" || root == "Prod" || root == "Sigma" || root == "Subtype" ||
  root == "Eq" || root == "LE" || root == "LT" || root == "GE" || root == "GT" ||
  root == "And" || root == "Or" || root == "Not" || root == "Iff" ||
  root == "Exists" || root == "True" || root == "False" ||
  root == "Decidable" || root == "ite" || root == "dite" || root == "Classical" ||
  root == "OfNat" || root == "HAdd" || root == "HSub" || root == "HMul" ||
  root == "HDiv" || root == "HPow" || root == "HMod" ||
  root == "Add" || root == "Mul" || root == "Sub" || root == "Div" ||
  root == "Mod" || root == "Neg" || root == "Inv" || root == "SMul" || root == "HSMul"

private def exprMaybeHasCCDiagram (e : Expr) : Bool :=
  e.hasFVar || e.foldConsts false fun n acc => acc || !isPureMathStdNamespace n

def renderCCDiagramHtml? (tbl : SymbolTable := {}) (e : Expr) : MetaM (Option String) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasSorry || e.hasLevelMVar then
    return none
  if !exprMaybeHasCCDiagram e then
    return none
  let fp := symbolTableFingerprint tbl
  let cacheKey := (fp, e)
  let cache ← diagHtmlCacheRef.get
  if let some cached := cache[cacheKey]? then
    return cached
  let aliases := toDiagramAliases tbl
  let res ← CCWidget.withDiagramAliases aliases (do
    if let some (j, _) ← withDiagHeartbeats 2500 (CCWidget.viewExprCore e false) then
      let html := CCWidget.panel (CCWidget.renderJudgment j #[])
      match CCWidget.staticHtml html with
      | .ok rendered => return some (stripEmbeddedStyles rendered)
      | .error _ => pure ()
    if let some viewHtml ← withDiagHeartbeats 2500 (CCWidget.proofViewHtml? e false) then
      match CCWidget.staticHtml (CCWidget.proofPanel viewHtml) with
      | .ok rendered => return some (stripEmbeddedStyles rendered)
      | .error _ => pure ()
    return none)
  diagHtmlCacheRef.modify fun m =>
    let m := if m.size ≥ 512 then {} else m
    m.insert cacheKey res
  return res

/-! ## 2. Type-Aware Symbol Inspector Builders -/

/-- Source location `(moduleName?, line?)` for a resolved constant, when recorded by Lean. -/
private def declLocation (env : Environment) (declName : Name) : MetaM (Option String × Option Nat) := do
  let mod? := (env.getModuleIdxFor? declName).map fun idx =>
    (env.header.moduleNames[idx.toNat]?.map (·.toString)).getD ""
  let mod? := mod?.bind fun s => if s.isEmpty then none else some s
  let line? ← try
    let ranges? ← Lean.findDeclarationRanges? declName
    pure (ranges?.map fun r => r.range.pos.line)
  catch _ =>
    pure none
  return (mod?, line?)

/-- Clean pretty-printed type string with macro scopes stripped. -/
private def cleanLeanTypeStr (ty : Expr) : MetaM String := do
  let ty ← normalizeForPresentation ty
  return (← ppExpr ty).pretty (width := 100)

/-- Build an `InspectorKind.interfaceTable` from `CCWidget.interfacePorts` and
`CCWidget.interfaceProjections` when `e` is an interface expression with registered schema. -/
private def buildInterfaceTable? (tbl : SymbolTable) (e : Expr) :
    MetaM (Option InspectorKind) := do
  let projections ← try CCWidget.interfaceProjections e catch _ => pure #[]
  if projections.isEmpty then
    return none
  let rawPorts ← try CCWidget.interfacePorts e catch _ => pure #[]
  let mut rows : Array PortRow := #[]
  for (portLabel, _, inputExpr, outputExpr) in rawPorts do
    let qTex ← try exprToLatex inputExpr tbl catch _ => pure (← CCWidget.typeNotation inputExpr).text
    let rTex ← try exprToLatex outputExpr tbl catch _ => pure (← CCWidget.typeNotation outputExpr).text
    rows := rows.push {
      port := portLabel
      queryLatex := qTex
      replyLatex := rTex
    }
  let mut domainLatex := ""
  for (sym, _, valExpr) in projections do
    if sym == "D" then
      domainLatex ← try CCWidget.domainNotation valExpr catch _ => exprToLatex valExpr tbl
  let budgetNote ← do
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    if fn.isConstOf interfaceQueryBudgetName && !args.isEmpty then
      let qTex ← exprToLatex args.back! tbl
      pure s!"Total query budget: \\({qTex}\\)"
    else if fn.isConstOf interfacePortBudgetName && !args.isEmpty then
      let qTex ← exprToLatex args.back! tbl
      pure s!"Per-port query budget: \\({qTex}\\)"
    else
      pure ""
  return some (.interfaceTable rows domainLatex budgetNote)

/-- Strip `.perPort` / `.typed` suffix when looking up parser-recorded DSL sources. -/
private def dslLookupName (declName : Name) : Name :=
  match declName with
  | .str p "perPort" => p
  | .str p "typed" => p
  | _ => declName

/-- Build an `InspectorKind.dslPseudocode` card from `SystemAlgebra.DSL.sourceDocuments`. -/
private def buildDslPseudocode? (env : Environment) (declName : Name) : Option InspectorKind :=
  let docs := SystemAlgebra.DSL.sourceDocuments.getState env
  let doc? := docs.find? declName <|> docs.find? (dslLookupName declName)
  match doc? with
  | none => none
  | some doc =>
      let bodyParts := doc.sections.filterMap fun sec =>
        if sec.proof then none else some (sec.header ++ sec.body)
      let body := String.intercalate "\n" bodyParts.toList |>.trimAscii.toString
      some (.dslPseudocode doc.header body doc.source)

/-- Build an `InspectorKind.witnessCard` for an `HCoefficient` or `Implication` witness type. -/
private def buildWitnessCard? (tbl : SymbolTable) (ty : Expr) : MetaM (Option InspectorKind) := do
  let ty ← normalizeForPresentation ty
  if isHCoefficientType ty then
    let args := ty.getAppArgs
    let mut rows : Array (String × String) := #[]
    if args.size ≥ 3 then
      let rTex ← exprToLatex args[args.size - 3]! tbl
      let sTex ← exprToLatex args[args.size - 2]! tbl
      let errTex ← exprToLatex args[args.size - 1]! tbl
      rows := rows.push ("Real system", s!"\\({rTex}\\)")
      rows := rows.push ("Ideal system", s!"\\({sTex}\\)")
      rows := rows.push ("Error bound", s!"\\({errTex}\\)")
    rows := rows.push ("Structure", "Sample law, real/ideal reveals, transcript classes, pointwise ratio, and expected error bound")
    return some (.witnessCard "H-coefficient witness" rows)
  if isImplicationType ty then
    let args := ty.getAppArgs
    let mut rows : Array (String × String) := #[]
    if args.size ≥ 1 then
      let usesTex ← exprToLatex args.back! tbl
      rows := rows.push ("Additional steps", s!"\\({usesTex}\\)")
    rows := rows.push ("Structure", "Counted substitution chain with exact endpoint and link equalities")
    return some (.witnessCard "Substitution chain witness" rows)
  return none

/-- Build an ambient-suppressed `InspectorKind.mathDefinition` for a project `defnInfo`. -/
private def buildMathDefinition (tbl : SymbolTable) (declName : Name) (info : DefinitionVal) :
    MetaM InspectorKind := do
  let (eqLatex, proseSummary) ←
    forallTelescope info.type fun fvars bodyTy => do
      let mut explicitParams : Array String := #[]
      for fv in fvars do
        let d ← fv.fvarId!.getDecl
        if ← isSuppressedLocalDecl d then continue
        if !d.binderInfo.isExplicit then continue
        explicitParams := explicitParams.push (← exprToLatex fv tbl)
      let desc ← describeType tbl bodyTy
      let lhsHead := formatMathIdent (shortConstName declName)
      let lhs :=
        if explicitParams.isEmpty then lhsHead
        else s!"{lhsHead}\\!\\left({String.intercalate ", " explicitParams.toList}\\right)"
      -- Instantiate the definition body with the same telescope fvars (stripping leading lambdas)
      let mut rhs := info.value
      for fv in fvars do
        match rhs.consumeMData with
        | .lam _ _ b _ => rhs := b.instantiate1 fv
        | _ => break
      let rhsTex ← exprToLatex rhs tbl
      let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
      let art := article (adj ++ desc.noun.singular)
      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
      let summary :=
        if desc.noun.singular.startsWith "element of " then
          ensurePeriod s!"Defined in {desc.noun.singular.drop 11}{acc}"
        else
          ensurePeriod s!"Defined as {art} {adj}{desc.noun.singular}{acc}"
      return (s!"{lhs} := {rhsTex}", summary)
  return .mathDefinition eqLatex proseSummary

/-- Internal Lean/category/plumbing constants that add noise rather than mathematical value
to a human reader's glossary. -/
private def isInspectorNoise (n : Name) : Bool :=
  let s := n.toString
  let leaf := shortConstName n
  leaf.startsWith "inst" ||
  leaf.startsWith "match_" ||
  ["casesOn", "below", "brecOn", "noConfusion", "noConfusionType", "binductionOn", "rec", "recOn"].contains leaf ||
  s.startsWith "CategoryTheory." ||
  s.endsWith ".toCategoryStruct" ||
  s.endsWith ".toQuiver" ||
  s.endsWith ".absorb" ||
  s.endsWith ".ClosedUnder" ||
  n == `SystemAlgebra.TypedSystem ||
  n == `SystemAlgebra.TypedConverter ||
  n == `SystemAlgebra.TypedDistinguisher ||
  n == `SystemAlgebra.TypedSystem.sample ||
  n == `SystemAlgebra.TypedSystem.ofFunction ||
  n == `SystemAlgebra.TypedSystem.ofConditional

private def isLibraryModuleRoot (root : Name) : Bool :=
  [`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `ProofWidgets].contains root

/-- Filter out Lean core, Mathlib, typeclass plumbing, and internal compiler helpers. -/
private def isLibraryConstant (env : Environment) (n : Name) : Bool :=
  if isCoreOrMathlib n || ambientTypeclassHeads.contains n || isInspectorNoise n then true
  else match env.getModuleIdxFor? n with
    | some idx =>
        match env.header.moduleNames[idx.toNat]? with
        | some modName => isLibraryModuleRoot modName.getRoot
        | none => false
    | none => false

/-- Strip fenced code blocks, markdown emphasis/backticks, and extra whitespace from docstrings,
dropping any upstream docstring containing Lean-isms flagged by the zero-leakage gate. -/
private def cleanDocString? (env : Environment) (declName : Name) : IO (Option String) := do
  let some raw ← Lean.findDocString? env declName | return none
  -- Drop fenced code blocks (```text ... ``` etc.); formal equations are already rendered via `equationLatex`
  let normalized := raw.replace "\r\n" "\n" |>.replace "\r" "\n" |>.replace "\t" " "
  let fenceParts := normalized.splitOn "```"
  let mut proseParts : Array String := #[]
  for i in [:fenceParts.length] do
    if i % 2 == 0 then
      let part := fenceParts[i]!
      proseParts := proseParts.push part
  let joined := String.intercalate " " proseParts.toList
  let cleanedChars := (joined.replace "**" "" |>.replace "`" "" |>.replace "--" "–")
  let words := (cleanedChars.replace "\n" " ").splitOn " " |>.filter (!·.isEmpty)
  let s := (String.intercalate " " words).trimAscii.toString
  -- Fix dangling `:` at end of lead-in right before stripped code block
  let s :=
    if s.endsWith ":" then (s.dropEnd 1).toString ++ "."
    else s
  if s.isEmpty then return none
  let lower := s.toLower
  let bannedCI := [
    "at interface", "whiskering", "interface(s)", "admissibility closure",
    "visible system", "user(s)", "query(s)", "resource(s)",
    "distinguishing distance", "transcript distance",
    "defined as an element of",
    "element of ennreal", "element of nnreal", "element of finset",
    "element of fin ", "element of zmod", "element of probdist",
    "element of bitstring", "element of typed", "element of distinguisher"
  ]
  if bannedCI.any (fun pat => (lower.splitOn pat).length > 1) then
    return none
  let bannedCS := [
    "_vcc_", "Exists(", "sum(univ", "Sigma(", "Subtype(",
    "Prod.fst", "Prod.snd", "BitString(", "Unit \\to", "Unit →",
    "_proof_", "self.", " => ", "fun "
  ]
  if bannedCS.any (fun pat => (s.splitOn pat).length > 1) then
    return none
  if !(auditZeroLeakage #[s]).isEmpty then
    return none
  return some s

/-- Detect compiler-generated `match_1` / `match_2` helpers inside an `Expr` in $O(\text{DAG})$ time. -/
private def containsMatchHelper (e : Expr) : Bool :=
  e.foldConsts (init := false) fun n acc =>
    acc || (shortConstName n).startsWith "match_"

/-- Fast bounded $O(\text{limit})$ DAG size check so pathological permutation tables never stall elaboration. -/
private partial def exprSizeBounded (e : Expr) (limit : Nat := 450) : Bool :=
  let rec go (cur : Expr) (st : Std.HashSet Expr × Nat) : Std.HashSet Expr × Nat :=
    if st.2 > limit || st.1.contains cur then st
    else
      let st := (st.1.insert cur, st.2 + 1)
      match cur with
      | .app f a => go a (go f st)
      | .lam _ d b _ => go b (go d st)
      | .forallE _ d b _ => go b (go d st)
      | .letE _ t v b _ => go b (go v (go t st))
      | .mdata _ inner => go inner st
      | .proj _ _ s => go s st
      | _ => st
  (go e ({}, 0)).2 ≤ limit

/-- Split conjunction chains `A ∧ B ∧ C` into individual `Expr` clauses. -/
private partial def splitAndClauses (e : Expr) : MetaM (Array Expr) := do
  let e ← normalizeForPresentation e
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``And && args.size ≥ 2 then
    return (← splitAndClauses args[args.size - 2]!) ++ (← splitAndClauses args[args.size - 1]!)
  return #[e]

/-- Unwrap `TypedSystem.sample` layers and extract clean sampling clauses `\pi \sim \mathrm{uniform}(...)`. -/
private partial def extractSampleClauses (tbl : SymbolTable) (e : Expr) :
    MetaM (Array String × Expr) := do
  let e ← normalizeForPresentation e
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf `SystemAlgebra.TypedSystem.sample && args.size ≥ 5 then
    let lawRaw := args[args.size - 3]!
    let lawClean := match lawRaw.consumeMData with
      | .letE _ _ val (.bvar 0) _ => val
      | other => other
    let lawTex ← exprToLatex lawClean tbl
    let bodyFn := args[args.size - 1]!.consumeMData
    match bodyFn with
    | .lam nm dom body bi =>
        withLocalDecl nm bi dom fun fv => do
          let varTex ← exprToLatex fv tbl
          let (restClauses, innerBody) ← extractSampleClauses tbl (body.instantiate1 fv)
          let clause := s!"\\text\{Sample } {varTex} \\sim {lawTex}"
          return (#[clause] ++ restClauses, innerBody)
    | _ =>
        return (#[s!"\\text\{Sample from } {lawTex}"], e)
  else
    return (#[], e)

/-- Unwrap `{R | P R}` (`setOf` / `Set.setOf` or lambda into `Prop`) for specification comprehensions. -/
private def unwrapSetComprehension? (tbl : SymbolTable) (e : Expr) :
    MetaM (Option (String × Array String)) := do
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let lamExpr? :=
    if fn.isConstOf `Set.setOf || fn.isConstOf `setOf then e.getAppArgs.back?
    else match e with | .lam .. => some e | _ => none
  let some (.lam nm dom body bi) := lamExpr? | return none
  withLocalDecl nm bi dom fun fv => do
    let varTex ← exprToLatex fv tbl
    let pred := body.instantiate1 fv
    let isP ← try isProp pred catch _ => pure false
    if !isP then return none
    let rawClauses ← splitAndClauses pred
    let mut renderedClauses : Array String := #[]
    for c in rawClauses do
      renderedClauses := renderedClauses.push (← exprToLatex c tbl)
    let predTex ← exprToLatex pred tbl
    let setTex := "\\left\\{ " ++ varTex ++ " \\;\\middle|\\; " ++ predTex ++ " \\right\\}"
    return some (setTex, renderedClauses)

/-- Build a concise role description and role badge for a local parameter using `Ontology.describeType`. -/
private def buildParameterRoleAndBadge (tbl : SymbolTable) (ty : Expr) :
    MetaM (String × String) := do
  let desc ← describeType tbl ty
  let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
  let art := article (adj ++ desc.noun.singular)
  let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
  let role := capitalizeFirst (ensurePeriod s!"{art} {adj}{desc.noun.singular}{acc}")
  let badge :=
    if ["interface", "resource", "converter", "specification", "game", "distinguisher", "solver"].contains desc.noun.singular then
      desc.noun.singular
    else "parameter"
  return (role, badge)

/-- Check if an expression references compiler-generated `match_` helpers or `sorryAx`.
(Proof-only `_proof_` terms inside explicit structures are omitted by `LeanTeX.collectExplicitArgs`,
so checking `match_` and `sorryAx` avoids falsely blanking definitions such as `oneTimePad`.) -/
private def containsAuxOrMatchDecl (e : Expr) : Bool :=
  containsMatchHelper e ||
  e.foldConsts (init := false) fun n acc =>
    acc || n == ``sorryAx

private def containsUnreducedCasesOrRec (e : Expr) : Bool :=
  e.foldConsts (init := false) fun n acc =>
    acc ||
      let s := n.getString!
      s == "casesOn" || s == "rec" || s == "recOn" || s == "noConfusion"

private def tupleCasesStruct? (n : Name) : Option Name :=
  if n == ``Prod.casesOn then some ``Prod
  else if n == ``PProd.casesOn then some ``PProd
  else if n == ``Sigma.casesOn then some ``Sigma
  else if n == ``PSigma.casesOn then some ``PSigma
  else none

private def projectTupleField (structName : Name) (idx : Nat) (discr : Expr) : Expr :=
  let d := discr.consumeMData
  if d.isAppOfArity ``Prod.mk 4 && structName == ``Prod then d.getAppArgs[2 + idx]!
  else if d.isAppOfArity ``PProd.mk 4 && structName == ``PProd then d.getAppArgs[2 + idx]!
  else if d.isAppOfArity ``Sigma.mk 4 && structName == ``Sigma then d.getAppArgs[2 + idx]!
  else if d.isAppOfArity ``PSigma.mk 4 && structName == ``PSigma then d.getAppArgs[2 + idx]!
  else mkProj structName idx discr

/-- Unfold compiler-generated `match_` helpers and tuple `.casesOn` destructuring
(such as `let (A, B) := G seed` in `PRGLengthExtension.H`) into clean field
projections without introducing `let` expressions. -/
private partial def expandMatchHelpersForDef (e : Expr) (depth : Nat := 16) : MetaM Expr := do
  if depth == 0 then return e
  let e := e.consumeMData
  match e with
  | .app .. =>
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    if fn.isLambda then
      let reduced := e.headBeta
      if reduced != e then
        return ← expandMatchHelpersForDef reduced (depth - 1)
    if let .const head lvls := fn then
      if (shortConstName head).startsWith "match_" then
        let unfolded? ← do
          if let some u ← withTransparency .default (Meta.unfoldDefinition? e) then
            pure (some u.headBeta)
          else if let some (.defnInfo dinfo) := (← getEnv).find? head then
            pure (some (mkAppN (dinfo.value.instantiateLevelParams dinfo.levelParams lvls) args).headBeta)
          else
            pure none
        if let some unfolded := unfolded? then
          if unfolded != e then
            return ← expandMatchHelpersForDef unfolded (depth - 1)
      if let some structName := tupleCasesStruct? head then
        if args.size ≥ 5 then
          let discr := args[3]!
          let k := args[4]!
          let extra := args.extract 5 args.size
          let f0 := projectTupleField structName 0 discr
          let f1 := projectTupleField structName 1 discr
          let next := (mkAppN (mkAppN k #[f0, f1]) extra).headBeta
          return ← expandMatchHelpersForDef next (depth - 1)
    let fn' ← expandMatchHelpersForDef fn (depth - 1)
    let args' ← args.mapM (expandMatchHelpersForDef · (depth - 1))
    let combined := mkAppN fn' args'
    if fn'.isLambda && combined.headBeta != combined then
      return ← expandMatchHelpersForDef combined.headBeta (depth - 1)
    return combined
  | .lam nm dom body bi =>
    withLocalDecl nm bi dom fun fv => do
      let inst ← expandMatchHelpersForDef (body.instantiate1 fv) (depth - 1)
      mkLambdaFVars #[fv] inst
  | .letE nm ty val body _ =>
    let val' ← expandMatchHelpersForDef val (depth - 1)
    if (cleanBinderName? nm).isNone || exprSizeBounded val' 32 then
      return ← expandMatchHelpersForDef (body.instantiate1 val') (depth - 1)
    withLetDecl nm ty val' fun fv => do
      let inst ← expandMatchHelpersForDef (body.instantiate1 fv) (depth - 1)
      mkLetFVars #[fv] inst
  | .proj sName idx inner =>
    return .proj sName idx (← expandMatchHelpersForDef inner (depth - 1))
  | _ => return e

private def buildStandardDefSummary (env : Environment) (declName : Name) (desc : TypeDescription)
    (isProj hasExplicitParams : Bool) (badge : String) : String :=
  let adj := if desc.adjectives.isEmpty then "" else String.intercalate " " desc.adjectives ++ " "
  let art := article (adj ++ desc.noun.singular)
  let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
  if isProj then
    if desc.noun.singular.startsWith "element of " then
      s!"Projection field {shortConstName declName} (in {desc.noun.singular.drop 11}{acc})."
    else
      s!"Projection field {shortConstName declName} ({art} {adj}{desc.noun.singular}{acc})."
  else if let some rule := getPaperDescribeRule? env declName then
    match rule.hoverTemplate? with
    | some hTmpl => hTmpl
    | none =>
        if desc.noun.singular.startsWith "element of " then
          ensurePeriod s!"Defined in {desc.noun.singular.drop 11}{acc}"
        else ensurePeriod s!"Defined as {art} {adj}{desc.noun.singular}{acc}"
  else if hasExplicitParams && badge == "definition" then
    if desc.noun.singular.startsWith "element of " then
      ensurePeriod s!"Function returning a value in {desc.noun.singular.drop 11}{acc}"
    else
      ensurePeriod s!"Function returning {art} {adj}{desc.noun.singular}{acc}"
  else if desc.noun.singular.startsWith "element of " then
    ensurePeriod s!"Defined in {desc.noun.singular.drop 11}{acc}"
  else
    ensurePeriod s!"Defined as {art} {adj}{desc.noun.singular}{acc}"

/-- Build an ambient-suppressed `InspectorKind.mathDefinition` plus `(roleBadge, clauses)`
for a project `defnInfo`. -/
private def buildMathDefinitionRich (tbl : SymbolTable) (declName : Name) (info : DefinitionVal) :
    MetaM (InspectorKind × String × Array String) := do
  let env ← getEnv
  forallTelescope info.type fun fvars bodyTy => do
    let mut explicitParams : Array String := #[]
    let mut explicitFVars : Array Expr := #[]
    let mut selfFVars : Array Expr := #[]
    let mut domainNouns : List String := []
    let mut expIdx := 0
    let hidden := tbl.hiddenArgs.getD declName []
    let isProj := env.isProjectionFn declName
    for fv in fvars do
      let d ← fv.fvarId!.getDecl
      if ← isSuppressedLocalDecl d then continue
      if !d.binderInfo.isExplicit then continue
      if ← isProp d.type then continue
      explicitFVars := explicitFVars.push fv
      let cleanNm := cleanBinderName d.userName "x"
      if cleanNm == "self" then
        selfFVars := selfFVars.push fv
      let pTex ←
        if isProj && cleanNm == "self" then pure "x"
        else if cleanNm == "self" then pure "x"
        else exprToLatex fv tbl
      if !hidden.contains expIdx then
        explicitParams := explicitParams.push pTex
      let pd ← describeType tbl d.type
      if !pd.noun.singular.startsWith "element of" then
        domainNouns := domainNouns ++ [pd.noun.plural]
      expIdx := expIdx + 1
    let bodyTyClean ← normalizeForPresentation bodyTy
    let desc ← describeType tbl bodyTyClean
    let isPredicate := bodyTyClean == .sort .zero
    let badge ←
      if isPredicate then pure "predicate"
      else if (← resourceInterface? bodyTyClean).isSome then pure "resource"
      else if (← converterInterfaces? bodyTyClean).isSome then pure "converter"
      else if (← specificationInterface? bodyTyClean).isSome then pure "specification"
      else if (← isInterfaceType bodyTyClean) then pure "interface"
      else if isProj then pure "parameter field"
      else pure "definition"
    let lhsHead := tbl.constAliases.getD declName (formatMathIdent (shortConstName declName))
    let lhs :=
      if isProj && explicitParams.size == 1 then
        s!"{explicitParams[0]!}.\\mathrm\{{escapeLatex (shortConstName declName)}}"
      else if explicitParams.isEmpty then lhsHead
      else s!"{lhsHead}\\!\\left({String.intercalate ", " explicitParams.toList}\\right)"
    -- Instantiate the definition body with the same telescope fvars (stripping leading lambdas)
    let mut rhs := info.value
    for fv in fvars do
      match rhs.consumeMData with
      | .lam _ _ b _ => rhs := b.instantiate1 fv
      | _ => break
    let mut rhsTbl := tbl
    for sfv in selfFVars do
      rhsTbl := rhsTbl.withExprAlias sfv "x"
    if isProj && explicitFVars.size == 1 && selfFVars.isEmpty then
      rhsTbl := rhsTbl.withExprAlias explicitFVars[0]! (explicitParams.getD 0 "x")
    if rhs.approxDepth > 55 || !exprSizeBounded rhs 900 then
      let summary := buildStandardDefSummary env declName desc isProj (!explicitParams.isEmpty) badge
      return (.mathDefinition "" summary, badge, #[])
    let rhsNorm ← normalizeForPresentation rhs
    -- 1. Predicate (`→ Prop`): unfold conjunct clauses cleanly!
    if isPredicate then
      let rawClauses ← splitAndClauses rhsNorm
      let mut clauses : Array String := #[]
      for c in rawClauses do
        if !containsAuxOrMatchDecl c then
          clauses := clauses.push (← exprToLatex c rhsTbl)
      let summary :=
        if let some firstDom := domainNouns.head? then
          s!"Predicate on {firstDom}."
        else
          "Checked mathematical predicate."
      let eqLatex ←
        if containsAuxOrMatchDecl rhsNorm then pure ""
        else if clauses.isEmpty then do
          pure s!"{lhs} := {← exprToLatex rhsNorm rhsTbl}"
        else
          pure s!"{lhs} \\iff {String.intercalate " \\wedge " clauses.toList}"
      return (.mathDefinition eqLatex summary, badge, clauses)
    -- 2. Specification set comprehension (`Set (TypedSystem ...)`): extract membership condition!
    if badge == "specification" then
      if let some (setTex, clauses) ← unwrapSetComprehension? rhsTbl rhsNorm then
        let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
        let summary := ensurePeriod s!"{capitalizeFirst desc.noun.singular}{acc}"
        return (.mathDefinition s!"{lhs} = {setTex}" summary, badge, clauses)
    -- 3. Resource with `TypedSystem.sample` / `TypedSystem.ofFunction` (`match_1` clean handling!)
    if badge == "resource" then
      let (sampleClauses, innerBody) ← extractSampleClauses rhsTbl rhsNorm
      let acc := if desc.accessories.isEmpty then "" else " " ++ joinAnd desc.accessories
      let summary := ensurePeriod s!"{capitalizeFirst desc.noun.singular}{acc}"
      if !sampleClauses.isEmpty || containsAuxOrMatchDecl rhsNorm then
        let ifaceStr ← match ← resourceInterface? bodyTyClean with
          | some iface => do
              let itex ← exprToLatex iface rhsTbl
              pure s!"\\text\{Port behavior at } {itex}"
          | none => pure "\\text{Deterministic port evaluation}"
        let finalClauses ←
          if containsAuxOrMatchDecl innerBody then
            pure (sampleClauses.push ifaceStr)
          else do
            let bodyTex ← exprToLatex innerBody rhsTbl
            pure (sampleClauses.push bodyTex)
        return (.mathDefinition "" summary, badge, finalClauses)
    -- 4. Standard definition / projection
    let summary := buildStandardDefSummary env declName desc isProj (!explicitParams.isEmpty) badge
    let rhsForEq ←
      if containsAuxOrMatchDecl rhsNorm then
        let expanded ← expandMatchHelpersForDef rhsNorm
        let expanded ← normalizeForPresentation expanded
        if !containsAuxOrMatchDecl expanded && !containsUnreducedCasesOrRec expanded &&
           exprSizeBounded expanded 600 then
          pure expanded
        else pure rhsNorm
      else pure rhsNorm
    let rhsTex ← if containsAuxOrMatchDecl rhsForEq then pure "" else exprToLatex rhsForEq rhsTbl
    let eqLatex :=
      if rhsTex.isEmpty || rhsTex == lhs || isProj then ""
      else s!"{lhs} := {rhsTex}"
    return (.mathDefinition eqLatex summary, badge, #[])

/-- Collect explicit project constants referenced inside `e` in $O(\text{DAG})$ time (excluding
core/Mathlib, implicit typeclass arguments, ambient typeclass heads, and internal instance plumbing). -/
private partial def collectExplicitProjectConstants (env : Environment) (e : Expr) :
    MetaM (Array Name) := do
  let rec go (cur : Expr) (acc : NameSet × Array Name × Std.HashSet Expr) :
      MetaM (NameSet × Array Name × Std.HashSet Expr) := do
    if acc.2.2.contains cur then return acc
    let seenE := acc.2.2.insert cur
    let acc := (acc.1, acc.2.1, seenE)
    match cur with
    | .const n _ =>
        if acc.1.contains n || isLibraryConstant env n then return acc
        if env.contains n then return (acc.1.insert n, acc.2.1.push n, seenE)
        else return acc
    | .app .. =>
        let fn := cur.getAppFn.consumeMData
        let args := cur.getAppArgs
        let mut curAcc ← go fn acc
        let visArgs ←
          if cur.hasLooseBVars then pure args
          else match fn.constName? with
          | some hn =>
              try
                let info ← getConstInfo hn
                let mut curTy := info.type
                let mut res : Array Expr := #[]
                for a in args do
                  if curTy.hasLooseBVars then
                    res := res.push a
                  else
                    curTy ← match curTy.consumeMData with
                      | f@(.forallE ..) => pure f
                      | other => withTransparency .reducible (whnf other)
                    match curTy with
                    | .forallE _ dom body bi =>
                        if bi.isExplicit && (dom.hasLooseBVars || !(← isAmbientTypeclass dom)) then
                          res := res.push a
                        curTy := body.instantiate1 a
                    | _ => res := res.push a
                pure res
              catch _ => pure args
          | none => pure args
        for a in visArgs do
          curAcc ← go a curAcc
        return curAcc
    | .lam _ d b _ =>
        let acc1 ← go d acc
        go b acc1
    | .forallE _ d b _ =>
        let acc1 ← go d acc
        go b acc1
    | .letE _ t v b _ =>
        let acc1 ← go t acc
        let acc2 ← go v acc1
        go b acc2
    | .mdata _ inner => go inner acc
    | .proj _ _ s => go s acc
    | _ => return acc
  let (_, res, _) ← go e ({}, #[], {})
  return res

/-- Fast $O(\text{DAG})$ scan of a proof term collecting non-theorem project definitions/interfaces. -/
private def collectProofDefConstants (env : Environment) (e : Expr) : Array Name :=
  let (_, out) := e.foldConsts (init := (({} : NameSet), (#[] : Array Name))) fun n (visited, out) =>
    if visited.contains n || isLibraryConstant env n then (visited, out)
    else
      match env.find? n with
      | some (.defnInfo _) | some (.opaqueInfo _) => (visited.insert n, out.push n)
      | _ => (visited.insert n, out)
  out

/-- Special operator display/metadata overrides for CC primitives whose 2D LaTeX comes from
registered `AppHandler`s rather than `constAliases`. -/
private def specialCCOperatorMeta? (declName : Name) : Option (String × String × String) :=
  if declName == distanceName || declName == transcriptDistanceName then
    some ("\\Delta", "metric",
      "Maximum distinguishing advantage over all compatible distinguishers.")
  else if declName == advantageDistanceName || declName == distinguisherAdvantageValName then
    some ("\\Delta", "advantage",
      "Distinguishing advantage between two resources or systems.")
  else if declName == rsWinProbabilityName || declName == typedSolverWinProbabilityName then
    some ("\\Gamma", "win probability",
      "Game winning probability achieved by a solver or distinguisher.")
  else if declName == constructsName || declName == constructsWithinName then
    some ("\\xrightarrow{\\pi}", "construction",
      "Constructive Cryptography realization relation between source and target specifications.")
  else if declName == substitutesWithinName then
    some ("\\simeq", "substitution",
      "Admissible-distinguisher substitution relation between resources within an error bound.")
  else
    none

/-- Inspect a single constant declaration in the environment and produce a rich, type-aware
`SymbolInspector`. -/
private def inspectConstant? (tbl : SymbolTable) (declName : Name) :
    MetaM (Option SymbolInspector) := do
  let env ← getEnv
  if isLibraryConstant env declName then return none
  let some info := env.find? declName | return none
  if ← isAmbientTypeclass info.type then return none
  let key := declName.toString
  let leanType ← cleanLeanTypeStr info.type
  let (sourceFile?, sourceLine?) ← declLocation env declName
  let docString? ← cleanDocString? env declName
  if let some (disp, badge, summary) := specialCCOperatorMeta? declName then
    return some {
      key, display := disp, kind := .mathDefinition "" summary,
      leanName? := some key, leanType, sourceFile?, sourceLine?,
      roleBadge? := some badge, docString?
    }
  let display ← exprToLatex (mkConst declName) tbl
  let isInterfaceDecl ← forallTelescope info.type fun _ bodyTy =>
    pure (bodyTy.consumeMData == mkConst interfaceName)
  -- 1. DSL `converter` / `system` / `interface` recorded by parser
  if let some dslKind := buildDslPseudocode? env declName then
    let badge ←
      if isInterfaceDecl then pure "interface"
      else forallTelescope info.type fun _ bodyTy => do
        if (← converterInterfaces? bodyTy).isSome then pure "converter"
        else if (← resourceInterface? bodyTy).isSome then pure "resource"
        else pure "system / converter"
    return some {
      key, display, kind := dslKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?, roleBadge? := some badge, docString?
    }
  -- 2. Closed `Interface` definition -> Port / Query / Reply / Domain table
  let cExpr := mkConst declName (info.levelParams.map Level.param)
  if isInterfaceDecl && info.type.consumeMData == mkConst interfaceName then
    if let some tableKind ← buildInterfaceTable? tbl cExpr then
      return some {
        key, display, kind := tableKind, leanName? := some key, leanType,
        sourceFile?, sourceLine?, roleBadge? := some "interface", docString?
      }
  -- 3. `HCoefficient` or `Implication` witness constant
  if let some witnessKind ← buildWitnessCard? tbl info.type then
    return some {
      key, display, kind := witnessKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?, roleBadge? := some "witness", docString?
    }
  -- 4. CC resource / converter / specification assembly -> live box-and-wire diagram
  if let .defnInfo dinfo := info then
    let (isRes, isConv, isSpec) ← forallTelescope info.type fun _ bodyTy => do
      let isRes := (← resourceInterface? bodyTy).isSome
      let isConv := (← converterInterfaces? bodyTy).isSome
      let isSpec := (← specificationInterface? bodyTy).isSome
      pure (isRes, isConv, isSpec)
    if (isRes || isConv || isSpec) && !info.type.isForall then
      if let some diagHtml ← renderCCDiagramHtml? tbl dinfo.value then
        let sumTex ← exprToLatex dinfo.value tbl
        let badge := if isConv then "converter" else if isSpec then "specification" else "resource"
        return some {
          key, display, kind := .ccDiagram diagHtml sumTex,
          leanName? := some key, leanType, sourceFile?, sourceLine?,
          roleBadge? := some badge, docString?
        }
    -- 5. Ambient-suppressed mathematical definition / predicate / resource / projection
    let (defKind, badge, clauses) ← buildMathDefinitionRich tbl declName dinfo
    return some {
      key, display, kind := defKind, leanName? := some key, leanType,
      sourceFile?, sourceLine?, roleBadge? := some badge, clauses, docString?
    }
  -- 5b. Prerequisite theorems / lemmas (`B4`) -> theorem-statement hover card (non-private only)
  if let .thmInfo tinfo := info then
    if Lean.isPrivateName declName then return none
    let title := (getOverlay env declName).title?.getD (humanDeclarationTitle env declName)
    let summary := ensurePeriod title
    let stmtLatex ←
      if tinfo.type.approxDepth > 55 || !exprSizeBounded tinfo.type 900 then
        pure ""
      else
        try exprToLatex tinfo.type tbl catch _ => pure ""
    return some {
      key, display := title, kind := .mathDefinition stmtLatex summary,
      leanName? := some key, leanType, sourceFile?, sourceLine?,
      roleBadge? := some "theorem", docString?
    }
  -- 6. Domain type / structure registered via `@[paper_describe]` / `paper_describe_for`
  -- Merge with structure field tuple equation (`R2a`) when the declaration is a Lean structure.
  let buildStructEqLatex : MetaM String := do
    if let some sinfo := Lean.getStructureInfo? env declName then
      let params ← forallTelescope info.type fun fvars _ => do
        let mut ps : Array String := #[]
        for fv in fvars do
          let d ← fv.fvarId!.getDecl
          if d.binderInfo.isExplicit && !(← isProp d.type) then
            ps := ps.push (← exprToLatex fv tbl)
        pure ps
      let lhsHead := tbl.constAliases.getD declName (formatMathIdent (shortConstName declName))
      let lhs := if params.isEmpty then lhsHead else s!"{lhsHead}\\!\\left({String.intercalate ", " params.toList}\\right)"
      let fieldNames := sinfo.fieldNames.map fun fn => formatMathIdent (shortConstName fn)
      if fieldNames.isEmpty then return ""
      else return s!"{lhs} := \\langle {String.intercalate ", " fieldNames.toList} \\rangle"
    else return ""
  if let some rule := getPaperDescribeRule? env declName then
    let art := article rule.noun.singular
    let summary := match rule.hoverTemplate? with
      | some h => h
      | none => ensurePeriod (capitalizeFirst s!"{art} {rule.noun.singular}")
    let eqLatex ← buildStructEqLatex
    return some {
      key, display, kind := .mathDefinition eqLatex summary,
      leanName? := some key, leanType, sourceFile?, sourceLine?,
      roleBadge? := some (if eqLatex.isEmpty then "type" else "structure"), docString?
    }
  -- 7. Unregistered structures / inductive types (`B3`: e.g. `ShannonCipher`, `DistAdversary`)
  if let .inductInfo iinfo := info then
    if let some sinfo := Lean.getStructureInfo? env declName then
      let eqLatex ← buildStructEqLatex
      let summary := s!"Mathematical structure with {countPhrase sinfo.fieldNames.size ⟨"component", "components"⟩}."
      return some {
        key, display, kind := .mathDefinition eqLatex summary,
        leanName? := some key, leanType, sourceFile?, sourceLine?,
        roleBadge? := some "structure", docString?
      }
    let summary := s!"Inductive type with {countPhrase iinfo.ctors.length ⟨"constructor", "constructors"⟩}."
    return some {
      key, display, kind := .mathDefinition "" summary,
      leanName? := some key, leanType, sourceFile?, sourceLine?,
      roleBadge? := some "type", docString?
    }
  return none

/-- Collect constant inspectors from an arbitrary array of expressions (used e.g. for Section Contexts). -/
def collectExprInspectors (tbl : SymbolTable) (exprs : Array Expr) : MetaM (Array SymbolInspector) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut out : Array SymbolInspector := #[]
  for e in exprs do
    for cn in (← collectExplicitProjectConstants env e) do
      if !seen.contains cn then
        seen := seen.insert cn
        try
          if let some ins ← inspectConstant? tbl cn then
            out := out.push ins
        catch _ => pure ()
  return out

/-- Inspect a theorem statement's local non-hoisted parameters AND referenced constants from both
`theoremType` and `proofBody?` (+ `extraOriginDecls`), returning
`(localParamInspectors, typeConstInspectors, proofConstInspectors)`. -/
def collectScopedCCInspectors (tbl : SymbolTable) (declName : Name) (theoremType : Expr)
    (proofBody? : Option Expr) (hoistedParamSyms : Std.HashSet String)
    (extraOriginDecls : Array Name := #[]) :
    MetaM (Array SymbolInspector × Array SymbolInspector × Array SymbolInspector) := do
  let env ← getEnv
  let pushUnique (acc : Array SymbolInspector) (seen : Std.HashSet String) (ins : SymbolInspector) :
      Array SymbolInspector × Std.HashSet String :=
    if seen.contains ins.key then (acc, seen)
    else (acc.push ins, seen.insert ins.key)
  let (fvOut, typeConsts) ← forallTelescope theoremType fun fvars conclusion => do
    let fam ← collectAmbientFamilies
    let mut neededFVars : Std.HashSet FVarId := {}
    for id in (Lean.collectFVars {} conclusion).fvarIds do
      neededFVars := neededFVars.insert id
    let mut candParams : Array (Expr × TypeDescription × String × String) := #[]
    let mut consts : Array Name := #[]
    for fv in fvars do
      let decl ← fv.fvarId!.getDecl
      if ← isSuppressedLocalDecl decl then continue
      if ← isProp decl.type then
        consts := consts ++ (← collectExplicitProjectConstants env decl.type)
        for id in (Lean.collectFVars {} decl.type).fvarIds do
          neededFVars := neededFVars.insert id
        continue
      let desc ← describeType tbl decl.type
      if desc.isAmbient then continue
      if fam.categories.any (fun c => c == fv) then continue
      let clean := cleanBinderName decl.userName
      let display ← exprToLatex fv tbl
      if hoistedParamSyms.contains display then
        continue
      candParams := candParams.push (fv, desc, clean, display)
    let mut keptRev : Array (Expr × TypeDescription × String × String) := #[]
    for item in candParams.reverse do
      let (fv, desc, _, _) := item
      let decl ← fv.fvarId!.getDecl
      if desc.isWitness || neededFVars.contains fv.fvarId! then
        keptRev := keptRev.push item
        for id in (Lean.collectFVars {} decl.type).fvarIds do
          neededFVars := neededFVars.insert id
    let mut fvOut : Array SymbolInspector := #[]
    for (fv, _, clean, display) in keptRev.reverse do
      let decl ← fv.fvarId!.getDecl
      consts := consts ++ (← collectExplicitProjectConstants env decl.type)
      let leanType ← cleanLeanTypeStr decl.type
      let key := s!"param:{declName}:{clean}"
      let (kind, badge) : InspectorKind × String ← do
        if let some tableKind ← buildInterfaceTable? tbl fv then
          pure (tableKind, "interface")
        else if let some witnessKind ← buildWitnessCard? tbl decl.type then
          pure (witnessKind, "witness")
        else
          let isRes := (← resourceInterface? decl.type).isSome
          let isConv := (← converterInterfaces? decl.type).isSome
          let isSpec := (← specificationInterface? decl.type).isSome
          if isRes || isConv || isSpec then
            let b := if isConv then "converter" else if isSpec then "specification" else "resource"
            match ← renderCCDiagramHtml? tbl fv with
            | some html => pure (.ccDiagram html display, b)
            | none =>
                let (role, _) ← buildParameterRoleAndBadge tbl decl.type
                pure (.parameter role, b)
          else
            let (role, b) ← buildParameterRoleAndBadge tbl decl.type
            pure (.parameter role, b)
      fvOut := fvOut.push {
        key, display, kind, leanName? := none, leanType, roleBadge? := some badge
      }
    consts := consts ++ (← collectExplicitProjectConstants env conclusion)
    return (fvOut, consts)
  let mut typeIns : Array SymbolInspector := #[]
  let mut seenTypeKeys : Std.HashSet String := {}
  for cn in typeConsts do
    if !seenTypeKeys.contains cn.toString then
      try
        if let some ins ← inspectConstant? tbl cn then
          (typeIns, seenTypeKeys) := pushUnique typeIns seenTypeKeys ins
      catch _ => pure ()
  let mut proofConsts : Array Name := match proofBody? with
    | some body => collectProofDefConstants env body
    | none => #[]
  for od in extraOriginDecls do
    proofConsts := proofConsts.push od
    if let some oinfo := env.find? od then
      proofConsts := proofConsts ++ (← collectExplicitProjectConstants env oinfo.type)
  let mut proofIns : Array SymbolInspector := #[]
  let mut seenProofKeys := seenTypeKeys
  for cn in proofConsts do
    if !seenProofKeys.contains cn.toString then
      try
        if let some ins ← inspectConstant? tbl cn then
          (proofIns, seenProofKeys) := pushUnique proofIns seenProofKeys ins
      catch _ => pure ()
  return (fvOut, typeIns, proofIns)

/-- Legacy flat collector compatibility wrapper. -/
def collectCCInspectors (tbl : SymbolTable) (theoremType : Expr) :
    MetaM (Array SymbolInspector) := do
  let (fvOut, typeIns, _) ← collectScopedCCInspectors tbl .anonymous theoremType none {}
  return fvOut ++ typeIns

/-! ## 3. Module Initialization (Auto-Registration) -/

/-- Register the CC diagram hook and type-aware symbol inspector collectors with `ProofGraph`. -/
def registerAll : IO Unit := do
  registerDiagramHook (fun tbl e => renderCCDiagramHtml? tbl e)
  registerClearDiagramCacheHook (diagHtmlCacheRef.set {})
  registerInspectorCollector collectCCInspectors
  registerScopedInspectorCollector fun tbl declName theoremType proofBody? hoistedParamSyms extra =>
    collectScopedCCInspectors tbl declName theoremType proofBody? hoistedParamSyms extra

initialize registerAll

end Informalization.CC.Inspectors
