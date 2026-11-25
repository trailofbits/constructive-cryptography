/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.LeanTeX
import Informalization.Core.Presentation

/-!
# Compile-Time-Checked Optional Flow & Notation Overlay (~10% Layer)

Any CC proof informalizes cleanly with **zero annotations** (90% pure Kyle Miller).
When an author wants to polish reading flow—adding brief, inconsequential transition or
motivation notes, disambiguating notation clashes (such as `r` for sponge rate vs. `P` for
public queries), or marking low-level bit-slicing lemmas as opaque stops—they attach them
in a lightweight companion module using the commands below.

**Trust boundary:**
* Every declaration name is resolved and checked against the live Lean environment at
  elaboration time (`realizeGlobalConstNoOverloadWithInfo`). If upstream CC renames a
  declaration, the overlay fails loudly at compile time.
* Flow notes are strictly rendered as visually distinct marginalia/signposting and **never**
  replace, suppress, or alter a Lean-checked statement, bound, or dependency edge.
-/

namespace Informalization.Core.Overlay

open Lean Elab Command Informalization.Core.LeanTeX Informalization.Core.Presentation

/-- Pre-theorem exposition block metadata (`informal_section_prelude[_decl]`). -/
structure PreludeSpec where
  kind : String
  label : String := ""
  title : String := ""
  bodyText : String := ""
  lines : Array (Nat × String) := #[]
  rows : Array (String × String) := #[]
  declName? : Option Name := none
  deriving Inhabited, Repr

/-- Presentation-only metadata attached to a resolved Lean declaration. -/
structure DeclOverlay where
  title? : Option String := none
  flowBefore? : Option String := none
  flowAfter? : Option String := none
  symbolLatex? : Option String := none
  binderAliases : Array (String × String) := #[]
  /-- Natural-language `(singular, plural)` noun for a domain type (kills "element of T"). -/
  noun? : Option (String × String) := none
  /-- Natural-language English predicate phrase for a domain proposition (e.g. "is a supported sponge"). -/
  predPhrase? : Option String := none
  /-- 0-based explicit argument positions suppressed when rendering applications of this constant. -/
  hiddenArgs : List Nat := []
  /-- Render applications of this constant purely as its short symbol (e.g. `blockBytes (hash p)` -> `r`). -/
  isZeroArgNotation : Bool := false
  /-- Presentation kind ("Theorem", "Lemma", "Proposition", "Corollary"). -/
  entryKind? : Option String := none
  /-- Optional paper section heading starting at this declaration. -/
  sectionTitle? : Option String := none
  /-- Optional 1-2 sentence Maurer-voice section overview shown under `sectionTitle?`. -/
  sectionIntro? : Option String := none
  /-- First-class pre-theorem exposition blocks anchored before this declaration. -/
  sectionPreludes : Array PreludeSpec := #[]
  /-- Stop cross-lemma recursion at this declaration (e.g., low-level bit-slicing arithmetic). -/
  isOpaqueLeaf : Bool := false
  /-- Treat this declaration as a prominent mathematical proof joint (never auto-inlined). -/
  isProofJoint : Bool := false
  /-- Declaration-scoped expression aliases `(nBinders, closedPattern, latexSymbol, gloss?)`. -/
  theoremNotations : Array (Nat × Expr × String × Option String) := #[]
  deriving Inhabited, Repr

private def mergeOverlay (old new : DeclOverlay) : DeclOverlay := {
  title?            := new.title? <|> old.title?
  flowBefore?       := new.flowBefore? <|> old.flowBefore?
  flowAfter?        := new.flowAfter? <|> old.flowAfter?
  symbolLatex?      := new.symbolLatex? <|> old.symbolLatex?
  binderAliases     := old.binderAliases ++ new.binderAliases
  noun?             := new.noun? <|> old.noun?
  predPhrase?       := new.predPhrase? <|> old.predPhrase?
  hiddenArgs        := if new.hiddenArgs.isEmpty then old.hiddenArgs else new.hiddenArgs
  isZeroArgNotation := old.isZeroArgNotation || new.isZeroArgNotation
  entryKind?        := new.entryKind? <|> old.entryKind?
  sectionTitle?     := new.sectionTitle? <|> old.sectionTitle?
  sectionIntro?     := new.sectionIntro? <|> old.sectionIntro?
  sectionPreludes   := old.sectionPreludes ++ new.sectionPreludes
  isOpaqueLeaf      := old.isOpaqueLeaf || new.isOpaqueLeaf
  isProofJoint      := old.isProofJoint || new.isProofJoint
  theoremNotations  := old.theoremNotations ++ new.theoremNotations
}

initialize overlayExt :
    SimplePersistentEnvExtension (Name × DeclOverlay) (NameMap DeclOverlay) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, ov) =>
      match m.get? n with
      | some prev => m.insert n (mergeOverlay prev ov)
      | none => m.insert n ov
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (n, ov) =>
        match m.get? n with
        | some prev => m.insert n (mergeOverlay prev ov)
        | none => m.insert n ov
  }

def getOverlay (env : Environment) (decl : Name) : DeclOverlay :=
  (overlayExt.getState env).getD decl {}

/-- Persistent namespace-scoped binder symbol overrides (`informal_binder_for Namespace "r" "P"`). -/
initialize namespaceBinderExt :
    SimplePersistentEnvExtension (Name × String × String) (Array (Name × String × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun arr entry => arr.push entry
    addImportedFn := fun parts => parts.foldl (init := #[]) fun acc a => acc ++ a
  }

/-- Layered `(singular, plural)` noun lookup: `Overlay` wins over `@[interface_resource_noun]`
and `@[paper_describe]` / `paper_describe_for`. -/
def effectiveNoun? (env : Environment) (decl : Name) : Option (String × String) :=
  (getOverlay env decl).noun? <|>
  (getMathPresentation env decl).interfaceResourceNoun? <|>
  (getPaperDescribeRule? env decl).map fun r => (r.noun.singular, r.noun.plural)

/-- Layered predicate phrase lookup: `Overlay` (`informal_pred`) wins over `@[math_pred]`. -/
def effectivePredPhrase? (env : Environment) (decl : Name) : Option String :=
  (getOverlay env decl).predPhrase? <|> (getMathPresentation env decl).predPhrase?

/-- Layered opaque-leaf guard: either `informal_opaque` or `@[math_opaque]`. -/
def effectiveIsOpaqueLeaf (env : Environment) (decl : Name) : Bool :=
  (getOverlay env decl).isOpaqueLeaf || (getMathPresentation env decl).isOpaqueLeaf

/-- Layered proof-joint guard: either `informal_joint` or `@[math_joint]`. -/
def effectiveIsProofJoint (env : Environment) (decl : Name) : Bool :=
  (getOverlay env decl).isProofJoint || (getMathPresentation env decl).isProofJoint

/-- Layered wrapper guard: `@[math_wrapper]`. -/
def effectiveIsWrapper (env : Environment) (decl : Name) : Bool :=
  (getMathPresentation env decl).isWrapper

/-- Build a `SymbolTable` populated first with `@[math_notation]` (`mathPresentationExt`),
then layered over by `Overlay` (`overlayExt`) so `SequenceHashOverlay.lean` and per-theorem
`informal_binder` / notation overlays ALWAYS take precedence. -/
def buildSymbolTable (env : Environment) (rootDecl : Name) : SymbolTable := Id.run do
  let mut tbl : SymbolTable := {}
  -- Layer 1: definition-site & module presentation registry (`Core/Presentation.lean`)
  for (n, mp) in getAllMathPresentations env do
    if let some sym := mp.symbolLatex? then
      tbl := tbl.withConst n sym
      if mp.isZeroArgNotation then
        tbl := tbl.withShortAlias n sym
    if let some tmpl := compileNotationTemplate? mp (mp.explicitNonPropArity?.getD 8) then
      tbl := tbl.withConstTemplate n tmpl
    if !mp.hiddenArgs.isEmpty then
      tbl := tbl.withHiddenArgs n mp.hiddenArgs
    if mp.isZeroArgNotation then
      tbl := tbl.withZeroArgConst n
  -- Layer 2: explicit overlay (`Core/Overlay.lean`) ALWAYS wins over Layer 1
  let state := overlayExt.getState env
  for (n, ov) in state.toList do
    if let some sym := ov.symbolLatex? then
      tbl := tbl.withConst n sym
    if !ov.hiddenArgs.isEmpty then
      tbl := tbl.withHiddenArgs n ov.hiddenArgs
    if ov.isZeroArgNotation then
      tbl := tbl.withZeroArgConst n
  -- Layer 2b: namespace-scoped binder aliases (more specific sub-namespaces override parents)
  let nsBindersIndexed :=
    ((namespaceBinderExt.getState env).mapIdx fun i e => (i, e)).filter
      fun (_, (ns, _, _)) => ns.isPrefixOf rootDecl
  let nsBindersSorted := nsBindersIndexed.qsort fun (i1, (ns1, _, _)) (i2, (ns2, _, _)) =>
    let d1 := ns1.getNumParts
    let d2 := ns2.getNumParts
    if d1 != d2 then d1 < d2 else i1 < i2
  for (_, (_, b, sym)) in nsBindersSorted do
    tbl := tbl.withBinder b sym
  -- Layer 3: per-theorem `informal_binder` always overrides namespace-scoped aliases
  let rootOv := getOverlay env rootDecl
  for (b, sym) in rootOv.binderAliases do
    tbl := tbl.withBinder b sym
  return tbl

private def addCheckedOverlay (id : Ident) (ov : DeclOverlay) : CommandElabM Unit := do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  modifyEnv fun env => overlayExt.addEntry env (decl, ov)

/-- Give a theorem/lemma a clean human title (checked against the Lean environment). -/
elab "informal_title " id:ident title:str : command =>
  addCheckedOverlay id { title? := some title.getString }

/-- Attach a short, inconsequential flow/motivation note before a declaration or proof step. -/
elab "informal_flow_before " id:ident note:str : command =>
  addCheckedOverlay id { flowBefore? := some note.getString }

/-- Attach a short, inconsequential caveat or transition note after a declaration. -/
elab "informal_flow_after " id:ident note:str : command =>
  addCheckedOverlay id { flowAfter? := some note.getString }

/-- Register a clean LaTeX display symbol for a resolved constant (e.g. `Π±`). -/
elab "informal_symbol " id:ident latex:str : command =>
  addCheckedOverlay id { symbolLatex? := some latex.getString }

/-- Register a zero-arg short LaTeX symbol for a record projection or ambient quantity
(e.g. `blockBytes (hash p)` → `r`, `customizationBytes limits` → `L_{\mathrm{cust}}`). -/
elab "informal_short_symbol " id:ident latex:str : command =>
  addCheckedOverlay id { symbolLatex? := some latex.getString, isZeroArgNotation := true }

/-- Register natural English `(singular, plural)` noun phrasing for a domain type
(eliminates `"element of MyStruct"`). -/
elab "informal_noun " id:ident sg:str pl:str : command =>
  addCheckedOverlay id { noun? := some (sg.getString, pl.getString) }

/-- Register natural English predicate phrasing for a unary/ambient domain proposition
(e.g. `supportedSponge p` → `"p is a supported sponge"`). -/
elab "informal_pred " id:ident phrase:str : command =>
  addCheckedOverlay id { predPhrase? := some phrase.getString }

/-- Suppress ambient leading explicit arguments (0-based indices) when printing applications
of a verbose Lean definition (e.g. `informal_hide_args keccakReal 0 1`). -/
elab "informal_hide_args " id:ident idxs:num* : command =>
  addCheckedOverlay id { hiddenArgs := idxs.toList.map (·.getNat) }

/-- Override a local binder's display symbol inside a theorem (e.g. disambiguate `r` → `P`). -/
elab "informal_binder " id:ident binder:str latex:str : command =>
  addCheckedOverlay id { binderAliases := #[(binder.getString, latex.getString)] }

/-- Override a local binder's display symbol across an entire Lean namespace prefix
(e.g. `informal_binder_for SequenceHash.SpongeTranscript "r" "P"`). -/
elab "informal_binder_for " ns:ident binder:str latex:str : command =>
  modifyEnv fun env => namespaceBinderExt.addEntry env (ns.getId, binder.getString, latex.getString)

private def isMarkdownTableDivider (line : String) : Bool :=
  let t := line.trimAscii.toString
  !t.isEmpty && (t.splitOn "|").length > 1 &&
    t.all (fun c => c == '|' || c == '-' || c == ':' || c == ' ' || c == '\t')

private def countLeadingSpaces (s : String) : Nat :=
  (s.toList.takeWhile fun c => c == ' ' || c == '\t').foldl
    (init := 0) fun acc c => acc + (if c == '\t' then 2 else 1)

private def parsePreludeBody (kind rawBody : String) :
    String × Array (Nat × String) × Array (String × String) := Id.run do
  let norm := (rawBody.replace "\r\n" "\n").replace "\r" "\n"
  let rawLines := norm.splitOn "\n"
  if kind == "symbolTable" then
    let mut proseLines : Array String := #[]
    let mut rows : Array (String × String) := #[]
    for line in rawLines do
      if isMarkdownTableDivider line then
        continue
      else if (line.splitOn "|").length > 1 then
        let t0 := line.trimAscii.toString
        let t1 := if t0.startsWith "|" then (t0.drop 1).toString else t0
        let t2 := if t1.endsWith "|" then (t1.dropEnd 1).toString else t1
        let parts := t2.splitOn "|"
        let left := (parts.headD "").trimAscii.toString
        let right := (String.intercalate "|" (parts.drop 1)).trimAscii.toString
        if !left.isEmpty || !right.isEmpty then
          rows := rows.push (left, right)
      else
        proseLines := proseLines.push line
    let bodyText := (String.intercalate "\n" proseLines.toList).trimAscii.toString
    return (bodyText, #[], rows)
  else if kind == "attackGame" || kind == "construction" || kind == "converterDef" then
    let isGtLine (l : String) : Bool := l.startsWith "> " || l == ">"
    let isIndentedLine (l : String) : Bool := l.startsWith "  " && !l.trimAscii.isEmpty
    let hasCode := rawLines.any fun l => isGtLine l || isIndentedLine l
    if hasCode then
      let mut introLines : Array String := #[]
      let mut rawCode : Array (Bool × Nat × String) := #[]
      let mut minSpaceIndent : Option Nat := none
      for line in rawLines do
        if isGtLine line then
          let afterGt := if line.startsWith "> " then (line.drop 2).toString else (line.drop 1).toString
          let sp := countLeadingSpaces afterGt
          let txt := afterGt.trimAscii.toString
          if !txt.isEmpty then
            rawCode := rawCode.push (true, sp, txt)
        else if isIndentedLine line then
          let sp := countLeadingSpaces line
          let txt := line.trimAscii.toString
          minSpaceIndent := some (match minSpaceIndent with | some m => min m sp | none => sp)
          rawCode := rawCode.push (false, sp, txt)
        else
          introLines := introLines.push line
      let baseSp := minSpaceIndent.getD 0
      let lines := rawCode.map fun (isGt, sp, txt) =>
        let ind := if isGt then sp / 2 else (sp - baseSp) / 2
        (ind, txt)
      let bodyText := (String.intercalate "\n" introLines.toList).trimAscii.toString
      return (bodyText, lines, #[])
  return (norm.trimAscii.toString, #[], #[])

private def validPreludeKinds : List String :=
  ["definition", "construction", "attackGame", "interfaceSpec", "converterDef", "symbolTable"]

private def validatePreludeKind (k : String) : CommandElabM Unit := do
  unless validPreludeKinds.contains k do
    let allowed := String.intercalate ", " validPreludeKinds
    throwError "Unknown prelude kind `{k}`; expected one of: {allowed}"

/-- Attach a pre-theorem exposition block (definition, construction, attack game, interface spec,
converter definition, or symbol table) rendered immediately before `anchorDecl`. -/
elab "informal_section_prelude " anchor:ident kind:str label:str title:str body:str : command => do
  validatePreludeKind kind.getString
  let (bodyText, lines, rows) := parsePreludeBody kind.getString body.getString
  let spec : PreludeSpec := {
    kind := kind.getString
    label := label.getString
    title := title.getString
    bodyText
    lines
    rows
    declName? := none
  }
  addCheckedOverlay anchor { sectionPreludes := #[spec] }

/-- Attach a pre-theorem exposition block backed by a compile-time-resolved target declaration
(`targetDecl`) rendered immediately before `anchorDecl` with a live inspector link. -/
elab "informal_section_prelude_decl " anchor:ident target:ident kind:str label:str title:str : command => do
  validatePreludeKind kind.getString
  let anchorDecl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo anchor
  let targetDecl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let spec : PreludeSpec := {
    kind := kind.getString
    label := label.getString
    title := title.getString
    declName? := some targetDecl
  }
  modifyEnv fun env => overlayExt.addEntry env (anchorDecl, { sectionPreludes := #[spec] })

/-- Override the presentation header (`"Theorem"`, `"Lemma"`, `"Proposition"`, `"Corollary"`). -/
elab "informal_kind " id:ident kind:str : command =>
  addCheckedOverlay id { entryKind? := some kind.getString }

/-- Start a named paper section at this declaration, with an optional concise overview sentence. -/
elab "informal_section " id:ident title:str intro:(str)? : command =>
  addCheckedOverlay id {
    sectionTitle? := some title.getString
    sectionIntro? := intro.map (·.getString)
  }

/-- Mark a low-level lemma as an opaque stop-point for cross-lemma recursion. -/
elab "informal_opaque " id:ident : command =>
  addCheckedOverlay id { isOpaqueLeaf := true }

/-- Mark a lemma as a prominent proof joint that Paper mode should never auto-inline. -/
elab "informal_joint " id:ident : command =>
  addCheckedOverlay id { isProofJoint := true }

/-- Register a theorem-scoped paper notation alias `(expr ↦ latex)` elaborated inside `id`'s
parameter telescope, with an optional author gloss for the hover inspector. -/
elab "informal_theorem_notation " id:ident exprStx:term:max latex:str gloss?:(str)? : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let entry ← Elab.Command.runTermElabM fun _ => do
    let info ← getConstInfo decl
    Meta.forallTelescope info.type fun fvars _ => do
      let pat ← Elab.Term.elabTerm exprStx none
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let pat ← instantiateMVars pat
      let patTy ← Meta.inferType pat
      let patTyW ← Meta.whnf patTy
      if patTyW == Expr.sort .zero then
        throwError "Formula-forgery guard: `informal_theorem_notation` cannot alias 0-ary `Prop` `{← Meta.ppExpr pat}` to `{latex.getString}`"
      let isPred : Bool ←
        if ← Meta.isProp patTy then pure true
        else Meta.forallTelescopeReducing patTy fun _ body =>
          return (← Meta.whnf body) == Expr.sort .zero
      if isPred && Informalization.Core.Presentation.isFormulaForgeryString latex.getString then
        throwError "Formula-forgery guard: `informal_theorem_notation` cannot alias predicate/Prop `{← Meta.ppExpr pat}` to formula string `{latex.getString}`"
      let pat ← Informalization.Core.Hygiene.normalizeForPresentation pat
      let symTrim := latex.getString.trimAscii.toString
      let prevNotations := (getOverlay (← getEnv) decl).theoremNotations
      for (nBind, prevClosedPat, prevSym, _) in prevNotations do
        if prevSym.trimAscii.toString == symTrim then
          let sameExpr ←
            if nBind ≤ fvars.size then
              let prevPat := prevClosedPat.instantiateRev (fvars.extract 0 nBind)
              try Meta.isDefEq prevPat pat catch _ => pure false
            else pure false
          if !sameExpr then
            logWarning m!"Notation collision: symbol '{symTrim}' is mapped to two distinct expressions in the same proof; disambiguate with a distinct symbol or subscript."
            break
      let closedPat := pat.abstract fvars
      return (fvars.size, closedPat, latex.getString, gloss?.map (·.getString))
  modifyEnv fun env => overlayExt.addEntry env (decl, { theoremNotations := #[entry] })

end Informalization.Core.Overlay
