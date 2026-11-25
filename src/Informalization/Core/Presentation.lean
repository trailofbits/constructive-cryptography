/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.Linter.Basic
import Lean.Linter.Util
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX

/-!
# Compile-Time Presentation Registry, Pure-Data `PaperDescribe`, & `linter.paperPresentation`

Provides definition-site and external zero-edit presentation metadata without `Meta.evalExpr`:

* **Presentation attributes (`mathPresentationExt`):**
  `@[math_notation]`, `@[math_pred]`, `@[math_opaque]`, `@[math_wrapper]`, `@[math_joint]`,
  `@[paper_role]`, `@[interface_resource_noun]`, `@[paper_module]`, plus `paper_module` and
  `scoped_notation` commands. Includes compile-time arity, slot, brace, and formula-forgery checks.
* **Pure-data type description rules (`paperDescribeExt`):**
  `@[paper_describe]` (definition site) and `paper_describe_for` (external zero-edit overlay),
  storing closed noun, `isGenericCarrier`, `varStyle?`, index-resolved `qualifierTemplate?`,
  verified `unpackFields`, and `hoverTemplate?`. Eliminates `Meta.evalExpr` gaps on open `FVar`s.
* **Opt-in presentation linter (`linter.paperPresentation`, default `false`):**
  Active when `linter.paperPresentation` is set to `true` or in modules/declarations annotated
  with `paper_module` / `@[paper_module]`. Enforces `PP01`–`PP06` with declaration-scoped `PP03`.
-/

declare_syntax_cat mathNotationOpt
syntax "(" &"zeroArg" ":=" ident ")" : mathNotationOpt
syntax "(" &"hide" ":=" "[" num,* "]" ")" : mathNotationOpt
syntax "(" &"sub" ":=" "[" num,* "]" ")" : mathNotationOpt
syntax "(" &"sup" ":=" "[" num,* "]" ")" : mathNotationOpt

declare_syntax_cat paperVarStyle
syntax "." ident : paperVarStyle
syntax ident : paperVarStyle

declare_syntax_cat paperUnpackItem
syntax ident : paperUnpackItem
syntax str : paperUnpackItem

declare_syntax_cat paperDescribeOpt
syntax "(" &"plural" ":=" str ")" : paperDescribeOpt
syntax "(" &"carrier" ":=" ident ")" : paperDescribeOpt
syntax "(" &"varStyle" ":=" paperVarStyle ")" : paperDescribeOpt
syntax "(" &"qualifier" ":=" str ")" : paperDescribeOpt
syntax "(" &"unpack" ":=" (optional("#")) "[" paperUnpackItem,* "]" ")" : paperDescribeOpt
syntax "(" &"hover" ":=" str ")" : paperDescribeOpt

syntax (name := Lean.Parser.Attr.math_notation) "math_notation" str mathNotationOpt* : attr
syntax (name := Lean.Parser.Attr.math_pred) "math_pred" str : attr
syntax (name := Lean.Parser.Attr.math_opaque) "math_opaque" : attr
syntax (name := Lean.Parser.Attr.math_wrapper) "math_wrapper" : attr
syntax (name := Lean.Parser.Attr.math_joint) "math_joint" : attr
syntax (name := Lean.Parser.Attr.paper_role) "paper_role" str : attr
syntax (name := Lean.Parser.Attr.interface_resource_noun) "interface_resource_noun" str str : attr
syntax (name := Lean.Parser.Attr.paper_module) "paper_module" : attr
syntax (name := Lean.Parser.Attr.paper_describe) "paper_describe" str paperDescribeOpt* : attr

namespace Informalization.Core.Presentation

open Lean Elab Meta Command
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX

/-! ## 1. Options & Module Opt-In (`paper_module`) -/

register_option linter.paperPresentation : Bool := {
  defValue := false
  descr := "Enable presentation quality checks PP01–PP06 for paper-authored Lean modules."
}

initialize paperModuleExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun arr =>
      arr.foldl (init := ({} : NameSet)) fun s a =>
        a.foldl (init := s) fun acc n => acc.insert n
  }

def isPaperPresentationActive (env : Environment) (opts : _root_.Lean.Linter.LinterOptions)
    (declNames : List Name := []) : Bool :=
  _root_.Lean.Linter.getLinterValue linter.paperPresentation opts ||
  (paperModuleExt.getState env).contains env.header.mainModule ||
  declNames.any fun n => (paperModuleExt.getState env).contains n

/-! ## 2. `mathPresentationExt`: Compile-Time Checked Notation & Role Registry -/

structure MathPresentationEntry where
  symbolLatex? : Option String := none
  notationTemplate? : Option String := none
  hiddenArgs : List Nat := []
  subscriptArgs : List Nat := []
  superscriptArgs : List Nat := []
  isZeroArgNotation : Bool := false
  predPhrase? : Option String := none
  isOpaqueLeaf : Bool := false
  isWrapper : Bool := false
  isProofJoint : Bool := false
  paperRole? : Option String := none
  interfaceResourceNoun? : Option (String × String) := none
  explicitNonPropArity? : Option Nat := none
  deriving Inhabited, Repr

private def mergeMathPres (old new : MathPresentationEntry) : MathPresentationEntry := {
  symbolLatex?          := new.symbolLatex? <|> old.symbolLatex?
  notationTemplate?     := new.notationTemplate? <|> old.notationTemplate?
  hiddenArgs            := if new.hiddenArgs.isEmpty then old.hiddenArgs else new.hiddenArgs
  subscriptArgs         := if new.subscriptArgs.isEmpty then old.subscriptArgs else new.subscriptArgs
  superscriptArgs       := if new.superscriptArgs.isEmpty then old.superscriptArgs else new.superscriptArgs
  isZeroArgNotation     := old.isZeroArgNotation || new.isZeroArgNotation
  predPhrase?           := new.predPhrase? <|> old.predPhrase?
  isOpaqueLeaf          := old.isOpaqueLeaf || new.isOpaqueLeaf
  isWrapper             := old.isWrapper || new.isWrapper
  isProofJoint          := old.isProofJoint || new.isProofJoint
  paperRole?            := new.paperRole? <|> old.paperRole?
  interfaceResourceNoun? := new.interfaceResourceNoun? <|> old.interfaceResourceNoun?
  explicitNonPropArity? := new.explicitNonPropArity? <|> old.explicitNonPropArity?
}

initialize mathPresentationExt :
    SimplePersistentEnvExtension (Name × MathPresentationEntry) (NameMap MathPresentationEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, e) =>
      match m.get? n with
      | some prev => m.insert n (mergeMathPres prev e)
      | none => m.insert n e
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (n, e) =>
        match m.get? n with
        | some prev => m.insert n (mergeMathPres prev e)
        | none => m.insert n e
  }

def getMathPresentation (env : Environment) (decl : Name) : MathPresentationEntry :=
  (mathPresentationExt.getState env).getD decl {}

def getAllMathPresentations (env : Environment) : List (Name × MathPresentationEntry) :=
  (mathPresentationExt.getState env).toList

/-! ## 3. Pure-Data `PaperDescribeRule` (`paperDescribeExt`, ZERO `Meta.evalExpr`) -/

/-- Closed, inspectable, pure-data rule describing how a domain type renders as prose/symbols.
All qualifier and hover placeholders are resolved at registration time to 0-based explicit
non-Prop parameter indices `{0}`, `{1}`, ... so runtime rendering works directly on open
`Expr.fvar` arguments without invoking `Meta.evalExpr`. -/
structure PaperDescribeRule where
  noun : CountNoun
  isGenericCarrier : Bool := false
  varStyle? : Option MathFontStyle := none
  qualifierTemplate? : Option String := none
  unpackFields : Array String := #[]
  hoverTemplate? : Option String := none
  deriving Inhabited, Repr, BEq

initialize paperDescribeExt :
    SimplePersistentEnvExtension (Name × PaperDescribeRule) (NameMap PaperDescribeRule) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, r) => m.insert n r
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (n, r) => m.insert n r
  }

def getPaperDescribeRule? (env : Environment) (decl : Name) : Option PaperDescribeRule :=
  (paperDescribeExt.getState env).get? decl

/-- Optional hooks populated by `Core/ContextProfile.lean` and `CC/Ontology.lean` so `Presentation`
remains strictly below `Overlay`, `ContextProfile`, and `CC` in the module DAG. -/
initialize pp06ProfileCheckHookRef : IO.Ref (Environment → Name → Bool) ←
  IO.mkRef (fun _ _ => false)

initialize ccKnownCarrierHookRef : IO.Ref (Expr → MetaM Bool) ←
  IO.mkRef (fun _ => pure false)

def registerPP06ProfileCheckHook (f : Environment → Name → Bool) : IO Unit :=
  pp06ProfileCheckHookRef.set f

def registerCCKnownCarrierHook (f : Expr → MetaM Bool) : IO Unit :=
  ccKnownCarrierHookRef.set f

/-! ## 4. Compile-Time Validation & Pure-Data Template Helpers -/

/-- Verify that unescaped `{` and `}` braces are balanced in `s`. -/
def validateBalancedBraces (s : String) : Except String Unit := Id.run do
  let arr := s.toList.toArray
  let mut depth : Int := 0
  let mut i := 0
  while i < arr.size do
    let c := arr[i]!
    if c == '\\' && i + 1 < arr.size then
      let nxt := arr[i + 1]!
      if nxt == '{' || nxt == '}' then
        i := i + 2
        continue
    if c == '{' then
      depth := depth + 1
    else if c == '}' then
      depth := depth - 1
      if depth < 0 then
        return .error ("Unbalanced closing '}' in LaTeX template: " ++ s)
    i := i + 1
  if depth != 0 then
    return .error ("Unclosed '{' in LaTeX template: " ++ s)
  return .ok ()

/-- Collect explicit non-Prop argument binder names of a constant's telescope in order. -/
def getExplicitNonPropBinders (declName : Name) : MetaM (Array Name × Expr) := do
  let info ← getConstInfo declName
  forallTelescope info.type fun fvars bodyTy => do
    let mut names : Array Name := #[]
    for fv in fvars do
      let d ← fv.fvarId!.getDecl
      if d.binderInfo.isExplicit then
        let skipProp ← try isProp d.type catch _ => pure false
        if !skipProp then
          names := names.push (cleanBinderName d.userName "x").toName
    return (names, bodyTy)

/-- Collect explicit non-Prop arguments of an application matching `LeanTeX.collectExplicitArgs`. -/
def collectExplicitNonPropArgs (ty : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let mut curTy := ty
  let mut out : Array Expr := #[]
  for arg in args do
    let f ← match curTy.consumeMData with
      | x@(.forallE ..) => pure x
      | other => withTransparency .reducible (whnf other)
    match f.consumeMData with
    | .forallE _ dom body bi =>
        if bi.isExplicit then
          let skipProof ←
            if !dom.hasLooseBVars then
              (try isProp dom catch _ => pure false)
            else pure false
          if !skipProof then
            out := out.push arg
        curTy := body.instantiate1 arg
    | _ =>
        out := out.push arg
  return out

private def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

private def parseNat? (s : String) : Option Nat :=
  if s.isEmpty || !s.all isAsciiDigit then none else s.toNat?

private def hasSubstr (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

def isFormulaForgeryString (s : String) : Bool :=
  hasSubstr s "\\forall" || hasSubstr s "\\exists" || hasSubstr s "\\iff" ||
  hasSubstr s "\\implies" || hasSubstr s "\\Rightarrow" || hasSubstr s "\\Leftrightarrow" ||
  hasSubstr s "\\approx" || hasSubstr s "\\simeq" || hasSubstr s "\\equiv" ||
  hasSubstr s "\\in" || hasSubstr s "\\subseteq" ||
  hasSubstr s "\\wedge" || hasSubstr s "\\vee" || hasSubstr s "\\neg" ||
  hasSubstr s "\\to" || hasSubstr s "\\rightarrow" || hasSubstr s "\\mapsto" ||
  hasSubstr s "\\lt" || hasSubstr s "\\gt" ||
  hasSubstr s "∀" || hasSubstr s "∃" || hasSubstr s "↔" ||
  hasSubstr s "=" || hasSubstr s "<" || hasSubstr s ">" ||
  hasSubstr s "\\neq" || hasSubstr s "\\ne" ||
  hasSubstr s "\\le" || hasSubstr s "\\ge"

/-- Reject 0-arg `Prop` constants or formula-string forgery in `@[math_notation]`. -/
def validatePropNotation (declName : Name) (bodyTy : Expr) (tmpl : String)
    (visibleCount : Nat) : MetaM Unit := do
  let bodyWhnf ← whnf bodyTy
  if bodyWhnf == Expr.sort .zero then
    if visibleCount == 0 then
      throwError "Formula-forgery guard: `@[math_notation]` cannot alias 0-ary `Prop` `{declName}` to a display string; use `@[math_pred]` or prove equivalence."
    if isFormulaForgeryString tmpl then
      throwError "Formula-forgery guard: `@[math_notation]` on `Prop`-valued `{declName}` cannot contain logical/relational formula syntax (`{tmpl}`); use `@[math_pred]` or an operator symbol."

/-- Extract 1-based `#k` placeholders from a notation template and validate bounds. -/
def validateNotationTemplate (declName : Name) (explicitCount : Nat)
    (hidden sub sup : List Nat) (tmpl : String) : MetaM Unit := do
  match validateBalancedBraces tmpl with
  | .error msg => throwError "{declName}: {msg}"
  | .ok () => pure ()
  for i in hidden do
    if i ≥ explicitCount then
      throwError "{declName}: `hide` index {i} out of bounds (explicit non-Prop arity is {explicitCount})"
  for i in sub do
    if i ≥ explicitCount then
      throwError "{declName}: `sub` index {i} out of bounds (explicit non-Prop arity is {explicitCount})"
  for i in sup do
    if i ≥ explicitCount then
      throwError "{declName}: `sup` index {i} out of bounds (explicit non-Prop arity is {explicitCount})"
  let visibleCount := (List.range explicitCount).countP (fun i => !hidden.contains i)
  let arr := tmpl.toList.toArray
  let mut i := 0
  while i < arr.size do
    if arr[i]! == '#' && i + 1 < arr.size && isAsciiDigit arr[i + 1]! then
      let mut j := i + 1
      let mut digits : List Char := []
      while j < arr.size && isAsciiDigit arr[j]! do
        digits := arr[j]! :: digits
        j := j + 1
      let slot := (String.ofList digits.reverse).toNat!
      if slot == 0 || slot > visibleCount then
        throwError "{declName}: template placeholder `#{slot}` out of bounds (visible explicit arity is {visibleCount})"
      i := j
    else
      i := i + 1

/-- Compile `symbolLatex?` + `hiddenArgs` + `subscriptArgs` + `superscriptArgs` into a `#1`, `#2`, ...
template string compatible with `LeanTeX.SymbolTable.constTemplates`. -/
def compileNotationTemplate? (entry : MathPresentationEntry) (explicitCount : Nat) :
    Option String := Id.run do
  if let some tmpl := entry.notationTemplate? then
    if hasSubstr tmpl "#1" || hasSubstr tmpl "#2" || hasSubstr tmpl "#3" then
      return some tmpl
  if entry.subscriptArgs.isEmpty && entry.superscriptArgs.isEmpty then
    return none
  let some sym := entry.symbolLatex? | return none
  let visibleIndices := (List.range explicitCount).filter (fun i => !entry.hiddenArgs.contains i)
  let slotOf (expIdx : Nat) : Option String :=
    match visibleIndices.findIdx? (· == expIdx) with
    | some pos => some ("#" ++ toString (pos + 1))
    | none => none
  let subSlots := entry.subscriptArgs.filterMap slotOf
  let supSlots := entry.superscriptArgs.filterMap slotOf
  let restSlots := visibleIndices.filterMap fun idx =>
    if entry.subscriptArgs.contains idx || entry.superscriptArgs.contains idx then none
    else slotOf idx
  let mut out := sym
  if !subSlots.isEmpty then
    out := out ++ "_{" ++ String.intercalate ", " subSlots ++ "}"
  if !supSlots.isEmpty then
    out := out ++ "^{" ++ String.intercalate ", " supSlots ++ "}"
  if !restSlots.isEmpty then
    out := out ++ "\\!\\left(" ++ String.intercalate ", " restSlots ++ "\\right)"
  return some out

/-- Resolve `{0}`, `{K}`, `{self}` placeholders in a pure-data `qualifier` or `hover` template
against `declName`'s explicit non-Prop telescope binders at registration time.
Ignores TeX command/sub/sup braces like `\mathcal{E}`, `_{0}`, `^{1}`. -/
def resolveTemplatePlaceholders (declName : Name) (binderNames : Array Name)
    (tmpl : String) (allowSelf : Bool := false) : MetaM String := do
  match validateBalancedBraces tmpl with
  | .error msg => throwError "{declName}: {msg}"
  | .ok () => pure ()
  let arr := tmpl.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < arr.size do
    let c := arr[i]!
    let prev? := if i > 0 then some arr[i - 1]! else none
    let isLatexArgBrace := match prev? with
      | some '_' | some '^' | some '\\' => true
      | some p => p.isAlpha
      | none => false
    if c == '{' && !isLatexArgBrace then
      let mut j := i + 1
      let mut tok : List Char := []
      let mut simple := true
      while j < arr.size && arr[j]! != '}' do
        if arr[j]! == '{' || arr[j]! == ' ' then
          simple := false
        tok := arr[j]! :: tok
        j := j + 1
      let tokStr := String.ofList tok.reverse
      if simple && j < arr.size && arr[j]! == '}' && !tokStr.isEmpty then
        if tokStr == "self" then
          if !allowSelf then
            throwError "{declName}: `self` placeholder is only permitted in `hover` templates"
          out := out ++ "{self}"
          i := j + 1
          continue
        else if let some idx := parseNat? tokStr then
          if idx ≥ binderNames.size then
            throwError "{declName}: template placeholder index {idx} out of bounds (explicit non-Prop arity is {binderNames.size})"
          out := out ++ "{" ++ toString idx ++ "}"
          i := j + 1
          continue
        else
          match binderNames.findIdx? (fun nm => nm.toString == tokStr) with
          | some idx =>
              out := out ++ "{" ++ toString idx ++ "}"
              i := j + 1
              continue
          | none =>
              if tokStr.all (fun ch => ch.isAlphanum || ch == '_') then
                throwError "{declName}: unknown template placeholder `{tokStr}` (expected {binderNames.toList} or 0..{binderNames.size - 1})"
    out := out.push c
    i := i + 1
  return out

/-- Pure-data expansion of a validated `{0}`, `{1}`, `{self}` template on live `Expr` arguments
(including open `Expr.fvar`s), with ZERO `Meta.evalExpr`. -/
def expandPureTemplate (tbl : SymbolTable) (tmpl : String) (expArgs : Array Expr)
    (selfTex? : Option String := none) : MetaM String := do
  let mut out := tmpl
  if let some selfTex := selfTex? then
    out := out.replace "{self}" s!"\\({selfTex}\\)"
  for idx in [:expArgs.size] do
    let slot := "{" ++ toString idx ++ "}"
    if hasSubstr out slot then
      let argTex ← exprToLatex expArgs[idx]! tbl
      out := out.replace slot s!"\\({argTex}\\)"
  return out

/-- Verify that every field name in `unpackFields` belongs to structure `declName`. -/
def validateUnpackFields (declName : Name) (fields : Array String) : MetaM Unit := do
  if fields.isEmpty then return ()
  let env ← getEnv
  let some sinfo := Lean.getStructureInfo? env declName
    | throwError "`{declName}` is not a structure, so `unpack := [...]` is invalid"
  for f in fields do
    if !sinfo.fieldNames.contains f.toName then
      throwError "`{f}` is not a field of structure `{declName}` (fields: {sinfo.fieldNames.toList})"

/-! ## 5. Syntax & Attributes (`@[math_notation]`, `@[paper_describe]`, etc.) -/

syntax (name := paperDescribeForCmd) "paper_describe_for" ident str paperDescribeOpt* : command
syntax (name := paperModuleCmd) "paper_module" : command
syntax (name := scopedNotationCmd) "scoped_notation" ident str mathNotationOpt* : command

private def parseBoolIdent (stx : Syntax) : CoreM Bool := do
  match stx.getId with
  | `true => return true
  | `false => return false
  | other => throwError "expected `true` or `false`, got `{other}`"

private def parseVarStyleStx (stx : TSyntax `paperVarStyle) : CoreM MathFontStyle := do
  let rawName : Name := match stx with
    | `(paperVarStyle| .$id:ident) => id.getId
    | `(paperVarStyle| $id:ident) => id.getId
    | _ => `italic
  match rawName.toString with
  | "italic" => return .italic
  | "mathcal" => return .mathcal
  | "mathbf" => return .mathbf
  | "mathbb" => return .mathbb
  | "mathsf" => return .mathsf
  | other => throwError "unknown `varStyle`: `{other}` (expected italic, mathcal, mathbf, mathbb, or mathsf)"

private def parseMathNotationOpts (opts : Array (TSyntax `mathNotationOpt)) :
    CoreM (Bool × List Nat × List Nat × List Nat) := do
  let mut zeroArg := false
  let mut hide : List Nat := []
  let mut sub : List Nat := []
  let mut sup : List Nat := []
  for opt in opts do
    match opt with
    | `(mathNotationOpt| (zeroArg := $b:ident)) =>
        zeroArg ← parseBoolIdent b
    | `(mathNotationOpt| (hide := [$nums:num,*])) =>
        hide := nums.getElems.toList.map (·.getNat)
    | `(mathNotationOpt| (sub := [$nums:num,*])) =>
        sub := nums.getElems.toList.map (·.getNat)
    | `(mathNotationOpt| (sup := [$nums:num,*])) =>
        sup := nums.getElems.toList.map (·.getNat)
    | _ => throwError "unexpected math_notation option"
  return (zeroArg, hide, sub, sup)

private def addMathNotationFor (declName : Name) (tmpl : String)
    (opts : Array (TSyntax `mathNotationOpt)) : MetaM Unit := do
  let (zeroArg, hide, sub, sup) ← parseMathNotationOpts opts
  let (binders, bodyTy) ← getExplicitNonPropBinders declName
  let explicitCount := binders.size
  let visibleCount := (List.range explicitCount).countP (fun i => !hide.contains i)
  validateNotationTemplate declName explicitCount hide sub sup tmpl
  validatePropNotation declName bodyTy tmpl visibleCount
  let hasSlot := hasSubstr tmpl "#1" || hasSubstr tmpl "#2" || hasSubstr tmpl "#3"
  let entry : MathPresentationEntry := {
    symbolLatex? := if hasSlot then none else some tmpl
    notationTemplate? := if hasSlot then some tmpl else none
    hiddenArgs := hide
    subscriptArgs := sub
    superscriptArgs := sup
    isZeroArgNotation := zeroArg
    explicitNonPropArity? := some explicitCount
  }
  modifyEnv fun env => mathPresentationExt.addEntry env (declName, entry)

initialize registerBuiltinAttribute {
  name := `math_notation
  descr := "Register compile-time checked mathematical notation for a declaration"
  add := fun declName stx _ => do
    match stx with
    | `(attr| math_notation $tmpl:str $opts:mathNotationOpt*) =>
        let _ ← MetaM.run' <| addMathNotationFor declName tmpl.getString opts
    | _ => throwError "unexpected `@[math_notation]` syntax"
}

initialize registerBuiltinAttribute {
  name := `math_pred
  descr := "Register a natural-language predicate phrase for a Prop-returning declaration"
  add := fun declName stx _ => do
    match stx with
    | `(attr| math_pred $phrase:str) =>
        let _ ← MetaM.run' do
          let (binders, bodyTy) ← getExplicitNonPropBinders declName
          let bodyWhnf ← whnf bodyTy
          if bodyWhnf != Expr.sort .zero then
            throwError "`@[math_pred]` requires a `Prop`-returning declaration; `{declName}` returns `{← ppExpr bodyTy}`"
          match validateBalancedBraces phrase.getString with
          | .error msg => throwError "{declName}: {msg}"
          | .ok () => pure ()
          modifyEnv fun env => mathPresentationExt.addEntry env (declName, {
            predPhrase? := some phrase.getString
            explicitNonPropArity? := some binders.size
          })
    | _ => throwError "unexpected `@[math_pred]` syntax"
}

initialize registerBuiltinAttribute {
  name := `math_opaque
  descr := "Mark a declaration as an opaque proof stop for informalization"
  add := fun declName _ _ => do
    modifyEnv fun env => mathPresentationExt.addEntry env (declName, { isOpaqueLeaf := true })
}

initialize registerBuiltinAttribute {
  name := `math_wrapper
  descr := "Mark a helper lemma as a trivial forwarding/wrapper step"
  add := fun declName _ _ => do
    modifyEnv fun env => mathPresentationExt.addEntry env (declName, { isWrapper := true })
}

initialize registerBuiltinAttribute {
  name := `math_joint
  descr := "Mark a lemma as a prominent proof joint that Paper mode must never inline"
  add := fun declName _ _ => do
    modifyEnv fun env => mathPresentationExt.addEntry env (declName, { isProofJoint := true })
}

initialize registerBuiltinAttribute {
  name := `paper_role
  descr := "Attach an explicit semantic role or noun override to a declaration"
  add := fun declName stx _ => do
    match stx with
    | `(attr| paper_role $r:str) =>
        let roleStr := r.getString.trimAscii.toString
        if roleStr.isEmpty then
          throwError "`@[paper_role]` string must not be empty"
        modifyEnv fun env => mathPresentationExt.addEntry env (declName, { paperRole? := some roleStr })
    | _ => throwError "unexpected `@[paper_role]` syntax"
}

initialize registerBuiltinAttribute {
  name := `interface_resource_noun
  descr := "Attach an explicit (singular, plural) resource noun to an Interface declaration"
  add := fun declName stx _ => do
    match stx with
    | `(attr| interface_resource_noun $sg:str $pl:str) =>
        modifyEnv fun env => mathPresentationExt.addEntry env (declName, {
          interfaceResourceNoun? := some (sg.getString, pl.getString)
        })
    | _ => throwError "unexpected `@[interface_resource_noun]` syntax"
}

initialize registerBuiltinAttribute {
  name := `paper_module
  descr := "Activate linter.paperPresentation and presentation-grade audit checks on a declaration"
  add := fun declName _ _ => do
    modifyEnv fun env => paperModuleExt.addEntry env declName
}

private def addPaperDescribeFor (declName : Name) (sg : String)
    (opts : Array (TSyntax `paperDescribeOpt)) : MetaM Unit := do
  let mut plural := sg ++ "s"
  let mut isGenericCarrier := false
  let mut varStyle? : Option MathFontStyle := none
  let mut qualRaw? : Option String := none
  let mut unpack : Array String := #[]
  let mut hoverRaw? : Option String := none
  for opt in opts do
    match opt with
    | `(paperDescribeOpt| (plural := $p:str)) =>
        plural := p.getString
    | `(paperDescribeOpt| (carrier := $b:ident)) =>
        isGenericCarrier ← parseBoolIdent b
    | `(paperDescribeOpt| (varStyle := $vs:paperVarStyle)) =>
        varStyle? := some (← parseVarStyleStx vs)
    | `(paperDescribeOpt| (qualifier := $q:str)) =>
        qualRaw? := some q.getString
    | `(paperDescribeOpt| (unpack := $[#%$_]? [$items:paperUnpackItem,*])) =>
        for item in items.getElems do
          match item with
          | `(paperUnpackItem| $id:ident) => unpack := unpack.push id.getId.toString
          | `(paperUnpackItem| $s:str) => unpack := unpack.push s.getString
          | _ => throwError "unexpected unpack field item"
    | `(paperDescribeOpt| (hover := $h:str)) =>
        hoverRaw? := some h.getString
    | _ => throwError "unexpected `paper_describe` option"
  validateUnpackFields declName unpack
  let (binders, _) ← getExplicitNonPropBinders declName
  let qualifierTemplate? ← qualRaw?.mapM fun q =>
    resolveTemplatePlaceholders declName binders q (allowSelf := false)
  let hoverTemplate? ← hoverRaw?.mapM fun h =>
    resolveTemplatePlaceholders declName binders h (allowSelf := true)
  let rule : PaperDescribeRule := {
    noun := ⟨sg, plural⟩
    isGenericCarrier
    varStyle?
    qualifierTemplate?
    unpackFields := unpack
    hoverTemplate?
  }
  modifyEnv fun env => paperDescribeExt.addEntry env (declName, rule)

initialize registerBuiltinAttribute {
  name := `paper_describe
  descr := "Attach pure-data paper description metadata (noun, carrier, varStyle, qualifier, unpack, hover)"
  add := fun declName stx _ => do
    match stx with
    | `(attr| paper_describe $sg:str $opts:paperDescribeOpt*) =>
        let _ ← MetaM.run' <| addPaperDescribeFor declName sg.getString opts
    | _ => throwError "unexpected `@[paper_describe]` syntax"
}

elab_rules : command
  | `(paper_describe_for $id:ident $sg:str $opts:paperDescribeOpt*) => do
      let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      Command.liftTermElabM <| addPaperDescribeFor declName sg.getString opts
  | `(paper_module) => do
      modifyEnv fun env => paperModuleExt.addEntry env env.header.mainModule
      Command.modifyScope fun s => { s with opts := linter.paperPresentation.set s.opts true }
  | `(scoped_notation $id:ident $tmpl:str $opts:mathNotationOpt*) => do
      let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
      Command.liftTermElabM <| addMathNotationFor declName tmpl.getString opts

/-! ## 6. Font-Style Hook (`varStyle?` & Algebraic `.mathbb` Detection) -/

private def algebraicTypeclassHeads : List Name :=
  [ `Group, `AddGroup, `CommGroup, `AddCommGroup,
    `Field, `Ring, `CommRing, `Semiring, `CommSemiring,
    `Monoid, `AddMonoid, `CommMonoid, `AddCommMonoid ]

private def detectFVarMathStyle (fv : FVarId) (ty : Expr) : MetaM (Option MathFontStyle) := do
  let env ← getEnv
  if let .const head _ := ty.getAppFn.consumeMData then
    if let some rule := getPaperDescribeRule? env head then
      if let some st := rule.varStyle? then
        return some st
  if ty.consumeMData.isSort then
    let lctx ← getLCtx
    for d in lctx do
      if d.isImplementationDetail then continue
      let dtype := d.type.consumeMData
      if let .const clsHead _ := dtype.getAppFn.consumeMData then
        if algebraicTypeclassHeads.contains clsHead then
          for arg in dtype.getAppArgs do
            if arg.consumeMData == .fvar fv then
              return some .mathbb
  return none

initialize registerFVarStyleHook detectFVarMathStyle

/-! ## 7. Opt-In Presentation Linter (`linter.paperPresentation`: `PP01`–`PP06`) -/

private def isCompilerGeneratedName (n : Name) : Bool :=
  let s := n.toString
  hasSubstr s "._proof_" || hasSubstr s "._simp_" || hasSubstr s "._eq_" ||
  hasSubstr s "._match_" || hasSubstr s ".match_"

private def isLinterSkipDecl (env : Environment) (n : Name) : Bool :=
  let isRec := match env.find? n with | some (.recInfo _) => true | _ => false
  Lean.isPrivateName n || isCompilerGeneratedName n || env.isProjectionFn n ||
  env.isConstructor n || isRec || n.toString.endsWith ".mk"

private def isLibraryDeclForLint (env : Environment) (n : Name) : Bool :=
  let s := n.toString
  let root := n.getRoot
  root == `Lean || root == `Init || root == `Std || root == `Mathlib ||
  root == `Battery || root == `Batteries || root == `Qq ||
  root == `Informalization || root == `ConstructiveCryptography ||
  root == `RandomSystems || root == `SystemAlgebra || root == `Probability ||
  s.startsWith "Aesop" || s.startsWith "Auto" ||
  (env.getModuleIdxFor? n).any fun idx =>
    let modStr := (env.header.moduleNames[idx.toNat]?.map (·.toString)).getD ""
    modStr.startsWith "Init." || modStr.startsWith "Std." ||
    modStr.startsWith "Lean." || modStr.startsWith "Mathlib." ||
    modStr.startsWith "Batteries."

private def isScalarOrBasicType (ty : Expr) : Bool :=
  let t := ty.consumeMData
  t.isSort || t == mkConst ``Nat || t == mkConst ``Int || t == mkConst ``Bool ||
  t == mkConst ``Unit || t == mkConst ``PUnit || t == mkConst ``String ||
  t == mkConst `Real || t == mkConst `NNReal || t == mkConst `ENNReal ||
  t.isAppOf ``List || t.isAppOf ``Fin || t.isAppOf ``Option ||
  t.isAppOf ``Prod || t.isAppOf ``Subtype || t.isAppOf ``Sigma ||
  t.isAppOf `ZMod || t.isAppOf `Finset || t.isForall

private def styleTagOfLatex (s : String) : MathFontStyle × String :=
  if hasSubstr s "\\mathcal{" then (.mathcal, (s.replace "\\mathcal{" "").replace "}" "")
  else if hasSubstr s "\\mathbf{" then (.mathbf, (s.replace "\\mathbf{" "").replace "}" "")
  else if hasSubstr s "\\mathbb{" then (.mathbb, (s.replace "\\mathbb{" "").replace "}" "")
  else if hasSubstr s "\\mathsf{" then (.mathsf, (s.replace "\\mathsf{" "").replace "}" "")
  else (.italic, s)

private def emitPaperLint (stx : Syntax) (msg : MessageData) : CommandElabM Unit := do
  let opts ← _root_.Lean.Linter.getLinterOptions
  if _root_.Lean.Linter.getLinterValue linter.paperPresentation opts then
    _root_.Lean.Linter.logLint linter.paperPresentation stx msg
  else
    logWarningAt stx (m!"[paperPresentation] " ++ msg)

private def lintDeclPresentation (stx : Syntax) (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  if isLinterSkipDecl env declName then return ()
  let some info := env.find? declName | return ()
  let isThm := match info with | .thmInfo _ => true | _ => false
  let isStructOrInduct := match info with | .inductInfo _ => true | _ => false
  let (pp01Msg?, pp03Msg?, pp05BindersMsg?, pp06Msgs, referencedProjConsts) ←
    liftTermElabM do
      forallTelescope info.type fun fvars bodyTy => do
        let bodyClean ← whnf bodyTy
        let isSortBody := bodyClean.isSort && bodyClean != Expr.sort .zero
        -- PP01: missing @[paper_describe] on Type-valued def/structure/inductive
        let pp01 : Option MessageData :=
          if !isThm && (isStructOrInduct || isSortBody) &&
             (getPaperDescribeRule? env declName).isNone then
            some m!"[PP01] Type/structure `{.ofConstName declName}` lacks `@[paper_describe]` or `paper_describe_for`."
          else none
        -- PP03 & PP05 & PP06 over explicit non-Prop parameters
        let mut seenRender : Std.HashMap (String × String) String := {}
        let mut pp03 : Option MessageData := none
        let mut pp05Binders : Array String := #[]
        let mut pp06 : Array MessageData := #[]
        let mut projConsts : Array Name := #[]
        for fv in fvars do
          let d ← fv.fvarId!.getDecl
          if d.isImplementationDetail || !d.binderInfo.isExplicit then continue
          if ← isAmbientTypeclass d.type then continue
          if ← isProp d.type then continue
          let rawName := d.userName.eraseMacroScopes.toString
          if hasSubstr rawName "_vcc_" || hasSubstr rawName "_proof_" || hasSubstr rawName "_since_" then
            pp05Binders := pp05Binders.push rawName
          -- PP03 binder style + stem
          let clean := cleanBinderName d.userName "x"
          let st := (← detectFVarMathStyle fv.fvarId! d.type).getD .italic
          let stKey := toString (repr st)
          let prev? := seenRender.get? (stKey, clean)
          if let some prev := prev? then
            if prev != s!"binder:{fv.fvarId!.name}" && pp03.isNone then
              pp03 := some m!"[PP03] Symbol collision in `{.ofConstName declName}`: `{clean}` collides with `{prev}` under style `{stKey}`."
          else
            seenRender := seenRender.insert (stKey, clean) s!"binder:{clean}"
          -- PP06 un-contextualized domain carrier / parameter check
          if !isScalarOrBasicType d.type then
            let knownCC ← (← ccKnownCarrierHookRef.get) d.type
            if !knownCC then
              if let .const tyHead _ := d.type.getAppFn.consumeMData then
                if !isLibraryDeclForLint env tyHead then
                  let rule? := getPaperDescribeRule? env tyHead
                  let mp := getMathPresentation env tyHead
                  let hasExplicitDesc := match rule? with
                    | some r => !r.isGenericCarrier
                    | none => false
                  let hasRole := mp.paperRole?.isSome || mp.interfaceResourceNoun?.isSome
                  let hasProfile := (← pp06ProfileCheckHookRef.get) env declName
                  if !hasExplicitDesc && !hasRole && !hasProfile then
                    pp06 := pp06.push
                      m!"[PP06] Domain parameter `{clean}` of type `{.ofConstName tyHead}` in `{.ofConstName declName}` has no `@[paper_describe]`, `@[paper_role]`, or `paper_context`."
        -- Collect project constants in type for PP02 and PP03
        let typeConsts := info.type.foldConsts (init := (#[] : Array Name)) fun cn acc =>
          if acc.contains cn then acc else acc.push cn
        for cn in typeConsts do
          if env.isProjectionFn cn && !isLibraryDeclForLint env cn then
            let mp := getMathPresentation env cn
            if mp.symbolLatex?.isNone && mp.notationTemplate?.isNone &&
               !mp.isWrapper && !mp.isOpaqueLeaf then
              projConsts := projConsts.push cn
          if !isLibraryDeclForLint env cn && !isLinterSkipDecl env cn then
            let mp := getMathPresentation env cn
            if let some sym := mp.symbolLatex? then
              let (st, stem) := styleTagOfLatex sym
              let stKey := toString (repr st)
              if let some prev := seenRender.get? (stKey, stem) then
                if prev != s!"const:{cn}" && pp03.isNone then
                  pp03 := some m!"[PP03] Symbol collision in `{.ofConstName declName}`: constant `{.ofConstName cn}` (`{sym}`) collides with `{prev}`."
              else
                seenRender := seenRender.insert (stKey, stem) s!"const:{cn}"
        let pp05Msg :=
          if pp05Binders.isEmpty then none
          else some m!"[PP05] Leaked internal binder name(s) {pp05Binders.toList} in `{.ofConstName declName}`."
        return (pp01, pp03, pp05Msg, pp06, projConsts)
  if let some m := pp01Msg? then
    emitPaperLint stx m
  -- PP02: un-annotated opaque accessors/projections (cap 3)
  let mut pp02Count := 0
  for cn in referencedProjConsts do
    if pp02Count < 3 then
      emitPaperLint stx m!"[PP02] Projection/accessor `{.ofConstName cn}` referenced in `{.ofConstName declName}` has no `@[math_notation]`, `@[math_wrapper]`, or `@[math_opaque]`."
      pp02Count := pp02Count + 1
  if let some m := pp03Msg? then
    emitPaperLint stx m
  -- PP04: check notation entry on this declaration if any
  let mpSelf := getMathPresentation env declName
  if let some tmpl := mpSelf.notationTemplate? <|> mpSelf.symbolLatex? then
    if let .error errMsg := validateBalancedBraces tmpl then
      emitPaperLint stx m!"[PP04] {errMsg}"
  -- PP05: sorryAx or leaked binder names
  if let some val := info.value? then
    if exprContainsSorryAx val then
      emitPaperLint stx m!"[PP05] Declaration `{.ofConstName declName}` uses `sorryAx`."
  if let some m := pp05BindersMsg? then
    emitPaperLint stx m
  for m in pp06Msgs do
    emitPaperLint stx m

def paperPresentationLinter : _root_.Lean.Elab.Command.Linter where
  run := Lean.withSetOptionIn fun stx => do
    if (← get).messages.hasErrors then return
    let env ← getEnv
    let opts ← _root_.Lean.Linter.getLinterOptions
    let mut decls : List Name := []
    for t in ← getInfoTrees do
      for d in _root_.Lean.Linter.getNewDecls t do
        if !decls.contains d then decls := d :: decls
      for d in _root_.Lean.Linter.getDeclsByBody t do
        if !decls.contains d then decls := d :: decls
    unless isPaperPresentationActive env opts decls do
      return
    for d in decls.reverse do
      lintDeclPresentation stx d

initialize _root_.Lean.Elab.Command.addLinter paperPresentationLinter

end Informalization.Core.Presentation
