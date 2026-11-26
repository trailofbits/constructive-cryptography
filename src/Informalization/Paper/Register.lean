/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Register
import Informalization.Core.Overlay
import Informalization.Core.Presentation
import Informalization.Core.ContextProfile

/-!
# Paper-Centric Section Register, Setting, and Construction Commands

Lean elaboration commands allowing `Paper/*.lean` formalizations to declare:

* `paper_register <nsOrDecl> <gameBased | constructive | randomSystems>`
  (`paper_register_ns` for explicit namespace-wide contracts),
* `paper_setting <nsOrDecl> "prose..." (suppress := [...]) (suppress_preds := [...])`
  (`paper_setting_ns` for namespace-wide settings, with optional `(anchor := decl)`),
* `paper_construction <anchorDecl> "Label" "Title" "optional motivation" (lines := [...])`,
* `paper_motivation <anchorDecl> "prose..."`,
* `paper_table <anchorDecl> "Label" "Title" "intro" (rows := [("Col1", "Col2"), ...])`
  (checked to forbid per-theorem `Parameter | Meaning` dumps).

Every command resolves concrete declarations at compile time via
`realizeGlobalConstNoOverloadWithInfo` or namespace scopes cleanly without compiler reflection
auto-glosses.
-/

namespace Informalization.Paper.Register

open Lean Elab Command Term Meta
open Informalization.Core.Register
open Informalization.Core.Overlay

private def resolveDeclOnly (id : Ident) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

private def resolveNamespaceScope (id : Ident) : CommandElabM Name := do
  try
    liftCoreM <| Lean.resolveUniqueNamespace id
  catch err =>
    let env ← getEnv
    let currNs ← liftCoreM getCurrNamespace
    let raw := id.getId
    if env.isNamespace raw then
      return raw
    else if !currNs.isAnonymous &&
        (currNs == raw || currNs.componentsRev.head? == some raw) then
      return currNs
    else if !currNs.isAnonymous && env.isNamespace (currNs ++ raw) then
      return currNs ++ raw
    else
      throw err

/-- Resolve `<nsOrDecl>` as either a concrete declaration (`isDecl := true`) or a namespace
(`isDecl := false`). -/
private def resolveScopeOrDecl (id : Ident) : CommandElabM (Name × Bool) := do
  try
    let decl ← resolveDeclOnly id
    return (decl, true)
  catch _ =>
    let ns ← resolveNamespaceScope id
    return (ns, false)

private def parseRegisterIdent (regStx : Ident) : CommandElabM CryptoRegister := do
  let raw := regStx.getId.toString
  match CryptoRegister.ofString? raw with
  | some reg => return reg
  | none =>
      throwErrorAt regStx
        m!"unknown cryptographic register `{raw}`; expected `gameBased`, `constructive`, or `randomSystems`"

/-- Preserve the existing register for `scope` (or parent namespace) so `mergeSectionSpec` never
silently resets `.gameBased` / `.randomSystems` back to `.constructive`. -/
private def preserveRegisterForScope (env : Environment) (scope : Name) : CryptoRegister :=
  (getPaperSectionSpec? env scope).map (·.register) |>.getD .constructive

/-- Bind a `CryptoRegister` (`gameBased`, `constructive`, `randomSystems`) on a declaration or
namespace scope in `paperSectionExt`. -/
elab "paper_register " id:ident reg:ident : command => do
  let (scope, _) ← resolveScopeOrDecl id
  let r ← parseRegisterIdent reg
  modifyEnv fun env => paperSectionExt.addEntry env (scope, { scope, register := r })

/-- Explicitly bind a `CryptoRegister` (`gameBased`, `constructive`, `randomSystems`) across a
namespace in `paperSectionExt`. -/
elab "paper_register_ns " ns:ident reg:ident : command => do
  let scope ← resolveNamespaceScope ns
  let r ← parseRegisterIdent reg
  modifyEnv fun env => paperSectionExt.addEntry env (scope, { scope, register := r })

declare_syntax_cat paperSettingOpt
syntax "(" &"suppress" " := " "[" str,* "]" ")" : paperSettingOpt
syntax "(" &"suppress_preds" " := " "[" ident,* "]" ")" : paperSettingOpt
syntax "(" &"anchor" " := " ident ")" : paperSettingOpt
syntax "(" &"title" " := " str ")" : paperSettingOpt
syntax "(" &"register" " := " ident ")" : paperSettingOpt

private structure ParsedSettingOpts where
  suppressedBinders : Array String := #[]
  suppressedPredicates : Array Name := #[]
  anchorDecl? : Option Name := none
  title? : Option String := none
  register? : Option CryptoRegister := none

private def parseSettingOpts (opts : TSyntaxArray `paperSettingOpt) :
    CommandElabM ParsedSettingOpts := do
  let mut acc : ParsedSettingOpts := {}
  for opt in opts do
    match opt with
    | `(paperSettingOpt| (suppress := [$[$bs:str],*])) =>
        let strs := bs.map (·.getString)
        acc := { acc with suppressedBinders := acc.suppressedBinders ++ strs }
    | `(paperSettingOpt| (suppress_preds := [$[$ps:ident],*])) =>
        let mut resolved : Array Name := #[]
        for p in ps do
          let decl ← resolveDeclOnly p
          resolved := resolved.push decl
        acc := { acc with suppressedPredicates := acc.suppressedPredicates ++ resolved }
    | `(paperSettingOpt| (anchor := $a:ident)) =>
        let decl ← resolveDeclOnly a
        acc := { acc with anchorDecl? := some decl }
    | `(paperSettingOpt| (title := $t:str)) =>
        acc := { acc with title? := some t.getString }
    | `(paperSettingOpt| (register := $r:ident)) =>
        let reg ← parseRegisterIdent r
        acc := { acc with register? := some reg }
    | _ =>
        throwErrorAt opt "unrecognized `paper_setting` option"
  return acc

private def applyPaperSetting (scope : Name) (isDecl : Bool) (prose : String)
    (opts : ParsedSettingOpts) : CommandElabM Unit := do
  let env ← getEnv
  let reg := opts.register?.getD (preserveRegisterForScope env scope)
  let spec : PaperSectionSpec := {
    scope
    register := reg
    title? := opts.title?
    settingProse? := some prose
    suppressedBinders := opts.suppressedBinders
    suppressedPredicates := opts.suppressedPredicates
  }
  modifyEnv fun env => paperSectionExt.addEntry env (scope, spec)
  let targetDecl? := opts.anchorDecl? <|> (if isDecl then some scope else none)
  if let some targetDecl := targetDecl? then
    let preludeSpec : PreludeSpec := {
      kind := "setting"
      label := "Setting"
      title := opts.title?.getD "Section Setting"
      bodyText := prose
      declName? := none
    }
    modifyEnv fun env =>
      overlayExt.addEntry env (targetDecl, {
        sectionTitle? := opts.title?
        sectionPreludes := #[preludeSpec]
      })

/-- Declare flowing prose section setting plus section-fixed binder/predicate suppressions for a
declaration or namespace scope. -/
elab "paper_setting " id:ident prose:str opts:paperSettingOpt* : command => do
  let (scope, isDecl) ← resolveScopeOrDecl id
  let parsed ← parseSettingOpts opts
  applyPaperSetting scope isDecl prose.getString parsed

/-- Namespace-explicit variant of `paper_setting` for section-wide standing assumptions. -/
elab "paper_setting_ns " ns:ident prose:str opts:paperSettingOpt* : command => do
  let scope ← resolveNamespaceScope ns
  let parsed ← parseSettingOpts opts
  applyPaperSetting scope false prose.getString parsed

declare_syntax_cat paperLinesOpt
syntax "(" &"lines" " := " "[" str,* "]" ")" : paperLinesOpt

/-- Attach a purpose-driven construction box with optional motivation and explicit mathematical
steps/equations (`PreludeSpec` of kind `"construction"`), without compiler type glosses. -/
elab "paper_construction " id:ident label:str title:str motivation?:(str)? linesOpt:(paperLinesOpt)? : command => do
  let decl ← resolveDeclOnly id
  let motiv := (motivation?.map (·.getString)).getD ""
  let rawLines : Array String ← match linesOpt with
    | none => pure #[]
    | some lo =>
        match lo with
        | `(paperLinesOpt| (lines := [$[$ls:str],*])) => pure (ls.map (·.getString))
        | _ => throwErrorAt lo "expected `(lines := [\"...\", ...])`"
  let indexed := rawLines.map fun line =>
    let rec countIndent : List Char → Nat → Nat × String
      | ' ' :: cs, n => countIndent cs (n + 1)
      | '\t' :: cs, n => countIndent cs (n + 2)
      | cs, n => (min 3 (n / 2), String.ofList cs)
    countIndent line.toList 0
  let spec : PreludeSpec := {
    kind := "construction"
    label := label.getString
    title := title.getString
    bodyText := motiv
    lines := indexed
    declName? := none
  }
  modifyEnv fun env => overlayExt.addEntry env (decl, { sectionPreludes := #[spec] })

declare_syntax_cat paperTitleOpt
syntax "(" &"title" " := " str ")" : paperTitleOpt

/-- Attach non-claiming section motivation / overview prose (`sectionIntro?`) to a declaration
or namespace. -/
elab "paper_motivation " id:ident prose:str titleOpt:(paperTitleOpt)? : command => do
  let (scope, isDecl) ← resolveScopeOrDecl id
  let tOpt? ← match titleOpt with
    | none => pure none
    | some titleOptStx =>
        match titleOptStx with
        | `(paperTitleOpt| (title := $t:str)) => pure (some t.getString)
        | _ => throwErrorAt titleOptStx "expected `(title := \"...\")`"
  let proseStr := prose.getString
  let env ← getEnv
  let reg := preserveRegisterForScope env scope
  modifyEnv fun env =>
    paperSectionExt.addEntry env (scope, {
      scope
      register := reg
      title? := tOpt?
      motivation? := some proseStr
    })
  if isDecl then
    modifyEnv fun env =>
      overlayExt.addEntry env (scope, {
        sectionTitle? := tOpt?
        sectionIntro? := some proseStr
      })

syntax paperTablePair := "(" str "," str ")"
declare_syntax_cat paperRowsOpt
syntax "(" &"rows" " := " "[" paperTablePair,* "]" ")" : paperRowsOpt

private def isBannedParameterHeader (col : String) : Bool :=
  let low := col.trimAscii.toString.toLower
  ["parameter", "parameters", "symbol", "symbols", "notation", "variable", "variables",
    "binder", "binders", "argument", "arguments"].contains low

/-- Emit a genuine analytical comparison table (`PreludeSpec` of kind `"symbolTable"`). Rejects
per-theorem `Parameter | Meaning` dumps at compile time. -/
elab "paper_table " id:ident label:str title:str intro?:(str)? rowsOpt:(paperRowsOpt)? : command => do
  let decl ← resolveDeclOnly id
  let titleStr := title.getString
  let labelStr := label.getString
  let lowTitle := titleStr.trimAscii.toString.toLower
  if lowTitle.startsWith "parameter" || lowTitle.startsWith "notation" ||
      (lowTitle.splitOn "symbol table").length > 1 then
    throwErrorAt title
      "`paper_table` is only for analytical comparison tables (e.g. Attack Summary); describe parameters in `paper_setting` prose instead."
  let rowPairs : Array (String × String) ← match rowsOpt with
    | none => pure #[]
    | some ro =>
        match ro with
        | `(paperRowsOpt| (rows := [$[$ps:paperTablePair],*])) =>
            ps.mapM fun p =>
              match p with
              | `(paperTablePair| ($c1:str, $c2:str)) => pure (c1.getString, c2.getString)
              | _ => throwErrorAt p "expected `(\"Col1\", \"Col2\")`"
        | _ => throwErrorAt ro "expected `(rows := [(\"Col1\", \"Col2\"), ...])`"
  if let some (h1, _) := rowPairs[0]? then
    if isBannedParameterHeader h1 then
      throwError
        m!"`paper_table` rejected `{h1}` header: parameter/symbol tables are forbidden; use `paper_setting` + inline definitions instead."
  let spec : PreludeSpec := {
    kind := "symbolTable"
    label := labelStr
    title := titleStr
    bodyText := (intro?.map (·.getString)).getD ""
    rows := rowPairs
    declName? := some decl
  }
  modifyEnv fun env => overlayExt.addEntry env (decl, { sectionPreludes := #[spec] })

end Informalization.Paper.Register
