import Lean.Meta.ExprLens
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.HtmlDisplay
import Rendering.Pseudocode
import Rendering.Inspector
import Rendering.Notation
import Rendering.TypeNotation
import Rendering.ProofView

/-!
# Deterministic system diagrams

This theory-free engine projects elaborated expressions through declaration roles
registered by optional semantic adapters. `Rendering.Widget` owns the CC roles.
See `Rendering/README.md` for the interpretation contract and extension workflow.

Binary parallel grouping, category-order serial composition, and all unknown
subterms remain explicit. No algebraic normalization, name-based role inference,
automatic unfolding, simulator inference, or probability simplification occurs.
Native MathML renders registered interface operations; other labels retain Lean's
pretty-printed text. The original statement remains selectable beneath the view.

Importing this module enables `CCDiagram` at the cursor; `set_option cc.diagram.auto false`
disables automatic views. `#cc_diagram_show t`
also displays a term or statement; the check/view commands provide CI diagnostics.
-/

register_option cc.diagram.auto : Bool := {
  defValue := true
  descr := "Show diagrams or recorded DSL source automatically at the cursor."
}

syntax (name := Lean.Parser.Attr.ccDiagram) "cc_diagram" (ppSpace str)? : attr

namespace CCWidget
open Lean Server Meta ProofWidgets

/-! ## Label registration -/

/-- Display labels used by `CCDiagram` for resource/converter constants
appearing in goals, indexed by constant name. -/
initialize ccDiagramLabels : SimpleScopedEnvExtension (Name × String) (NameMap String) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, s) => m.insert n s
    initial := {}
  }

/-- Author-supplied names for exact closed expressions, including every applied argument. -/
initialize ccDiagramTermLabels : SimpleScopedEnvExtension (Expr × String)
    (Array (Expr × String)) ← registerSimpleScopedEnvExtension {
  addEntry := fun labels entry => labels.push entry
  initial := #[] }

/-! ## Extensible semantic declaration roles

The renderer must depend on mathematical roles, not a closed list of Lean
implementation heads.  Argument indices are counted from the end of the fully
applied expression (`0` is the last explicit/implicit argument), which keeps
registrations stable across universe and type parameters. -/

inductive DeclRole where
  | application (converterFromEnd resourceFromEnd : Nat)
  | attachment (interfaceFromEnd converterFromEnd resourceFromEnd : Nat)
  | parallel (leftFromEnd rightFromEnd : Nat)
  | game (systemFromEnd eventFromEnd : Nat)
  | transparent (targetFromEnd : Nat)
  | distance (leftFromEnd rightFromEnd : Nat) (symbol : String)
  | winning (systemFromEnd : Nat) (symbol : String)
  | conditional (leftFromEnd rightFromEnd : Nat)
  | construction (realFromEnd converterFromEnd idealFromEnd : Nat)
  | constructionWithin (realFromEnd converterFromEnd idealFromEnd errorFromEnd : Nat)
  | substitution (leftFromEnd rightFromEnd errorFromEnd : Nat) (symbol : String)
  | whiskerRight (convFromEnd ifaceFromEnd : Nat)
  | whiskerLeft (ifaceFromEnd convFromEnd : Nat)
  | resourceType (interfaceFromEnd : Nat)
  | resourceFamily (categoryFromEnd familyFromEnd : Nat)
  | specificationType (interfaceFromEnd : Nat)
  | converterType (outerFromEnd innerFromEnd : Nat)
  | arrowType (categoryFromEnd outerFromEnd innerFromEnd : Nat)
  | serial (leftFromEnd rightFromEnd : Nat)
  | tensor (leftFromEnd rightFromEnd : Nat)
  | interfaceTensor (leftFromEnd rightFromEnd : Nat)
  | interfaceConstructor
  | identity
  | action
  deriving BEq, Repr, Inhabited

structure DeclRule where
  head : Name
  role : DeclRole
  deriving Repr, Inhabited

initialize ccDiagramRules : SimpleScopedEnvExtension DeclRule (NameMap DeclRole) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m r => m.insert r.head r.role
    initial := {}
  }

/-- Argument positions consumed by each role. -/
def DeclRole.indices : DeclRole → List Nat
  | .application a b | .parallel a b | .game a b | .distance a b _
  | .conditional a b | .converterType a b | .serial a b | .tensor a b
  | .interfaceTensor a b | .resourceFamily a b => [a, b]
  | .attachment a b c | .construction a b c | .arrowType a b c => [a, b, c]
  | .constructionWithin a b c d => [a, b, c, d]
  | .substitution a b c _ => [a, b, c]
  | .whiskerRight a b | .whiskerLeft a b => [a, b]
  | .transparent a | .winning a _ | .resourceType a | .specificationType a => [a]
  | .action | .interfaceConstructor | .identity => []

/-- A resolved, fully applied declaration is the adapter boundary. Registrations
cannot refer to missing or duplicate argument positions. Meaning is audited by
adapter tests, not inferred from the declaration's spelling. -/
def registerRole (n : Syntax) (role : DeclRole) : Elab.Command.CommandElabM Unit := do
  let (name, arity) ← Elab.Command.liftCoreM do
    let name ← Elab.realizeGlobalConstNoOverloadWithInfo n
    return (name, (← getConstInfo name).type.getForallArity)
  unless role.indices.all (· < arity) && role.indices.eraseDups.length == role.indices.length do
    throwError "cc_diagram: invalid argument positions for {name} (arity {arity})"
  if let some previous := (ccDiagramRules.getState (← getEnv)).find? name then
    unless previous == role do throwError "cc_diagram: conflicting role for {name}"
  Elab.Command.liftCoreM <| ccDiagramRules.add { head := name, role } .global

def natOfSyntax (stx : Syntax) : Nat := stx.isNatLit?.getD 0

/-- Actual structure projections supplied by a semantic adapter, in display order. -/
structure InterfaceSchema where
  fields : Array (String × Name)
  deriving BEq, Inhabited

initialize interfaceSchemas : SimpleScopedEnvExtension (Name × InterfaceSchema)
    (NameMap InterfaceSchema) ← registerSimpleScopedEnvExtension {
  addEntry := fun state (name, schema) => state.insert name schema
  initial := {} }

/-- Register labels, input/output families and the history predicate. Each must be an actual
projection of this structure; spellings do not establish an interface's meaning. -/
elab "cc_diagram_interface " n:ident i:ident x:ident y:ident d:ident : command => do
  let (name, fields) ← Elab.Command.liftCoreM do
    let name ← Elab.realizeGlobalConstNoOverloadWithInfo n
    let fields ← #[i, x, y, d].mapM Elab.realizeGlobalConstNoOverloadWithInfo
    for field in fields do
      let some p := (← getEnv).getProjectionFnInfo? field
        | throwError "cc_diagram: {field} is not a structure projection"
      let .ctorInfo ctor ← getConstInfo p.ctorName
        | throwError "cc_diagram: invalid projection constructor"
      unless ctor.induct == name do
        throwError "cc_diagram: {field} is not a projection of {name}"
    unless fields.toList.eraseDups.length == fields.size do
      throwError "cc_diagram: duplicate interface projections"
    return (name, fields)
  let schema : InterfaceSchema := ⟨#["I", "X", "Y", "D"].zip fields⟩
  if let some previous := (interfaceSchemas.getState (← getEnv)).find? name then
    unless previous == schema do throwError "cc_diagram: conflicting interface schema for {name}"
  Elab.Command.liftCoreM <| interfaceSchemas.add (name, schema) .global

syntax (name := ccDiagramApplicationCmd)
  "cc_diagram_application " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramAttachmentCmd)
  "cc_diagram_attachment " ident ppSpace num ppSpace num ppSpace num : command
syntax (name := ccDiagramParallelCmd)
  "cc_diagram_parallel " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramGameCmd)
  "cc_diagram_game " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramTransparentCmd)
  "cc_diagram_transparent " ident ppSpace num : command
syntax (name := ccDiagramRuleCheckCmd) "#cc_diagram_rule_check " ident : command
syntax (name := ccDiagramDistanceCmd)
  "cc_diagram_distance " ident ppSpace num ppSpace num ppSpace str : command
syntax (name := ccDiagramWinningCmd)
  "cc_diagram_winning " ident ppSpace num ppSpace str : command
syntax (name := ccDiagramConditionalCmd)
  "cc_diagram_conditional " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramConstructionCmd)
  "cc_diagram_construction " ident ppSpace num ppSpace num ppSpace num : command

/-- Register `head converter resource` as a serial converter application.
Numeric arguments are positions counted from the end. -/
elab_rules : command
  | `(cc_diagram_application $n:ident $c:num $r:num) =>
      registerRole n (.application (natOfSyntax c) (natOfSyntax r))
  | `(cc_diagram_attachment $n:ident $i:num $c:num $r:num) =>
      registerRole n (.attachment (natOfSyntax i) (natOfSyntax c) (natOfSyntax r))
  | `(cc_diagram_parallel $n:ident $l:num $r:num) =>
      registerRole n (.parallel (natOfSyntax l) (natOfSyntax r))
  | `(cc_diagram_game $n:ident $s:num $e:num) =>
      registerRole n (.game (natOfSyntax s) (natOfSyntax e))
  | `(cc_diagram_transparent $n:ident $t:num) =>
      registerRole n (.transparent (natOfSyntax t))
  | `(cc_diagram_distance $n:ident $l:num $r:num $s:str) =>
      registerRole n (.distance (natOfSyntax l) (natOfSyntax r) s.getString)
  | `(cc_diagram_winning $n:ident $a:num $s:str) =>
      registerRole n (.winning (natOfSyntax a) s.getString)
  | `(cc_diagram_conditional $n:ident $l:num $r:num) =>
      registerRole n (.conditional (natOfSyntax l) (natOfSyntax r))
  | `(cc_diagram_construction $n:ident $r:num $p:num $i:num) =>
      registerRole n (.construction (natOfSyntax r) (natOfSyntax p) (natOfSyntax i))
  | `(#cc_diagram_rule_check $n:ident) => do
      let present ← Elab.Command.liftCoreM do
        let name ← Elab.realizeGlobalConstNoOverloadWithInfo n
        return (ccDiagramRules.getState (← getEnv)).contains name
      unless present do
        throwError "cc_diagram: no semantic rule registered for {n.getId}"

def declRole? (e : Expr) : CoreM (Option DeclRole) := do
  let e := e.consumeMData
  let .const head _ := e.getAppFn | return none
  let some info := (← getEnv).find? head | return none
  unless e.getAppNumArgs == info.type.getForallArity do return none
  return (ccDiagramRules.getState (← getEnv)).find? head

def argFromEnd? (args : Array Expr) (n : Nat) : Option (Nat × Expr) :=
  if n < args.size then
    let i := args.size - 1 - n
    some (i, args[i]!)
  else none

/-- The `cc_diagram` attribute registers a display label — works on
declarations from imported modules too (`attribute [cc_diagram "KEY"] keyRes`). -/
initialize registerBuiltinAttribute {
    name := `ccDiagram
    descr := "display label for the CCDiagram proof widget"
    add := fun declName stx kind => do
      let label ← match stx with
        | `(attr| cc_diagram $s:str) => pure s.getString
        | `(attr| cc_diagram) =>
          match declName with
          | .str _ s => pure s
          | n => pure n.toString
        | _ => throwError "unexpected cc_diagram attribute syntax"
      ccDiagramLabels.add (declName, label) kind
  }

/-- One item of a `cc_diagram_labels` command. -/
syntax ccDiagramLabelItem := ident ppSpace str

/-- `cc_diagram_labels realResource "R", idealResource "S", …` — register display
labels for the `CCDiagram` widget in one line.  Unlike the
`@[cc_diagram]` attribute, the named constants need not exist yet
so the command can sit before their definitions. Forward references must
use fully qualified declaration names; matching is always exact. -/
elab "cc_diagram_labels " items:ccDiagramLabelItem,+ : command => do
  for item in items.getElems do
    match item with
    | `(ccDiagramLabelItem| $n:ident $l:str) =>
      Elab.Command.liftCoreM <| ccDiagramLabels.add (n.getId, l.getString) .global
    | _ => Elab.throwUnsupportedSyntax

/-- Give one exact applied term a display name. No unfolding or unification is used to match it.
`local` limits the name to its section; imported global names retain their compiled expression. -/
elab localName:("local ")? "cc_diagram_name " label:str " := " term:term : command => do
  if label.getString.trimAscii.toString.isEmpty then
    throwError "cc_diagram_name: the display name must not be empty"
  let e ← Elab.Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTerm term none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars then
      throwError "cc_diagram_name: use a closed expression with all types and universes fixed"
    return e
  Elab.Command.liftCoreM <| ccDiagramTermLabels.add (e, label.getString)
    (if localName.isSome then .local else .global)

/-! ## Typed semantic adapters -/

elab "cc_diagram_resource_type " n:ident i:num : command =>
  registerRole n (.resourceType i.getNat)
elab "cc_diagram_resource_family " n:ident c:num f:num : command =>
  registerRole n (.resourceFamily c.getNat f.getNat)
elab "cc_diagram_specification_type " n:ident i:num : command =>
  registerRole n (.specificationType i.getNat)
elab "cc_diagram_converter_type " n:ident a:num b:num : command =>
  registerRole n (.converterType a.getNat b.getNat)
elab "cc_diagram_arrow_type " n:ident c:num a:num b:num : command =>
  registerRole n (.arrowType c.getNat a.getNat b.getNat)
elab "cc_diagram_serial " n:ident a:num b:num : command =>
  registerRole n (.serial a.getNat b.getNat)
elab "cc_diagram_tensor " n:ident a:num b:num : command =>
  registerRole n (.tensor a.getNat b.getNat)
elab "cc_diagram_interface_tensor " n:ident a:num b:num : command =>
  registerRole n (.interfaceTensor a.getNat b.getNat)
elab "cc_diagram_interface_constructor " n:ident : command =>
  registerRole n .interfaceConstructor
elab "cc_diagram_identity " n:ident : command =>
  registerRole n .identity
elab "cc_diagram_action " n:ident : command =>
  registerRole n .action
elab "cc_diagram_construction_within " n:ident r:num c:num s:num e:num : command =>
  registerRole n (.constructionWithin r.getNat c.getNat s.getNat e.getNat)
elab "cc_diagram_substitution " n:ident l:num r:num e:num s:str : command =>
  registerRole n (.substitution l.getNat r.getNat e.getNat s.getString)
elab "cc_diagram_whisker_right " n:ident c:num i:num : command =>
  registerRole n (.whiskerRight c.getNat i.getNat)
elab "cc_diagram_whisker_left " n:ident i:num c:num : command =>
  registerRole n (.whiskerLeft i.getNat c.getNat)

/-! ## Lossless view model -/

inductive BoxKind where
  | res | conv | sim | spec | chip
  deriving BEq, Repr, ToJson, Inhabited

/-- Only registered interface operators become mathematical notation. An opaque
label is literal Lean text, including its namespace and arguments. -/
inductive MathLabel where
  | literal (text : String) (identifier : Bool := false)
  | tensor (left right : MathLabel)
  deriving Repr, ToJson, Inhabited

structure InterfaceField where
  symbol : String
  projection : String
  value : String
  type : String
  presentation : String := ""
  deriving Repr, ToJson, Inhabited

structure InterfacePort where
  label : String
  source : String
  input : String
  output : String
  signature : String
  inputNotation : String := ""
  outputNotation : String := ""
  deriving Repr, ToJson, Inhabited

structure Iface where
  label : MathLabel
  source : String
  type : String
  /-- Expanded interface constructions live in the inspector, not on the diagram canvas. -/
  detailsOnly : Bool := false
  fields : Array InterfaceField := #[]
  ports : Array InterfacePort := #[]
  /-- Whether the literal enumeration is complete, including the empty enumeration. -/
  enumerated : Bool := false
  deriving Repr, ToJson, Inhabited

structure Elem where
  label : String
  /-- Whether an author supplied this label, rather than ordinary mathematical notation. -/
  named : Bool := false
  /-- Complete pretty-printed term; a display alias never replaces this. -/
  source : String
  type : String
  kind : BoxKind := .chip
  pos : Array Nat := #[]
  /-- Exposed interface, not a query alphabet or an enumerated party. -/
  outer? : Option Iface := none
  inner? : Option Iface := none
  identifier : Bool := false
  /-- Original generic declaration, never a reconstructed or instantiated procedure. -/
  pseudocode? : Option SystemAlgebra.DSL.SourceDocument := none
  deriving Repr, ToJson, Inhabited

/-- A syntax-preserving tree. Parallel and tensor are binary, and serial is in
category order (outer converter first). A wrapper retains the complete term when
only part of its structure is registered. -/
inductive Diagram where
  | atom (elem : Elem)
  | attach (elem : Elem) (converter resource : Diagram) (atInterface? : Option String := none)
  | parallel (elem : Elem) (left right : Diagram)
  | serial (elem : Elem) (left right : Diagram)
  | tensor (elem : Elem) (left right : Diagram)
  | wrapper (elem : Elem) (body : Diagram)
  deriving Repr, ToJson, Inhabited

def Diagram.elem : Diagram → Elem
  | .atom e | .attach e .. | .parallel e .. | .serial e .. | .tensor e .. | .wrapper e .. => e

/-- Horizontal complexity controls an earlier vertical layout for long chains.
This changes presentation only; it never flattens the expression tree. -/
def Diagram.horizontalSpan : Diagram → Nat
  | .atom _ => 1
  | .attach _ c r _ | .serial _ c r => c.horizontalSpan + r.horizontalSpan
  | .parallel _ l r | .tensor _ l r => max l.horizontalSpan r.horizontalSpan + 1
  | .wrapper _ b => b.horizontalSpan

/-- Long, exact interface labels need vertical space before a chain's boxes do. -/
def Diagram.hasWideInterface (d : Diagram) : Bool :=
  let wide := #[d.elem.outer?, d.elem.inner?].any fun iface =>
    match iface with
    | some { label := .literal text _, detailsOnly, .. } => !detailsOnly && text.length > 48
    | _ => false
  wide || match d with
    | .atom _ => false
    | .attach _ a b _ | .parallel _ a b | .serial _ a b | .tensor _ a b =>
      a.hasWideInterface || b.hasWideInterface
    | .wrapper _ b => b.hasWideInterface

structure SystemView where
  diagram : Diagram
  deriving Repr, ToJson, Inhabited

inductive AdvCard where
  | dist (sym : String) (l r : SystemView)
  | win (sym : String) (s : SystemView)
  | mass (d : SystemView) (event : String)
  | num (label : String) (pos : Array Nat := #[])
  deriving Repr, ToJson, Inhabited

structure JudgmentView where
  real : SystemView := default
  ideal? : Option SystemView := none
  rel : String := ""
  eps? : Option String := none
  epsPos? : Option (Array Nat) := none
  protocol? : Option Diagram := none
  note? : Option String := none
  bridge? : Option (Array AdvCard × Array AdvCard) := none
  /-- Exact statement or term, never reconstructed from diagram labels. -/
  source : String := ""
  sourcePos : Array Nat := #[]
  deriving Repr, ToJson, Inhabited

/-! ## Expression projection -/

/-- Scoped Unicode alias overrides threaded by `Informalization` diagram export while leaving
interactive Lean Infoview behavior (`active := false`) 100% unchanged. -/
structure DiagramAliases where
  active : Bool := false
  constAliases : NameMap String := {}
  shortAliases : NameMap String := {}
  binderAliases : Std.HashMap String String := {}
  exprAliases : Array (Expr × String) := #[]
  hiddenArgs : NameMap (List Nat) := {}
  zeroArgConsts : NameSet := {}
  constTemplates : NameMap String := {}
  deriving Inhabited

initialize diagramAliasesRef : IO.Ref DiagramAliases ← IO.mkRef {}

def withDiagramAliases {α : Type} (aliases : DiagramAliases) (x : MetaM α) : MetaM α := do
  let saved ← diagramAliasesRef.get
  diagramAliasesRef.set aliases
  try x
  finally diagramAliasesRef.set saved

private def diagramLeakPrefixes : List String := [
  "CategoryTheory.MonoidalCategoryStruct.",
  "CategoryTheory.CategoryStruct.",
  "CategoryTheory.",
  "ConstructiveCryptography.CryptographicAlgebra.Specification.",
  "ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.",
  "ConstructiveCryptography.CryptographicAlgebra.DistinctionGames.",
  "ConstructiveCryptography.CryptographicAlgebra.",
  "ConstructiveCryptography.SubstitutionRelation.",
  "ConstructiveCryptography.Specification.",
  "ConstructiveCryptography.",
  "SystemAlgebra.Interface.",
  "SystemAlgebra.DSL.",
  "SystemAlgebra.",
  "SequenceHash.SpongeTranscript.",
  "SequenceHash.Implementation.",
  "SequenceHash.",
  "AuthenticatedEncryption.",
  "Examples.PRGLengthExtension.",
  "RandomSystems.Typed.",
  "RandomSystems.",
  "Probability.Distribution.",
  "Probability.",
  "Commons.Indifferentiability.",
  "Commons."
]

private def sanitizeDiagramText (s : String) : String := Id.run do
  let mut out := s
  for pfx in diagramLeakPrefixes do
    out := out.replace pfx ""
  return out

private def cleanDiagramBinder (n : Name) : String :=
  let base := n.eraseMacroScopes.getString!
  let cleaned := base.replace "✝" ""
  if cleaned.isEmpty then "x" else cleaned

private def shortDiagramConst (n : Name) : String := Id.run do
  let rec dropSuffixes : Name → Name
    | .str p "perPort" => dropSuffixes p
    | .str p "system" => dropSuffixes p
    | other => other
  let n' := dropSuffixes n
  match n' with
  | .str p s =>
    if (s == "Ideal" || s == "Real" || s == "Secure" || s == "INDCCA" ||
        s == "INTPTXT" || s == "INTCTXT" || s == "Security" || s == "specification" ||
        s == "leftContext" || s == "rightContext") && p != .anonymous then
      let ps := p.getString!
      if ps.isEmpty || ps == "Commons" || ps == "ConstructiveCryptography" then s
      else s!"{ps}.{s}"
    else s
  | _ => sanitizeDiagramText n'.toString

private def isDiagramPropOrTypeclass (dom : Expr) : MetaM Bool := do
  if !dom.hasLooseBVars then
    if ← (try isProp dom catch _ => pure false) then return true
  let fn := dom.consumeMData.getAppFn.consumeMData
  if let .const n _ := fn then
    let env ← getEnv
    if Lean.isClass env n then return true
    let s := n.toString
    if s == "ConstructiveCryptography.ResourceTheory" ||
       s == "ConstructiveCryptography.CompatiblePseudoMetric" ||
       s == "ConstructiveCryptography.AdmissibleDistinguishers" ||
       s == "ConstructiveCryptography.CompatibleDistinguisherClass" ||
       s == "ConstructiveCryptography.CryptographicAlgebra" then
      return true
  return false

private def collectDiagramExplicitArgs (ty : Expr) (args : Array Expr)
    (hidden : List Nat) : MetaM (Array Expr) := do
  let mut curTy := ty
  let mut expIdx := 0
  let mut out : Array Expr := #[]
  for arg in args do
    let f ← match curTy.consumeMData with
      | x@(.forallE ..) => pure x
      | other => withTransparency .reducible (whnf other)
    match f.consumeMData with
    | .forallE _ dom body bi =>
      if bi.isExplicit then
        let skip ← isDiagramPropOrTypeclass dom
        if !skip then
          if !hidden.contains expIdx then
            out := out.push arg
          expIdx := expIdx + 1
      curTy := body.instantiate1 arg
    | _ =>
      out := out.push arg
  return out

private partial def diagramExprText (aliases : DiagramAliases) (e : Expr)
    (depth : Nat := 24) : MetaM String := do
  if depth == 0 then return "…"
  let eRaw := e.consumeMData
  if let some (_, symAlias) := aliases.exprAliases.reverse.find?
      (fun (pat, _) => pat.consumeMData == eRaw) then
    return symAlias
  let recGo : Expr → MetaM String := fun x => diagramExprText aliases x (depth - 1)
  match eRaw with
  | .lit (.natVal n) => return toString n
  | .lit (.strVal s) => return reprStr s
  | .fvar fid =>
    let decl ← fid.getDecl
    let clean := cleanDiagramBinder decl.userName
    return (aliases.binderAliases.get? clean)
      |>.orElse (fun _ => aliases.binderAliases.get? decl.userName.toString)
      |>.getD clean
  | .bvar i => return s!"x_{i}"
  | .mvar _ => return "?"
  | .sort .zero => return "Prop"
  | .sort _ => return "Type"
  | .mdata _ inner => diagramExprText aliases inner depth
  | .letE nm ty val body _ =>
    if !body.hasLooseBVar 0 then recGo body
    else
      let vName := cleanDiagramBinder nm
      let vStr ← recGo val
      withLetDecl (Name.mkSimple vName) ty val fun fv => do
        let bStr ← recGo (body.instantiate1 fv)
        return s!"({bStr} [where {vName} := {vStr}])"
  | .lam nm dom body bi =>
    let freshName := cleanDiagramBinder nm
    withLocalDecl (Name.mkSimple freshName) bi dom fun fv => do
      let vText ← recGo fv
      let bText ← recGo (body.instantiate1 fv)
      return s!"{vText} ↦ {bText}"
  | .forallE nm dom body bi =>
    if ← isDiagramPropOrTypeclass dom then
      if !body.hasLooseBVar 0 then
        if ← (try isProp dom catch _ => pure false) then
          return s!"{← recGo dom} → {← recGo body}"
        else
          return ← recGo body
      else
        let freshName := cleanDiagramBinder nm
        withLocalDecl (Name.mkSimple freshName) bi dom fun fv => recGo (body.instantiate1 fv)
    else if !body.hasLooseBVar 0 then
      return s!"{← recGo dom} → {← recGo body}"
    else
      let freshName := cleanDiagramBinder nm
      withLocalDecl (Name.mkSimple freshName) bi dom fun fv => do
        let vText ← recGo fv
        let dText ← recGo dom
        let bText ← recGo (body.instantiate1 fv)
        return s!"∀ ({vText} : {dText}), {bText}"
  | .proj structName idx s =>
    if (structName == ``Subtype || structName == ``Fin) && idx == 0 then
      return ← recGo s
    let sText ← recGo s
    if structName == ``Prod || structName == ``PProd || structName == ``Sigma then
      return s!"{sText}.{idx + 1}"
    if let some sinfo := getStructureInfo? (← getEnv) structName then
      if h : idx < sinfo.fieldNames.size then
        return s!"{sText}.{sinfo.fieldNames[idx].getString!}"
    return s!"{sText}.{idx}"
  | .const name _ =>
    if name == ``Prod.fst || name == ``PProd.fst || name == ``Sigma.fst then return "π₁"
    if name == ``Prod.snd || name == ``PProd.snd || name == ``Sigma.snd then return "π₂"
    if name == `CategoryTheory.CategoryStruct.id then return "𝟙"
    return (aliases.shortAliases.get? name)
      |>.orElse (fun _ => aliases.constAliases.get? name)
      |>.getD (shortDiagramConst name)
  | .app .. =>
    let fn := eRaw.getAppFn.consumeMData
    let args := eRaw.getAppArgs
    if let .const head _ := fn then
      let headStr := head.toString
      -- Transparent numeric/set/subtype coercions
      if head == `Nat.cast || head == `Int.cast || head == ``Coe.coe ||
         head == `CoeHTCF.coe || head == ``Subtype.val || head == ``Fin.val ||
         headStr == "NNReal.toENNReal" || headStr == "ENNReal.ofReal" ||
         headStr == "ENNReal.ofNNReal" || headStr == "ENNReal.coe" ||
         headStr == "ENNReal.ofNat" || headStr == "Real.toNNReal" then
        if let some inner := args.back? then
          return ← recGo inner
      if headStr == "Singleton.singleton" || headStr == "Set.singleton" then
        if let some inner := args.back? then
          return ← recGo inner
      if head == ``OfNat.ofNat && args.size ≥ 2 then
        return ← recGo args[1]!
      -- Relaxation & indifferentiability wrappers
      if headStr == "DFunLike.coe" && args.size ≥ 6 then
        let relaxFn := args[4]!.consumeMData
        let specArg := args[5]!
        let rfName := relaxFn.getAppFn.consumeMData.constName?.map (·.toString) |>.getD ""
        if (rfName == "ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation" ||
            rfName == "ConstructiveCryptography.Specification.epsilonRelaxation") &&
            relaxFn.getAppArgs.size ≥ 1 then
          return s!"{← recGo specArg}^[{← recGo relaxFn.getAppArgs.back!}]"
      if headStr == "ConstructiveCryptography.Relaxation.relaxedBy" && args.size ≥ 3 then
        let specArg := args[args.size - 2]!
        let relaxFn := args[args.size - 1]!.consumeMData
        let rfName := relaxFn.getAppFn.consumeMData.constName?.map (·.toString) |>.getD ""
        if (rfName == "ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation" ||
            rfName == "ConstructiveCryptography.Specification.epsilonRelaxation") &&
            relaxFn.getAppArgs.size ≥ 1 then
          return s!"{← recGo specArg}^[{← recGo relaxFn.getAppArgs.back!}]"
        return s!"{← recGo specArg}^[{← recGo relaxFn}]"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation" ||
         headStr == "ConstructiveCryptography.Specification.epsilonRelaxation" then
        if let some err := args.back? then
          return s!"relax[{← recGo err}]"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage" &&
         args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} • {← recGo args[args.size - 1]!}"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.star" &&
         args.size ≥ 1 then
        return s!"{← recGo args.back!}*"
      if headStr == "Commons.Indifferentiability.specification" && args.size ≥ 3 then
        let idealT ← recGo args[args.size - 3]!
        let simT ← recGo args[args.size - 2]!
        let errT ← recGo args[args.size - 1]!
        return s!"({simT} • {idealT})^[{errT}]"
      -- Categorical, monoidal, and CC operators
      if headStr == "CategoryTheory.MonoidalCategoryStruct.whiskerRight" && args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} ▷ {← recGo args[args.size - 1]!}"
      if headStr == "CategoryTheory.MonoidalCategoryStruct.whiskerLeft" && args.size ≥ 4 then
        return s!"{← recGo args[args.size - 4]!} ◁ {← recGo args[args.size - 1]!}"
      if headStr == "CategoryTheory.MonoidalCategoryStruct.tensorHom" && args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} ⊗ₘ {← recGo args[args.size - 1]!}"
      if headStr == "CategoryTheory.MonoidalCategoryStruct.tensorObj" && args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} ⊗ {← recGo args[args.size - 1]!}"
      if headStr == "CategoryTheory.CategoryStruct.comp" && args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} ≫ {← recGo args[args.size - 1]!}"
      if headStr == "CategoryTheory.CategoryStruct.id" then
        return "𝟙"
      if (headStr == "ConstructiveCryptography.CryptographicAlgebra.parallel" ||
          headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.parallel") &&
         args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} ∥ {← recGo args[args.size - 1]!}"
      if (head == ``HSMul.hSMul || head == ``SMul.smul ||
          headStr == "ConstructiveCryptography.ResourceTheory.attach" ||
          headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.map") &&
         args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!} • {← recGo args[args.size - 1]!}"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.distance" && args.size ≥ 2 then
        return s!"Δ({← recGo args[args.size - 2]!}, {← recGo args[args.size - 1]!})"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs" &&
         args.size ≥ 3 then
        return s!"{← recGo args[args.size - 2]!} —[{← recGo args[args.size - 3]!}]→ {← recGo args[args.size - 1]!}"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin" &&
         args.size ≥ 4 then
        return s!"{← recGo args[args.size - 3]!} —[{← recGo args[args.size - 4]!}; {← recGo args[args.size - 1]!}]→ {← recGo args[args.size - 2]!}"
      if headStr == "ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin" &&
         args.size ≥ 3 then
        return s!"{← recGo args[args.size - 2]!} ≃[{← recGo args[args.size - 3]!}] {← recGo args[args.size - 1]!}"
      if (headStr == "ConstructiveCryptography.DistinguisherAction.absorb" ||
          headStr == "SystemAlgebra.TypedDistinguisher.absorb") && args.size ≥ 2 then
        return s!"{← recGo args[args.size - 2]!}({← recGo args[args.size - 1]!})"
      if headStr == "SystemAlgebra.TypedConverter.leftContext" && args.size ≥ 2 then
        return s!"({← recGo args[args.size - 2]!} ∥ 𝟙)"
      if headStr == "SystemAlgebra.TypedConverter.rightContext" && args.size ≥ 2 then
        return s!"(𝟙 ∥ {← recGo args[args.size - 1]!})"
      if headStr == "ConstructiveCryptography.DistinctionGames.visible" && args.size ≥ 1 then
        return s!"visible({← recGo args.back!})"
      -- Common arithmetic / relations / types
      if head == ``Eq && args.size == 3 then
        return s!"{← recGo args[1]!} = {← recGo args[2]!}"
      if head == ``LE.le && args.size == 4 then
        return s!"{← recGo args[2]!} ≤ {← recGo args[3]!}"
      if head == ``LT.lt && args.size == 4 then
        return s!"{← recGo args[2]!} < {← recGo args[3]!}"
      if head == ``GE.ge && args.size == 4 then
        return s!"{← recGo args[2]!} ≥ {← recGo args[3]!}"
      if head == ``GT.gt && args.size == 4 then
        return s!"{← recGo args[2]!} > {← recGo args[3]!}"
      if head == ``And && args.size == 2 then
        return s!"{← recGo args[0]!} ∧ {← recGo args[1]!}"
      if head == ``HAdd.hAdd && args.size == 6 then
        return s!"{← recGo args[4]!} + {← recGo args[5]!}"
      if head == ``HSub.hSub && args.size == 6 then
        return s!"{← recGo args[4]!} - {← recGo args[5]!}"
      if head == ``HMul.hMul && args.size == 6 then
        return s!"{← recGo args[4]!} · {← recGo args[5]!}"
      if head == ``HDiv.hDiv && args.size == 6 then
        return s!"{← recGo args[4]!} / {← recGo args[5]!}"
      if head == ``HPow.hPow && args.size == 6 then
        return s!"{← recGo args[4]!}^{← recGo args[5]!}"
      if (head == `Min.min || head == `Nat.min) && args.size ≥ 2 then
        return s!"min({← recGo args[args.size - 2]!}, {← recGo args[args.size - 1]!})"
      if (head == `Max.max || head == `Nat.max) && args.size ≥ 2 then
        return s!"max({← recGo args[args.size - 2]!}, {← recGo args[args.size - 1]!})"
      if head == ``Prod && args.size == 2 then
        return s!"{← recGo args[0]!} × {← recGo args[1]!}"
      if head == ``Prod.mk && args.size == 4 then
        return s!"({← recGo args[2]!}, {← recGo args[3]!})"
      if (head == ``Prod.fst || head == ``PProd.fst || head == ``Sigma.fst) && args.size ≥ 3 then
        return s!"{← recGo args[2]!}.1"
      if (head == ``Prod.snd || head == ``PProd.snd || head == ``Sigma.snd) && args.size ≥ 3 then
        return s!"{← recGo args[2]!}.2"
      if headStr == "Fintype.card" && args.size ≥ 1 then
        return s!"|{← recGo args[0]!}|"
      if headStr == "List.length" && args.size ≥ 1 then
        return s!"|{← recGo args.back!}|"
      if headStr == "Probability.Distribution.ProbDist.uniform" ||
         headStr == "Probability.Distribution.uniform" ||
         headStr == "Distribution.uniform" then
        if let some info := (← getEnv).find? head then
          let expArgs ← collectDiagramExplicitArgs info.type args []
          if expArgs.size == 1 then
            return s!"𝒰[{← recGo expArgs[0]!}]"
      -- Template & zero-arg overrides from SymbolTable
      if let some tmpl := aliases.constTemplates.get? head then
        if let some info := (← getEnv).find? head then
          let hidden := aliases.hiddenArgs.getD head []
          let vis ← collectDiagramExplicitArgs info.type args hidden
          let mut out := tmpl
          for idx in [:vis.size] do
            out := out.replace s!"#{idx + 1}" (← recGo vis[idx]!)
          return sanitizeDiagramText out
      if aliases.zeroArgConsts.contains head then
        return ← recGo fn
      if let some info := (← getEnv).find? head then
        if !aliases.constAliases.contains head && !aliases.shortAliases.contains head then
          if let some projInfo := (← getEnv).getProjectionFnInfo? head then
            if let some (.ctorInfo cinfo) := (← getEnv).find? projInfo.ctorName then
              let sName := cinfo.induct
              if (sName == ``Fin || sName == ``Subtype) && projInfo.i == 0 &&
                 args.size == projInfo.numParams + 1 then
                return ← recGo args[projInfo.numParams]!
        let hidden := aliases.hiddenArgs.getD head []
        let vis ← collectDiagramExplicitArgs info.type args hidden
        let headLabel ← recGo fn
        if vis.isEmpty then
          return headLabel
        let argStrs ← vis.mapM recGo
        return s!"{headLabel}({String.intercalate ", " argStrs.toList})"
    let fnStr ← recGo fn
    let vis ← try
      let fTy ← inferType fn
      collectDiagramExplicitArgs fTy args []
    catch _ => pure args
    if vis.isEmpty then return fnStr
    let argStrs ← vis.mapM recGo
    return s!"{fnStr}({String.intercalate ", " argStrs.toList})"

def argPos (p : SubExpr.Pos) (arity i : Nat) : SubExpr.Pos :=
  ((arity - 1 - i).fold (fun _ _ q => q.pushAppFn) p).pushAppArg

def ppShort (e : Expr) : MetaM String := do
  let aliases ← diagramAliasesRef.get
  if aliases.active then
    return ← diagramExprText aliases e
  return (← Meta.ppExpr e).pretty (width := 100)

/-- Replace only the tagged printing placeholder, never an argument with similar text. -/
partial def renamePrintedHead (head : Expr) (label : String) : Widget.CodeWithInfos →
    Widget.CodeWithInfos
  | .text text => .text text
  | .append parts => .append (parts.map (renamePrintedHead head label))
  | .tag info body =>
    match info.info.val.info with
    | .ofTermInfo term =>
      if term.expr == head then .tag info (.text label)
      else .tag info (renamePrintedHead head label body)
    | _ => .tag info (renamePrintedHead head label body)

/-- Resolve explicit display names without changing the expression. A declaration nickname
renames only its printed head; Lean still prints the application's arguments. -/
def explicitLabel? (e : Expr) : MetaM (Option String) := do
  let eRaw := e.consumeMData
  if let some (_, label) := (ccDiagramTermLabels.getState (← getEnv)).reverse.find?
      (fun (term, _) => term == eRaw) then return some label
  if let .const name _ := eRaw.getAppFn.consumeMData then
    if let some label := (ccDiagramLabels.getState (← getEnv)).find? name then
      if !eRaw.isApp then return some label
      let aliases ← diagramAliasesRef.get
      if aliases.active then
        return some (← diagramExprText { aliases with constAliases := aliases.constAliases.insert name label } eRaw)
      return some (← withLocalDeclD `ccDisplayHead (← inferType eRaw.getAppFn) fun head => do
        let printed ← Widget.ppExprTagged (mkAppN head eRaw.getAppArgs)
        return (renamePrintedHead head label printed).stripTags)
  let aliases ← diagramAliasesRef.get
  if aliases.active then
    if let some (_, symAlias) := aliases.exprAliases.reverse.find?
        (fun (pat, _) => pat.consumeMData == eRaw) then
      return some symAlias
    if (← declRole? eRaw).isNone then
      match eRaw with
      | .fvar fid =>
        let decl ← fid.getDecl
        let clean := cleanDiagramBinder decl.userName
        if let some alias := aliases.binderAliases.get? clean <|> aliases.binderAliases.get? decl.userName.toString then
          return some alias
      | _ =>
        if let .const name _ := eRaw.getAppFn.consumeMData then
          if aliases.constAliases.contains name || aliases.shortAliases.contains name then
            return some (← diagramExprText aliases eRaw)
  return none

/-- Exact registered identities have the conventional label `𝟙`; their interfaces and full
source remain attached to the same expression. Unknown declarations retain Lean's printer. -/
def labelFor (e : Expr) : MetaM String := do
  if let some label ← explicitLabel? e then return label
  if (← declRole? e) == some .identity then return "𝟙"
  return ← ppShort e

/-- Bounded recursion gives a literal fallback for unusually deep terms. -/
def mathLabel (e : Expr) (depth : Nat := 32) : MetaM MathLabel := do
  match depth with
  | 0 => return .literal (← ppShort e)
  | depth + 1 =>
    if let some label ← explicitLabel? e then return .literal label e.isFVar
    if let some (.interfaceTensor lf rf) ← declRole? e then
      if let some (_, l) := argFromEnd? e.consumeMData.getAppArgs lf then
        if let some (_, r) := argFromEnd? e.consumeMData.getAppArgs rf then
          return .tensor (← mathLabel l depth) (← mathLabel r depth)
    return .literal (← ppShort e) e.isFVar

/-- Explicit ambient capabilities identify abstract carrier families. No typeclass
search or reduction guesses whether an arbitrary `F A` denotes a resource. -/
def resourceFamilies : MetaM (Array (Expr × Expr)) := do
  let mut families := #[]
  for localDecl in ← getLCtx do
    let type ← instantiateMVars localDecl.type
    if let some (.resourceFamily ci fi) ← declRole? type then
      if let some (_, category) := argFromEnd? type.getAppArgs ci then
        if let some (_, family) := argFromEnd? type.getAppArgs fi then
          families := families.push (category, family)
  return families

/-- Interface of a registered concrete carrier or an explicitly selected abstract
resource family. Opaque aliases retain their complete type as a literal fallback. -/
def resourceBoundary? (ty : Expr) : MetaM (Option Expr) := do
  if let some (.resourceType i) ← declRole? ty then
    if let some (_, boundary) := argFromEnd? ty.getAppArgs i then
      return some boundary
  if let .app family boundary := ty then
    if (← resourceFamilies).any (fun (_, f) => f == family) then
      return some boundary
  return none

/-- Follow only structure projections to the explicitly selected ambient instance.
An alternative category on the same object type is a different choice. -/
def projectsFrom (e base : Expr) (depth : Nat := 8) : CoreM Bool := do
  if e == base then return true
  match depth with
  | 0 => return false
  | depth + 1 =>
    if let .proj _ _ value := e then return ← projectsFrom value base depth
    if let .const name _ := e.getAppFn then
      if let some info := (← getEnv).getProjectionFnInfo? name then
        if e.getAppNumArgs == info.numParams + 1 then
          return ← projectsFrom e.getAppArgs[info.numParams]! base depth
    return false

/-- Interface fields are actual registered projections. Only reducible definitions and
projection/beta reduction are used to expose values; no theorem rewriting or enumeration. -/
def interfaceProjections (e : Expr) : MetaM (Array (String × Expr × Expr)) := do
  let ty ← whnf (← inferType e)
  let .const name _ := ty.getAppFn | return #[]
  let some schema := (interfaceSchemas.getState (← getEnv)).find? name | return #[]
  schema.fields.mapM fun (symbol, projection) => do
    let field ← mkAppM projection #[e]
    let value ← withTransparency .reducible <| whnf field
    -- An unresolved structure projection has a useful name; do not expose its numeric index.
    return (symbol, field, if value.isProj then field else value)

/-- A literal enumeration type has exactly its nullary constructors as labels. Other label
types remain symbolic; this does not evaluate a `Fintype`, enumerate payloads or guess ports. -/
def interfacePorts (e : Expr) : MetaM (Array (String × Expr × Expr × Expr)) := do
  let fields ← interfaceProjections e
  let some (_, _, labels) := fields.find? (·.1 == "I") | return #[]
  let some (_, _, input) := fields.find? (·.1 == "X") | return #[]
  let some (_, _, output) := fields.find? (·.1 == "Y") | return #[]
  let .const head levels := labels.getAppFn | return #[]
  let .inductInfo ind ← getConstInfo head | return #[]
  if ind.numIndices != 0 || ind.ctors.length > 32 then return #[]
  let mut ports := #[]
  for name in ind.ctors do
    let .ctorInfo ctor ← getConstInfo name | return #[]
    unless ctor.numFields == 0 do return #[]
    let port := mkAppN (mkConst name levels) labels.getAppArgs
    unless ← isDefEq (← inferType port) labels do return #[]
    let x ← whnfCore (mkApp input port)
    let y ← whnfCore (mkApp output port)
    ports := ports.push (name.getString!, port, x, y)
  return ports

/-- Compound boundaries also keep expanded constructors in their inspector. Named aliases
remain literal; this follows registered tensor arguments without unfolding them. -/
def interfaceDetailsOnly (e : Expr) (depth : Nat := 32) : MetaM Bool := do
  if (← explicitLabel? e).isSome then return false
  match depth with
  | 0 => return false
  | depth + 1 =>
    match ← declRole? e with
    | some .interfaceConstructor => return true
    | some (.interfaceTensor lf rf) =>
      if let some (_, l) := argFromEnd? e.getAppArgs lf then
        if let some (_, r) := argFromEnd? e.getAppArgs rf then
          return (← interfaceDetailsOnly l depth) || (← interfaceDetailsOnly r depth)
    | _ => pure ()
    if let .const name _ := e.getAppFn then
      if let .ctorInfo _ ← getConstInfo name then return true
    return false

def interfaceOf (e : Expr) : MetaM Iface := do
  let aliases ← diagramAliasesRef.get
  let cleanNote (s : String) := if aliases.active then sanitizeDiagramText s else s
  let fields ← (← interfaceProjections e).mapM fun (symbol, projection, value) => do
    let presentation ← if symbol == "D" then cleanNote <$> domainNotation value else pure ""
    return { symbol, projection := ← ppShort projection,
             value := ← ppShort value, type := ← ppShort (← inferType projection),
             presentation : InterfaceField }
  let ports ← (← interfacePorts e).mapM fun (label, port, input, output) => do
    return { label, source := ← ppShort port,
             input := ← ppShort input, output := ← ppShort output,
             signature := ← ppShort (← mkArrow input output),
             inputNotation := cleanNote (← typeNotation input).text,
             outputNotation := cleanNote (← typeNotation output).text : InterfacePort }
  let mut label ← mathLabel e
  let mut detailsOnly := false
  -- An anonymous interface record is deliberately elided, never renamed to an invented object.
  -- Its complete expression and every registered field remain in the inspector.
  if !fields.isEmpty then
    detailsOnly ← interfaceDetailsOnly e
    if let .const name _ := e.getAppFn then
      if let .ctorInfo _ ← getConstInfo name then
        label := .literal "⟨…⟩"
        detailsOnly := true
  if let some name ← explicitLabel? e then
    label := .literal name
    detailsOnly := false
  let mut enumerated := !ports.isEmpty
  for (symbol, _, value) in ← interfaceProjections e do
    if symbol == "I" then
      if let .const name _ := value.getAppFn then
        if let .inductInfo ind ← getConstInfo name then
          if ind.numIndices == 0 && ind.ctors.isEmpty then enumerated := true
  return { label, source := ← ppShort e, type := ← ppShort (← inferType e),
           detailsOnly, fields, ports, enumerated }

/-- The inferred type determines the two boundaries. Category projections must come from
the selected resource capability; unrelated categorical arrows acquire no interface fields. -/
def typeInterfaces (ty : Expr) : MetaM (BoxKind × Option Expr × Option Expr) := do
  if let some boundary ← resourceBoundary? ty then return (.res, some boundary, none)
  if let some role ← declRole? ty then
    match role with
    | .specificationType i =>
      if let some (_, carrier) := argFromEnd? ty.getAppArgs i then
        if let some boundary ← resourceBoundary? carrier then
          return (.spec, some boundary, none)
    | .converterType a b | .arrowType _ a b =>
      let admitted : Bool ← match role with
        | .arrowType c _ _ => do
          match argFromEnd? ty.getAppArgs c with
          | some (_, quiver) =>
            (← resourceFamilies).anyM (fun (category, _) => projectsFrom quiver category)
          | none => pure false
        | _ => pure true
      unless admitted do
        -- Reduce the selected arrow type, never the source expression. Concrete
        -- category instances can expose a separately registered converter type.
        let reduced ← withTransparency .instances <| whnfHeadPred ty fun t => do
          return match ← declRole? t with | some (.converterType ..) => false | _ => true
        if let some (.converterType a b) ← declRole? reduced then
          if let some (_, outer) := argFromEnd? reduced.getAppArgs a then
            if let some (_, inner) := argFromEnd? reduced.getAppArgs b then
              return (.conv, some outer, some inner)
        return (.chip, none, none)
      if let some (_, outer) := argFromEnd? ty.getAppArgs a then
        if let some (_, inner) := argFromEnd? ty.getAppArgs b then
          return (.conv, some outer, some inner)
    | _ => pure ()
  return (.chip, none, none)

/-- Types are inspected before reduction: an unknown type stays unknown. -/
def elemOf (e : Expr) (p : SubExpr.Pos) (fallback : BoxKind := .chip) : MetaM Elem := do
  let ty ← instantiateMVars (← inferType e)
  let (kind, outer, inner) ← typeInterfaces ty
  let documents := SystemAlgebra.DSL.sourceDocuments.getState (← getEnv)
  let pseudocode? := match e.getAppFn with
    | .const name _ => documents.find? name
    | _ => none
  return { label := ← labelFor e, source := ← ppShort e, type := ← ppShort ty,
           named := (← explicitLabel? e).isSome,
           kind := if kind == .chip then fallback else kind, pos := p.toArray,
           identifier := e.isFVar, outer? := ← outer.mapM interfaceOf,
           inner? := ← inner.mapM interfaceOf, pseudocode? }

/-- Recognize action notation only for an explicitly registered instance.
Arbitrary scalar multiplication is not converter attachment. -/
def operationRole? (e : Expr) : CoreM (Option DeclRole) := do
  let e := e.consumeMData
  if e.isAppOfArity ``HSMul.hSMul 6 then
    if let some .action ← declRole? e.getAppArgs[3]! then
      return some (.application 1 0)
  if e.isAppOfArity ``SMul.smul 5 then
    if let some .action ← declRole? e.getAppArgs[2]! then
      return some (.application 1 0)
  return ← declRole? e

private partial def unwrapDiagramSide (e : Expr) (depth : Nat := 8) : MetaM Expr := do
  match depth with
  | 0 => return e
  | depth + 1 =>
    let e := e.consumeMData
    if e.isAppOfArity `Singleton.singleton 4 then
      return ← unwrapDiagramSide e.getAppArgs[3]! depth
    let pair? : Option (Nat × Expr) :=
      match e with
      | .proj ``Prod 0 s => some (0, s)
      | .proj ``Prod 1 s => some (1, s)
      | _ =>
        if e.isAppOfArity ``Prod.fst 3 then some (0, e.getAppArgs[2]!)
        else if e.isAppOfArity ``Prod.snd 3 then some (1, e.getAppArgs[2]!)
        else none
    if let some (idx, pair) := pair? then
      let pairUnfolded ← do
        let p := pair.consumeMData
        if p.isAppOfArity ``Prod.mk 4 then pure p
        else pure ((← withTransparency .default (Meta.unfoldDefinition? p)).getD p)
      let p := pairUnfolded.consumeMData
      if p.isAppOfArity ``Prod.mk 4 then
        return ← unwrapDiagramSide p.getAppArgs[2 + idx]! depth
    return e

/-- Project only registered operations. In particular, no definitional unfolding
can manufacture subexpression positions in the original term. -/
partial def parseDiagram (e : Expr) (p : SubExpr.Pos := .root) (depth : Nat := 64)
    (fallback : BoxKind := .chip) : MetaM Diagram := do
  let aliases ← diagramAliasesRef.get
  let e ← if aliases.active then unwrapDiagramSide e else pure e.consumeMData
  let el ← elemOf e p fallback
  match depth with
  | 0 => return .atom el
  | depth + 1 =>
    let args := e.getAppArgs
    let child (i : Nat) (kind : BoxKind := .chip) :=
      parseDiagram args[i]! (argPos p args.size i) depth kind
    if aliases.active && e.getAppFn.consumeMData.isConstOf `Commons.Indifferentiability.specification && args.size ≥ 3 then
      return .wrapper el (← child (args.size - 3) .res)
    if let some role ← operationRole? e then
      match role with
      | .application cf rf | .attachment _ cf rf =>
        if let some (ci, _) := argFromEnd? args cf then
          if let some (ri, _) := argFromEnd? args rf then
            let at? ← match role with
              | .attachment inf _ _ => match argFromEnd? args inf with
                | some (_, iface) => pure (some (← ppShort iface))
                | none => pure none
              | _ => pure none
            return .attach el (← child ci .conv) (← child ri .res) at?
      | .parallel lf rf | .serial lf rf | .tensor lf rf =>
        -- A morphism in an unrelated category is not a CC converter.
        if (match role with | .serial .. | .tensor .. => true | _ => false) &&
            el.kind != .conv then return .atom el
        if let some (li, _) := argFromEnd? args lf then
          if let some (ri, _) := argFromEnd? args rf then
            let kind := match role with | .parallel .. => .res | _ => .conv
            let l ← child li kind
            let r ← child ri kind
            return match role with
              | .parallel .. => .parallel el l r
              | .serial .. => .serial el l r
              | _ => .tensor el l r
      | .whiskerRight cf inf | .whiskerLeft inf cf =>
        if el.kind != .conv then return .atom el
        if let some (ci, _) := argFromEnd? args cf then
          if let some (ii, ifaceExpr) := argFromEnd? args inf then
            let convDiag ← child ci .conv
            let wireIface? ← try some <$> interfaceOf ifaceExpr catch _ => pure none
            let idSource ← ppShort ifaceExpr
            let idEl : Elem := {
              label := "𝟙"
              source := idSource
              type := s!"{idSource} ⟶ {idSource}"
              kind := .conv
              pos := (argPos p args.size ii).toArray
              outer? := wireIface?
              inner? := wireIface?
            }
            let idDiag := Diagram.atom idEl
            return match role with
              | .whiskerRight .. => .tensor el convDiag idDiag
              | _ => .tensor el idDiag convDiag
      | .game sf _ | .transparent sf =>
        if let some (si, _) := argFromEnd? args sf then
          -- Retain the wrapper and all its arguments. No invented MBO lane.
          return .wrapper el (← child si)
      | _ => pure ()
    return .atom el

def parseSide (e : Expr) (p : SubExpr.Pos := .root) : MetaM SystemView := do
  return { diagram := ← parseDiagram e p }

def Diagram.recognized (d : Diagram) : Bool :=
  match d with
  | .atom e => e.kind != .chip
  | _ => true

/-- A distance is kept as an operator applied to two systems, including its
original comparison relation. `d = ε` must never become `d ≤ ε`. -/
def parseAdv (e : Expr) (p : SubExpr.Pos) : MetaM (Array AdvCard) := do
  if let some role ← declRole? e then
    let args := e.getAppArgs
    match role with
    | .distance lf rf sym =>
      if let some (li, l) := argFromEnd? args lf then
        if let some (ri, r) := argFromEnd? args rf then
          return #[.dist sym (← parseSide l (argPos p args.size li))
            (← parseSide r (argPos p args.size ri))]
    | .winning sf sym =>
      if let some (si, s) := argFromEnd? args sf then
        return #[.win sym (← parseSide s (argPos p args.size si))]
    | _ => pure ()
  -- Unknown arithmetic, coercions, sums and probability operators remain literal.
  return #[.num (← ppShort e) p.toArray]

def AdvCard.isNum : AdvCard → Bool
  | .num .. => true
  | _ => false

def parseJudgment? (e : Expr) (p : SubExpr.Pos := .root)
    (sel : Array (Array Nat) := #[]) : MetaM (Option JudgmentView) := do
  let _ := sel
  let e := (← instantiateMVars e).consumeMData
  let source ← ppShort e
  let sourcePos := p.toArray
  let args := e.getAppArgs
  if let some role ← declRole? e then
    match role with
    | .construction rf cf sf | .constructionWithin rf cf sf _ =>
      if let some (ri, r) := argFromEnd? args rf then
        if let some (ci, c) := argFromEnd? args cf then
          if let some (si, s) := argFromEnd? args sf then
            let mut j : JudgmentView :=
              { real := ← parseSide r (argPos p args.size ri),
                ideal? := some (← parseSide s (argPos p args.size si)),
                protocol? := some (← parseDiagram c (argPos p args.size ci) (fallback := .conv)),
                rel := "⟶", source, sourcePos }
            if let .constructionWithin _ _ _ ef := role then
              if let some (ei, error) := argFromEnd? args ef then
                j :=
                  { j with
                    eps? := some (← ppShort error)
                    epsPos? := some (argPos p args.size ei).toArray }
            return some j
    | .substitution lf rf ef sym =>
      if let some (li, l) := argFromEnd? args lf then
        if let some (ri, r) := argFromEnd? args rf then
          let mut j : JudgmentView :=
            { real := ← parseSide l (argPos p args.size li),
              ideal? := some (← parseSide r (argPos p args.size ri)),
              rel := sym, source, sourcePos }
          if let some (ei, error) := argFromEnd? args ef then
            j :=
              { j with
                eps? := some (← ppShort error)
                epsPos? := some (argPos p args.size ei).toArray }
          return some j
    | .conditional lf rf =>
      if let some (li, l) := argFromEnd? args lf then
        if let some (ri, r) := argFromEnd? args rf then
          return some
            { real := ← parseSide l (argPos p args.size li),
              ideal? := some (← parseSide r (argPos p args.size ri)),
              rel := "|≡", source, sourcePos }
    | _ => pure ()
  let cmp? :=
    if e.isAppOfArity ``Eq 3 then some (1, 2, "=")
    else if e.isAppOfArity ``LE.le 4 then some (2, 3, "≤")
    else if e.isAppOfArity ``LT.lt 4 then some (2, 3, "<")
    else if e.isAppOfArity ``GE.ge 4 then some (2, 3, "≥")
    else if e.isAppOfArity ``GT.gt 4 then some (2, 3, ">")
    else none
  if let some (li, ri, rel) := cmp? then
    let lp := argPos p args.size li
    let rp := argPos p args.size ri
    let l ← parseAdv args[li]! lp
    let r ← parseAdv args[ri]! rp
    if !(l.all (·.isNum) && r.all (·.isNum)) then
      return some { rel, bridge? := some (l, r), source, sourcePos }
    if rel == "=" then
      let l ← parseSide args[li]! lp
      let r ← parseSide args[ri]! rp
      if l.diagram.recognized || r.diagram.recognized then
        return some { real := l, ideal? := some r, rel, source, sourcePos }
  return none

/-! ## Source-linked labels -/

abbrev Codes := Array ((Array Nat × String) × Html)

def codeFor? (codes : Codes) (pos : Array Nat) (part : String := "") : Option Html :=
  (codes.find? (·.1 == (pos, part))).map (·.2)

/-- Retain the exact expression's RPC information when a display alias or record elision is
shown. A missing root tag falls back to the complete interactive expression. -/
partial def rootCodeInfo? : Widget.CodeWithInfos → Option Widget.SubexprInfo
  | .text _ => none
  | .append parts => parts.findSome? rootCodeInfo?
  | .tag info child =>
      if info.subexprPos == .root then some info else rootCodeInfo? child

def interactiveCode (e : Expr) (label? : Option String := none) : MetaM Html := do
  let mut fmt ← Widget.ppExprTagged e
  if let some label := label? then
    if let some info := rootCodeInfo? fmt then fmt := .tag info (.text label)
  return Html.ofComponent InteractiveCode { fmt } #[]

/-- Interface tensor labels retain each component's name and original hover in the infoview.
The tensor operator's hover refers to the complete original interface expression. -/
def interactiveInterfaceLabel (e : Expr) (depth : Nat := 32) : MetaM Html := do
  let label ← mathLabel e depth
  if let .literal text _ := label then
    return ← interactiveCode e (if text == (← ppShort e) then none else some text)
  match depth with
  | 0 => interactiveCode e
  | depth + 1 =>
    if let some (.interfaceTensor lf rf) ← declRole? e then
      if let some (_, l) := argFromEnd? e.getAppArgs lf then
        if let some (_, r) := argFromEnd? e.getAppArgs rf then
          return .element "span" #[] #[.text "(", ← interactiveInterfaceLabel l depth,
            .text " ", ← interactiveCode e (some "⊗"), .text " ",
            ← interactiveInterfaceLabel r depth, .text ")"]
    interactiveCode e

/-- Symbols keep individual native hovers, including nested alphabets. Operator hovers show
the complete original type, preserving its grouping and the selected type constructors. -/
def interactiveTypeNotation (t : TypeNotation) (context : Nat := 0) : MetaM Html := do
  let body ← match t with
    | .atom source label _ => interactiveCode source (some label)
    | .binary source op p l r => do
      return .element "span" #[] #[← interactiveTypeNotation l (p + 1), .text " ",
        ← interactiveCode source (some op), .text " ", ← interactiveTypeNotation r (p + 1)]
  if t.precedence < context then
    return .element "span" #[] #[.text "(", body, .text ")"]
  return body

partial def Diagram.positions (d : Diagram) : Array (Array Nat) :=
  #[d.elem.pos] ++ match d with
  | .atom _ => #[]
  | .attach _ c r _ | .parallel _ c r | .serial _ c r | .tensor _ c r =>
    c.positions ++ r.positions
  | .wrapper _ b => b.positions

def collectPositions (j : JudgmentView) : Array (Array Nat) := Id.run do
  let mut ps := #[j.sourcePos] ++ j.real.diagram.positions
  if let some s := j.ideal? then ps := ps ++ s.diagram.positions
  if let some c := j.protocol? then ps := ps ++ c.positions
  if let some p := j.epsPos? then ps := ps.push p
  if let some (l, r) := j.bridge? then
    for c in l ++ r do
      match c with
      | .dist _ a b => ps := ps ++ a.diagram.positions ++ b.diagram.positions
      | .win _ a | .mass a _ => ps := ps ++ a.diagram.positions
      | .num _ p => ps := ps.push p
  return ps.foldl (fun acc p => if acc.contains p then acc else acc.push p) #[]

/-- Native hover entries shared by standalone interfaces and component boundaries. -/
def interfaceCodes (boundary : Expr) (side : String) : MetaM (Array (String × Html)) := do
  let mut entries := #[]
  let iface ← interfaceOf boundary
  let label ← match iface.label with
    | .literal label _ =>
      interactiveCode boundary (if label != iface.source then some label else none)
    | _ => interactiveInterfaceLabel boundary
  entries := entries ++ #[(side ++ ".label", label),
    (side ++ ".source", ← interactiveCode boundary),
    (side ++ ".type", ← interactiveCode (← inferType boundary))]
  for (symbol, projection, value) in ← interfaceProjections boundary do
    entries := entries ++
      #[(side ++ "." ++ symbol ++ ".name", ← interactiveCode projection (some symbol)),
        (side ++ "." ++ symbol ++ ".value", ← interactiveCode value)]
    if symbol == "D" then
      entries := entries.push (side ++ ".D.notation",
        ← interactiveCode value (some (← domainNotation value)))
  if !iface.enumerated && !iface.fields.isEmpty then
    let projections ← interfaceProjections boundary
    let some (_, labels, _) := projections.find? (·.1 == "I") | return entries
    let some (_, input, _) := projections.find? (·.1 == "X") | return entries
    let some (_, output, _) := projections.find? (·.1 == "Y") | return entries
    let family ← withLocalDeclD `i labels fun i => do
      return #[(side ++ ".family.port", ← interactiveCode i (some "i")),
        (side ++ ".family.input", ← interactiveCode (mkApp input i) (some "X(i)")),
        (side ++ ".family.output", ← interactiveCode (mkApp output i) (some "Y(i)"))]
    entries := entries ++ family
  for (label, port, input, output) in ← interfacePorts boundary do
    entries := entries ++
      #[(side ++ ".port." ++ label, ← interactiveCode port (some label)),
        (side ++ ".input." ++ label,
          ← interactiveTypeNotation (← typeNotation input)),
        (side ++ ".output." ++ label,
          ← interactiveTypeNotation (← typeNotation output)),
        (side ++ ".signature." ++ label, ← interactiveCode (← mkArrow input output))]
  return entries

def buildCodes (j : JudgmentView) (root : Expr) : MetaM Codes := do
  let mut codes := #[]
  for p in collectPositions j do
    try
      let entries ← Meta.viewSubexpr (fun _ sub => do
        let source ← interactiveCode sub
        let label ← labelFor sub
        let label? := if label == (← ppShort sub) then none else some label
        let mut entries := #[("", ← interactiveCode sub label?), ("source", source)]
        let ty ← instantiateMVars (← inferType sub)
        entries := entries.push ("type", ← interactiveCode ty)
        let (_, outer, inner) ← typeInterfaces ty
        for (side, boundary?) in #[("outer", outer), ("inner", inner)] do
          if let some boundary := boundary? then
            entries := entries ++ (← interfaceCodes boundary side)
        return entries)
        (SubExpr.Pos.ofArray p) root
      codes := codes ++ entries.map fun (part, html) => ((p, part), html)
    catch _ => pure ()
  return codes

/-! ## Responsive, intrinsic layout -/

def sattr (k v : String) : String × Json := (k, Json.str v)

def divClass (cls : String) (children : Array Html) : Html :=
  .element "div" #[sattr "className" cls] children

partial def mathBody : MathLabel → Html
  | .literal s true => .element "mi" #[] #[.text s]
  | .literal s false => .element "mtext" #[] #[.text s]
  | .tensor l r => .element "mrow" #[]
      #[.element "mo" #[] #[.text "("], mathBody l,
        .element "mo" #[] #[.text "⊗"], mathBody r,
        .element "mo" #[] #[.text ")"]]

def mathHtml (label : MathLabel) : Html :=
  match label with
  | .literal s identifier =>
    if identifier && s.length ≤ 24 then
      .element "math" #[sattr "xmlns" "http://www.w3.org/1998/Math/MathML"] #[mathBody label]
    else .element "span" #[sattr "className" "cc-literal-label"] #[.text s]
  | .tensor .. =>
    .element "math" #[sattr "xmlns" "http://www.w3.org/1998/Math/MathML"] #[mathBody label]

/-- Interface information uses exact projections and their inferred types. The same content
is a top-layer popover in the infoview and a keyboard disclosure in static exports. -/
def interfaceLabel (iface : Iface) (pos : Array Nat) (side : String) (codes : Codes) : Html :=
  let code (part text : String) : Html :=
    (codeFor? codes pos (side ++ "." ++ part)).getD (.element "code" #[] #[.text text])
  let fieldHtml (f : InterfaceField) : Html :=
    .element "div" #[sattr "className" "cc-interface-field", sattr "data-field" f.symbol]
      #[.element "dt" #[sattr "title" (f.projection ++ " : " ++ f.type)]
          #[(codeFor? codes pos (side ++ "." ++ f.symbol ++ ".name")).getD (.text f.symbol)],
        .element "dd" #[sattr "title" f.type] #[.text "= ", code (f.symbol ++ ".value") f.value]]
  let fields := iface.fields.filterMap fun f =>
    if f.symbol == "D" then some <|
      .element "div" #[sattr "className" "cc-interface-domain", sattr "data-field" "D"]
        #[.element "dt" #[] #[.text "Domain ", code "D.name" "D"],
          .element "dd" #[sattr "title" ("ε = empty sequence; |s| = sequence length\n" ++ f.value)]
            #[code "D.notation" f.presentation]]
    else if f.symbol == "I" && !iface.enumerated then some (fieldHtml f) else none
  let portRows := iface.ports.map fun p =>
    .element "tr" #[sattr "className" "cc-port-signature", sattr "data-port" p.source]
      #[.element "td" #[sattr "title" p.source] #[code ("port." ++ p.label) p.label],
        .element "td" #[sattr "className" "cc-alphabet", sattr "title" p.input]
          #[code ("input." ++ p.label) p.inputNotation],
        .element "td" #[sattr "className" "cc-alphabet", sattr "title" p.output]
          #[code ("output." ++ p.label) p.outputNotation]]
  let portRows := if iface.enumerated || iface.fields.isEmpty then portRows else
    #[.element "tr" #[sattr "className" "cc-port-family"]
      #[.element "td" #[] #[code "family.port" "i", .text " ∈ ", code "I.name" "I"],
        .element "td" #[] #[code "family.input" "X(i)"],
        .element "td" #[] #[code "family.output" "Y(i)"]]]
  let ports := if iface.fields.isEmpty then Html.text "" else
    if iface.enumerated && iface.ports.isEmpty then
      divClass "cc-empty-ports" #[.text "Ports ∅"]
    else .element "table" #[sattr "className" "cc-port-signatures"]
      #[.element "thead" #[] #[.element "tr" #[]
          (#["Port", "Query", "Reply"].map fun label =>
            .element "th" #[sattr "scope" "col"] #[.text label])],
        .element "tbody" #[] portRows]
  let content := divClass "cc-interface-info"
    #[divClass "cc-interface-title" #[code "label" (match iface.label with
        | .literal s _ => s | _ => iface.source),
        if iface.fields.isEmpty then .element "span" #[] #[.text " : ", code "type" iface.type]
        else .text ""],
      ports, .element "dl" #[] fields,
      .element "details" #[sattr "className" "cc-interface-source"]
        #[.element "summary" #[] #[.text "Lean"], code "source" iface.source,
          .text " : ", code "type" iface.type,
          .element "dl" #[] (iface.fields.map fieldHtml)]]
  let inspector := if (codeFor? codes pos (side ++ ".label")).isSome then
      Html.ofComponent Inspector
        { label := "Interface types and domain", identity := iface.source ++ " : " ++ iface.type }
        #[content]
    else .element "details" #[sattr "className" "cc-inspector cc-inspector-static",
        sattr "name" "cc-interface-inspector"]
      #[.element "summary" #[sattr "aria-label" "Interface types and domain",
          sattr "title" "Interface types and domain"] #[.text "ⓘ"],
        divClass "cc-inspector-body" #[content]]
  divClass "cc-interface-label"
    (if iface.detailsOnly then #[inspector] else
      #[(codeFor? codes pos (side ++ ".label")).getD (mathHtml iface.label), inspector])

def boundary (iface : Iface) (pos : Array Nat) (side : String) (codes : Codes) : Html :=
  divClass "cc-boundary" #[interfaceLabel iface pos side codes]

/-- Branch ports already expose a parallel group's interfaces. Its aggregate
type remains in the tooltip and on any actual connection to another component. -/
def Diagram.exposedLabels (d : Diagram) (codes : Codes) : Array Html :=
  match d with
  | .parallel .. | .tensor .. => #[]
  | _ => d.elem.outer?.map (fun l => #[boundary l d.elem.pos "outer" codes]) |>.getD #[]

def Diagram.innerLabels (d : Diagram) (codes : Codes) : Array Html :=
  match d with
  | .parallel .. | .tensor .. => #[]
  | _ => d.elem.inner?.map (fun l => #[boundary l d.elem.pos "inner" codes]) |>.getD #[]

/-- Wires show attachment, not message direction. The label is the actual
interface at this connection, when supplied by the inferred type. -/
def wire (label? : Option Html := none) : Html :=
  divClass "cc-wire" (label?.map (fun l =>
    #[.element "span" #[sattr "className" "cc-wire-label"] #[l]]) |>.getD #[])

def kindClass : BoxKind → String
  | .res => "cc-resource"
  | .conv => "cc-converter"
  | .sim => "cc-simulator"
  | .spec => "cc-specification"
  | .chip => "cc-opaque"

/-- A notation label keeps its Lean hover when available. -/
def elemLabel (el : Elem) (codes : Codes) : Html :=
  .element "span" #[sattr "className"
    ("cc-object-label" ++ if el.identifier then " cc-identifier" else "")]
    #[(codeFor? codes el.pos).getD (mathHtml (.literal el.label el.identifier))]

def domBox (el : Elem) (sel : Array (Array Nat)) (codes : Codes) : Html :=
  .element "div"
    #[sattr "className" ("cc-node " ++ kindClass el.kind ++
        (if sel.contains el.pos then " cc-selected" else "")),
      sattr "title" (el.source ++ " : " ++ el.type),
      sattr "data-source" el.source]
    #[match el.pseudocode? with
      | none => elemLabel el codes
      | some doc => .element "details" #[sattr "className" "cc-pseudocode-leaf"]
          #[.element "summary" #[sattr "title" "Pseudocode of the original declaration"]
              #[elemLabel el codes], renderPseudocode doc]]

/-- Every recursive group is retained. Nested attachment is a chain; a tensor
converter remains a grouped converter rather than being distributed over a
parallel resource by an unrequested rewrite. -/
partial def renderDiagram (d : Diagram) (sel : Array (Array Nat)) (codes : Codes) : Html :=
  match d with
  | .atom e => domBox e sel codes
  | .attach e c r at? =>
    let connection := match at? with
      | some i => wire (some (mathHtml (.literal i)))
      | none => wire (c.elem.inner?.map (interfaceLabel · c.elem.pos "inner" codes))
    let body := divClass "cc-attachment"
      #[renderDiagram c sel codes, connection, renderDiagram r sel codes]
    if e.named then
      .element "div" #[sattr "className" "cc-named-composition",
        sattr "title" (e.source ++ " : " ++ e.type), sattr "data-source" e.source]
        #[divClass "cc-group-label" #[elemLabel e codes], body]
    else body
  | .parallel e l r | .tensor e l r =>
    let isTensor := match d with | .tensor .. => true | _ => false
    let symbol := if isTensor then "⊗ₘ" else "∥"
    let branch (b : Diagram) : Html :=
      divClass "cc-branch"
        (b.exposedLabels codes ++ #[renderDiagram b sel codes] ++ b.innerLabels codes)
    .element "div"
      #[sattr "className" ("cc-parallel" ++ (if isTensor then " cc-tensor" else "") ++
          (if e.named then " cc-named" else "")),
        sattr "title" (e.source ++ " : " ++ e.type), sattr "data-source" e.source]
      #[divClass "cc-group-label"
          (if e.named then #[elemLabel e codes, .text (" · " ++ symbol)] else #[.text symbol]),
        branch l, branch r]
  | .serial e l r =>
    .element "div" #[sattr "className" ("cc-serial" ++ if e.named then " cc-named" else ""),
      sattr "title" e.source]
      #[divClass "cc-group-label"
          (if e.named then #[elemLabel e codes, .text " · ≫"] else #[.text "≫"]),
        renderDiagram l sel codes,
        wire (l.elem.inner?.map (interfaceLabel · l.elem.pos "inner" codes)),
        renderDiagram r sel codes]
  | .wrapper e b =>
    divClass "cc-wrapper" #[domBox { e with kind := .chip } sel codes,
      renderDiagram b sel codes]

def renderSystemComponent (s : SystemView) (sel : Array (Array Nat) := #[])
    (codes : Codes := #[]) (_compact : Bool := false) : Html :=
  let d := s.diagram
  divClass ("cc-system" ++ if d.horizontalSpan ≥ 5 || d.hasWideInterface then " cc-dense" else "")
    #[divClass "cc-system-outer" (d.exposedLabels codes),
      divClass "cc-system-body" #[renderDiagram d sel codes],
      divClass "cc-system-inner" (d.innerLabels codes)]

/-- Static rendering and the interactive panel share the same component tree. -/
def renderSystem (s : SystemView) (sel : Array (Array Nat) := #[])
    (codes : Codes := #[]) : Html := renderSystemComponent s sel codes

def renderCard (sel : Array (Array Nat)) (codes : Codes) : AdvCard → Html
  | .dist sym l r => divClass "cc-distance"
      #[divClass "cc-operator" #[.text sym], divClass "cc-delimiter" #[.text "("],
        divClass "cc-operands"
        #[renderSystemComponent l sel codes,
          divClass "cc-comma" #[.text ","], renderSystemComponent r sel codes],
        divClass "cc-delimiter" #[.text ")"]]
  | .win sym s => divClass "cc-distance"
      #[divClass "cc-operator" #[.text sym], renderSystemComponent s sel codes]
  | .mass s event => divClass "cc-distance"
      #[divClass "cc-operator" #[.text "mass"], renderSystemComponent s sel codes,
        divClass "cc-literal" #[.text event]]
  | .num label p => divClass "cc-literal" #[(codeFor? codes p).getD (.text label)]

def renderCards (cards : Array AdvCard) (sel : Array (Array Nat)) (codes : Codes) : Html :=
  divClass "cc-cards" (cards.map (renderCard sel codes))

def sourceHtml (j : JudgmentView) (codes : Codes) : Html :=
  .element "details" #[sattr "className" "cc-source-toggle"]
    #[.element "summary" #[sattr "title" "Original Lean expression"] #[.text "Lean"],
      .element "div" #[sattr "className" "cc-source", sattr "aria-label" "Lean expression"]
        #[(codeFor? codes j.sourcePos "source").getD (.element "code" #[] #[.text j.source])]]

def renderJudgment (j : JudgmentView) (sel : Array (Array Nat))
    (codes : Codes := #[]) (footer : Array Html := #[]) : Html := Id.run do
  let mut relation : Array Html := #[]
  let mut annotation : Array Html := #[]
  if let some c := j.protocol? then
    let label := match c with
      | .atom el => .element "span"
          #[sattr "title" (el.source ++ " : " ++ el.type)] #[elemLabel el codes]
      | _ => renderDiagram c sel codes
    annotation := annotation.push label
  if let some error := j.eps? then
    let epsChildren :=
      if j.protocol?.isSome then
        #[.text "; ", (j.epsPos?.bind (codeFor? codes)).getD (.text error)]
      else
        #[(j.epsPos?.bind (codeFor? codes)).getD (.text error)]
    annotation := annotation.push <| divClass "cc-error" epsChildren
  if !annotation.isEmpty then relation := relation.push (divClass "cc-protocol" annotation)
  relation := relation.push (divClass "cc-relation-symbol" #[.text j.rel])
  let rel := divClass "cc-relation" relation
  let content := match j.bridge? with
    | some (l, r) => #[renderCards l sel codes,
        divClass "cc-comparison-tail" #[rel, renderCards r sel codes]]
    | none => match j.ideal? with
      | some ideal => #[renderSystemComponent j.real sel codes, rel,
          renderSystemComponent ideal sel codes]
      | none => #[renderSystemComponent j.real sel codes]
  let drawing := .element "div"
    #[sattr "className" "cc-comparison", sattr "tabIndex" "0",
      sattr "role" "region", sattr "aria-label" "System structure"] content
  let source := if footer.isEmpty then sourceHtml j codes
    else divClass "cc-step-footer" (#[sourceHtml j codes] ++ footer)
  let mut body := #[drawing, source]
  if let some note := j.note? then body := body.push (divClass "cc-note" #[.text note])
  return divClass "cc-surface" body

def renderInline (j : JudgmentView) (sel : Array (Array Nat))
    (codes : Codes := #[]) (footer : Array Html := #[]) : Html :=
  renderJudgment j sel codes footer

def stylesheet : String := include_str "cc-diagram.css"

def sect (s : String) : Html := divClass "cc-section" #[.text s]

def invisible : Html := .element "span" #[("hidden", Json.bool true)] #[]

def panel (inner : Html) : Html :=
  .element "details" #[("open", Json.bool true), sattr "className" "ccw"]
    #[.element "summary" #[] #[.text "Diagram"],
      .element "style" #[] #[.text stylesheet], inner]
/-- Native and exported proof views share the same expression projection. -/
def proofTypedSystem (e : Expr) : Expr :=
  if e.isAppOf ``Subtype.val then e.getAppArgs.back! else e

def proofRenderContext (interactive : Bool) : ProofRenderContext := {
  interactive
  code := fun e label? => do
    if interactive then return ← interactiveCode e label?
    return .element "code" #[sattr "title" (← ppShort e)] #[.text (label?.getD (← ppShort e))]
  diagram := fun e footer => do
    let candidate := proofTypedSystem e
    let e ← if (← resourceBoundary? (← inferType candidate)).isSome then pure candidate
      else pure e
    let j? ← if ← isProp e then parseJudgment? e else do
      let side ← parseSide e
      let source ← ppShort e
      pure (if side.diagram.recognized then
        some { real := side, source : JudgmentView } else none)
    if let some j := j? then
      return renderJudgment j #[] (← if interactive then buildCodes j e else pure #[]) footer
    let code ← if interactive then interactiveCode e
      else pure (.element "code" #[] #[.text (← ppShort e)])
    return proofDiv "cc-step-fallback"
      #[proofDiv "cc-step-statement" #[code], proofDiv "cc-step-footer" footer] }

def proofPanel (body : Html) : Html :=
  .element "details" #[("open", .bool true), sattr "className" "ccw"]
    #[.element "summary" #[] #[.text "Proof"],
      .element "style" #[] #[.text stylesheet], body]

/-- The registered witness keeps its original expression and elaboration context. -/
def proofViewHtml? (e : Expr) (interactive : Bool) : MetaM (Option Html) :=
  withProofView e fun view => renderProofView (proofRenderContext interactive) view

/-! ## The calc ladder and enclosing-theorem context

A panel RPC can see the surrounding *syntax* through the command
snapshot: each elaborated `calc` relation is displayed with its own source
locations. The step number navigates to that relation in the editor. -/

def rangeContains (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  match stx.getRange? with
  | some r => r.start ≤ pos && pos ≤ r.stop
  | none => false

/-- Smallest `calcSteps` node containing `pos`. -/
partial def findCalcSteps? (stx : Syntax) (pos : String.Pos.Raw) : Option Syntax :=
  if !rangeContains stx pos then none
  else
    let deeper := stx.getArgs.findSome? (findCalcSteps? · pos)
    match deeper with
    | some d => some d
    | none => if stx.getKind == `Lean.calcSteps then some stx else none

/-- The elaborated `Expr` (and its elaboration context) recorded for a
syntax range — how the ladder recovers each step's statement with the
`calc` `_` placeholders resolved. -/
def termInfoFor? (tree : Elab.InfoTree) (target : Syntax) :
    Option (Elab.ContextInfo × Elab.TermInfo) := Id.run do
  let some r := target.getRange? | return none
  let results := tree.foldInfo (init := #[]) fun ci i acc =>
    match i with
    | .ofTermInfo ti =>
      match ti.stx.getRange? with
      | some r' => if r' == r then acc.push (ci, ti) else acc
      | none => acc
    | _ => acc
  return results[0]?

/-- Failed term elaboration retains its expected type in a partial info node. -/
def partialTermInfoFor? (tree : Elab.InfoTree) (target : Syntax) :
    Option (Elab.ContextInfo × Elab.PartialTermInfo) := do
  let range ← target.getRange?
  let results := tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofPartialTermInfo ti =>
      if ti.stx.getRange? == some range then acc.push (ci, ti) else acc
    | _ => acc
  results[0]?


/-- An unfinished `by` block has tactic information even when no term was produced. -/
def unfinishedProofAt? (tree : Elab.InfoTree) (target : Syntax)
    (interactive : Bool) : IO (Option Html) := do
  let some range := target.getRange? | return none
  let tactics := tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofTacticInfo ti =>
      if ti.stx.getRange? == some range then acc.push (ci, ti) else acc
    | _ => acc
  for (ci, ti) in tactics do
    let view? ← { ci with mctx := ti.mctxAfter }.runMetaM {} do
      let mut obligations : Array Html := #[]
      for goal in ti.goalsAfter do
        unless ← goal.isAssigned do
          let body ← goal.withContext do
            (proofRenderContext interactive).code (← goal.getType) none
          obligations := obligations.push body
      if obligations.isEmpty then return none
      return some (proofDiv "cc-proof-justification"
        #[proofDiv "cc-proof-obligations" (#[Html.text "Unfinished"] ++ obligations),
          proofDetails "Proof" #[.element "pre" #[] #[.text (target.reprint.getD "")]]])
    if view?.isSome then return view?
  return none


structure Rung where
  jv? : Option JudgmentView
  codes : Codes
  /-- Interactive mathematical term (fallback when the step does not draw). -/
  code? : Option Html
  /-- The actual elaborated proof and its unfinished obligations, if any. -/
  justification? : Option Html := none
  /-- Pretty relation text, retained only as a plain fallback. -/
  title : String
  current : Bool
  /-- Step start, for click-to-navigate. -/
  target : Lsp.Range
  deriving Inhabited

/-- Extract the ladder from the calc block containing `pos`. -/
def calcLadderFromTree? (stx : Syntax) (tree : Elab.InfoTree) (text : FileMap)
    (pos : String.Pos.Raw) (sel : Array (Array Nat)) (interactive := true) :
    IO (Option (Array Rung)) := do
  let some steps := findCalcSteps? stx pos | return none
  -- flatten: calcFirstStep :: calcStep*
  let mut stepStxs : Array Syntax := #[]
  for a in steps.getArgs do
    if a.getKind == `Lean.calcFirstStep || a.getKind == `Lean.calcStep then
      stepStxs := stepStxs.push a
    else
      for b in a.getArgs do
        if b.getKind == `Lean.calcFirstStep || b.getKind == `Lean.calcStep then
          stepStxs := stepStxs.push b
  if stepStxs.size ≤ 1 then return none
  let mut rungs : Array Rung := #[]
  for st in stepStxs do
    let termStx := st[0]!
    let proofStx? := match st with
      | `(calcFirstStep| $_ := $proof) => some proof.raw
      | `(calcStep| $_ := $proof) => some proof.raw
      | _ => none
    let title := ((termStx.reprint.getD "…").replace "\n" " ").trimAscii.toString
    let current := rangeContains st pos
    let some stepRange := st.getRange? | continue
    let target : Lsp.Range :=
      { start := text.utf8PosToLspPos stepRange.start
        «end» := text.utf8PosToLspPos stepRange.start }
    let mut jv? : Option JudgmentView := none
    let mut codes : Codes := #[]
    let mut code? : Option Html := none
    let mut justification? : Option Html := none
    if let some proofStx := proofStx? then
      if let some (ci, ti) := termInfoFor? tree proofStx then
        justification? ← ci.runMetaM ti.lctx do
          try
            return some (← proofMethodJustification (proofRenderContext interactive)
              ti.expr proofStx.reprint)
          catch _ => pure none
      else if let some (ci, ti) := partialTermInfoFor? tree proofStx then
        justification? ← ci.runMetaM ti.lctx do
          let mut children := #[Html.text "Unfinished"]
          if let some ty := ti.expectedType? then
            children := children.push (← (proofRenderContext interactive).code
              (← instantiateMVars ty) none)
          return some (proofDiv "cc-proof-justification"
            #[proofDiv "cc-proof-obligations" children,
              proofDetails "Proof" #[.element "pre" #[] #[.text (proofStx.reprint.getD "")]]])
      if justification?.isNone then
        justification? ← unfinishedProofAt? tree proofStx interactive
    -- Lean annotates a subsequent step's leading hole before elaboration. Its
    -- relation may therefore have no original syntax range in the info tree.
    -- The proof's expected type is the elaborated relation, with that hole solved.
    let info? := (termInfoFor? tree termStx).map (fun (ci, ti) => (ci, ti, false))
      |>.orElse (fun _ => proofStx?.bind fun proof =>
        (termInfoFor? tree proof).map (fun (ci, ti) => (ci, ti, true)))
    if let some (ci, ti, fromProof) := info? then
      let r ← ci.runMetaM ti.lctx do
        try
          let stmt ← if fromProof then
              match ti.expectedType? with
              | some type => pure type
              | none => inferType ti.expr
            else pure ti.expr
          let stmt ← instantiateMVars stmt
          let code ← (proofRenderContext interactive).code stmt none
          match ← parseJudgment? stmt (sel := sel) with
          | some jv =>
            let cs ← if interactive then buildCodes jv stmt else pure #[]
            pure (some (some jv, cs, code))
          | none => pure (some (none, #[], code))
        catch _ => pure none
      if let some (parsed, cs, code) := r then
        jv? := parsed
        codes := cs
        code? := some code
    rungs := rungs.push { jv?, codes, code?, justification?, title, current, target }
  return some rungs

/-- The enclosing theorem's own statement: shown dimmed when the current
goal is bookkeeping inside a CC proof. -/
def enclosingJudgment? (snap : Snapshots.Snapshot) :
    RequestM (Option (JudgmentView × Codes)) := do
  let outer := snap.infoTree.foldInfo
      (init := (none : Option (Elab.ContextInfo × Elab.TacticInfo))) fun ci i acc =>
    match i with
    | .ofTacticInfo ti =>
      match acc with
      | none => some (ci, ti)
      | some (_, ti') =>
        let sz  := (ti.stx.getRange?.map fun r => r.stop.byteIdx - r.start.byteIdx).getD 0
        let sz' := (ti'.stx.getRange?.map fun r => r.stop.byteIdx - r.start.byteIdx).getD 0
        if sz > sz' then some (ci, ti) else acc
    | _ => acc
  let some (ci, ti) := outer | return none
  let some g := ti.goalsBefore.head? | return none
  ci.runMetaM {} do
    setMCtx ti.mctxBefore
    g.withContext do
      try
        let stmt ← instantiateMVars (← g.getType)
        match ← parseJudgment? stmt with
        | some jv => pure (some (jv, ← buildCodes jv stmt))
        | none => pure none
      catch _ => pure none

def renderRungs (rungs : Array Rung) (sel : Array (Array Nat))
    (dm : Lean.Server.DocumentMeta) (interactive := true) : Html := Id.run do
  let mut steps : Array Html := #[]
  for i in [0:rungs.size] do
    let r := rungs[i]!
    let numLink : Html := if !interactive then .text s!"{i + 1} / {rungs.size}" else
      .ofComponent MakeEditLink
      (.ofReplaceRange' dm r.target "" (some r.target))
      #[.element "span"
        #[sattr "className" "rgn", sattr "title" s!"Go to calculation step {i + 1}",
          sattr "aria-label" s!"Go to calculation step {i + 1}"] #[.text "↗"]]
    let footer := #[r.justification?.getD (.text ""),
      divClass "cc-step-navigation" #[numLink]]
    let content : Html := match r.jv? with
      | some jv => renderInline jv sel r.codes footer
      | none => divClass "cc-step-fallback"
          #[divClass "cc-step-statement" #[r.code?.getD (.text r.title)],
            divClass "cc-step-footer" footer]
    steps := steps.push <| proofStep content r.current
  if !interactive then return proofDiv "cc-proof-static-steps" steps
  let initialIndex := ((List.range rungs.size).find? fun i => rungs[i]!.current).getD 0
  let stepper := Html.ofComponent CalcStepper { initialIndex, labels := rungs.map (·.title) } steps
  return stepper

/-- Parse a CC judgment from a proposition, descending into conjunction arms and unfolding
Prop-valued security wrapper definitions when the outer head is not itself a logical
connective or registered `DeclRole`. -/
partial def parseJudgmentInProp? (e : Expr) (p : SubExpr.Pos := .root)
    (unfolded : Bool := false) (depth : Nat := 8) :
    MetaM (Option (JudgmentView × Bool)) := do
  let e := e.consumeMData
  if let some j ← parseJudgment? e p then
    return some (j, unfolded)
  if depth == 0 then return none
  if e.isAppOfArity ``And 2 then
    let args := e.getAppArgs
    if let some res ← parseJudgmentInProp? args[0]! (argPos p 2 0) unfolded (depth - 1) then
      return some res
    if let some res ← parseJudgmentInProp? args[1]! (argPos p 2 1) unfolded (depth - 1) then
      return some res
    return none
  if let .const head _ := e.getAppFn.consumeMData then
    if head == ``Eq || head == ``LE.le || head == ``LT.lt ||
       head == ``GE.ge || head == ``GT.gt || head == ``Iff ||
       head == ``Or || head == ``Not || head == ``Exists ||
       head == ``True || head == ``False then
      return none
    if (← declRole? e).isNone && (← isProp e) then
      if let some next ← withTransparency .default (Meta.unfoldDefinition? e) then
        let rec zetaHead : Expr → Expr
          | .letE _ _ v b _ => zetaHead (b.instantiate1 v)
          | .mdata _ inner => zetaHead inner
          | x => x
        let next := zetaHead next
        if next != e then
          return ← forallTelescope next fun _ uBody =>
            parseJudgmentInProp? uBody .root true (depth - 1)
  return none

/-- Project an already elaborated expression. Quantified statements keep their original source. -/
def viewExprCore (e : Expr) (interactive : Bool) : MetaM (Option (JudgmentView × Codes)) := do
  let ty ← inferType e
  let stmt ← if (← isProp e) then pure e else if (← isProp ty) then pure ty else pure e
  if (← isProp stmt) then
    return ← forallTelescope stmt fun _ body => do
      let some (j, unfolded) ← parseJudgmentInProp? body | return none
      let j := { j with source := ← ppShort stmt }
      let mut codes ← if interactive && !unfolded then buildCodes j body else pure #[]
      if interactive then
        codes := codes.filter (·.1 != (j.sourcePos, "source"))
        codes := codes.push ((j.sourcePos, "source"), ← interactiveCode stmt)
      return some (j, codes)
  let s ← parseSide e
  if s.diagram.recognized then
    let j := { real := s, source := ← ppShort e : JudgmentView }
    return some (j, ← if interactive then buildCodes j e else pure #[])
  return none

def pseudocodePanel (doc : SystemAlgebra.DSL.SourceDocument) : Html :=
  .element "details" #[("open", .bool true), sattr "className" "ccw cc-pseudocode-panel"]
    #[.element "summary" #[] #[.text "Pseudocode"],
      .element "style" #[] #[.text stylesheet], renderPseudocode doc]


/-- Only terms whose recorded source range contains the cursor are candidates. Smaller terms
come first; an unapplied head cannot hide its enclosing, fully applied system. -/
def cursorTerms (tree : Elab.InfoTree) (pos : String.Pos.Raw) :
    Array (Elab.ContextInfo × Elab.TermInfo) :=
  (tree.foldInfo (init := #[]) fun ci info acc =>
    match info with
    | .ofTermInfo ti =>
      if ti.stx.getRange? (canonicalOnly := true) |>.any (·.contains pos true) then
        acc.push (ci, ti)
      else acc
    | _ => acc).qsort fun a b =>
      let width (ti : Elab.TermInfo) :=
        ti.stx.getRange?.map fun r => r.stop.byteIdx - r.start.byteIdx
      (width a.2).getD 0 < (width b.2).getD 0

/-- Options come from the cursor's elaboration context, including `set_option … in`. -/
def automaticEnabledAt (tree : Elab.InfoTree) (pos : String.Pos.Raw)
    (fallback : Options) : Bool :=
  cc.diagram.auto.get <| ((tree.hoverableInfoAtM? (m := Id) pos (includeStop := true))
    |>.map (·.ctx.options)).getD fallback

/-- Explicit panels own their command range, including under a scoped option. -/
partial def explicitViewAt (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  rangeContains stx pos &&
    (stx.getKind == `CCWidget.ccDiagramShow || stx.getKind == `CCWidget.ccPseudocodeShow ||
      stx.getKind == `CCWidget.ccProofShow ||
      stx.getArgs.any (explicitViewAt · pos))

/-- Use only actual elaborated terms. Unresolved expressions and error placeholders do not
supply diagrams. A bare parameterized DSL declaration may show its recorded source instead. -/
def cursorView? (tree : Elab.InfoTree) (pos : String.Pos.Raw) : IO (Option Html) := do
  let mut source? := none
  let mut unresolved := false
  for (ci, ti) in cursorTerms tree pos do
    try
      let (view?, doc?, incomplete) ← ci.runMetaM ti.lctx do
        let e ← instantiateMVars ti.expr
        if e.hasExprMVar || e.hasSorry then return (none, none, true)
        if let some view ← proofViewHtml? e true then
          return (some (proofPanel view), none, false)
        -- A theorem head still awaiting arguments must not hide its enclosing proof
        -- application behind a diagram of the theorem's universally quantified type.
        if e.getAppFn.constName?.any (proofBridges.getState (← getEnv) |>.contains) then
          return (none, none, false)
        if e.hasLevelMVar then return (none, none, true)
        if let some (j, codes) ← viewExprCore e true then
          return (some (panel (renderJudgment j #[] codes)), none, false)
        if !(← interfaceProjections e).isEmpty then
          let iface ← interfaceOf e
          let codes := (← interfaceCodes e "outer").map fun (part, html) => ((#[], part), html)
          return (some (panel (interfaceLabel iface #[] "outer" codes)), none, false)
        let documents := SystemAlgebra.DSL.sourceDocuments.getState (ci.cmdEnv?.getD (← getEnv))
        let doc? := e.getAppFn.constName?.bind documents.find?
        return (none, doc?, false)
      unresolved := unresolved || incomplete
      if view?.isSome then return view?
      if source?.isNone then source? := doc?
    catch _ => pure ()
  return if unresolved then none else source?.map pseudocodePanel

/-! ## The panel widget -/

@[server_rpc_method]
def CCDiagram.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) := do
  let doc ← RequestM.readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos props.pos
  RequestM.withWaitFindSnapAtPos props.pos fun snap => do
    let options ← snap.runCoreM doc.meta getOptions
    unless automaticEnabledAt snap.infoTree pos options do return invisible
    if explicitViewAt snap.stx pos then return invisible
    -- selections only make sense against the first tactic goal
    let sel := match props.goals[0]? with
      | some g => props.selectedLocations.filterMap fun l =>
          if l.mvarId == g.mvarId then
            match l.loc with
            | .target pos => some pos.toArray
            | _ => none
          else none
      | none => #[]
    -- the current statement: the tactic goal, else the term-mode goal
    let goalJv? ←
      if let some g := props.goals[0]? then
        g.ctx.val.runMetaM {} <| g.mvarId.withContext do
          try
            let stmt ← instantiateMVars (← g.mvarId.getType)
            match ← parseJudgment? stmt (sel := sel) with
            | some jv => pure (some (jv, ← buildCodes jv stmt))
            | none => pure none
          catch _ => pure none
      else if let some tg := props.termGoal? then
        tg.ctx.val.runMetaM tg.term.val.lctx do
          try
            let stmt ← match tg.term.val.expectedType? with
              | some ty => pure ty
              | none => inferType tg.term.val.expr
            let stmt ← instantiateMVars stmt
            match ← parseJudgment? stmt (sel := sel) with
            | some jv => pure (some (jv, ← buildCodes jv stmt))
            | none => pure none
          catch _ => pure none
      else pure none
    -- inside a calc block the ladder renders from the syntax alone
    let ladder? ← try calcLadderFromTree? snap.stx snap.infoTree text pos sel catch _ => pure none
    if let some rungs := ladder? then
      let rungs := rungs.map fun r =>
        if r.current && r.jv?.isNone then
          match goalJv? with
          | some (jv, cs) => { r with jv? := some jv, codes := cs }
          | none => r
        else r
      if rungs.any fun r => r.jv?.isSome then
        return panel (renderRungs rungs sel doc.meta)
    if let some view ← cursorView? snap.infoTree pos then return view
    match goalJv? with
    | some (jv, codes) => return panel (renderJudgment jv sel codes)
    | none =>
      if props.goals.isEmpty && props.termGoal?.isNone then
        return invisible
      -- bookkeeping goal inside a CC theorem — keep the context strip
      let ctx? ← try enclosingJudgment? snap catch _ => pure none
      match ctx? with
      | some (jv, codes) =>
        return panel <| .element "div"
          #[("style", Json.mkObj [("opacity", Json.str "0.66")])]
          #[.element "div" #[sattr "className" "cc-note", sattr "title" "Enclosing statement"]
            #[.text "Context"], renderJudgment jv #[] codes]
      | none => return invisible

/-- The constructive-cryptography goal diagram.  Shown automatically in
every module importing `Rendering.CCWidget`, unless `cc.diagram.auto` is false.
Uses recognized goals or terms at the cursor, and stays empty for unrelated terms. -/
@[widget_module]
def CCDiagram : Component PanelWidgetProps :=
  mk_rpc_widget% CCDiagram.rpc

/-! ## Command integration -/

/-- Explicit commands elaborate once, then use the same projection as automatic views. -/
def elabViewCore (t : Syntax.Term) (interactive : Bool) :
    Elab.TermElabM (Option (JudgmentView × Codes)) := do
  let e ← Elab.Term.elabTerm t none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  viewExprCore (← instantiateMVars e) interactive

def elabView (t : Syntax.Term) : Elab.TermElabM (Option JudgmentView) := do
  return (← elabViewCore t false).map (·.1)

elab "#cc_diagram_check " t:term : command =>
  Elab.Command.runTermElabM fun _ => do
    unless (← elabView t).isSome do throwError "cc_diagram: expression not recognized"

elab "#cc_diagram_view " t:term : command =>
  Elab.Command.runTermElabM fun _ => do
    let some j ← elabView t | throwError "cc_diagram: expression not recognized"
    logInfo m!"{toJson j}"

elab (name := ccDiagramShow) stx:"#cc_diagram_show " t:term : command => do
  let h ← Elab.Command.runTermElabM fun _ => do
    let some (j, codes) ← elabViewCore t true
      | throwError "cc_diagram: expression not recognized"
    return panel (renderJudgment j #[] codes)
  Elab.Command.liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript) (return json% { html: $(← rpcEncode h) }) stx

/-- Elaborate an explicitly selected proof object without guessing unresolved arguments. -/
def elabProofView (t : Syntax.Term) (interactive : Bool) : Elab.TermElabM Html := do
  let e ← Elab.Term.elabTerm t none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let some view ← proofViewHtml? (← instantiateMVars e) interactive
    | throwError "cc_proof: expression has no registered proof view"
  return proofPanel view

elab (name := ccProofShow) stx:"#cc_proof_show " t:term : command => do
  let html ← Elab.Command.runTermElabM fun _ => elabProofView t true
  Elab.Command.liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript) (return json% { html: $(← rpcEncode html) }) stx

end CCWidget

open CCWidget in
show_panel_widgets [CCDiagram]
