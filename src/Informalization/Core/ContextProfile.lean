/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Lean.Elab.Declaration
import Lean.Linter.Util
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Presentation
import Informalization.Core.Overlay
import Informalization.CC.Registry

/-!
# Context Profiles & 5-Level Anti-Clobbering Semantic-Role Lattice (`P0.3`)

Provides composable paper domain contexts (`BaseCC` → `SchemeContext`, `ChannelContext`,
`MPCContext`, `IndiffContext`, `GameBasedContext`), persistent declaration/namespace context
binding (`declContextExt`, `nsContextExt`), positional `SemanticRole` inference with a true
semilattice join (`{.realResource, .idealResource} ↦ .hybridResource`), and the strict
5-level resolution hierarchy:

1. **Level 1**: Explicit `@[paper_role]` or `With role` override
2. **Level 2**: Concrete non-carrier `PaperDescribeRule` (`carrier := false`) — never clobbered
3. **Level 3**: Interface-specific `@[interface_resource_noun]` / `informal_noun`
4. **Level 4**: Joined positional `SemanticRole` (with `{real, ideal} ↦ hybrid`)
5. **Level 5**: Inherited `ContextProfile` carrier/resource default
-/

syntax (name := Lean.Parser.Attr.paper_context) "paper_context" ident : attr

namespace Informalization.Core.ContextProfile

open Lean Elab Meta Command
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Presentation
open Informalization.Core.Overlay
open Informalization.CC.Registry

/-! ## 1. `SemanticRole` & Semilattice Join -/

inductive SemanticRole
  | realResource
  | idealResource
  | hybridResource
  | assumedResource
  | schemeUnderTest
  | honestProtocol
  | simulator
  | adversary
  | distinguisher
  | underlyingPrimitive
  | leakage
  | errorBound
  | genericParameter
  deriving DecidableEq, Repr, BEq, Inhabited, Ord

/-- Semilattice join on inferred positional roles:
`{.realResource, .idealResource} ↦ .hybridResource` (hybrid absorbs both real and ideal),
`.genericParameter` is bottom, and identical roles are idempotent. -/
def SemanticRole.join (a b : SemanticRole) : SemanticRole :=
  if a == b then a
  else match a, b with
    | .realResource, .idealResource | .idealResource, .realResource => .hybridResource
    | .hybridResource, .realResource | .realResource, .hybridResource => .hybridResource
    | .hybridResource, .idealResource | .idealResource, .hybridResource => .hybridResource
    | .genericParameter, x | x, .genericParameter => x
    | .assumedResource, .realResource | .realResource, .assumedResource => .hybridResource
    | _, _ => a

def SemanticRole.ofString? (s : String) : Option SemanticRole :=
  match s.trimAscii.toString.toLower with
  | "real" | "realresource" | "real_resource" | "real resource" | "real channel" | "real functionality" => some .realResource
  | "ideal" | "idealresource" | "ideal_resource" | "ideal resource" | "ideal channel" | "ideal functionality" => some .idealResource
  | "hybrid" | "hybridresource" | "hybrid_resource" | "hybrid resource" | "hybrid channel" | "hybrid functionality" => some .hybridResource
  | "assumed" | "assumedresource" | "assumed_resource" | "assumed resource" => some .assumedResource
  | "scheme" | "schemeundertest" | "scheme_under_test" | "cryptographic scheme" => some .schemeUnderTest
  | "protocol" | "honest" | "honestprotocol" | "honest_protocol" | "honest protocol" => some .honestProtocol
  | "simulator" => some .simulator
  | "adversary" => some .adversary
  | "distinguisher" => some .distinguisher
  | "primitive" | "underlyingprimitive" | "underlying_primitive" | "underlying primitive" => some .underlyingPrimitive
  | "leakage" => some .leakage
  | "error" | "errorbound" | "error_bound" | "error bound" => some .errorBound
  | _ => none

/-- Canonical role identifier string corresponding to `SemanticRole` (inverse of `ofString?`). -/
def SemanticRole.toCanonicalString : SemanticRole → String
  | .realResource => "realResource"
  | .idealResource => "idealResource"
  | .hybridResource => "hybridResource"
  | .assumedResource => "assumedResource"
  | .schemeUnderTest => "schemeUnderTest"
  | .honestProtocol => "honestProtocol"
  | .simulator => "simulator"
  | .adversary => "adversary"
  | .distinguisher => "distinguisher"
  | .underlyingPrimitive => "underlyingPrimitive"
  | .leakage => "leakage"
  | .errorBound => "errorBound"
  | .genericParameter => "genericParameter"

/-- Semilattice join on raw role strings when both parse as recognized `SemanticRole`s. -/
def mergeRoleStrings (prev? : Option String) (next : String) : String :=
  match prev? with
  | none => next
  | some prev =>
      match SemanticRole.ofString? prev, SemanticRole.ofString? next with
      | some sr1, some sr2 => (sr1.join sr2).toCanonicalString
      | _, _ => next

/-! ## 2. Inheriting `ContextProfile` Hierarchy & Persistence (`declContextExt`) -/

structure PaperContextProfile where
  name : Name
  parent? : Option Name := none
  carrierRoleNoun? : Option CountNoun := none
  defaultResourceNoun? : Option CountNoun := none
  roleNouns : List (SemanticRole × CountNoun) := []
  defaultVarStyles : List (SemanticRole × MathFontStyle) := []
  preferMathcalSchemes : Bool := true
  deriving Inhabited, Repr

initialize contextProfileExt :
    SimplePersistentEnvExtension (Name × PaperContextProfile) (NameMap PaperContextProfile) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, p) => m.insert n p
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (n, p) => m.insert n p
  }

/-- Per-declaration persistent context assignment (`.olean` CLI == live Infoview). -/
initialize declContextExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (d, p) => m.insert d p
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (d, p) => m.insert d p
  }

/-- Zero-edit namespace-level persistent context mapping (`paper_context_for Namespace Profile`). -/
initialize nsContextExt :
    SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (ns, p) => m.insert ns p
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (ns, p) => m.insert ns p
  }

/-- Scoped active `paper_context` option (pushed/popped automatically by `section ... end`). -/
register_option paper.context : String := {
  defValue := ""
  descr := "Active domain ContextProfile name for declarations elaborated in the current scope."
}

private def baseCCProfile : PaperContextProfile := {
  name := `BaseCC
  parent? := none
  carrierRoleNoun? := none
  defaultResourceNoun? := some ⟨"resource", "resources"⟩
  roleNouns := [
    (.realResource, ⟨"real resource", "real resources"⟩),
    (.idealResource, ⟨"ideal resource", "ideal resources"⟩),
    (.hybridResource, ⟨"hybrid resource", "hybrid resources"⟩),
    (.assumedResource, ⟨"assumed resource", "assumed resources"⟩),
    (.schemeUnderTest, ⟨"cryptographic scheme", "cryptographic schemes"⟩),
    (.honestProtocol, ⟨"protocol", "protocols"⟩),
    (.simulator, ⟨"simulator", "simulators"⟩),
    (.adversary, ⟨"adversary", "adversaries"⟩),
    (.distinguisher, ⟨"distinguisher", "distinguishers"⟩),
    (.underlyingPrimitive, ⟨"underlying primitive", "underlying primitives"⟩),
    (.leakage, ⟨"leakage function", "leakage functions"⟩),
    (.errorBound, ⟨"error bound", "error bounds"⟩)
  ]
}

private def builtinProfiles : List PaperContextProfile := [
  baseCCProfile,
  { name := `SchemeContext
    parent? := some `BaseCC
    carrierRoleNoun? := some ⟨"cryptographic space", "cryptographic spaces"⟩
    roleNouns := [
      (.schemeUnderTest, ⟨"cryptographic scheme", "cryptographic schemes"⟩)
    ] },
  { name := `ChannelContext
    parent? := some `BaseCC
    defaultResourceNoun? := some ⟨"channel", "channels"⟩
    roleNouns := [
      (.realResource, ⟨"real channel", "real channels"⟩),
      (.idealResource, ⟨"ideal channel", "ideal channels"⟩),
      (.hybridResource, ⟨"hybrid channel", "hybrid channels"⟩),
      (.assumedResource, ⟨"assumed channel", "assumed channels"⟩),
      (.schemeUnderTest, ⟨"channel protocol", "channel protocols"⟩)
    ] },
  { name := `MPCContext
    parent? := some `BaseCC
    defaultResourceNoun? := some ⟨"functionality", "functionalities"⟩
    roleNouns := [
      (.realResource, ⟨"real-world functionality", "real-world functionalities"⟩),
      (.idealResource, ⟨"ideal functionality", "ideal functionalities"⟩),
      (.hybridResource, ⟨"hybrid functionality", "hybrid functionalities"⟩),
      (.honestProtocol, ⟨"multiparty protocol", "multiparty protocols"⟩),
      (.adversary, ⟨"corrupting adversary", "corrupting adversaries"⟩)
    ] },
  { name := `IndiffContext
    parent? := some `BaseCC
    roleNouns := [
      (.realResource, ⟨"real construction", "real constructions"⟩),
      (.idealResource, ⟨"idealized primitive", "idealized primitives"⟩),
      (.hybridResource, ⟨"hybrid construction", "hybrid constructions"⟩),
      (.simulator, ⟨"indifferentiability simulator", "indifferentiability simulators"⟩),
      (.underlyingPrimitive, ⟨"idealized component", "idealized components"⟩)
    ] },
  { name := `GameBasedContext
    parent? := some `BaseCC
    defaultResourceNoun? := some ⟨"game", "games"⟩
    roleNouns := [
      (.realResource, ⟨"real-or-random game", "real-or-random games"⟩),
      (.idealResource, ⟨"idealized game", "idealized games"⟩),
      (.hybridResource, ⟨"hybrid game", "hybrid games"⟩),
      (.adversary, ⟨"adversary", "adversaries"⟩)
    ] }
]

private def lookupRawProfile? (env : Environment) (name : Name) : Option PaperContextProfile :=
  (contextProfileExt.getState env).get? name <|>
  builtinProfiles.find? (·.name == name)

/-- Merge `child` over inherited `parent` fields. -/
private def mergeProfiles (parent child : PaperContextProfile) : PaperContextProfile :=
  let mergedRoles :=
    child.roleNouns ++ parent.roleNouns.filter (fun (r, _) => !child.roleNouns.any (·.1 == r))
  let mergedStyles :=
    child.defaultVarStyles ++ parent.defaultVarStyles.filter (fun (r, _) => !child.defaultVarStyles.any (·.1 == r))
  {
    name := child.name
    parent? := child.parent?
    carrierRoleNoun? := child.carrierRoleNoun? <|> parent.carrierRoleNoun?
    defaultResourceNoun? := child.defaultResourceNoun? <|> parent.defaultResourceNoun?
    roleNouns := mergedRoles
    defaultVarStyles := mergedStyles
    preferMathcalSchemes := child.preferMathcalSchemes
  }

/-- Resolve a named `PaperContextProfile` across its full inheritance chain (`BaseCC` fallback). -/
partial def resolveProfile (env : Environment) (name : Name) (fuel : Nat := 16) : PaperContextProfile :=
  if fuel == 0 then baseCCProfile
  else match lookupRawProfile? env name with
    | none => baseCCProfile
    | some p =>
        match p.parent? with
        | none => p
        | some parName =>
            let par := resolveProfile env parName (fuel - 1)
            mergeProfiles par p

def PaperContextProfile.lookupRoleNoun? (p : PaperContextProfile) (role : SemanticRole) : Option CountNoun :=
  (p.roleNouns.find? (·.1 == role)).map (·.2)

/-- Look up the explicitly configured context profile name (if any) for `declName`. -/
def getEffectiveContextProfileName? (env : Environment) (declName : Name) : Option Name := Id.run do
  if let some p := (declContextExt.getState env).get? declName then
    return some p
  else
    let nsMap := nsContextExt.getState env
    let mut best? : Option (Name × Nat) := none
    for (ns, prof) in nsMap.toList do
      if ns.isPrefixOf declName then
        let depth := ns.getNumParts
        if best?.all (fun (_, d) => depth > d) then
          best? := some (prof, depth)
    return best?.map (·.1)

/-- Resolve the active `PaperContextProfile` for `declName` (defaulting to `BaseCC`). -/
def getEffectiveContextProfile (env : Environment) (declName : Name) : PaperContextProfile :=
  match getEffectiveContextProfileName? env declName with
  | some p => resolveProfile env p
  | none => resolveProfile env `BaseCC

initialize registerPP06ProfileCheckHook fun env declName =>
  (getEffectiveContextProfileName? env declName).isSome

/-! ## 3. Commands & Attributes (`paper_context`, `paper_context_for`, `@[paper_context]`) -/

declare_syntax_cat paperRoleEntry
syntax ident ":=" str ("," str)? : paperRoleEntry

declare_syntax_cat paperContextItem
syntax "(" &"carrier" ":=" str ("," str)? ")" : paperContextItem
syntax "(" &"defaultResource" ":=" str ("," str)? ")" : paperContextItem
syntax "(" &"role" paperRoleEntry ")" : paperContextItem

syntax (name := paperContextExtendCmd)
  "paper_context" ident "extends" ident paperContextItem* : command
syntax (name := paperContextUseCmd) "paper_context" ident : command
syntax (name := paperContextForCmd) "paper_context_for" ident ident : command

private def validateProfileExists (env : Environment) (name : Name) : CoreM Unit := do
  if (lookupRawProfile? env name).isNone then
    throwError "unknown context profile `{name}` (known built-ins: BaseCC, SchemeContext, ChannelContext, MPCContext, IndiffContext, GameBasedContext)"

initialize registerBuiltinAttribute {
  name := `paper_context
  descr := "Bind a declaration persistently to a ContextProfile for informalization"
  add := fun declName stx _ => do
    match stx with
    | `(attr| paper_context $prof:ident) =>
        let env ← getEnv
        validateProfileExists env prof.getId
        modifyEnv fun env => declContextExt.addEntry env (declName, prof.getId)
    | _ => throwError "unexpected `@[paper_context]` syntax"
}

elab_rules : command
  | `(paper_context $child:ident extends $parent:ident $items:paperContextItem*) => do
      let env ← getEnv
      liftCoreM <| validateProfileExists env parent.getId
      let mut carrier? : Option CountNoun := none
      let mut defRes? : Option CountNoun := none
      let mut roles : List (SemanticRole × CountNoun) := []
      for item in items do
        match item with
        | `(paperContextItem| (carrier := $sg:str $[, $pl:str]?)) =>
            let s := sg.getString
            carrier? := some ⟨s, (pl.map (·.getString)).getD (s ++ "s")⟩
        | `(paperContextItem| (defaultResource := $sg:str $[, $pl:str]?)) =>
            let s := sg.getString
            defRes? := some ⟨s, (pl.map (·.getString)).getD (s ++ "s")⟩
        | `(paperContextItem| (role $rId:ident := $sg:str $[, $pl:str]?)) =>
            let some role := SemanticRole.ofString? rId.getId.toString
              | throwError "unknown SemanticRole `{rId.getId}`"
            let s := sg.getString
            roles := roles ++ [(role, ⟨s, (pl.map (·.getString)).getD (s ++ "s")⟩)]
        | _ => throwError "unexpected paper_context item"
      let prof : PaperContextProfile := {
        name := child.getId
        parent? := some parent.getId
        carrierRoleNoun? := carrier?
        defaultResourceNoun? := defRes?
        roleNouns := roles
      }
      modifyEnv fun env => contextProfileExt.addEntry env (child.getId, prof)
  | `(paper_context $prof:ident) => do
      let env ← getEnv
      liftCoreM <| validateProfileExists env prof.getId
      Command.modifyScope fun s => { s with opts := paper.context.set s.opts prof.getId.toString }
  | `(paper_context_for $ns:ident $prof:ident) => do
      let env ← getEnv
      liftCoreM <| validateProfileExists env prof.getId
      modifyEnv fun env => nsContextExt.addEntry env (ns.getId, prof.getId)

/-! ## 4. Positional `SemanticRole` Inference + Semilattice Join (Layer 4) -/

private def addJoinedRole (roles : Std.HashMap FVarId SemanticRole) (fv : FVarId)
    (r : SemanticRole) : Std.HashMap FVarId SemanticRole :=
  match roles.get? fv with
  | some prev => roles.insert fv (prev.join r)
  | none => roles.insert fv r

private def collectExprFVarIds (e : Expr) : Array FVarId :=
  (Lean.collectFVars {} e).fvarIds

private def tagExprFVars (roles : Std.HashMap FVarId SemanticRole) (e : Expr)
    (r : SemanticRole) : Std.HashMap FVarId SemanticRole :=
  (collectExprFVarIds e).foldl (init := roles) fun acc fv => addJoinedRole acc fv r

private def argFromEnd? (args : Array Expr) (offset : Nat) : Option Expr :=
  if offset < args.size then args[args.size - 1 - offset]? else none

private partial def collectRolesInExpr (e : Expr)
    (roles : Std.HashMap FVarId SemanticRole) : MetaM (Std.HashMap FVarId SemanticRole) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  match e with
  | .forallE _ dom body _ =>
      let roles ← collectRolesInExpr dom roles
      if !body.hasLooseBVars then
        collectRolesInExpr body roles
      else
        return roles
  | .app .. =>
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      let mut acc := roles
      for a in args do
        acc ← collectRolesInExpr a acc
      if let .const head _ := fn then
        if head == constructsName && args.size ≥ 3 then
          if let some conv := argFromEnd? args 2 then
            acc := tagConverterExpr acc conv
          if let some src := argFromEnd? args 1 then
            acc := tagResourceTargetExpr acc src .realResource
          if let some tgt := argFromEnd? args 0 then
            acc := tagResourceTargetExpr acc tgt .idealResource
        else if head == constructsWithinName && args.size ≥ 4 then
          if let some conv := argFromEnd? args 3 then
            acc := tagConverterExpr acc conv
          if let some src := argFromEnd? args 2 then
            acc := tagResourceTargetExpr acc src .realResource
          if let some tgt := argFromEnd? args 1 then
            acc := tagResourceTargetExpr acc tgt .idealResource
          if let some err := argFromEnd? args 0 then
            acc := tagExprFVars acc err .errorBound
        else if head == substitutesWithinName && args.size ≥ 3 then
          if let some lhs := argFromEnd? args 2 then
            acc := tagResourceTargetExpr acc lhs .realResource
          if let some rhs := argFromEnd? args 1 then
            acc := tagResourceTargetExpr acc rhs .idealResource
          if let some err := argFromEnd? args 0 then
            acc := tagExprFVars acc err .errorBound
        else if (head == conditionallyEquivalentName || head == rsConditionallyEquivalentName) && args.size ≥ 2 then
          if let some g := argFromEnd? args 1 then
            acc := tagResourceTargetExpr acc g .realResource
          if let some t := argFromEnd? args 0 then
            acc := tagResourceTargetExpr acc t .idealResource
        else if head == rsGameEquivalentName && args.size ≥ 2 then
          if let some g := argFromEnd? args 1 then
            acc := tagResourceTargetExpr acc g .realResource
          if let some h := argFromEnd? args 0 then
            acc := tagResourceTargetExpr acc h .idealResource
      return acc
  | _ => return roles
where
  tagConverterExpr (acc : Std.HashMap FVarId SemanticRole) (conv : Expr) :
      Std.HashMap FVarId SemanticRole :=
    let c := conv.consumeMData
    let fn := c.getAppFn.consumeMData
    let args := c.getAppArgs
    if fn.isConstOf whiskerLeftName && args.size ≥ 5 then
      tagExprFVars acc args[args.size - 1]! .adversary
    else if fn.isConstOf whiskerRightName && args.size ≥ 5 then
      tagExprFVars acc args[args.size - 2]! .honestProtocol
    else
      tagExprFVars acc c .honestProtocol
  tagResourceTargetExpr (acc : Std.HashMap FVarId SemanticRole) (expr : Expr)
      (defaultRole : SemanticRole) : Std.HashMap FVarId SemanticRole := Id.run do
    let e := expr.consumeMData
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    if (fn.isConstOf simulatorImageName || fn.isConstOf starName) && args.size ≥ 2 then
      let acc := tagExprFVars acc args[args.size - 2]! .simulator
      return tagExprFVars acc args[args.size - 1]! .idealResource
    if (fn.isConstOf attachName || fn.isConstOf ``HSMul.hSMul) && args.size ≥ 2 then
      let lhs := args[args.size - 2]!
      let rhs := args[args.size - 1]!
      let acc := tagConverterExpr acc lhs
      return tagResourceTargetExpr acc rhs defaultRole
    if (fn.isConstOf parallelName || fn.isConstOf tensorObjName) && args.size ≥ 2 then
      let lhs := args[args.size - 2]!
      let rhs := args[args.size - 1]!
      let acc := tagResourceTargetExpr acc lhs defaultRole
      return tagResourceTargetExpr acc rhs defaultRole
    if fn.isConstOf ``Singleton.singleton then
      if let some inner := args.back? then
        return tagResourceTargetExpr acc inner defaultRole
    return tagExprFVars acc e defaultRole

/-- Infer joined positional `SemanticRole` for every free variable in `theoremType` (given
an optional pre-computed `forallTelescope`). `{.realResource, .idealResource} ↦ .hybridResource`. -/
def inferTheoremSemanticRoles (fvars : Array Expr) (conclusion : Expr) :
    MetaM (Std.HashMap FVarId SemanticRole) := do
  let mut roles : Std.HashMap FVarId SemanticRole := {}
  for fv in fvars do
    let decl ← fv.fvarId!.getDecl
    if ← isProp decl.type then
      roles ← collectRolesInExpr decl.type roles
    else if (← distinguisherInterface? decl.type).isSome then
      roles := addJoinedRole roles fv.fvarId! .distinguisher
  roles ← collectRolesInExpr conclusion roles
  return roles

/-! ## 5. Normalized Kernel Role-Override Metadata & Collision-Safe Field Unpacking -/

/-- Check if structure projections / fields of `fv` (for `head`) are actually referenced inside
`exprs`, and return the referenced field names in declaration order. -/
def usedStructFieldsForBinder (env : Environment) (structHead : Name) (allowedFields : Array String)
    (fvId : FVarId) (exprs : Array Expr) : Array String := Id.run do
  let some sinfo := Lean.getStructureInfo? env structHead | return #[]
  let mut usedSet : Std.HashSet String := {}
  let rec visit : Expr → Std.HashSet String → Std.HashSet String
    | .mdata _ inner, s => visit inner s
    | .proj sName idx inner, s =>
        let s := visit inner s
        if sName == structHead && inner.consumeMData == .fvar fvId then
          if h : idx < sinfo.fieldNames.size then
            let fn := sinfo.fieldNames[idx].toString
            if allowedFields.contains fn then s.insert fn else s
          else s
        else s
    | .app fn a, s =>
        let s := visit fn s
        let s := visit a s
        match (Expr.app fn a).getAppFn.consumeMData with
        | .const projName _ =>
            match env.getProjectionFnInfo? projName with
            | some pinfo =>
                let args := (Expr.app fn a).getAppArgs
                if pinfo.numParams < args.size &&
                   args[pinfo.numParams]!.consumeMData == .fvar fvId then
                  let short := match projName.eraseMacroScopes with
                    | .str _ s => s
                    | other => other.toString
                  if allowedFields.contains short then s.insert short else s
                else s
            | none => s
        | _ => s
    | .lam _ d b _, s => visit b (visit d s)
    | .forallE _ d b _, s => visit b (visit d s)
    | .letE _ t v b _, s => visit b (visit v (visit t s))
    | _, s => s
  for e in exprs do
    usedSet := visit e usedSet
  return allowedFields.filter (usedSet.contains ·)

/-- Result of 5-level context resolution for a single binder type. -/
structure ResolvedBinderPresentation where
  noun : CountNoun
  accessories : List String := []
  deriving Inhabited, Repr

/-- 5-Level Anti-Clobbering Type Description Resolution (`Bug 9A–9D`).
Takes baseline `(baseNoun, baseAccessories, isAmbient, isWitness)` and resolves strictly:
1. Level 1: explicit `@[paper_role]` or `With role`
2. Level 2: concrete non-carrier `PaperDescribeRule` (`carrier := false`) — beats ContextProfile & positional role!
3. Level 3: `@[interface_resource_noun]` / explicit `Overlay.noun?` (on type head or CC interface)
4. Level 4: joined positional `SemanticRole` (`{.realResource, .idealResource} ↦ .hybridResource`)
5. Level 5: inherited `ContextProfile` generic carrier / resource default. -/
def resolveDescription5Level (profile : PaperContextProfile)
    (fv : Expr) (ty : Expr)
    (baseNoun : CountNoun) (baseAccessories : List String)
    (isAmbient isWitness : Bool)
    (role? : Option SemanticRole) (explicitRole? : Option String)
    (allBinders : Array (FVarId × Expr)) (visibleExprs : Array Expr) :
    MetaM ResolvedBinderPresentation := do
  if isAmbient || isWitness then
    return { noun := baseNoun, accessories := baseAccessories }
  let env ← getEnv
  let tyClean ← normalizeForPresentation ty
  let tyHead? := match tyClean.getAppFn.consumeMData with
    | .const head _ => some head
    | _ => none
  -- Level 1: explicit `@[paper_role]` or `With role`
  let l1Role? := explicitRole? <|> tyHead?.bind fun h => (getMathPresentation env h).paperRole?
  if let some rStr := l1Role? then
    if let some sr := SemanticRole.ofString? rStr then
      if let some noun := profile.lookupRoleNoun? sr then
        return { noun, accessories := baseAccessories }
    let artNoun : CountNoun := ⟨rStr, rStr ++ "s"⟩
    return { noun := artNoun, accessories := baseAccessories }
  -- Level 2: concrete non-carrier `PaperDescribeRule` (`carrier := false`)
  if let some head := tyHead? then
    if let some rule := getPaperDescribeRule? env head then
      if !rule.isGenericCarrier then
        let mut accs := baseAccessories
        -- Conditional, collision-safe field unpacking (`Bug 9D`)
        if !rule.unpackFields.isEmpty then
          let usedFields := usedStructFieldsForBinder env head rule.unpackFields fv.fvarId! visibleExprs
          if !usedFields.isEmpty then
            let sameHeadCount : Nat := allBinders.foldl (init := 0) fun c (_, bty) =>
              match bty.getAppFn.consumeMData with
              | .const bh _ => if bh == head then c + 1 else c
              | _ => c
            if sameHeadCount ≤ 1 then
              let fieldMath := usedFields.toList.map fun f =>
                s!"\\(\\mathrm\{{escapeLatex f}}\\)"
              if accs.any (·.startsWith "with ") then
                accs := accs.map fun a =>
                  if a.startsWith "with " then s!"{a} (with components {joinAnd fieldMath})"
                  else a
              else
                accs := accs ++ [s!"with components {joinAnd fieldMath}"]
        return { noun := rule.noun, accessories := accs }
  -- Level 3: explicit `@[interface_resource_noun]` or `Overlay.noun?` on head or CC interface
  if let some head := tyHead? then
    if let some (sg, pl) := (getOverlay env head).noun? <|> (getMathPresentation env head).interfaceResourceNoun? then
      return { noun := ⟨sg, pl⟩, accessories := baseAccessories }
  if let some iface ← resourceInterface? tyClean then
    if let .const ifaceHead _ := iface.getAppFn.consumeMData then
      if let some (sg, pl) := (getOverlay env ifaceHead).noun? <|>
          (getMathPresentation env ifaceHead).interfaceResourceNoun? then
        return { noun := ⟨sg, pl⟩, accessories := baseAccessories }
  -- Level 4: joined positional `SemanticRole` (type-compatible gate!)
  let isRes := (← resourceInterface? tyClean).isSome || (← gameInterface? tyClean).isSome
  let isConv := (← converterInterfaces? tyClean).isSome || tyClean.isAppOf endoFamilyName
  let isDist := (← distinguisherInterface? tyClean).isSome
  let isGenericCarrier := match tyHead? with
    | some h => (getPaperDescribeRule? env h).any (·.isGenericCarrier)
    | none => tyClean.isSort
  if let some role := role? then
    let compatible := match role with
      | .realResource | .idealResource | .hybridResource | .assumedResource =>
          isRes || isGenericCarrier
      | .honestProtocol | .simulator | .adversary | .schemeUnderTest =>
          isConv || isRes || isGenericCarrier
      | .distinguisher => isDist || isGenericCarrier
      | .underlyingPrimitive | .leakage => isRes || isConv || isGenericCarrier
      | .errorBound | .genericParameter => false
    if compatible then
      if let some noun := profile.lookupRoleNoun? role then
        return { noun, accessories := baseAccessories }
  -- Level 5: inherited `ContextProfile` generic/resource default
  if isRes then
    if let some noun := profile.defaultResourceNoun? then
      if baseNoun.singular == "resource" then
        return { noun, accessories := baseAccessories }
  if isGenericCarrier then
    if let some noun := profile.carrierRoleNoun? then
      return { noun := noun, accessories := baseAccessories }
  return { noun := baseNoun, accessories := baseAccessories }

/-- Intercept declarations elaborated under `paper_context P` and stamp `declContextExt`
persistently so `.olean` CLI builds match live Infoview rendering (`Bug 9D` persistence).
Must sit last in this module so it is never evaluated inside its own defining module. -/
@[command_elab Lean.Parser.Command.declaration]
def elabDeclWithPaperContext : CommandElab := fun stx => do
  let profStr := paper.context.get (← getOptions)
  if profStr.isEmpty then
    throwUnsupportedSyntax
  let profName := profStr.toName
  let envBefore ← getEnv
  Lean.Elab.Command.elabDeclaration stx
  let envAfter ← getEnv
  let isSkipAux (n : Name) : Bool :=
    let s := n.toString
    Lean.isPrivateName n || envAfter.isProjectionFn n || envAfter.isConstructor n ||
    (s.splitOn "._").length > 1 || (s.splitOn ".match_").length > 1
  for (d, _) in envAfter.constants.map₂.toList do
    if !envBefore.constants.contains d && !isSkipAux d then
      modifyEnv fun env => declContextExt.addEntry env (d, profName)

end Informalization.Core.ContextProfile
