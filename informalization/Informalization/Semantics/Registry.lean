/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Semantics.IR
import Informalization.Semantics.LanguageDesign

/-!
# Declaration semantics registry

Semantic adapters register stable, fully qualified Lean declarations here.
The payload is a typed role plus a map from elaborated arguments to their
mathematical roles.  It contains no final prose and never inspects local
variable names.
-/

namespace Informalization.Semantics.Registry

open Lean Meta Elab Command
open Informalization.Semantics
open CryptoLanguage.LanguageDesign

/-- How to recover one argument from an elaborated declaration application.

`application` counts every term argument, including implicit parameters and
typeclass instances.  `explicit` counts only explicit binders in the
declaration's type.  `parameter` addresses the declaration telescope directly
and is independent of binder spelling.  `binder` is retained for adapters
whose source API exposes stable parameter names.  `result` denotes the
inferred type of the whole expression. -/
inductive ArgumentSelector where
  | application (index : Nat)
  | explicit (index : Nat)
  | parameter (index : Nat)
  | binder (name : Name)
  | result
  deriving Inhabited, BEq, Repr

/-- A declaration-level map from a Lean argument to a semantic argument. -/
structure ArgumentBinding where
  selector : ArgumentSelector
  role : ArgumentRole
  /-- Stable, domain-semantic name of this operand or proof obligation.

  The slot is data for canonical decoders, not display prose.  In particular,
  it lets two declarations with different binder names expose the same proof
  obligation (for example, `sourceNonnegative` or `equalWeight`). -/
  slot? : Option Name := none
  salience : Salience := .primary
  deriving Inhabited, BEq, Repr

/-- A declaration role may be valid only when one selected operand has a
domain carrier at its type head.  This is semantic admission data, not a
pretty-printer heuristic. -/
structure ArgumentTypeConstraint where
  role : ArgumentRole
  allowedTypeHeads : Array Name
  deriving Inhabited, BEq, Repr

/-- Typed metadata associated with one fully qualified Lean declaration. -/
structure Entry where
  declaration : Name
  role : NodeRole
  arguments : Array ArgumentBinding := #[]
  argumentTypeConstraints : Array ArgumentTypeConstraint := #[]
  /-- Whether the checked body of this registered proof rule is part of its
  public semantic explanation.  Expansion is declaration metadata, not a
  theorem-name or tactic heuristic. -/
  expandProof : Bool := false
  /-- Whether this rule is semantic only inside an explicitly expanded public
  proof.  This prevents a generic closure lemma from changing unrelated
  top-level discourse while still exposing its role in an opted-in argument. -/
  expansionOnly : Bool := false
  deriving Inhabited, BEq, Repr

/-- A binding together with the exact checked argument selected from one
declaration application.  Unlike `SemanticArgument`, this view retains the
registry's stable slot name for canonical rule decoders. -/
structure ResolvedBinding where
  binding : ArgumentBinding
  argument : SemanticArgument
  deriving Inhabited, BEq, Repr

/-- Find a stable semantic slot in one declaration schema. -/
def Entry.bindingForSlot? (entry : Entry) (slot : Name) : Option ArgumentBinding :=
  entry.arguments.find? (·.slot? == some slot)

/-- Recover the stable slot attached to one semantic argument role.  Premise
roles include their ordinal, so this is the bridge from a planned premise to
the declaration schema that named its mathematical obligation. -/
def Entry.slotForRole? (entry : Entry) (role : ArgumentRole) : Option Name := do
  let binding ← entry.arguments.find? (·.role == role)
  binding.slot?

/-- Named slots are keys within a declaration schema. -/
def Entry.hasUniqueSlots (entry : Entry) : Bool :=
  entry.arguments.all fun binding =>
    match binding.slot? with
    | none => true
    | some slot => (entry.arguments.filter (·.slot? == some slot)).size == 1

/-- A profile-owned collection of declaration semantics.  Catalogs cross the
external-workspace boundary explicitly; environment entries remain available
for source modules that import and register their own semantics. -/
abbrev Catalog := Array Entry

initialize entries : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `Informalization.Semantics.Registry.entries
    addImportedFn := fun imported => imported.flatten
    addEntryFn := fun state entry => state.push entry
  }

/-- All declaration semantics visible in an elaborated environment. -/
def all (environment : Environment) : Array Entry :=
  SimplePersistentEnvExtension.getState entries environment

/-- Look up semantic metadata by a fully qualified declaration name. -/
def lookup? (environment : Environment) (declaration : Name) : Option Entry :=
  (all environment).find? (·.declaration == declaration)

/-- Look up a declaration in an explicit profile catalog. -/
def lookupCatalog? (catalog : Catalog) (declaration : Name) : Option Entry :=
  catalog.find? (·.declaration == declaration)

/-- Look up a declaration with profile-owned semantics taking precedence over
entries carried by the elaborated source environment. -/
def lookupWith? (environment : Environment) (catalog : Catalog)
    (declaration : Name) : Option Entry :=
  lookupCatalog? catalog declaration <|> lookup? environment declaration

/-- Whether a catalog assigns at most one role to each declaration. -/
def Catalog.hasUniqueDeclarations (catalog : Catalog) : Bool :=
  catalog.all fun entry =>
    (catalog.filter (·.declaration == entry.declaration)).size == 1

/-- Static catalog validation failures in a target elaboration environment. -/
inductive ValidationIssue where
  | duplicateDeclaration (declaration : Name)
  | duplicateSlot (declaration : Name) (slot : Name)
  | missingDeclaration (declaration : Name)
  | invalidSelector (declaration : Name) (selector : ArgumentSelector)
  | missingSourceAttestation (declaration : Name) (rule : RuleId)
  deriving Inhabited, BEq, Repr

private partial def declarationBinders (type : Expr) : Array (Name × BinderInfo) :=
  match type.consumeMData with
  | .forallE name _ body info => #[(name, info)] ++ declarationBinders body
  | _ => #[]

private def selectorValid (binders : Array (Name × BinderInfo)) : ArgumentSelector → Bool
  | .application index | .parameter index => index < binders.size
  | .explicit index => index < (binders.filter (·.2.isExplicit)).size
  | .binder name => binders.any (·.1 == name)
  | .result => true

/-- Resolve exact declaration-scoped authority for public domain prose.
Semantic registration and linguistic licensing are deliberately separate: a
checked-library entry may be useful to the proof graph without licensing an
English gloss. -/
def publicLanguageLicenseFor? (declaration : Name)
    (role : ProofRuleRole) : Option CryptoLanguage.LanguageDesign.Corpus.Attestation := do
  let attestation ←
    CryptoLanguage.LanguageDesign.Corpus.exactAttestationForDeclaration?
      declaration
      (Informalization.Semantics.LanguageDesign.proofRuleRole role)
  guard attestation.isPubliclyLicensed
  return attestation

/-- Resolve a public prose license for one occurrence inside a selected theorem.
Application-scoped evidence is checked before declaration-global evidence; in
both cases the exact proof declaration and semantic role remain mandatory. -/
def publicLanguageLicenseForOccurrence? (root? : Option Name)
    (declaration : Name) (role : ProofRuleRole) :
    Option CryptoLanguage.LanguageDesign.Corpus.Attestation :=
  let rule := Informalization.Semantics.LanguageDesign.proofRuleRole role
  let application? := root?.bind fun root =>
    CryptoLanguage.LanguageDesign.Corpus.informalizationApplicationAttestationFor?
      root declaration rule
  match application? with
  | some attestation => if attestation.isPubliclyLicensed then some attestation else none
  | none => publicLanguageLicenseFor? declaration role

/-- Validate declaration existence, selectors, and semantic provenance against
the target project's current signatures.  This does not grant a prose
license; realization separately requires `publicLanguageLicenseFor?`. -/
def validateCatalog (environment : Environment) (catalog : Catalog) :
    Array ValidationIssue := Id.run do
  let mut issues := #[]
  for entry in catalog do
    if let .proofRule role := entry.role then
      let rule := Informalization.Semantics.LanguageDesign.proofRuleRole role
      unless CryptoLanguage.LanguageDesign.Corpus.attestationForDeclaration?
          entry.declaration rule |>.any
          (·.isValid) do
        issues := issues.push (.missingSourceAttestation entry.declaration rule)
    if (catalog.filter (·.declaration == entry.declaration)).size != 1 then
      unless issues.contains (.duplicateDeclaration entry.declaration) do
        issues := issues.push (.duplicateDeclaration entry.declaration)
    for argument in entry.arguments do
      if let some slot := argument.slot? then
        if (entry.arguments.filter (·.slot? == some slot)).size != 1 then
          unless issues.contains (.duplicateSlot entry.declaration slot) do
            issues := issues.push (.duplicateSlot entry.declaration slot)
    let some information := environment.find? entry.declaration
      | issues := issues.push (.missingDeclaration entry.declaration); continue
    let binders := declarationBinders information.type
    for argument in entry.arguments do
      unless selectorValid binders argument.selector do
        issues := issues.push (.invalidSelector entry.declaration argument.selector)
  return issues

/-- Register typed declaration semantics in the current module.

Adapters normally call this from `run_cmd`.  Duplicate registrations are
rejected so import order cannot silently change a declaration's meaning. -/
def register (entry : Entry) : CommandElabM Unit := do
  let environment ← getEnv
  if (lookup? environment entry.declaration).isSome then
    throwError "semantic role already registered for {entry.declaration}"
  unless entry.hasUniqueSlots do
    throwError "semantic slots are not unique for {entry.declaration}"
  modifyEnv fun environment => entries.addEntry environment entry

/-- The head constant of an elaborated application, ignoring metadata. -/
def headDeclaration? (expression : Expr) : Option Name :=
  match expression.consumeMData.getAppFn.consumeMData with
  | .const declaration _ => some declaration
  | _ => none

/-- The value carried by an elaborated subtype projection.  This is the
kernel form used both by `.1` and by coercion from a subtype to its carrier. -/
private def subtypeValue? (expression : Expr) : Option Expr := do
  guard (headDeclaration? expression == some ``Subtype.val)
  expression.consumeMData.getAppArgs.back?

/-- Match a registered constructor without unfolding it.  The only wrapper
crossed here is the proof-erasing `Subtype.val` projection, and it is crossed
only when its payload is itself headed by a registered declaration.  Thus a
value such as `(PDS.adjoin S A).1` retains the `adjoin` constructor and its
operands instead of reducing to its implementation. -/
partial def matchExpressionWith? (environment : Environment) (catalog : Catalog)
    (expression : Expr) (remainingProjections : Nat := 4) :
    Option (Entry × Expr) :=
  if let some declaration := headDeclaration? expression then
    if let some entry := lookupWith? environment catalog declaration then
      some (entry, expression)
    else if remainingProjections == 0 then none
    else do
      let value ← subtypeValue? expression
      matchExpressionWith? environment catalog value (remainingProjections - 1)
  else none

/-- Look up an expression by its head declaration.  Local argument names are
therefore irrelevant to semantic classification. -/
def lookupExpression? (environment : Environment) (expression : Expr) : Option Entry := do
  return (← matchExpressionWith? environment #[] expression).1

/-- Expression lookup across an explicit profile catalog and the source
environment. -/
def lookupExpressionWith? (environment : Environment) (catalog : Catalog)
    (expression : Expr) : Option Entry := do
  return (← matchExpressionWith? environment catalog expression).1

private partial def collectExplicitArguments (type : Expr) (arguments : Array Expr)
    (index : Nat) (result : Array Expr) : MetaM (Array Expr) := do
  if index == arguments.size then return result
  let type ← whnf type
  match type with
  | .forallE _ _ body binderInfo =>
      let argument := arguments[index]!
      let result := if binderInfo.isExplicit then result.push argument else result
      collectExplicitArguments (body.instantiate1 argument) arguments (index + 1) result
  | _ => return result

private partial def findBinderArgument? (type : Expr) (arguments : Array Expr)
    (target : Name) (index : Nat := 0) : MetaM (Option Expr) := do
  if index == arguments.size then return none
  let type ← whnf type
  match type with
  | .forallE name _ body _ =>
      let argument := arguments[index]!
      if name == target then return some argument
      findBinderArgument? (body.instantiate1 argument) arguments target (index + 1)
  | _ => return none

/-- Explicit arguments of an elaborated application, omitting inferred type
parameters and instance dictionaries according to the declaration's type. -/
def explicitArguments (expression : Expr) : MetaM (Array Expr) := do
  let expression ← instantiateMVars expression
  let function := expression.getAppFn.consumeMData
  collectExplicitArguments (← inferType function) expression.getAppArgs 0 #[]

private def resolveArgument (expression : Expr) (selector : ArgumentSelector) :
    MetaM Expr := do
  match selector with
  | .application index =>
      let arguments := expression.getAppArgs
      let some argument := arguments[index]?
        | throwError "semantic application-argument index {index} is out of bounds"
      return argument
  | .explicit index =>
      let arguments ← explicitArguments expression
      let some argument := arguments[index]?
        | throwError "semantic explicit-argument index {index} is out of bounds"
      return argument
  | .parameter index =>
      let arguments := expression.getAppArgs
      let some argument := arguments[index]?
        | throwError "semantic declaration-parameter index {index} is out of bounds"
      return argument
  | .binder name =>
      let function := expression.getAppFn.consumeMData
      let some argument ← findBinderArgument? (← inferType function)
          expression.getAppArgs name
        | throwError "semantic binder {name} is absent from this application"
      return argument
  | .result => inferType expression

private def recoverBindings (entry : Entry) (expression : Expr) :
    MetaM (Array ResolvedBinding) := do
  let mut result := #[]
  for binding in entry.arguments do
    let source ← resolveArgument expression binding.selector
    result := result.push {
      binding
      argument := {
        role := binding.role
        source
        provenance := {
          expression := source
          declaration? := some entry.declaration
          evidenceKind := .application
        }
        salience := binding.salience
      }
    }
  return result

/-- Resolve a declaration schema against one elaborated application while
retaining stable operand and obligation slots. -/
def resolveBindings (entry : Entry) (expression : Expr) :
    MetaM (Array ResolvedBinding) :=
  recoverBindings entry expression

private def instantiateFrom (entry : Entry) (application source : Expr) : MetaM Node := do
  let application ← instantiateMVars application
  let source ← instantiateMVars source
  let arguments := (← recoverBindings entry application).map (·.argument)
  for constraint in entry.argumentTypeConstraints do
    let some argument := arguments.find? (·.role == constraint.role)
      | throwError "registered semantic type constraint names a missing argument role"
    let argumentType ← instantiateMVars (← inferType argument.source)
    let head? := argumentType.consumeMData.getAppFn.consumeMData.constName?
    unless head?.any constraint.allowedTypeHeads.contains do
      throwError m!"the `{repr constraint.role}` operand has carrier {argumentType}, outside the declaration's registered semantic domain"
  let evidenceKind := match entry.role with
    | .entity _ => EvidenceKind.declaration
    | .proposition _ => .proposition
    | .proofRule _ => .proofTerm
    | _ => .application
  let provenance : Provenance := {
    expression := source
    declaration? := some entry.declaration
    evidenceKind
  }
  match entry.role with
  | .entity role =>
      return .entity { role, source, provenance }
  | .system role =>
      return .system { role, source, arguments, provenance }
  | .game role =>
      return .game { role, source, arguments, provenance }
  | .converter role =>
      return .converter { role, source, arguments, provenance }
  | .quantity role =>
      return .quantity { role, source, arguments, provenance }
  | .proposition role =>
      return .proposition { role, source, arguments, provenance }
  | .proofRule role =>
      return .proofApplication {
        role
        source
        conclusion := ← inferType source
        arguments
        provenance
      }

/-- Instantiate registered declaration metadata at one checked Lean
expression, producing a typed semantic node with source provenance. -/
def instantiate (entry : Entry) (expression : Expr) : MetaM Node :=
  instantiateFrom entry expression expression

/-- Recover a semantic node when the expression's head declaration is
registered. -/
def recover? (environment : Environment) (expression : Expr) : MetaM (Option Node) := do
  let some (entry, application) := matchExpressionWith? environment #[] expression
    | return none
  try
    return some (← instantiateFrom entry application expression)
  catch _ =>
    return none

/-- Recover semantics using a profile catalog even when the separately
elaborated source module did not import the adapter that owns that catalog. -/
def recoverWith? (environment : Environment) (catalog : Catalog) (expression : Expr) :
    MetaM (Option Node) := do
  let some (entry, application) := matchExpressionWith? environment catalog expression
    | return none
  try
    return some (← instantiateFrom entry application expression)
  catch _ =>
    return none

private structure GraphState where
  nodes : Array Node := #[]
  edges : Array Edge := #[]

private def existingNode? (state : GraphState) (expression : Expr) : Option NodeId := do
  let index ← state.nodes.findIdx? (·.provenance.expression == expression)
  return { index }

private partial def recoverGraphNodeWith? (environment : Environment) (catalog : Catalog)
    (expression : Expr) (remainingDepth : Nat) (state : GraphState) :
    MetaM (Option NodeId × GraphState) := do
  if let some existing := existingNode? state expression then
    return (some existing, state)
  if remainingDepth == 0 then return (none, state)
  let some node ← recoverWith? environment catalog expression | return (none, state)
  let parent : NodeId := { index := state.nodes.size }
  let mut state := { state with nodes := state.nodes.push node }
  for argument in node.arguments do
    let (child?, nextState) ← recoverGraphNodeWith? environment catalog argument.source
      (remainingDepth - 1) state
    state := nextState
    if let some child := child? then
      state := { state with edges := state.edges.push { parent, child, argument } }
  return (some parent, state)

/-- Recover a compositional graph from a profile catalog and target project
environment.  Unknown or stale child registrations remain exact raw
arguments instead of aborting the whole root. -/
def recoverGraphWith? (environment : Environment) (catalog : Catalog) (expression : Expr)
    (maximumDepth : Nat := 64) : MetaM (Option Graph) := do
  let (root?, state) ← recoverGraphNodeWith? environment catalog expression maximumDepth {}
  let some root := root? | return none
  return some { root, nodes := state.nodes, edges := state.edges }

/-- Environment-only compositional recovery. -/
def recoverGraph? (environment : Environment) (expression : Expr)
    (maximumDepth : Nat := 64) : MetaM (Option Graph) :=
  recoverGraphWith? environment #[] expression maximumDepth

end Informalization.Semantics.Registry
