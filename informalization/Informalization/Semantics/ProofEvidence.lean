/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.Registry

/-!
# Checked proof evidence for semantic planning

This module reads the kernel value of a declaration and finds fully applied
constants registered as proof rules.  Classification depends only on the
constant's fully qualified declaration and typed registry entry.  Tactic
syntax and local user names are not inputs.

Every proof-valued argument of a registered rule is retained recursively.  A
region that is not itself a registered rule remains an exact `fallback` node,
so semantic planning can never silently discard an unclassified proof term.

Three deliberately bounded forms of checked indirection are followed:

* a proof-valued local `let`/`have` variable is followed to its local value;
* a registered rule with no registered premise interface, or one whose
  registry entry explicitly enables expansion, is treated as a semantic
  macro, and its instantiated checked body is inspected for registered child
  rules;
* while such an explicitly expanded public rule is open, fully applied proof
  helpers are traversed transparently and retained only when their checked
  bodies reach registered semantic rules.

Transparent helper traversal never assigns a role to the helper declaration
itself.  This exposes checked structure below private or refactored helpers
without depending on their names, while the explicit public-rule expansion
boundary prevents arbitrary library implementation details from being opened.
-/

namespace Informalization.Semantics.ProofEvidence

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Registry

/-- Exact checked material shared by classified and fallback evidence nodes. -/
structure Payload where
  proof : Expr
  expected : Expr
  localContext : LocalContext
  deriving Inhabited

/-- One instantiated binder of a constant application. -/
structure AppliedArgument where
  position : Nat
  explicitPosition? : Option Nat
  binderName : Name
  binderInfo : BinderInfo
  value : Expr
  instantiatedType : Expr
  isProof : Bool
  deriving Inhabited, BEq, Repr

/-- A constant application together with its instantiated declaration
telescope. `fullyApplied` means no declaration binder remains after consuming
the application arguments. -/
structure AppliedConstant where
  declaration : Name
  application : Expr
  arguments : Array AppliedArgument
  resultType : Expr
  fullyApplied : Bool
  deriving Inhabited, BEq, Repr

/-- The semantic identity of a proof-valued argument.  Registered premise
metadata takes precedence; otherwise `premise position` is assigned from the
declaration telescope, never from a local hypothesis name. -/
structure PremiseDescriptor where
  position : Nat
  role : ArgumentRole
  salience : Salience
  proposition : Expr
  deriving Inhabited, BEq, Repr

mutual
  /-- A recursively retained checked proof region. -/
  inductive Tree where
    | rule
        (payload : Payload)
        (application : ProofApplication)
        (semanticGraph : Graph)
        (premises : Array Premise)
        (macroExpansion? : Option Tree)
    | fallback (payload : Payload) (children : Array Tree)
    deriving Inhabited

  /-- One proof-valued argument and the evidence that proves it. -/
  structure Premise where
    descriptor : PremiseDescriptor
    evidence : Tree
    deriving Inhabited
end

/-- Evidence recovered for one named declaration. -/
structure DeclarationEvidence where
  name : Name
  theoremType : Expr
  evidence : Tree
  deriving Inhabited

namespace Tree

/-- Exact evidence payload at this tree node. -/
def payload : Tree → Payload
  | .rule payload .. | .fallback payload .. => payload

/-- Direct evidence children, including the proof of every premise. -/
def children : Tree → Array Tree
  | .rule _ _ _ premises expansion? =>
      expansion?.elim (premises.map (·.evidence)) fun expansion =>
        (premises.map (·.evidence)).push expansion
  | .fallback _ children => children

/-- Whether at least one region remains on the checked fallback path. -/
partial def hasFallback : Tree → Bool
  | .fallback _ _ => true
  | .rule _ _ _ premises expansion? =>
      premises.any (hasFallback ·.evidence) ||
        expansion?.any hasFallback

/-- Number of registered proof-rule applications in the evidence tree. -/
partial def ruleCount : Tree → Nat
  | .rule _ _ _ premises expansion? =>
      1 + premises.foldl
        (fun (count : Nat) (premise : Premise) => count + ruleCount premise.evidence) 0 +
        (expansion?.map ruleCount |>.getD 0)
  | .fallback _ children =>
      children.foldl (fun count child => count + ruleCount child) 0

end Tree

private structure TelescopeState where
  arguments : Array AppliedArgument := #[]
  resultType : Expr
  explicitCount : Nat := 0
  consumed : Nat := 0

private partial def consumeApplicationArguments (type : Expr) (values : Array Expr)
    (position explicitCount : Nat) (result : Array AppliedArgument) :
    MetaM TelescopeState := do
  if position == values.size then
    return {
      arguments := result
      resultType := type
      explicitCount
      consumed := position
    }
  let type ← whnf type
  match type with
  | .forallE binderName domain body binderInfo =>
      let value := values[position]!
      let explicitPosition? :=
        if binderInfo.isExplicit then some explicitCount else none
      let isProof ← isProp domain
      let argument : AppliedArgument := {
        position
        explicitPosition?
        binderName
        binderInfo
        value
        instantiatedType := domain
        isProof
      }
      consumeApplicationArguments (body.instantiate1 value) values (position + 1)
        (if binderInfo.isExplicit then explicitCount + 1 else explicitCount)
        (result.push argument)
  | _ =>
      return {
        arguments := result
        resultType := type
        explicitCount
        consumed := position
      }

/-- Recover a constant application's instantiated telescope. -/
def appliedConstant? (expression : Expr) : MetaM (Option AppliedConstant) := do
  let expression ← instantiateMVars expression
  let function := expression.getAppFn.consumeMData
  let .const declaration _ := function | return none
  let state ← consumeApplicationArguments (← inferType function)
    expression.getAppArgs 0 0 #[]
  -- Do not weak-head normalize the conclusion here.  A fully applied theorem
  -- can return a proposition whose *definition* unfolds to a `forall` (for
  -- example conditional equivalence).  Full application is a property of the
  -- declaration telescope, not of the reducible shape of its result.
  let resultType := state.resultType.consumeMData
  let fullyApplied := state.consumed == expression.getAppArgs.size &&
    !resultType.isForall
  return some {
    declaration
    application := expression
    arguments := state.arguments
    resultType
    fullyApplied
  }

private def selectorMatches (argument : AppliedArgument) : ArgumentSelector → Bool
  | .application index | .parameter index => argument.position == index
  | .explicit index => argument.explicitPosition? == some index
  | .binder name => argument.binderName == name
  | .result => false

private def registeredPremiseBinding? (entry : Entry)
    (argument : AppliedArgument) : Option ArgumentBinding :=
  entry.arguments.find? fun binding =>
    selectorMatches argument binding.selector &&
      match binding.role with
      | .premise _ => true
      | _ => false

private def premiseDescriptor (entry? : Option Entry) (argument : AppliedArgument)
    (proofOrdinal : Nat) : PremiseDescriptor :=
  match entry?.bind (registeredPremiseBinding? · argument) with
  | some binding => {
      position := argument.position
      role := binding.role
      salience := binding.salience
      proposition := argument.instantiatedType
    }
  | none => {
      position := argument.position
      role := .premise proofOrdinal
      salience := if argument.binderInfo.isExplicit then .supporting else .implicit
      proposition := argument.instantiatedType
    }

private def hasRegisteredPremiseInterface (entry : Entry) : Bool :=
  entry.arguments.any fun binding =>
    match binding.role with
    | .premise _ => true
    | _ => false

private def instantiatedDeclarationValue? (application : AppliedConstant) : MetaM (Option Expr) := do
  let information ← getConstInfo application.declaration
  let some value := information.value? (allowOpaque := true) | return none
  let levels := application.application.getAppFn.constLevels!
  let value := value.instantiateLevelParams information.levelParams levels
  return some (value.beta (application.arguments.map (·.value)))

/-- Contract only consecutive beta-redexes at the head of a proof term.

Elaborated tactic proofs can introduce several nested immediate lambda
applications around the theorem that carries the mathematical step.  One
`Expr.headBeta` call need not cross all of them.  The small fuel bound keeps
this normalization local and deterministic; no declaration is unfolded. -/
private partial def contractHeadBeta (expression : Expr)
    (remaining : Nat := 64) : Expr :=
  if remaining == 0 then expression
  else
    let reduced := match expression.getAppFn.consumeMData with
      | function@(.lam ..) => function.beta expression.getAppArgs
      | _ => expression.headBeta
    if reduced == expression then expression
    else contractHeadBeta reduced (remaining - 1)

private partial def extractAux (environment : Environment) (catalog : Catalog)
    (proof expected : Expr) (remainingDepth remainingMacroDepth remainingHelperDepth : Nat)
    (followHelperBodies : Bool) (helperModule? : Option ModuleIdx)
    (activeLocalDefinitions : Array FVarId)
    (activeExpandedDeclarations : Array Name) : MetaM Tree := do
  -- Tactic elaboration frequently leaves a theorem application beneath an
  -- immediately applied lambda (for example after `apply`, `simpa`, or a
  -- locally elaborated helper).  This is definitional structure, not a proof
  -- boundary.  Contract only the beta-redex at the head so registered
  -- descendants remain discoverable without unfolding arbitrary constants.
  let proof := contractHeadBeta (← instantiateMVars proof)
  let expected ← instantiateMVars expected
  let payload : Payload := { proof, expected, localContext := ← getLCtx }
  if remainingDepth == 0 then return .fallback payload #[]

  match proof.consumeMData with
  | .lam binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun localVar => do
        let bodyProof := body.instantiate1 localVar
        let expectedBody ←
          match (← whnf expected) with
          | .forallE _ _ body _ => pure (body.instantiate1 localVar)
          | _ => inferType bodyProof
        let child ← extractAux environment catalog bodyProof expectedBody
          (remainingDepth - 1) remainingMacroDepth remainingHelperDepth followHelperBodies
          helperModule? activeLocalDefinitions activeExpandedDeclarations
        return .fallback payload #[child]
  | .letE binderName type value body _ =>
      withLetDecl binderName type value fun localVar => do
        let bodyProof := body.instantiate1 localVar
        let child ← extractAux environment catalog bodyProof expected
          (remainingDepth - 1) remainingMacroDepth remainingHelperDepth followHelperBodies
          helperModule? activeLocalDefinitions activeExpandedDeclarations
        return .fallback payload #[child]
  | .mdata _ inner =>
      let child ← extractAux environment catalog inner expected
        (remainingDepth - 1) remainingMacroDepth remainingHelperDepth followHelperBodies
        helperModule? activeLocalDefinitions activeExpandedDeclarations
      return .fallback payload #[child]
  | .fvar fvarId =>
      if activeLocalDefinitions.contains fvarId then
        return .fallback payload #[]
      let declaration ← fvarId.getDecl
      let some value := declaration.value? (allowNondep := true)
        | return .fallback payload #[]
      unless ← isProp declaration.type do
        return .fallback payload #[]
      let child ← extractAux environment catalog value declaration.type
        (remainingDepth - 1) remainingMacroDepth remainingHelperDepth followHelperBodies
        helperModule? (activeLocalDefinitions.push fvarId) activeExpandedDeclarations
      return .fallback payload #[child]
  | expression =>
      let application? ← appliedConstant? expression
      let registeredEntry? := application?.bind fun application =>
        if application.fullyApplied then
          (lookupWith? environment catalog application.declaration).bind fun entry =>
            if !entry.expansionOnly || followHelperBodies then some entry else none
        else none
      let registeredRule? := registeredEntry?.bind fun entry =>
        match entry.role with
        | .proofRule _ => some entry
        | _ => none

      if let some entry := registeredRule? then
        let some node ← recoverWith? environment catalog expression
          | return .fallback payload #[]
        let .proofApplication application := node
          | return .fallback payload #[]
        let some semanticGraph ← recoverGraphWith? environment catalog expression
          | return .fallback payload #[]
        let applied := application?.get!
        let mut premises := #[]
        let mut proofOrdinal := 0
        for argument in applied.arguments do
          if argument.isProof then
            let descriptor := premiseDescriptor (some entry) argument proofOrdinal
            let evidence ← extractAux environment catalog argument.value
              argument.instantiatedType (remainingDepth - 1) remainingMacroDepth
              remainingHelperDepth followHelperBodies helperModule? activeLocalDefinitions
              activeExpandedDeclarations
            premises := premises.push { descriptor, evidence }
            proofOrdinal := proofOrdinal + 1
        let mut macroExpansion? := none
        if remainingMacroDepth > 0 &&
            (!hasRegisteredPremiseInterface entry || entry.expandProof) &&
            !activeExpandedDeclarations.contains applied.declaration then
          if let some instantiatedValue ← instantiatedDeclarationValue? applied then
            let expansion ← extractAux environment catalog instantiatedValue applied.resultType
              (remainingDepth - 1) (remainingMacroDepth - 1) remainingHelperDepth
              (followHelperBodies || entry.expandProof)
              (if entry.expandProof then environment.getModuleIdxFor? applied.declaration
                else helperModule?) activeLocalDefinitions
              (activeExpandedDeclarations.push applied.declaration)
            -- The application payload already retains the complete checked
            -- rule use.  Keep its body only when it contributes a registered
            -- semantic child, rather than attaching irrelevant implementation
            -- fallback from an otherwise atomic helper.
            if expansion.ruleCount > 0 then
              macroExpansion? := some expansion
        return .rule payload application semanticGraph premises macroExpansion?

      let mut children := #[]
      if let some applied := application? then
        for argument in applied.arguments do
          if argument.isProof then
            children := children.push (← extractAux environment catalog argument.value
              argument.instantiatedType (remainingDepth - 1) remainingMacroDepth
              remainingHelperDepth followHelperBodies helperModule? activeLocalDefinitions
              activeExpandedDeclarations)
        if followHelperBodies && remainingHelperDepth > 0 && applied.fullyApplied &&
            environment.getModuleIdxFor? applied.declaration == helperModule? &&
            !activeExpandedDeclarations.contains applied.declaration then
          if let some instantiatedValue ← instantiatedDeclarationValue? applied then
            let expansion ← extractAux environment catalog instantiatedValue applied.resultType
              (remainingDepth - 1) remainingMacroDepth (remainingHelperDepth - 1) true
              helperModule? activeLocalDefinitions
              (activeExpandedDeclarations.push applied.declaration)
            if expansion.ruleCount > 0 then
              children := children.push expansion
      else
        match expression with
        | .proj _ _ source =>
            let sourceType ← inferType source
            if ← isProp sourceType then
              children := children.push (← extractAux environment catalog source sourceType
                (remainingDepth - 1) remainingMacroDepth remainingHelperDepth
                followHelperBodies helperModule? activeLocalDefinitions
                activeExpandedDeclarations)
        | _ => pure ()
      return .fallback payload children

/-- Extract checked evidence from an arbitrary proof term. -/
def fromProofWith (environment : Environment) (catalog : Catalog) (proof expected : Expr)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 8)
    (maximumHelperExpansionDepth : Nat := 48) : MetaM Tree :=
  extractAux environment catalog proof expected maximumDepth maximumMacroExpansionDepth
    maximumHelperExpansionDepth false none #[] #[]

/-- Environment-only form of `fromProofWith`. -/
def fromProof (environment : Environment) (proof expected : Expr)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 8)
    (maximumHelperExpansionDepth : Nat := 48) : MetaM Tree :=
  fromProofWith environment #[] proof expected maximumDepth maximumMacroExpansionDepth
    maximumHelperExpansionDepth

/-- Extract checked proof evidence for a named declaration. -/
def fromDeclarationWith? (environment : Environment) (catalog : Catalog) (name : Name)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 8)
    (maximumHelperExpansionDepth : Nat := 48) :
    MetaM (Option DeclarationEvidence) := do
  let information ← getConstInfo name
  let some proof := information.value? (allowOpaque := true) | return none
  withLCtx {} #[] do
    let evidence ← fromProofWith environment catalog proof information.type maximumDepth
      maximumMacroExpansionDepth maximumHelperExpansionDepth
    return some { name, theoremType := information.type, evidence }

/-- Environment-only form of `fromDeclarationWith?`. -/
def fromDeclaration? (environment : Environment) (name : Name)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 8)
    (maximumHelperExpansionDepth : Nat := 48) :
    MetaM (Option DeclarationEvidence) :=
  fromDeclarationWith? environment #[] name maximumDepth maximumMacroExpansionDepth
    maximumHelperExpansionDepth

end Informalization.Semantics.ProofEvidence
