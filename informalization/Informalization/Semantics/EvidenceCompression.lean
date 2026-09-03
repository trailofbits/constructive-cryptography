/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.CanonicalProof

/-!
# Checked implementation-evidence compression

This module classifies only a deliberately small set of proof effects.  It
never reads tactic syntax, local user names, or theorem-name substrings.
Every canonical proof node receives an evidence-coverage entry, and an unrecognized node stays
on the uncovered frontier.

The compressible effects are proposition-directed: reflexive singleton
membership/equality wrappers and definitional or coercion normalization.
`Nonempty` and `Nontrivial` are retained as mathematical carrier assumptions,
while profile-declared primary hypotheses remain visible in their own class.
-/

namespace Informalization.Semantics.EvidenceCompression

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Registry
open Informalization.Semantics.ProofEvidence
open Informalization.Semantics.Canonical
open Informalization.Semantics.CanonicalProof

/-- Checked proof effects which may be compressed out of the reader-facing
mathematical argument. -/
inductive RoutineEffect where
  | singletonMembership
  | singletonEqualityWrapper
  | definitionalOrCoercionNormalization
  deriving Inhabited, BEq, Repr

/-- Canonical mathematical assumptions on the carrier. -/
inductive CarrierAssumptionKind where
  | inhabited
  | nontrivial
  deriving Inhabited, BEq, Repr

/-- Structural evidence traversed by the checked proof extractor.  These
coverage entries account for implementation structure; they are not mathematical
proof steps. -/
inductive StructuralEffect where
  | binderIntroduction
  | localDefinition
  | localDefinitionReference
  | metadata
  | projection
  | logicalAssembly
  | equalityElimination
  deriving Inhabited, BEq, Repr

/-- Safe, alpha-stable description of an expected proposition.  The hash is
computed from metadata-free expression structure using local-context
positions for free variables and ignoring binder spelling.  Definitional
normalization is performed only by the bounded effect check below; globally
reducing a cryptographic statement can expose an arbitrarily large
implementation. -/
structure PropositionFingerprint where
  head? : Option Name
  normalizedHash : UInt64
  deriving Inhabited, BEq, Repr

/-- Classification attached to exactly one checked canonical-proof node. -/
inductive EvidenceDisposition where
  | registeredSemanticStep
  | registeredPremise (role : ArgumentRole) (salience : Salience)
  | expandedImplementation
  | structural (effect : StructuralEffect)
  | absorbed (effect : RoutineEffect)
  | carrierAssumption (kind : CarrierAssumptionKind)
  | primaryHypothesis (declaration : Name)
  | uncovered
  deriving Inhabited, BEq, Repr

/-- Complete evidence-coverage entry for one canonical proof node. -/
structure EvidenceCoverage where
  path : ProofPath
  payload : Payload
  proposition : PropositionFingerprint
  disposition : EvidenceDisposition
  deriving Inhabited

/-- One explicit carrier assumption, with all checked occurrences retained. -/
structure CarrierAssumption where
  kind : CarrierAssumptionKind
  proposition : PropositionFingerprint
  occurrences : Array ProofPath
  deriving Inhabited

/-- One primary mathematical hypothesis, with all checked occurrences
retained. -/
structure PrimaryHypothesis where
  declaration : Name
  proposition : PropositionFingerprint
  occurrences : Array ProofPath
  deriving Inhabited

/-- An evidence region which could not be classified by the bounded semantic
checker. -/
structure UncoveredRegion where
  path : ProofPath
  payload : Payload
  proposition : PropositionFingerprint
  deriving Inhabited

/-- Result of checked compression.  `coverage` covers every node of the
canonical proof, including structural wrappers and registered rules. -/
structure Result where
  coverage : Array EvidenceCoverage
  rootEffect? : Option RoutineEffect
  absorbedEffects : Array RoutineEffect
  carrierAssumptions : Array CarrierAssumption
  primaryHypotheses : Array PrimaryHypothesis
  uncoveredRegions : Array UncoveredRegion
  evidenceCount : Nat
  coverageComplete : Bool
  deriving Inhabited

/-- Refactoring-stable public comparison key for routine evidence.  Structural
wrapper counts and proof terms are deliberately absent; normalized
proposition identities and checked effects remain. -/
structure Fingerprint where
  absorbedEffects : Array RoutineEffect
  carrierAssumptions : Array (CarrierAssumptionKind × PropositionFingerprint)
  primaryHypotheses : Array (Name × PropositionFingerprint)
  uncovered : Array PropositionFingerprint
  deriving Inhabited, BEq, Repr

private structure ClassificationContext where
  /-- Alpha-stable hashes of systems occurring as singleton members in the
  decoded root construction. -/
  rootSingletonMembers : Array UInt64 := #[]
  rootSingletonHeads : Array Name := #[]

/-- Why an unregistered node is already accounted for by a checked semantic
boundary.  Premise and expanded-body coverage retain exact proof payloads; the
classification does not infer a new mathematical rule for them. -/
private inductive CoverageContext where
  | ordinary
  | registeredPremise (role : ArgumentRole) (salience : Salience)
  | expandedImplementation

private def fvarPosition? (localContext : LocalContext) (target : FVarId) : Option Nat :=
  Id.run do
    for index in [0:localContext.decls.size] do
      if let some declaration := localContext.decls[index]! then
        if declaration.fvarId == target then return some index
    return none

/-- A local-name-free structural code used only to construct a safe hash. -/
private partial def expressionCode (localContext : LocalContext) (raw : Expr) : String :=
  match raw.consumeMData with
  | .bvar index => s!"b:{index}"
  | .fvar id => s!"f:{fvarPosition? localContext id |>.getD localContext.decls.size}"
  | .mvar _ => "m"
  | .sort level => s!"s:{repr level}"
  | .const declaration levels => s!"c:{declaration}:{repr levels}"
  | .app function argument =>
      s!"a({expressionCode localContext function})({expressionCode localContext argument})"
  | .lam _ domain body info =>
      s!"l:{repr info}({expressionCode localContext domain})({expressionCode localContext body})"
  | .forallE _ domain body info =>
      s!"p:{repr info}({expressionCode localContext domain})({expressionCode localContext body})"
  | .letE _ type value body nondep =>
      s!"e:{nondep}({expressionCode localContext type})({expressionCode localContext value})" ++
        s!"({expressionCode localContext body})"
  | .lit literal => s!"i:{repr literal}"
  | .mdata _ expression => expressionCode localContext expression
  | .proj typeName index expression =>
      s!"j:{typeName}:{index}({expressionCode localContext expression})"

private def expressionFingerprint (localContext : LocalContext) (expression : Expr) : UInt64 :=
  (expressionCode localContext expression).hash

private def rootSingletonOperands (profile : DecoderProfile) (theoremType : Expr) :
    MetaM (Array UInt64 × Array Name) :=
  forallTelescope theoremType fun _ conclusion => do
    let some claim ← decodeClaim? profile conclusion | return (#[], #[])
    let .construction _ source _ target _ := claim | return (#[], #[])
    let localContext ← getLCtx
    let singletonMember? : SpecificationTerm → Option (UInt64 × Option Name)
      | .singleton _ system =>
          some (expressionFingerprint localContext system.source,
            headDeclaration? system.source)
      | .opaque _ => none
    let operands := #[singletonMember? source, singletonMember? target].filterMap id
    return (operands.map (·.1), operands.filterMap (·.2))

private def propositionFingerprint (payload : Payload) : MetaM PropositionFingerprint :=
  withLCtx payload.localContext #[] do
    let expected ← instantiateMVars payload.expected
    return {
      head? := headDeclaration? expected
      normalizedHash := (expressionCode payload.localContext expected).hash
    }

private def equalityOperands? (expression : Expr) : Option (Expr × Expr) := do
  let expression := expression.consumeMData
  guard (headDeclaration? expression == some ``Eq)
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  return (arguments[arguments.size - 2]!, arguments[arguments.size - 1]!)

private def reduciblyEqual (left right : Expr) : MetaM Bool := do
  if left == right then return true
  let normalizedLeft ← whnf left
  let normalizedRight ← whnf right
  if normalizedLeft == normalizedRight then return true
  withTransparency .reducible do isDefEq left right

private def reflexiveEquality? (expression : Expr) : MetaM Bool := do
  let some (left, right) := equalityOperands? expression | return false
  reduciblyEqual left right

private def singletonMembershipOperands? (expression : Expr) : Option (Expr × Expr) := do
  let expression := expression.consumeMData
  guard (headDeclaration? expression == some ``Membership.mem)
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  let collection := arguments[arguments.size - 2]!.consumeMData
  let member := arguments[arguments.size - 1]!
  let collectionHead := headDeclaration? collection
  guard (collectionHead == some ``Singleton.singleton)
  let some singletonMember := collection.getAppArgs.back? | none
  return (member, singletonMember)

private def reflexiveEquivalence? (expression : Expr) : MetaM Bool := do
  let expression := expression.consumeMData
  unless headDeclaration? expression == some ``Iff do return false
  let arguments := expression.getAppArgs
  unless arguments.size == 2 do return false
  return arguments[0]! == arguments[1]!

private def proofIrrelevantEquality? (expression : Expr) : MetaM Bool := do
  let some (left, right) := equalityOperands? expression | return false
  let leftType ← inferType left
  let rightType ← inferType right
  unless ← isProp leftType do return false
  if leftType == rightType then return true
  withTransparency .reducible do isDefEq leftType rightType

private def propositionTruthNormalization? (expression : Expr) : MetaM Bool := do
  let some (left, right) := equalityOperands? expression | return false
  unless (← isProp left) && (← isProp right) do return false
  if headDeclaration? left == some ``True then
    return ← reflexiveEquality? right
  if headDeclaration? right == some ``True then
    return ← reflexiveEquality? left
  if (← reflexiveEquality? left) && (← reflexiveEquality? right) then
    return true
  return false

private def singletonEqualityWrapper? (expression : Expr) : MetaM Bool := do
  let expression := expression.consumeMData
  unless headDeclaration? expression == some ``Iff do return false
  let arguments := expression.getAppArgs
  unless arguments.size == 2 do return false
  let check (membership equality : Expr) : MetaM Bool := do
    let some (member, singletonMember) := singletonMembershipOperands? membership
      | return false
    let some (left, right) := equalityOperands? equality | return false
    let direct ← reduciblyEqual member left
    let singletonDirect ← reduciblyEqual singletonMember right
    if direct && singletonDirect then return true
    let reversed ← reduciblyEqual member right
    let singletonReversed ← reduciblyEqual singletonMember left
    return reversed && singletonReversed
  if ← check arguments[0]! arguments[1]! then return true
  check arguments[1]! arguments[0]!

private def hasMembershipSide (expression : Expr) : Bool :=
  if headDeclaration? expression == some ``Membership.mem then true
  else if headDeclaration? expression == some ``Iff then
    expression.getAppArgs.any fun argument =>
      headDeclaration? argument == some ``Membership.mem
  else false

/-- Recognize a routine effect from the checked expected proposition and the
normalized singleton operands decoded from the theorem root. -/
private def isRootSingletonMember (context : ClassificationContext)
    (localContext : LocalContext) (expression : Expr) : Bool :=
  context.rootSingletonMembers.contains (expressionFingerprint localContext expression)

private def hasRootSingletonHead (context : ClassificationContext) (expression : Expr) : Bool :=
  (headDeclaration? expression).any context.rootSingletonHeads.contains

private def routineEffect? (context : ClassificationContext)
    (localContext : LocalContext) (expected : Expr) :
    MetaM (Option RoutineEffect) := do
  if let some (member, singletonMember) := singletonMembershipOperands? expected then
    if (← reduciblyEqual member singletonMember) ||
        isRootSingletonMember context localContext singletonMember ||
        hasRootSingletonHead context singletonMember then
      return some .singletonMembership
  if hasMembershipSide expected && (← singletonEqualityWrapper? expected) then
    return some .singletonEqualityWrapper
  if let some (left, right) := equalityOperands? expected then
    if isRootSingletonMember context localContext left ||
        isRootSingletonMember context localContext right ||
        hasRootSingletonHead context left || hasRootSingletonHead context right then
      return some .singletonEqualityWrapper
  if ← proofIrrelevantEquality? expected then
    return some .definitionalOrCoercionNormalization
  if ← propositionTruthNormalization? expected then
    return some .definitionalOrCoercionNormalization
  if ← reflexiveEquality? expected then
    return some .definitionalOrCoercionNormalization
  if ← reflexiveEquivalence? expected then
    return some .definitionalOrCoercionNormalization
  return none

private def carrierAssumptionKind? (expected : Expr) : Option CarrierAssumptionKind :=
  match headDeclaration? expected with
  | some ``Nonempty => some .inhabited
  | some declaration =>
      if declaration == Name.mkSimple "Nontrivial" then some .nontrivial else none
  | _ => none

private def structuralEffect? (payload : Payload) (hasOneChild : Bool) : MetaM
    (Option StructuralEffect) := do
  unless hasOneChild do return none
  match payload.proof with
  | .mdata .. => return some .metadata
  | _ => pure ()
  match payload.proof.consumeMData with
  | .lam .. => return some .binderIntroduction
  | .letE .. => return some .localDefinition
  | .proj .. => return some .projection
  | .fvar id =>
      return if (← id.getDecl).value?.isSome then some .localDefinitionReference else none
  | _ => return none

private def applicationStructuralEffect? (proof : Expr) : Option StructuralEffect :=
  match headDeclaration? proof with
  | some ``Exists.intro | some ``And.intro => some .logicalAssembly
  | some ``Eq.ndrec | some ``Eq.mpr | some ``Eq.symm | some ``Iff.mp |
      some ``congrArg => some .equalityElimination
  | _ => none

private def classifyFallback (profile : DecoderProfile) (context : ClassificationContext)
    (coverageContext : CoverageContext) (node : FallbackNode)
    (childrenCovered childrenContainSemantic : Bool) :
    MetaM EvidenceDisposition := do
  if let some effect ← withLCtx node.payload.localContext #[] do
      structuralEffect? node.payload (node.children.size == 1) then
    return .structural effect
  if let some effect := applicationStructuralEffect? node.payload.proof then
    match effect with
    | .logicalAssembly =>
        if childrenContainSemantic then return .structural effect
    | _ => return .structural effect
  if childrenCovered && node.children.size == 1 then
    let child := node.children[0]!.primaryEvidence
    if node.payload.expected == child.expected then
      return .absorbed .definitionalOrCoercionNormalization
  let expectedHead := headDeclaration? node.payload.expected
  if let some declaration := expectedHead then
    if profile.primaryHypotheses.contains declaration then
      return .primaryHypothesis declaration
  if let some kind := carrierAssumptionKind? node.payload.expected then
    return .carrierAssumption kind
  if let some effect ← withLCtx node.payload.localContext #[] do
      routineEffect? context node.payload.localContext node.payload.expected then
    return .absorbed effect
  match coverageContext with
  | .registeredPremise role salience => return .registeredPremise role salience
  | .expandedImplementation => return .expandedImplementation
  | .ordinary => return .uncovered

private partial def coverageOf (profile : DecoderProfile) (context : ClassificationContext)
    (proof : CanonicalProof) (coverageContext : CoverageContext := .ordinary) :
    MetaM (Array EvidenceCoverage) := do
  match proof with
  | .rule node =>
      let proposition ← propositionFingerprint node.payload
      let mut coverage := #[{
        path := node.path
        payload := node.payload
        proposition
        disposition := .registeredSemanticStep
      }]
      for premise in node.premises do
        coverage := coverage ++ (← coverageOf profile context premise.proof
          (.registeredPremise premise.descriptor.role premise.descriptor.salience))
      if let some expansion := node.macroExpansion? then
        coverage := coverage ++ (← coverageOf profile context expansion
          .expandedImplementation)
      return coverage
  | .fallback node =>
      let mut childCoverage := #[]
      for child in node.children do
        childCoverage := childCoverage ++ (← coverageOf profile context child coverageContext)
      let childrenCovered := !childCoverage.any (·.disposition == .uncovered)
      let childrenContainSemantic :=
        childCoverage.any (·.disposition == .registeredSemanticStep)
      let disposition ← classifyFallback profile context coverageContext node childrenCovered
        childrenContainSemantic
      let proposition ← propositionFingerprint node.payload
      let mut coverage := #[{
        path := node.path
        payload := node.payload
        proposition := proposition
        disposition := disposition
      }]
      coverage := coverage ++ childCoverage
      return coverage

private def pushUnique {α : Type} [BEq α] (values : Array α) (value : α) : Array α :=
  if values.contains value then values else values.push value

private def addAssumption (result : Array CarrierAssumption) (entry : EvidenceCoverage)
    (kind : CarrierAssumptionKind) : Array CarrierAssumption :=
  match result.findIdx? fun assumption =>
      assumption.kind == kind && assumption.proposition == entry.proposition with
  | some index => result.modify index fun assumption =>
      { assumption with occurrences := assumption.occurrences.push entry.path }
  | none => result.push {
      kind
      proposition := entry.proposition
      occurrences := #[entry.path]
    }

private def addPrimaryHypothesis (result : Array PrimaryHypothesis) (entry : EvidenceCoverage)
    (declaration : Name) : Array PrimaryHypothesis :=
  match result.findIdx? fun hypothesis =>
      hypothesis.declaration == declaration &&
        hypothesis.proposition == entry.proposition with
  | some index => result.modify index fun hypothesis =>
      { hypothesis with occurrences := hypothesis.occurrences.push entry.path }
  | none => result.push {
      declaration
      proposition := entry.proposition
      occurrences := #[entry.path]
    }

private def pathsUnique (coverage : Array EvidenceCoverage) : Bool :=
  coverage.all fun entry =>
    (coverage.filter (·.path == entry.path)).size == 1

/-- Classify every node of a checked canonical proof.  The theorem type is
decoded once so singleton-membership assembly can be checked against the
actual root operands rather than against a declaration or theorem name. -/
def classify (profile : DecoderProfile) (theoremType : Expr)
    (proof : CanonicalProof) : MetaM Result := do
  let (rootSingletonMembers, rootSingletonHeads) ←
    rootSingletonOperands profile theoremType
  let context : ClassificationContext := {
    rootSingletonMembers
    rootSingletonHeads
  }
  let coverage ← coverageOf profile context proof
  let rootEffect? ← forallTelescope theoremType fun _ conclusion => do
    let localContext ← getLCtx
    routineEffect? context localContext conclusion
  let mut absorbedEffects : Array RoutineEffect := #[]
  let mut carrierAssumptions : Array CarrierAssumption := #[]
  let mut primaryHypotheses : Array PrimaryHypothesis := #[]
  let mut uncoveredRegions : Array UncoveredRegion := #[]
  for entry in coverage do
    match entry.disposition with
    | .absorbed effect =>
        absorbedEffects := pushUnique absorbedEffects effect
    | .carrierAssumption kind =>
        carrierAssumptions := addAssumption carrierAssumptions entry kind
    | .primaryHypothesis declaration =>
        primaryHypotheses := addPrimaryHypothesis primaryHypotheses entry declaration
    | .uncovered =>
        uncoveredRegions := uncoveredRegions.push {
          path := entry.path
          payload := entry.payload
          proposition := entry.proposition
        }
    | .registeredSemanticStep | .registeredPremise _ _ |
        .expandedImplementation | .structural _ => pure ()
  let evidenceCount := proof.allEvidence.size
  let coverageComplete := coverage.size == evidenceCount && pathsUnique coverage
  unless coverageComplete do
    throwError "checked evidence compression did not cover the canonical proof exactly"
  return {
    coverage
    rootEffect?
    absorbedEffects
    carrierAssumptions
    primaryHypotheses
    uncoveredRegions
    evidenceCount
    coverageComplete
  }

def Result.hasUncovered (result : Result) : Bool :=
  !result.uncoveredRegions.isEmpty

def Result.fingerprint (result : Result) : Fingerprint := {
  absorbedEffects := result.rootEffect?.map (#[·]) |>.getD result.absorbedEffects
  carrierAssumptions := result.carrierAssumptions.map fun assumption =>
    (assumption.kind, assumption.proposition)
  primaryHypotheses := result.primaryHypotheses.map fun hypothesis =>
    (hypothesis.declaration, hypothesis.proposition)
  uncovered := result.uncoveredRegions.map (·.proposition)
}

end Informalization.Semantics.EvidenceCompression
