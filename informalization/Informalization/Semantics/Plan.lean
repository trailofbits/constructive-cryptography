/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.CanonicalProof
import Informalization.Semantics.EvidenceCompression

/-!
# Domain proof-plan classification

The first planning slice classifies registered proof-rule applications into
distinct cryptographic proof genres.  It does not realize prose and does not
inspect tactics, local names, or theorem-name substrings.

The plan retains its complete `ProofEvidence.Tree`; the classified steps are a
semantic index over that checked evidence rather than a replacement for it.
-/

namespace Informalization.Semantics.Plan

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Registry
open Informalization.Semantics.ProofEvidence
open Informalization.Semantics.Canonical
open Informalization.Semantics.CanonicalProof
open Informalization.Semantics.EvidenceCompression

/-- Cryptographic proof genres that require different discourse plans. -/
inductive Genre where
  | exactEquivalence
  | conditionalEquivalence
  | blindWinningBound
  | hTechnique
  | hybrid
  | gameHop
  | counting
  | generic
  deriving Inhabited, BEq, Repr

/-- Coarse checked plan shapes.  The conditional-equivalence/blind-bound chain
is explicit so a later discourse planner does not infer it from a generic bad
event or confuse it with H-technique or symmetric game hopping. -/
inductive Kind where
  | conditionalEquivalenceBlind
  | exactEquivalence
  | conditionalEquivalence
  | blindWinningBound
  | hTechnique
  | hybrid
  | gameHop
  | counting
  | generic
  | fallback
  deriving Inhabited, BEq, Repr

/-- Classify a typed proof-rule role.  In particular, the one-sided
conditional-equivalence route and the symmetric game-playing route are
different constructors even though both may use a bad condition. -/
def genreOfRule : ProofRuleRole → Genre
  | .exactEquivalence | .ignoreGameMBO => .exactEquivalence
  | .conditionalEquivalence | .conditionalEquivalenceUnderRestriction |
      .collisionConditionalEquivalence | .conditionalEquivalenceToBlindWinning =>
      .conditionalEquivalence
  | .blindWinningBound | .blindWinningToNonadaptive | .nonadaptiveQueriesFixed =>
      .blindWinningBound
  | .hTechnique => .hTechnique
  | .triangleHybrid => .hybrid
  | .gamePlayingFundamentalLemma => .gameHop
  | .counting | .collisionProbabilityBound | .collisionMassBound | .birthdayBound => .counting
  | .construction | .distanceBound | .advantageBound => .generic
  | _ => .generic

/-- One registered proof-rule application in semantic preorder.

`semanticDepth` increases only when a registered rule occurs inside a
proof-valued premise or the bounded checked expansion of another registered
semantic macro.  Unclassified kernel or tactic wrappers do not affect it. -/
structure Step where
  genre : Genre
  semanticDepth : Nat
  payload : Payload
  application : ProofApplication
  semanticGraph : Graph
  premises : Array Premise
  deriving Inhabited

/-- Exact origin of a registered step in the recursive semantic proof.  A
fallback wrapper is transparent in this primary support view, but remains in
`ProofPlan.canonicalProof`. -/
inductive StepOrigin where
  | root
  | premise (parentStepId : Nat) (key : ObligationKey)
      (descriptor : PremiseDescriptor)
  | macroExpansion (parentStepId : Nat)
  deriving Inhabited

/-- Flat compatibility record for consumers that cannot yet traverse
`SupportTree`.  `stepId` is the index of `step` in `ProofPlan.steps`; ancestry
comes from `origin`, never from `semanticDepth`. -/
structure StepView where
  stepId : Nat
  path : ProofPath
  parentStepId? : Option Nat := none
  origin : StepOrigin
  step : Step
  derivation? : Option DerivationApplication := none
  deriving Inhabited

/-- Recursive primary-support view over registered rules.  Complete checked
fallback and instance evidence remains available in `canonicalProof`; children
here are promoted only through transparent fallback wrappers. -/
structure SupportTree where
  view : StepView
  children : Array SupportTree := #[]

instance : Inhabited SupportTree := ⟨{
  view := default
  children := #[]
}⟩

def SupportTree.premiseChildren (tree : SupportTree) : Array SupportTree :=
  tree.children.filter fun child =>
    match child.view.origin with
    | .premise parentStepId _ _ => parentStepId == tree.view.stepId
    | _ => false

def SupportTree.childrenForPremise (tree : SupportTree)
    (key : ObligationKey) : Array SupportTree :=
  tree.children.filter fun child =>
    match child.view.origin with
    | .premise parentStepId childKey _ =>
        parentStepId == tree.view.stepId && childKey == key
    | _ => false

def SupportTree.macroChildren (tree : SupportTree) : Array SupportTree :=
  tree.children.filter fun child =>
    match child.view.origin with
    | .macroExpansion parentStepId => parentStepId == tree.view.stepId
    | _ => false

/-- A proof plan is an index over complete checked evidence. -/
structure ProofPlan where
  declaration : Name
  theoremType : Expr
  evidence : Tree
  /-- Complete recursively decoded evidence, including fallback wrappers. -/
  canonicalProof : CanonicalProof
  /-- Complete, checked classification of every canonical proof node. -/
  compression : EvidenceCompression.Result
  /-- Registered semantic roots and their recursive support edges. -/
  supportForest : Array SupportTree
  /-- Stable preorder compatibility view. -/
  stepViews : Array StepView
  steps : Array Step
  deriving Inhabited

private def stepOfRuleNode (node : RuleNode) : Step := {
  genre := genreOfRule node.application.role
  semanticDepth := node.path.semanticDepth
  payload := node.payload
  application := node.application
  semanticGraph := node.semanticGraph
  premises := node.premises.map (·.source)
}

private partial def supportForestAux (proof : CanonicalProof)
    (origin : StepOrigin) (parentStepId? : Option Nat) : Array SupportTree :=
  match proof with
  | .fallback node =>
      node.children.foldl (fun result child =>
        result ++ supportForestAux child origin parentStepId?) #[]
  | .rule node =>
      let step := stepOfRuleNode node
      let view : StepView := {
        stepId := node.stepId
        path := node.path
        parentStepId?
        origin
        step
        derivation? := node.derivation?
      }
      let premiseChildren := node.premises.foldl (fun result premise =>
        result ++ supportForestAux premise.proof
          (.premise node.stepId premise.key premise.descriptor) (some node.stepId)) #[]
      let children := node.macroExpansion?.elim premiseChildren fun expansion =>
        premiseChildren ++ supportForestAux expansion (.macroExpansion node.stepId)
          (some node.stepId)
      #[{ view, children }]

private partial def flattenSupportTree (tree : SupportTree) : Array StepView :=
  tree.children.foldl (fun result child => result ++ flattenSupportTree child)
    #[tree.view]

private def flattenSupportForest (forest : Array SupportTree) : Array StepView :=
  forest.foldl (fun result tree => result ++ flattenSupportTree tree) #[]

/-- Build a recursive proof plan from previously extracted declaration
evidence.  The decoder profile affects canonical claims and operands, not tree
identity or checked evidence. -/
def ofEvidence (declaration : DeclarationEvidence)
    (canonicalProfile : DecoderProfile := {}) : MetaM ProofPlan := do
  let canonicalProof ← CanonicalProof.ofEvidence canonicalProfile declaration.evidence
  let compression ← EvidenceCompression.classify canonicalProfile declaration.theoremType
    canonicalProof
  let supportForest := supportForestAux canonicalProof .root none
  let stepViews := flattenSupportForest supportForest
  -- `CanonicalProof` assigns registered nodes in the same evidence preorder as
  -- the compatibility array.  Check the contract here rather than asking a
  -- downstream consumer to infer it.
  for index in [0:stepViews.size] do
    unless stepViews[index]!.stepId == index do
      throwError "canonical proof step identifiers are not preorder-contiguous"
  return {
    declaration := declaration.name
    theoremType := declaration.theoremType
    evidence := declaration.evidence
    canonicalProof
    compression
    supportForest
    stepViews
    steps := stepViews.map (·.step)
  }

/-- Extract and classify a named declaration with a profile catalog. -/
def fromDeclarationWith? (environment : Environment) (catalog : Catalog) (name : Name)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 4)
    (canonicalProfile : DecoderProfile := {}) :
    MetaM (Option ProofPlan) := do
  let some evidence ← ProofEvidence.fromDeclarationWith?
      environment catalog name maximumDepth maximumMacroExpansionDepth | return none
  return some (← ofEvidence evidence canonicalProfile)

/-- Profile-first convenience form for callers that already selected a
domain's canonical decoder alongside its semantic registry catalog. -/
def fromDeclarationWithProfile? (environment : Environment) (catalog : Catalog)
    (canonicalProfile : DecoderProfile) (name : Name)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 4) :
    MetaM (Option ProofPlan) :=
  fromDeclarationWith? environment catalog name maximumDepth
    maximumMacroExpansionDepth canonicalProfile

/-- Environment-only form of `fromDeclarationWith?`. -/
def fromDeclaration? (environment : Environment) (name : Name)
    (maximumDepth : Nat := 512) (maximumMacroExpansionDepth : Nat := 4)
    (canonicalProfile : DecoderProfile := {}) :
    MetaM (Option ProofPlan) :=
  fromDeclarationWith? environment #[] name maximumDepth maximumMacroExpansionDepth
    canonicalProfile

namespace ProofPlan

/-- Primary registered evidence used by the semantic support view. -/
def primaryEvidence (plan : ProofPlan) : Array Payload :=
  plan.stepViews.map (·.step.payload)

/-- Complete checked evidence, including fallback wrappers, implicit premises,
and semantic-macro implementations. -/
def allEvidence (plan : ProofPlan) : Array Payload :=
  plan.canonicalProof.allEvidence

/-- Genres occurring in the checked proof, in first semantic occurrence order. -/
def genres (plan : ProofPlan) : Array Genre := Id.run do
  let mut result := #[]
  for step in plan.steps do
    unless result.contains step.genre do result := result.push step.genre
  return result

/-- The first outermost classified genre.  A composite plan still retains all
genres through `genres` and all steps through `steps`. -/
def dominantGenre? (plan : ProofPlan) : Option Genre :=
  plan.steps[0]?.map (·.genre)

/-- Classify the checked plan from its typed rule genres. -/
def kind (plan : ProofPlan) : Kind :=
  let genres := plan.genres
  if genres.contains .conditionalEquivalence &&
      genres.contains .blindWinningBound then
    .conditionalEquivalenceBlind
  else
    match plan.dominantGenre? with
    | some .exactEquivalence => .exactEquivalence
    | some .conditionalEquivalence => .conditionalEquivalence
    | some .hTechnique => .hTechnique
    | some .hybrid => .hybrid
    | some .gameHop => .gameHop
    | some .blindWinningBound => .blindWinningBound
    | some .counting => .counting
    | some .generic => .generic
    | none => .fallback

abbrev FallbackRegion := EvidenceCompression.UncoveredRegion

private def sameFallbackRegion (left right : FallbackRegion) : Bool :=
  left.payload.proof == right.payload.proof &&
    left.payload.expected == right.payload.expected

private def deduplicateFallbacks (fallbacks : Array FallbackRegion) :
    Array FallbackRegion := Id.run do
  let mut result := #[]
  for fallback in fallbacks do
    unless result.any (sameFallbackRegion fallback) do
      result := result.push fallback
  return result

/-- Exact uncovered regions left by checked evidence compression. -/
def fallbackRegions (plan : ProofPlan) : Array FallbackRegion :=
  deduplicateFallbacks plan.compression.uncoveredRegions

/-- The presentation frontier of evidence which no bounded semantic effect
checker classified.  Structural, carrier-assumption, primary-hypothesis, and
routine evidence coverage remains available through `compression.coverage`. -/
def fallbackEvidence (plan : ProofPlan) : Array Payload :=
  plan.fallbackRegions.map (·.payload)

/-- Whether the plan retains at least one unclassified checked region. -/
def hasFallback (plan : ProofPlan) : Bool :=
  plan.compression.hasUncovered

/-- Checked routine-evidence comparison key. -/
def compressionFingerprint (plan : ProofPlan) : EvidenceCompression.Fingerprint :=
  plan.compression.fingerprint

end ProofPlan

/-! ## Semantic fingerprint -/

/-- The stable part of one semantically bound argument. -/
structure ArgumentFingerprint where
  role : ArgumentRole
  salience : Salience
  deriving Inhabited, BEq, Repr

/-- One classified proof step after erasing expressions, declarations, local
names, source locations, and evidence IDs.  Fully qualified aliases registered
with the same semantic role therefore have the same fingerprint. -/
structure StepFingerprint where
  genre : Genre
  semanticDepth : Nat
  rule : ProofRuleRole
  arguments : Array ArgumentFingerprint
  premises : Array ArgumentFingerprint
  semanticNodes : Array NodeRole
  deriving Inhabited, BEq, Repr

/-- Semantic comparison key for a complete proof plan. -/
structure Fingerprint where
  kind : Kind
  dominantGenre? : Option Genre
  steps : Array StepFingerprint
  hasFallback : Bool
  evidenceCompression : EvidenceCompression.Fingerprint
  deriving Inhabited, BEq, Repr

/-- Comparison key for reader-visible proof structure.  Routine evidence
receipts remain available in `semanticFingerprint`, but do not distinguish two
proofs whose mathematical steps are identical. -/
structure PresentationFingerprint where
  kind : Kind
  dominantGenre? : Option Genre
  steps : Array StepFingerprint
  hasFallback : Bool
  deriving Inhabited, BEq, Repr

private def argumentFingerprint (argument : SemanticArgument) : ArgumentFingerprint :=
  { role := argument.role, salience := argument.salience }

private def premiseFingerprint (premise : Premise) : ArgumentFingerprint :=
  { role := premise.descriptor.role, salience := premise.descriptor.salience }

private def isPremiseRole : ArgumentRole → Bool
  | .premise _ => true
  | _ => false

/-- Roles on the semantic surface of a rule application.  Proof-premise
subgraphs are represented by separate checked plan steps, so excluding them
here makes the fingerprint invariant under moving a proof into a local
`have`. -/
private partial def semanticSurfaceNodeRolesAux (graph : Graph) (node : NodeId)
    (fuel : Nat) (visited : Array Nat) : Array NodeRole × Array Nat :=
  if fuel == 0 || visited.contains node.index then
    (#[], visited)
  else
    let visited := visited.push node.index
    let initial := (graph.nodes[node.index]?.map (fun value => #[value.role]) |>.getD #[], visited)
    graph.edges.foldl (init := initial) fun (result, visited) edge =>
      if edge.parent == node && !isPremiseRole edge.argument.role then
        let (childRoles, visited) := semanticSurfaceNodeRolesAux graph edge.child
          (fuel - 1) visited
        (result ++ childRoles, visited)
      else
        (result, visited)

private def semanticSurfaceNodeRoles (graph : Graph) : Array NodeRole :=
  (semanticSurfaceNodeRolesAux graph graph.root (graph.nodes.size + 1) #[]).1

private def stepFingerprint (step : Step) : StepFingerprint := {
  genre := step.genre
  semanticDepth := step.semanticDepth
  rule := step.application.role
  arguments := step.application.arguments.map argumentFingerprint
  premises := step.premises.map premiseFingerprint
  semanticNodes := semanticSurfaceNodeRoles step.semanticGraph
}

/-- Erase source-specific proof evidence while preserving the typed semantic
plan.  This function never reads local names, so alpha-renaming cannot affect
its result. -/
def ProofPlan.semanticFingerprint (plan : ProofPlan) : Fingerprint := {
  kind := plan.kind
  dominantGenre? := plan.dominantGenre?
  steps := plan.steps.map stepFingerprint
  hasFallback := plan.hasFallback
  evidenceCompression := plan.compressionFingerprint
}

/-- Erase both source syntax and absorbed routine-proof bookkeeping.  This is
the conformance key for informalization invariance under `rw`/`simpa`/`calc`,
local helper insertion, and irrelevant facts. -/
def ProofPlan.presentationFingerprint (plan : ProofPlan) : PresentationFingerprint := {
  kind := plan.kind
  dominantGenre? := plan.dominantGenre?
  steps := plan.steps.map stepFingerprint
  hasFallback := plan.hasFallback
}

end Informalization.Semantics.Plan
