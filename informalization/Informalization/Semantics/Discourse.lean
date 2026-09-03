/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.Plan
import Informalization.Semantics.Canonical

/-!
# Semantic discourse planning

This module turns a typed security-statement graph and checked proof plan into
paper-level discourse moves.  It does not render English and it does not
inspect theorem names, tactic syntax, or local names.

Every move points into an evidence index.  The index retains statement nodes,
their arguments, registered proof steps and premises, and every unclassified
formal fallback region.  Thus a concise narration is only a view over checked
evidence, never a replacement for it.
-/

namespace Informalization.Semantics.Discourse

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.ProofEvidence
open Informalization.Semantics.Plan
open Informalization.Semantics.Canonical

/-- Stable references used by discourse moves.

Statement node and proof-step identifiers are their positions in the semantic
graph and proof plan.  Premise and fallback identifiers are likewise stable
preorder positions in those checked artifacts. -/
inductive EvidenceRef where
  | statementNode (node : NodeId)
  | statementArgument (node : NodeId) (position : Nat)
  | proofStep (step : Nat)
  | proofPremise (step premise : Nat)
  | formalFallback (fallback : Nat)
  deriving Inhabited, BEq, Repr

/-- One exact item in the discourse evidence index.  `expected?` is populated
for proof evidence and records the checked proposition proved by `formal`. -/
structure EvidenceItem where
  reference : EvidenceRef
  formal : Expr
  expected? : Option Expr := none
  /-- Exact local context in which `expected?` is the active obligation.
  This remains backend data: it is consumed by the Massot--Miller goal-state
  humanizer and is never serialized as a Lean expression. -/
  localContext? : Option LocalContext := none
  declaration? : Option Name := none
  deriving Inhabited

/-- A reference to an argument recovered from a statement node. -/
structure ArgumentRef where
  node : NodeId
  position : Nat
  role : ArgumentRole
  formal : Expr
  deriving Inhabited, BEq, Repr

def ArgumentRef.evidenceRef (argument : ArgumentRef) : EvidenceRef :=
  .statementArgument argument.node argument.position

/-- A prose-free decomposition of a system expression.  `root` is the system
used by the advantage; `base` is a recursively recovered URF, URP, or other
typed base system; `queryRestriction?` records a converter in that expression.
No display name is guessed from the Lean declaration. -/
structure SystemDescriptor where
  root : NodeId
  base : NodeId
  baseRole : SystemRole
  queryRestriction? : Option NodeId := none
  deriving Inhabited, BEq, Repr

/-- The security objects which a conventional theorem opening may name.
All fields are optional: unsupported details are omitted from narration rather
than guessed from syntax. -/
structure SecurityContext where
  proposition : NodeId
  advantage? : Option NodeId := none
  sourceSystem? : Option NodeId := none
  targetSystem? : Option NodeId := none
  sourceRole? : Option ArgumentRole := none
  targetRole? : Option ArgumentRole := none
  sourceDescription? : Option SystemDescriptor := none
  targetDescription? : Option SystemDescriptor := none
  queryBudget? : Option ArgumentRef := none
  bound? : Option ArgumentRef := none
  deriving Inhabited, BEq, Repr

/-- Paper-level rhetorical moves.  These constructors describe proof
discourse, not Lean commands. -/
inductive MoveKind where
  | stateSecurityGoal
  | conditionalEquivalence
  | conditionalEquivalenceReduction
  | remainingBlindWinningObligation
  | blindWinningEstimate
  | combineConditionalEquivalenceBlind
  | hTechnique
  | hybrid
  | gameHop
  | counting
  | exactEquivalence
  | ignoreCollisionMBO
  | registeredRule (role : ProofRuleRole)
  | formalFallback
  deriving Inhabited, BEq, Repr

/-- The checked route by which a semantic subargument supports its parent.
Premise groups remain separate so equal claims used for different obligations
cannot be globally deduplicated. -/
inductive SupportOrigin where
  | premise (position : Nat) (role : ArgumentRole) (salience : Salience)
      (slot? : Option ObligationSlot := none)
  | macroExpansion
  deriving Inhabited, BEq, Repr

mutual
  /-- A recursively expandable registered proof step.  `semanticDepth` is the
  original checked depth and remains diagnostic metadata; presentation nesting
  is represented by `supports`.  `primaryEvidence` selects the local context of
  the preferred derivation after wrapper normalization, while `evidence`
  retains every checked step absorbed into the node. -/
  structure Detail where
    kind : MoveKind
    semanticDepth : Nat
    primaryEvidence : EvidenceRef
    evidence : Array EvidenceRef
    supports : Array Support := #[]
    /-- Operand-bearing mathematical transition decoded from the checked rule
    application.  It is independent of the sentence later chosen for it. -/
    derivation? : Option DerivationApplication := none
    deriving Inhabited, BEq, Repr

  /-- One proof-premise or bounded macro-expansion branch.  Children are
  ordered semantic dependencies within that branch; unclassified wrappers are
  retained only through the evidence index and do not become reader nodes. -/
  structure Support where
    origin : SupportOrigin
    evidence : Array EvidenceRef := #[]
    children : Array Detail := #[]
    deriving Inhabited, BEq, Repr
end

/-- One top-level planned discourse move and the checked evidence which
supports it.  Supporting proof steps are nested as `details`, so they are not
presented as peer conclusions after the proof has already combined its bounds. -/
structure Move where
  id : Nat
  kind : MoveKind
  semanticDepth : Nat := 0
  primaryEvidence? : Option EvidenceRef := none
  evidence : Array EvidenceRef
  supports : Array Support := #[]
  /-- Canonical conclusion and proof obligations for this move, when the
  selected domain profile recognizes them. -/
  derivation? : Option DerivationApplication := none
  deriving Inhabited, BEq, Repr

/-- A typed semantic document ready for language realization. -/
structure Document where
  /-- Selected theorem whose proof is being presented.  It scopes
  application-only linguistic evidence and never classifies mathematics. -/
  rootDeclaration? : Option Name := none
  security : Option SecurityContext
  /-- The checked theorem conclusion, decoded independently of its proof. -/
  rootClaim? : Option Claim := none
  /-- Application notation selected by the decoder profile. This is
  presentation metadata, not evidence and not a semantic classifier. -/
  declarationNotations : Array DeclarationNotation := #[]
  /-- Optional checked title and theorem introductions selected by the
  declaration profile. -/
  theoremPresentation? : Option TheoremPresentation := none
  planKind : Plan.Kind
  moves : Array Move
  evidenceIndex : Array EvidenceItem
  deriving Inhabited

private partial def theoremBinderNames : Expr → Array Name
  | .forallE binderName _ body _ =>
      #[binderName] ++ theoremBinderNames body
  | .letE _ _ value body _ => theoremBinderNames (body.instantiate1 value)
  | _ => #[]

private def validateTheoremPresentation (theoremType : Expr)
    (presentation : TheoremPresentation) : MetaM Unit := do
  unless presentation.isWellFormed do
    throwError "the theorem presentation for {presentation.declaration} is not well formed"
  let binders := theoremBinderNames theoremType
  let environment ← getEnv
  for paragraph in presentation.introductions do
    for fragment in paragraph.fragments do
      if let .reference reference := fragment then
        if reference.latex.trimAscii.isEmpty || reference.description.trimAscii.isEmpty then
          throwError "the theorem presentation for {presentation.declaration} contains an empty mathematical reference"
        match reference.target with
        | .theoremBinder binder =>
            unless binders.contains binder do
              throwError "the theorem presentation for {presentation.declaration} references missing binder {binder}"
        | .declaration declaration =>
            unless environment.contains declaration do
              throwError "the theorem presentation for {presentation.declaration} references missing declaration {declaration}"

private def childId? (graph : Graph) (parent : NodeId)
    (role : ArgumentRole) : Option NodeId :=
  (graph.edges.find? fun edge =>
    edge.parent == parent && edge.argument.role == role).map (·.child)

private def firstChildWithRole? (graph : Graph) (parent : NodeId)
    (roles : Array ArgumentRole) : Option (ArgumentRole × NodeId) :=
  roles.findSome? fun role => (childId? graph parent role).map (role, ·)

private def argumentRef? (graph : Graph) (node : NodeId)
    (role : ArgumentRole) : Option ArgumentRef := do
  let value <- graph.nodes[node.index]?
  let position <- value.arguments.findIdx? (fun argument => argument.role == role)
  let argument := value.arguments[position]!
  return { node, position, role, formal := argument.source }

private partial def descendants (graph : Graph) (roots : Array NodeId)
    (seen : Array NodeId := #[]) : Array NodeId :=
  if roots.isEmpty then
    seen
  else
    let current := roots[0]!
    let remaining := roots.extract 1 roots.size
    if seen.contains current then
      descendants graph remaining seen
    else
      let children := graph.edges.filterMap fun edge =>
        if edge.parent == current then some edge.child else none
      descendants graph (remaining ++ children) (seen.push current)

private def firstArgumentIn (graph : Graph) (nodes : Array NodeId)
    (role : ArgumentRole) : Option ArgumentRef :=
  nodes.findSome? fun node => argumentRef? graph node role

private def baseSystemRole? : NodeRole -> Option SystemRole
  | .system .uniformRandomFunction => some .uniformRandomFunction
  | .system .uniformRandomPermutation => some .uniformRandomPermutation
  | .system .presentationQuotient => some .presentationQuotient
  | .system .idealFunctionality => some .idealFunctionality
  | .system .atom => some .atom
  | .system (.custom name) => some (.custom name)
  | _ => none

private def systemDescriptor? (graph : Graph) (root : NodeId) :
    Option SystemDescriptor := do
  let scope := descendants graph #[root]
  let base <- scope.findSome? fun node => do
    let value <- graph.nodes[node.index]?
    return (node, <- baseSystemRole? value.role)
  let queryRestriction? := scope.find? fun node =>
    graph.nodes[node.index]?.any fun value =>
      value.role == .converter .queryRestriction ||
        value.role == .system .queryRestriction
  return {
    root
    base := base.1
    baseRole := base.2
    queryRestriction?
  }

/-- Recover only those security-statement objects justified by typed graph
roles.  In particular, a source/target pair is not relabeled real/ideal unless
the corresponding registered edge roles say so. -/
def securityContext? (graph : Graph) : Option SecurityContext := do
  let rootNode <- graph.rootNode?
  guard (rootNode.role == .proposition .upperBound ||
    rootNode.role == .proposition .advantageBound)
  let advantage <- childId? graph graph.root .subject
  let advantageNode <- graph.nodes[advantage.index]?
  guard (advantageNode.role == .quantity .distinguishingAdvantage)
  let source? := firstChildWithRole? graph advantage #[.sourceSystem, .realSystem]
  let target? := firstChildWithRole? graph advantage #[.targetSystem, .idealSystem]
  let sourceSystem? := source?.map (·.2)
  let targetSystem? := target?.map (·.2)
  let systemRoots := #[sourceSystem?, targetSystem?].filterMap id
  let scope := descendants graph systemRoots
  return {
    proposition := graph.root
    advantage? := some advantage
    sourceSystem?
    targetSystem?
    sourceRole? := source?.map (·.1)
    targetRole? := target?.map (·.1)
    sourceDescription? := sourceSystem?.bind (systemDescriptor? graph)
    targetDescription? := targetSystem?.bind (systemDescriptor? graph)
    queryBudget? := firstArgumentIn graph scope .queryBudget
    bound? := argumentRef? graph graph.root .bound
  }

private def statementEvidence (graph : Graph) : Array EvidenceItem := Id.run do
  let mut result := #[]
  for index in [0:graph.nodes.size] do
    let node := graph.nodes[index]!
    let id : NodeId := { index }
    result := result.push {
      reference := .statementNode id
      formal := node.provenance.expression
      declaration? := node.provenance.declaration?
    }
    for position in [0:node.arguments.size] do
      let argument := node.arguments[position]!
      result := result.push {
        reference := .statementArgument id position
        formal := argument.source
        declaration? := argument.provenance.declaration?
      }
  return result

private def proofEvidence (plan : ProofPlan) : Array EvidenceItem := Id.run do
  let mut result := #[]
  for stepIndex in [0:plan.steps.size] do
    let step := plan.steps[stepIndex]!
    result := result.push {
      reference := .proofStep stepIndex
      formal := step.application.source
      expected? := some step.application.conclusion
      localContext? := some step.payload.localContext
      declaration? := step.application.provenance.declaration?
    }
    for premiseIndex in [0:step.premises.size] do
      let premise := step.premises[premiseIndex]!
      result := result.push {
        reference := .proofPremise stepIndex premiseIndex
        formal := premise.evidence.payload.proof
        expected? := some premise.descriptor.proposition
        localContext? := some premise.evidence.payload.localContext
      }
  for fallbackIndex in [0:plan.fallbackEvidence.size] do
    let fallback := plan.fallbackEvidence[fallbackIndex]!
    result := result.push {
      reference := .formalFallback fallbackIndex
      formal := fallback.proof
      expected? := some fallback.expected
      localContext? := some fallback.localContext
    }
  return result

private def firstRootStep? (plan : ProofPlan) (predicate : Step -> Bool) :
    Option (Nat × Step) := do
  let tree ← plan.supportForest.find? fun tree => predicate tree.view.step
  return (tree.view.stepId, tree.view.step)

private def pushMove (moves : Array Move) (kind : MoveKind)
    (evidence : Array EvidenceRef) (supports : Array Support := #[])
    (derivation? : Option DerivationApplication := none)
    (primaryEvidence? : Option EvidenceRef := none) : Array Move :=
  moves.push {
    id := moves.size
    kind
    primaryEvidence?
    evidence
    supports
    derivation?
  }

/-- Conventional paragraph order for the conditional-equivalence route.  It
depends only on semantic move roles, so reordering independent `have`s in the
Lean proof does not scramble the reader argument. -/
private def conditionalRoutePriority : MoveKind → Nat
  | .stateSecurityGoal => 0
  | .registeredRule .restrictionApplicationEquation => 10
  | .registeredRule .commonDomainDataProcessing => 20
  | .ignoreCollisionMBO | .registeredRule .ignoreGameMBO => 30
  | .conditionalEquivalenceReduction => 40
  | .remainingBlindWinningObligation => 50
  | .blindWinningEstimate => 60
  | .combineConditionalEquivalenceBlind => 100
  | _ => 70

private def insertRouteMove (move : Move) : List Move → List Move
  | [] => [move]
  | head :: tail =>
      if conditionalRoutePriority move.kind < conditionalRoutePriority head.kind then
        move :: head :: tail
      else
        head :: insertRouteMove move tail

private def orderConditionalRoute (moves : Array Move) : Array Move :=
  let ordered := (moves.foldl (fun result move => insertRouteMove move result) []).toArray
  ordered.mapIdx fun index move => { move with id := index }

private def deduplicateEvidence (references : Array EvidenceRef) : Array EvidenceRef :=
  references.foldl (fun result reference =>
    if result.contains reference then result else result.push reference) #[]

private def hasNodeRole (graph : Graph) (role : NodeRole) : Bool :=
  graph.nodes.any (·.role == role)

private def semanticStepKind (step : Step) : MoveKind :=
  match step.application.role with
  | .conditionalEquivalence => .conditionalEquivalence
  | .conditionalEquivalenceToBlindWinning => .conditionalEquivalenceReduction
  | .blindWinningBound => .blindWinningEstimate
  | .hTechnique => .hTechnique
  | .triangleHybrid => .hybrid
  | .gamePlayingFundamentalLemma => .gameHop
  | .counting => .counting
  | .exactEquivalence => .exactEquivalence
  | .ignoreGameMBO =>
      if hasNodeRole step.semanticGraph (.entity .collisionCondition) then
        .ignoreCollisionMBO
      else
        .registeredRule .ignoreGameMBO
  | role => .registeredRule role

/-- Conventional dependency order for registered sibling moves inside one
support branch.  Parent/child structure is never reordered or inferred from
this priority; the key uses semantic roles, not proof syntax or names. -/
private def detailPriority : MoveKind → Nat
  | .registeredRule .collisionConditionalEquivalence => 0
  | .registeredRule .blindWinningToNonadaptive => 0
  | .registeredRule .conditionalEquivalenceUnderRestriction => 1
  | .registeredRule .nonadaptiveQueriesFixed => 1
  | .registeredRule .collisionProbabilityBound | .registeredRule .collisionMassBound => 2
  | .registeredRule .birthdayBound => 3
  | _ => 100

private def insertDetail (detail : Detail) : List Detail → List Detail
  | [] => [detail]
  | head :: tail =>
      if detailPriority detail.kind < detailPriority head.kind then
        detail :: head :: tail
      else
        head :: insertDetail detail tail

private def orderDetails (details : Array Detail) : Array Detail :=
  (details.foldl (fun result detail => insertDetail detail result) []).toArray

/-- Only conditional-equivalence discourse moves participate in the semantic
deduplication below.  In particular, a collision argument establishing the
base conditional equivalence is not interchangeable with the later rule that
preserves that equivalence under a query restriction. -/
private def isConditionalEquivalenceMove : MoveKind → Bool
  | .conditionalEquivalence => true
  | .registeredRule .conditionalEquivalenceUnderRestriction => true
  | .registeredRule .collisionConditionalEquivalence => true
  | _ => false

private def isConditionalEquivalenceRule : DerivationRule → Bool
  | .establishConditionalEquivalence | .preserveConditionalEquivalence => true
  | _ => false

/-- Named transformations have a stable semantic identity independent of the
concrete expression which applied them.  An unnamed transformation remains
opaque, so source equality is the only sound comparison available for it. -/
private def sameTransformationTerm
    (left right : TransformationTerm) : Bool :=
  match left.declaration?, right.declaration? with
  | some leftDeclaration, some rightDeclaration =>
      leftDeclaration == rightDeclaration && left.operands == right.operands
  | none, none => left.source == right.source
  | _, _ => false

/-- Conditions registered by declaration are compared by that declaration and
its operands.  Opaque predicates deliberately remain source-sensitive. -/
private def sameConditionTerm (left right : ConditionTerm) : Bool :=
  match left, right with
  | .opaque leftSource, .opaque rightSource => leftSource == rightSource
  | .named _ leftDeclaration leftOperands,
      .named _ rightDeclaration rightOperands =>
      leftDeclaration == rightDeclaration && leftOperands == rightOperands
  | _, _ => false

/- Source-insensitive equality for the canonical system/game language.

Different Lean constructions of a query restriction—for example a project
wrapper and the underlying transformed system—are the same semantic object
once the decoder has assigned the same constructors and operands.  Opaque
leaves remain source-sensitive because the backend has no stronger evidence
about them. -/
mutual
  private def sameSystemTerm : SystemTerm → SystemTerm → Bool
    | .opaque leftSource, .opaque rightSource => leftSource == rightSource
    | .named _ leftDeclaration leftOperands,
        .named _ rightDeclaration rightOperands =>
        leftDeclaration == rightDeclaration && leftOperands == rightOperands
    | .uniformRandomFunction _ leftInput leftOutput,
        .uniformRandomFunction _ rightInput rightOutput =>
        leftInput == rightInput && leftOutput == rightOutput
    | .uniformRandomPermutation _ leftAlphabet,
        .uniformRandomPermutation _ rightAlphabet =>
        leftAlphabet == rightAlphabet
    | .presentationQuotient _ leftPresentation,
        .presentationQuotient _ rightPresentation =>
        sameSystemTerm leftPresentation rightPresentation
    | .converterApplication _ leftConverter leftUnderlying,
        .converterApplication _ rightConverter rightUnderlying =>
        leftConverter == rightConverter &&
          sameSystemTerm leftUnderlying rightUnderlying
    | .transform _ leftTransformation leftUnderlying,
        .transform _ rightTransformation rightUnderlying =>
        sameTransformationTerm leftTransformation rightTransformation &&
          sameSystemTerm leftUnderlying rightUnderlying
    | .queryRestriction _ leftBudget leftUnderlying,
        .queryRestriction _ rightBudget rightUnderlying =>
        leftBudget == rightBudget && sameSystemTerm leftUnderlying rightUnderlying
    | .forgetGame _ leftGame, .forgetGame _ rightGame =>
        sameGameTerm leftGame rightGame
    | _, _ => false

  private def sameGameTerm : GameTerm → GameTerm → Bool
    | .opaque leftSource, .opaque rightSource => leftSource == rightSource
    | .named _ leftDeclaration leftOperands,
        .named _ rightDeclaration rightOperands =>
        leftDeclaration == rightDeclaration && leftOperands == rightOperands
    | .enhanceWithMBO _ leftSystem leftCondition,
        .enhanceWithMBO _ rightSystem rightCondition =>
        sameSystemTerm leftSystem rightSystem &&
          sameConditionTerm leftCondition rightCondition
    | .converterApplication _ leftConverter leftUnderlying,
        .converterApplication _ rightConverter rightUnderlying =>
        leftConverter == rightConverter &&
          sameGameTerm leftUnderlying rightUnderlying
    | .transform _ leftTransformation leftUnderlying,
        .transform _ rightTransformation rightUnderlying =>
        sameTransformationTerm leftTransformation rightTransformation &&
          sameGameTerm leftUnderlying rightUnderlying
    | .queryRestriction _ leftBudget leftUnderlying,
        .queryRestriction _ rightBudget rightUnderlying =>
        leftBudget == rightBudget && sameGameTerm leftUnderlying rightUnderlying
    | _, _ => false
end

/-- Two conditional-equivalence conclusions are duplicates only when their
canonical game and target-system operands agree.  This compares elaborated
operands, not theorem names, rendered expressions, or English text. -/
private def sameConditionalEquivalenceConclusion (left right : Claim) : Bool :=
  match left, right with
  | .conditionalEquivalence _ leftGame leftTarget,
      .conditionalEquivalence _ rightGame rightTarget =>
      sameGameTerm leftGame rightGame && sameSystemTerm leftTarget rightTarget
  | _, _ => false

private def duplicateConditionalEquivalenceDetails (left right : Detail) : Bool :=
  isConditionalEquivalenceMove left.kind && isConditionalEquivalenceMove right.kind &&
    match left.derivation?, right.derivation? with
    | some leftDerivation, some rightDerivation =>
        isConditionalEquivalenceRule leftDerivation.rule &&
          isConditionalEquivalenceRule rightDerivation.rule &&
          match leftDerivation.conclusion.claim?, rightDerivation.conclusion.claim? with
          | some leftConclusion, some rightConclusion =>
              sameConditionalEquivalenceConclusion leftConclusion rightConclusion
          | _, _ => false
    | _, _ => false

/-- A registered conditional-equivalence theorem may expand to a more generic
conditional-equivalence theorem whose canonical operands are deliberately
opaque at this boundary.  Equal move kinds plus the macro edge are sufficient
only for this theorem family; other same-kind semantic macros remain visible
as genuine disclosure levels. -/
private def sameConditionalEquivalenceMacroLayer (parent : Detail)
    (support : Support) (child : Detail) : Bool :=
  isConditionalEquivalenceMove parent.kind &&
    support.origin == .macroExpansion && child.kind == parent.kind

/-- Semantic obligations carry more information than generic side conditions.
The score is used only after two details have been shown to have the same
canonical conditional-equivalence conclusion. -/
private def obligationSlotInformation : ObligationSlot → Nat
  | .sideCondition | .custom _ => 0
  | .queryBudget => 1
  | _ => 2

private structure DetailInformation where
  rule : Nat
  slottedObligations : Nat
  claimedObligations : Nat
  obligations : Nat

private def DetailInformation.betterThan
    (candidate existing : DetailInformation) : Bool :=
  if candidate.rule != existing.rule then
    candidate.rule > existing.rule
  else if candidate.slottedObligations != existing.slottedObligations then
    candidate.slottedObligations > existing.slottedObligations
  else if candidate.claimedObligations != existing.claimedObligations then
    candidate.claimedObligations > existing.claimedObligations
  else
    candidate.obligations > existing.obligations

private def detailInformation (detail : Detail) : DetailInformation :=
  match detail.derivation? with
  | none => {
      rule := 0
      slottedObligations := 0
      claimedObligations := 0
      obligations := 0
    }
  | some derivation =>
      let rule := match derivation.rule with
        | .preserveConditionalEquivalence => 2
        | .establishConditionalEquivalence => 1
        | _ => 0
      let slottedObligations := derivation.obligations.foldl
        (fun total obligation => total + obligationSlotInformation obligation.slot) 0
      let claimedObligations := derivation.obligations.countP (fun obligation =>
        obligation.claim?.isSome)
      {
        rule
        slottedObligations
        claimedObligations
        obligations := derivation.obligations.size
      }

/-- Select the presentation-bearing representative of two already established
duplicate details.  Checked evidence and child supports are merged separately. -/
private def preferredDetail (existing candidate : Detail) : Detail :=
  if (detailInformation candidate).betterThan (detailInformation existing) then
    candidate
  else
    existing

/-- Locate a direct child which repeats its parent's canonical CE conclusion.
The search never crosses a support branch: returning the support index keeps
the later splice local to that exact premise or macro expansion. -/
private def equivalentChild? (parent : Detail) : Option (Nat × Nat × Detail) := do
  let supportIndex ← parent.supports.findIdx? fun support =>
    support.children.any fun child =>
      duplicateConditionalEquivalenceDetails parent child ||
        sameConditionalEquivalenceMacroLayer parent support child
  let support := parent.supports[supportIndex]!
  let childIndex ← support.children.findIdx?
    fun child => duplicateConditionalEquivalenceDetails parent child ||
      sameConditionalEquivalenceMacroLayer parent support child
  return (supportIndex, childIndex, support.children[childIndex]!)

private def spliceAbsorbedChild (supports : Array Support)
    (supportIndex childIndex : Nat) (replacement : Array Support) : Array Support :=
  let selected := supports[supportIndex]!
  let remainingChildren := selected.children.eraseIdxIfInBounds childIndex
  let remaining := if remainingChildren.isEmpty then #[] else
    #[{ selected with children := remainingChildren }]
  supports.extract 0 supportIndex ++ replacement ++ remaining ++
    supports.extract (supportIndex + 1) supports.size

mutual
  /-- Normalize one recursive detail postorder.  A semantically transparent
  wrapper is replaced by the richer equal child, but only along that direct
  support branch.  The child's own supports take the wrapper's position, so a
  base argument remains nested beneath the preserved canonical rule. -/
  private partial def normalizeDetail (detail : Detail) : Detail :=
    let supports := detail.supports.map normalizeSupport
    absorbEquivalentChildren { detail with supports }

  /-- Deduplicate equal sibling claims only inside this support group.  Equal
  claims used by different proof premises remain distinct. -/
  private partial def normalizeSupport (support : Support) : Support :=
    let children := support.children.map normalizeDetail
    let children := children.foldl (fun result candidate =>
      match result.findIdx? (duplicateConditionalEquivalenceDetails candidate) with
      | none => result.push candidate
      | some index =>
          let existing := result[index]!
          let preferred := preferredDetail existing candidate
          let merged := normalizeDetail {
            preferred with
            evidence := deduplicateEvidence (existing.evidence ++ candidate.evidence)
            supports := preferred.supports ++
              (if preferred.primaryEvidence == existing.primaryEvidence then
                candidate.supports
              else
                existing.supports)
          }
          result.set! index merged) #[]
    { support with children := orderDetails children }

  private partial def absorbEquivalentChildren (detail : Detail) : Detail :=
    match equivalentChild? detail with
    | none => detail
    | some (supportIndex, childIndex, child) =>
        -- A direct same-role macro child is the checked implementation of the
        -- public outer step.  Keep the outer step's reader-facing operands and
        -- splice in the child's mathematical supports; otherwise wrapper
        -- expansion can replace a concrete game by anonymous `G₁`/`T`
        -- placeholders.  For ordinary duplicate premises, retain the richer
        -- representative selected by canonical obligation information.
        let preferred :=
          if !duplicateConditionalEquivalenceDetails detail child &&
              sameConditionalEquivalenceMacroLayer detail
              detail.supports[supportIndex]! child then detail
          else preferredDetail detail child
        let absorbedBranchEvidence := detail.supports[supportIndex]!.evidence
        let supports := spliceAbsorbedChild detail.supports supportIndex childIndex
          child.supports
        absorbEquivalentChildren {
          preferred with
          evidence := deduplicateEvidence
            (detail.evidence ++ absorbedBranchEvidence ++ child.evidence)
          supports := supports.map normalizeSupport
        }
end

private def decodeStep? (profile : DecoderProfile) (step : Step) : MetaM
    (Option DerivationApplication) :=
  withLCtx step.payload.localContext #[] do
    decodeDerivation? profile step.application.source

mutual
  /-- Convert one recursively planned proof-rule application into a disclosure
  node without reconstructing ancestry from numeric depths. -/
  private partial def detailOfSupportTree (profile : DecoderProfile)
      (tree : SupportTree) : MetaM Detail := do
    let step := tree.view.step
    let reference := .proofStep tree.view.stepId
    let supports ← supportsOfSupportTree profile tree
    return normalizeDetail {
      kind := semanticStepKind step
      semanticDepth := step.semanticDepth
      primaryEvidence := reference
      evidence := #[reference]
      supports
      derivation? := ← decodeStep? profile step
    }

  /-- Preserve the direct premise and macro-expansion branches of a recursive
  plan node.  Fallback wrappers have already been promoted transparently by
  `ProofPlan.supportForest`; their exact leaves remain in the evidence index. -/
  private partial def supportsOfSupportTree (profile : DecoderProfile)
      (tree : SupportTree) : MetaM (Array Support) := do
    let stepId := tree.view.stepId
    let step := tree.view.step
    let mut result := #[]
    for proofOrdinal in [0:step.premises.size] do
      let premise := step.premises[proofOrdinal]!
      let key : ObligationKey := {
        telescopePosition := premise.descriptor.position
        proofOrdinal
      }
      let childTrees := tree.childrenForPremise key
      unless childTrees.isEmpty do
        let children ← childTrees.mapM (detailOfSupportTree profile)
        let slot? := tree.view.derivation?.bind fun derivation =>
          (derivation.obligations.find? (·.key == key)).map (·.slot)
        result := result.push (normalizeSupport {
          origin := .premise premise.descriptor.position premise.descriptor.role
            premise.descriptor.salience slot?
          evidence := #[.proofPremise stepId proofOrdinal]
          children
        })
    let macroChildren := tree.macroChildren
    unless macroChildren.isEmpty do
      let children ← macroChildren.mapM (detailOfSupportTree profile)
      result := result.push (normalizeSupport {
        origin := .macroExpansion
        evidence := #[.proofStep stepId]
        children
      })
    return result
end

/-- Plan conventional cryptographic discourse from typed roles.

The specialized chain is produced only when the checked plan contains both a
`conditionalEquivalenceToBlindWinning` step and a `blindWinningBound` step.
Merely mentioning a condition, a theorem name, or a local variable cannot
trigger it. -/
def ofGraphAndPlan (graph : Graph) (plan : ProofPlan)
    (profile : DecoderProfile := {}) : MetaM Document := do
  let presentations := profile.theoremPresentations.filter
    (fun presentation => presentation.declaration == plan.declaration)
  if presentations.size > 1 then
    throwError "multiple theorem presentations are registered for {plan.declaration}"
  let theoremPresentation? := presentations[0]?
  if let some presentation := theoremPresentation? then
    validateTheoremPresentation plan.theoremType presentation
  let security := securityContext? graph
  let rootClaim? ← match graph.rootNode? with
    | some node => decodeClaim? profile node.provenance.expression
    | none => pure none
  let mut moves := #[]
  if let some context := security then
    let mut refs := #[.statementNode context.proposition]
    if let some advantage := context.advantage? then
      refs := refs.push (.statementNode advantage)
    if let some source := context.sourceSystem? then
      refs := refs.push (.statementNode source)
    if let some target := context.targetSystem? then
      refs := refs.push (.statementNode target)
    if let some description := context.sourceDescription? then
      refs := refs.push (.statementNode description.base)
      if let some restriction := description.queryRestriction? then
        refs := refs.push (.statementNode restriction)
    if let some description := context.targetDescription? then
      refs := refs.push (.statementNode description.base)
      if let some restriction := description.queryRestriction? then
        refs := refs.push (.statementNode restriction)
    if let some budget := context.queryBudget? then
      refs := refs.push budget.evidenceRef
    if let some bound := context.bound? then
      refs := refs.push bound.evidenceRef
    moves := pushMove moves .stateSecurityGoal (deduplicateEvidence refs)
  else if rootClaim?.isSome then
    -- A construction is a security root even though it is not itself an
    -- advantage comparison.  Its decoded claim supplies the opening, while
    -- the root statement node supplies the exact checked evidence.
    moves := pushMove moves .stateSecurityGoal #[.statementNode graph.root]

  let ceReduction? := firstRootStep? plan fun step =>
    step.application.role == .conditionalEquivalenceToBlindWinning
  let blindBound? := firstRootStep? plan fun step =>
    step.application.role == .blindWinningBound

  -- Preserve the checked order of root proof moves.  Every registered premise
  -- and macro expansion remains in the recursive support tree attached to its
  -- actual parent; numeric semantic depth is no longer used to infer ancestry.
  for tree in plan.supportForest do
    let root := ← detailOfSupportTree profile tree
    let step := tree.view.step
    if step.application.role == .conditionalEquivalenceToBlindWinning then
      moves := pushMove moves .conditionalEquivalenceReduction root.evidence
        root.supports root.derivation? (some root.primaryEvidence)
      moves := pushMove moves .remainingBlindWinningObligation root.evidence
        #[] root.derivation? (some root.primaryEvidence)
    else
      moves := pushMove moves root.kind root.evidence root.supports root.derivation?
        (some root.primaryEvidence)

  if let some (ceIndex, _) := ceReduction? then
    if let some (blindIndex, _) := blindBound? then
      let mut refs := #[.proofStep ceIndex, .proofStep blindIndex]
      if let some context := security then
        refs := refs.push (.statementNode context.proposition)
      moves := pushMove moves .combineConditionalEquivalenceBlind refs

  if ceReduction?.isSome && blindBound?.isSome then
    moves := orderConditionalRoute moves

  if plan.steps.isEmpty && plan.hasFallback then
    moves := pushMove moves .formalFallback
      (Array.range plan.fallbackEvidence.size |>.map fun index => .formalFallback index)

  return {
    security
    rootClaim?
    declarationNotations := profile.declarationNotations
    theoremPresentation?
    planKind := plan.kind
    moves
    evidenceIndex := statementEvidence graph ++ proofEvidence plan
  }

end Informalization.Semantics.Discourse
