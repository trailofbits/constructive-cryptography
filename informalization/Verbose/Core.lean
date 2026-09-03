import LanguageDesign
import Lean

/-!
# Checked sentence execution

The parser-facing layer calls `runSentence` with one fixed descriptor and one
typed backend action.  Execution is transactional, the declared proof status
is checked, and successful steps emit typed `InfoTree` metadata.
-/

declare_syntax_cat verboseReference
syntax term:max (&"noted" str)? : verboseReference

register_option cryptoVerbose.applicationProfile : String := {
  defValue := ""
  descr := "select an application-scoped source license for controlled prose"
}

namespace CryptoLanguage.Verbose

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign

structure SentenceFormId where
  language : Name
  family : Name
  form : Name
deriving Repr, BEq, Hashable, Inhabited

inductive SuggestionPolicy
  | exactGoal
  | contextualTemplate
  | selectionRequired
deriving Repr, BEq, Inhabited

structure SentenceDescriptor where
  formId : SentenceFormId
  ruleId : RuleId
  act : SpeechAct
  effect : SentenceEffectSchema
  schema : RuleSchema
  summary : String
  backendDeclaration : Name
  sourceAttestation : Corpus.Attestation
  supportingSourceAttestations : Array Corpus.Attestation := #[]
  diagnosticId : Name
  suggestionPolicy : SuggestionPolicy
  routineClosures : Array Name := #[]
  /-- When routine receipts are present, the checked assertion proof must be
  headed by one of these registered mathematical combinators.  This prevents
  an opaque wrapper from retaining a routine proof as an ignored argument. -/
  routineRootCombinators : Array Name := #[]
  /-- A fixed-effect sentence may consume an operand literally called
  `proof` only as an immediate argument of one of these registered
  combinators.  Empty means that such an operand is not licensed. -/
  fixedProofCombinators : Array Name := #[]
  supportsNamedFact : Bool := false
deriving Repr, Inhabited

/-- Imported modules must contribute their sentence declarations. Lean's bare
`TagAttribute` intentionally forgets imported tags, so a persistent companion
extension owns the actual catalog. -/
initialize sentenceRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun declarations declaration =>
      if declarations.contains declaration then declarations
      else declarations.push declaration
    addImportedFn := fun imported =>
      imported.flatten.foldl (init := #[]) fun declarations declaration =>
        if declarations.contains declaration then declarations
        else declarations.push declaration
  }

initialize sentenceAttribute : TagAttribute ←
  registerTagAttribute `crypto_verbose_sentence
    "register a serializable Crypto Verbose sentence descriptor" fun declaration => do
      let information ← getConstInfo declaration
      unless information.type.isConstOf ``SentenceDescriptor do
        throwError "declaration {declaration} must have type SentenceDescriptor"
      modifyEnv fun environment => sentenceRegistry.addEntry environment declaration

/-- Evaluate all descriptor declarations registered in the current
environment.  `evalConstCheck` rejects a mis-typed registration. -/
unsafe def registeredSentenceDescriptors {m : Type → Type} [Monad m] [MonadEnv m]
    [MonadError m] [MonadOptions m] : m (Array SentenceDescriptor) := do
  let environment ← getEnv
  let declarations := (sentenceRegistry.getState environment).qsort Name.quickLt
  declarations.mapM fun declaration => do
    let descriptor ←
      evalConstCheck SentenceDescriptor ``SentenceDescriptor declaration
    unless environment.contains descriptor.backendDeclaration do
      throwError "sentence {descriptor.ruleId.layer}.{descriptor.ruleId.family}.{descriptor.ruleId.rule} names missing backend declaration {descriptor.backendDeclaration}"
    pure descriptor

structure ReferenceSyntax where
  term : Term
  readerNote? : Option String

structure OperandInput where
  role : ArgumentRole
  reference : ReferenceSyntax

/-- A backend action carries the declaration identity promised by the
descriptor.  Identity checking rejects the simplest parser/backend mismatch;
the transaction's checked-effect and evidence validation is the authoritative
test that the action actually established the advertised result. -/
structure BackendAction where
  private mk ::
  declaration : Name
  execute : TacticM Unit

private def authorizedBackendAction (declaration : Name)
    (execute : TacticM Unit) : BackendAction :=
  BackendAction.mk declaration execute

/-- Construct a backend capability from one syntactically fixed function
head.  The declaration identity and executable action are generated from the
same identifier, so a parser cannot label an arbitrary closure as a trusted
backend. -/
syntax "backendAction " ident "(" term,* ")" : term
macro "backendAction " backend:ident "(" arguments:term,* ")" : term => do
  let declarationTerm : Term := ⟨Syntax.node .none
    ``Lean.Parser.Term.doubleQuotedName #[
      Syntax.atom .none "`", Syntax.atom .none "`", backend]⟩
  let execute := Syntax.mkApp backend arguments.getElems
  `(authorizedBackendAction $declarationTerm $execute)

/-- A name produced by a sentence is not an input operand.  Its optional type
is checked only after Lean has introduced the local in the new goal context. -/
structure BindingInput where
  role : ArgumentRole
  name : Name
  declaredType? : Option Term := none

structure ElaboratedOperand where
  role : ArgumentRole
  expr : Expr
  type : Expr
  note? : Option String
deriving TypeName

structure ElaboratedBinding where
  role : ArgumentRole
  name : Name
  fvarId : FVarId
  type : Expr
deriving TypeName

structure RuleInvocation where
  ruleId : RuleId
  operands : Array ElaboratedOperand
deriving TypeName

inductive ExpectedEffect
  | closeMain
  | replaceMain (count : Nat)
  | addLocals (names : Array Name)
  | guardUnchanged
deriving Repr, BEq, Inhabited

structure LocalSnapshot where
  id : FVarId
  userName : Name
  type : Expr
  value? : Option Expr
deriving TypeName

structure GoalSnapshot where
  id : MVarId
  tag : Name
  target : Expr
  locals : Array LocalSnapshot
deriving TypeName

structure ResidualGoalEvent where
  role : ObligationRole
  tag : Name
  id : MVarId
  target : Expr
deriving TypeName

inductive AssertionDestination
  | closeMain
  | localFact (name : Name)
deriving Repr, BEq, Inhabited, TypeName

/-- The kernel-checked root retained only during lowering.  Public sentence
events contain a non-authoritative anchor and exact conclusion instead. -/
structure RoutineEvidenceAnchor where
  producer : Name
  goalClass : Name
  proofGoal : MVarId
  proposition : Expr
  proof : Expr
  inferredType : Expr
  declarations : Array Name
  proofDeclarations : Array Name
  cost : Nat
deriving TypeName

structure CheckedEvidenceRoot where
  proof : Expr
  inferredType : Expr
  routineSupport : Array RoutineEvidenceAnchor := #[]
deriving TypeName

structure CheckedAssertion where
  invocation : RuleInvocation
  exactConclusion : Expr
  evidenceRoot : CheckedEvidenceRoot
deriving TypeName

structure EvidenceAnchor where
  proofHash : UInt64
  inferredTypeHash : UInt64
  routineProducers : Array Name := #[]
  routineProofHashes : Array UInt64 := #[]
deriving Repr, BEq, Inhabited, TypeName

/-- Exact application occurrence selected by the elaborator.  Application-
scoped prose licenses compare this complete key; a rule identifier alone is
not sufficient authority. -/
structure ApplicationOccurrenceKey where
  profile : String
  declaration : Name
  backendDeclaration : Name
  ruleId : RuleId
deriving Repr, BEq, Inhabited, TypeName

structure AssertionOccurrenceSummary where
  invocation : RuleInvocation
  exactConclusion : Expr
  destination : AssertionDestination
  evidenceAnchor : EvidenceAnchor
  applicationKey? : Option ApplicationOccurrenceKey := none
deriving TypeName

inductive GoalEffect
  | closeMain
  | replaceMain (obligations : Array ResidualGoalEvent)
  | addLocalFact (role : ArgumentRole) (name : Name) (exactType : Expr)
  | introduce (bindings : Array ElaboratedBinding)
  | guardUnchanged
deriving TypeName

structure SentenceEvent where
  schemaVersion : Nat
  formId : SentenceFormId
  ruleId : RuleId
  act : SpeechAct
  invocation : RuleInvocation
  assertion? : Option AssertionOccurrenceSummary
  intrinsicEffect : GoalEffect
  outerEffect : GoalEffect
  goalsBefore : Array GoalSnapshot
  goalsAfter : Array GoalSnapshot
  residualGoals : Array ResidualGoalEvent
  localsAdded : Array FVarId
  bindingsAdded : Array ElaboratedBinding
  sourceRange? : Option Syntax.Range
  guidance : Array PresentationAnnotation
  sourceAttestation : Corpus.Attestation
  supportingSourceAttestations : Array Corpus.Attestation := #[]
  applicationKey? : Option ApplicationOccurrenceKey := none
  source : Syntax
deriving TypeName

/- The complete event is wrapped only after the lowering transaction has
validated it.  The wrapper, rather than a transferable field inside the
public payload, is the authority consumed by `Fact NAME:`. -/
private structure AuthenticatedSentenceEvent where
  event : SentenceEvent
  factNonce? : Option Name := none
deriving TypeName

private def factDestinationOption : Name := `cryptoVerbose.internal.factDestination
private def factSourceOption : Name := `cryptoVerbose.internal.factSource
private def factNonceOption : Name := `cryptoVerbose.internal.factNonce

/-- Minimal persistent whole-declaration trace.  Full checked payloads remain
in the `InfoTree`; this index exists so command elaborators and regression
tests can verify passage order after the theorem command has finished. -/
structure SentenceTraceEntry where
  declaration : Name
  ruleId : RuleId
  backendDeclaration : Name
  operandFingerprints : Array (ArgumentRole × UInt64 × UInt64) := #[]
  exactConclusionHash? : Option UInt64 := none
  assertionDestination? : Option AssertionDestination := none
  routineProducers : Array Name := #[]
  routineProofHashes : Array UInt64 := #[]
  sourceAttestation : Corpus.Attestation
  supportingSourceAttestations : Array Corpus.Attestation := #[]
  applicationKey? : Option ApplicationOccurrenceKey := none
  sourceText : String
deriving Repr, BEq, Inhabited

initialize sentenceTraceRegistry :
    SimplePersistentEnvExtension SentenceTraceEntry (Array SentenceTraceEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun entries entry => entries.push entry
    addImportedFn := fun imported => imported.flatten
  }

def sentenceTraceFor (environment : Environment) (declaration : Name) :
    Array SentenceTraceEntry :=
  (sentenceTraceRegistry.getState environment).filter (·.declaration == declaration)

structure PresentationEvent where
  schemaVersion : Nat
  goalsBefore : Array GoalSnapshot
  goalsAfter : Array GoalSnapshot
  sourceRange? : Option Syntax.Range
  guidance : Array PresentationAnnotation
deriving TypeName

initialize registerTraceClass `CryptoLanguage.Verbose.sentence
initialize registerTraceClass `CryptoLanguage.Verbose.presentation

private def snapshotGoals : TacticM (Array GoalSnapshot) := do
  (← getGoals).toArray.mapM fun goal => do
    goal.withContext do
      let locals := (← getLCtx).decls.toList.reduceOption.toArray.map fun decl =>
        { id := decl.fvarId, userName := decl.userName, type := decl.type,
          value? := decl.value? true }
      pure ⟨goal, ← goal.getTag, ← goal.getType, locals⟩

private def sameLocalSnapshot (left right : LocalSnapshot) : Bool :=
  left.id == right.id && left.userName == right.userName && left.type == right.type &&
    left.value? == right.value?

private def sameGoalSnapshot (left right : GoalSnapshot) : Bool :=
  left.id == right.id && left.tag == right.tag && left.target == right.target &&
    left.locals.size == right.locals.size &&
    (left.locals.zip right.locals).all fun pair => sameLocalSnapshot pair.1 pair.2

private def preservedTail (before after : Array GoalSnapshot)
    (newMainGoals : Nat) : Bool :=
  let oldTail := before.extract 1 before.size
  let newTail := after.extract newMainGoals after.size
  oldTail.size == newTail.size &&
    (oldTail.zip newTail).all fun pair => sameGoalSnapshot pair.1 pair.2

private def addedLocalsMatch (before after : GoalSnapshot)
    (names : Array Name) : Bool :=
  before.locals.size + names.size == after.locals.size &&
    (before.locals.zip (after.locals.extract 0 before.locals.size)).all
      fun pair => pair.1.id == pair.2.id &&
    ((after.locals.extract before.locals.size after.locals.size).map (·.userName)) == names

private def expectedMatchesSchema (schema : EffectSchema)
    (expected : ExpectedEffect) : Bool :=
  match schema, expected with
  | .closeMain, .closeMain => true
  | .replaceMain obligations _, .replaceMain count => obligations.size == count
  | .addLocalFact _, .addLocals names => names.size == 1
  | .introduce bindings, .addLocals names => bindings.size == names.size
  | .guardUnchanged, .guardUnchanged => true
  | _, _ => false

private def descriptorIsConsistent (descriptor : SentenceDescriptor) : Bool :=
  descriptor.ruleId == descriptor.schema.id &&
    descriptor.act == descriptor.schema.act &&
    match descriptor.effect with
    | .fixed effect => effect == descriptor.schema.effect
    | .assertion => descriptor.act == .assertion &&
        descriptor.schema.effect == .closeMain && descriptor.schema.outputs.isEmpty

private def operandsMatchSchema (schema : RuleSchema)
    (inputs : Array OperandInput) : Bool :=
  schema.inputs.size == inputs.size &&
    (schema.inputs.zip inputs).all fun pair =>
      pair.1.role == pair.2.role && pair.1.provision == .requireExplicit

private partial def containsConstName (expression : Expr) (wanted : Name) : Bool :=
  match expression with
  | .const name _ => name == wanted
  | .app function argument =>
      containsConstName function wanted || containsConstName argument wanted
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsConstName domain wanted || containsConstName body wanted
  | .letE _ type value body _ =>
      containsConstName type wanted || containsConstName value wanted ||
        containsConstName body wanted
  | .mdata _ body | .proj _ _ body => containsConstName body wanted
  | _ => false

private def containsAnyConst (expression : Expr) (wanted : Array Name) : Bool :=
  wanted.any (containsConstName expression)

private def isFunctionType (type : Expr) : MetaM Bool := do
  return (← whnf type).isForall

private def isDataType (type : Expr) : MetaM Bool :=
  return !(← isProp type)

private def hasDirectDomainShape (type : Expr) : Bool :=
  let type := type.consumeMData
  if type.isForall then false else
  let head? := type.getAppFn.consumeMData.constName?
  ![``List, ``Option, ``Array, ``Prod, ``Sigma, ``PSigma, ``Subtype].any
    (head? == some ·)

private def hasDirectDomainHead (type : Expr) (allowed : Array Name) : Bool :=
  let type := type.consumeMData
  !type.isForall && type.getAppFn.consumeMData.constName?.any allowed.contains

private def conceptMatchesOperand (concept : ConceptId)
    (operand : ElaboratedOperand) : MetaM Bool := do
  if concept == Ontology.proof || concept == Ontology.construction ||
      concept == Ontology.equation || concept == Ontology.compatibility ||
      concept == Ontology.support || concept == Ontology.equality then
    return ← isProp operand.type
  if concept == Ontology.proposition then
    return ← isProp operand.expr
  if concept == Ontology.alphabet then
    return operand.type.isSort
  if concept == Ontology.horizon then
    return ← isDefEq operand.type (mkConst ``Nat)
  if concept == Ontology.bound then
    let head? := operand.type.getAppFn.constName?
    return head? == some `Real || head? == some `NNReal ||
      head? == some `ENNReal
  if concept == Ontology.queryList then
    return (← whnf operand.type).getAppFn.constName? == some ``List
  if concept == Ontology.object then
    return !(← isProp operand.type)
  let type := operand.type
  if concept == Ontology.pdsLaw || concept == Ontology.probabilisticSystem then
    return hasDirectDomainShape type && hasDirectDomainHead type #[`RandomSystems.PDS,
      `Probability.Distribution, `Probability.Distribution.ProbDist]
  if concept == Ontology.game || concept == Ontology.probabilisticGame then
    return hasDirectDomainShape type && hasDirectDomainHead type #[`RandomSystems.PDG,
      `RandomSystems.System.DDG]
  if concept == Ontology.system || concept == Ontology.deterministicSystem ||
      concept == Ontology.commonDomainPresentation ||
      concept == Ontology.commonDomainProbabilityPresentation ||
      concept == Ontology.commonDomainSystem ||
      concept == Ontology.commonDomainProbabilitySystem ||
      concept == Ontology.ambientSystem ||
      concept == Ontology.ambientProbabilityPresentation then
    return hasDirectDomainShape type && hasDirectDomainHead type #[`RandomSystems.PDS, `RandomSystems.System.DDS,
      `RandomSystems.CommonDomain.Presentation,
      `RandomSystems.CommonDomain.ProbabilityPresentation,
      `RandomSystems.CommonDomain.RandomSystem,
      `RandomSystems.CommonDomain.ProbabilityRandomSystem,
      `RandomSystems.Ambient.RandomSystem]
  if concept == Ontology.monotoneCondition ||
      concept == Ontology.monotoneBinaryOutput || concept == Ontology.condition then
    return containsAnyConst type #[`RandomSystems.System.MonotoneCondition,
      `RandomSystems.System.MonotoneOutput,
      `RandomSystems.System.IsPrefixUpperSet] ||
      (containsConstName type ``Subtype &&
        containsConstName type ``List)
  if concept == Ontology.probabilityLaw then
    return containsAnyConst type #[`Probability.Distribution,
      `Probability.Distribution.ProbDist]
  if concept == Ontology.predicate || concept == Ontology.collisionEvent ||
      concept == Ontology.systemTransform || concept == Ontology.gameTransform then
    return ← isFunctionType type
  if concept == Ontology.protocol || concept == Ontology.simulator ||
      concept == Ontology.context || concept == Ontology.converter ||
      concept == Ontology.intermediate || concept == Ontology.distinguisherClass ||
      concept == Ontology.test then
    return ← isDataType type
  return false

private def constructedPatternType? (pattern : TypePattern)
    (operands : Array ElaboratedOperand) : MetaM (Option Expr) := do
  if pattern.operandRoles.isEmpty then return none
  let mut arguments := #[]
  for dependencyRole in pattern.operandRoles do
    let some operand := operands.find? (·.role == dependencyRole)
      | return none
    arguments := arguments.push operand.expr
  try
    return some (← mkAppM pattern.builder arguments)
  catch _ =>
    return none

private def typePatternMatchesOperand (pattern : TypePattern)
    (concept : ConceptId) (operand : ElaboratedOperand)
    (operands : Array ElaboratedOperand) : MetaM Bool := do
  let sortMatches ← match pattern.expectedSort with
    | .proposition => isProp operand.type
    | .data => isDataType operand.type
    | .anySort => pure true
  unless sortMatches && (← conceptMatchesOperand concept operand) do return false
  if pattern.operandRoles.isEmpty then
    return pattern.builder == concept.name
  let some expectedType ← constructedPatternType? pattern operands
    | return false
  return ← isDefEqGuarded operand.type expectedType

private def validateOperandConcepts (schema : RuleSchema)
    (operands : Array ElaboratedOperand) : MetaM Unit := do
  for (input, operand) in schema.inputs.zip operands do
    unless ← typePatternMatchesOperand input.typePattern input.concept operand
        operands do
      throwError m!"operand `{input.role.name}` of type {operand.type} does not inhabit the registered `{input.concept.name}` ontology class"

private def bindingsMatchSchema (schema : RuleSchema)
    (bindings : Array BindingInput) : Bool :=
  schema.outputs.size == bindings.size &&
    (schema.outputs.zip bindings).all fun pair => pair.1.role == pair.2.role

private def obligationTargetMatches (role : ObligationRole)
    (target : Expr) : MetaM Bool := do
  let target ← instantiateMVars target
  let head? := target.getAppFn.constName?
  return match role.name with
  | `membership => head? == some ``Membership.mem
  | `distance | `firstLeg | `secondLeg => head? == some ``LE.le
  | `blindWinning =>
      head? == some ``LE.le &&
        containsConstName target `RandomSystems.PDG.blindSupWinProb
  | `fixedEnvironment =>
      head? == some ``LE.le &&
        containsConstName target `RandomSystems.PDG.winningMass
  | `goodRatio => containsConstName target `RandomSystems.PDS.transcriptSystemFactor
  | `idealBadMass => containsConstName target `Probability.probBad
  | _ => false

private def residualsMatchSchema (schema : EffectSchema)
    (after : Array GoalSnapshot) : TacticM Bool := do
  let .replaceMain obligations _ := schema | return true
  if obligations.size > after.size then return false
  for (obligation, goal) in obligations.zip (after.extract 0 obligations.size) do
    unless goal.tag == obligation.name do return false
    unless ← obligationTargetMatches obligation goal.target do return false
  return true

private def conceptMatchesType (concept : ConceptId) (type : Expr) : MetaM Bool := do
  let type ← instantiateMVars type
  if concept == Ontology.proposition then
    return ← isProp type
  if concept == Ontology.horizon then
    return ← isDefEq type (mkConst ``Nat)
  if concept == Ontology.object then
    return !(← isProp type)
  if concept == Ontology.pdsLaw || concept == Ontology.probabilisticSystem then
    return hasDirectDomainShape type && hasDirectDomainHead type #[`RandomSystems.PDS,
      `Probability.Distribution, `Probability.Distribution.ProbDist]
  if concept == Ontology.game || concept == Ontology.probabilisticGame then
    return hasDirectDomainShape type && hasDirectDomainHead type #[`RandomSystems.PDG,
      `RandomSystems.System.DDG]
  if concept == Ontology.environment then
    let type ← whnf type
    let .forallE _ domain range _ := type | return false
    let domain ← whnf domain
    let range ← whnf range
    return domain.getAppFn.constName? == some ``List &&
      containsConstName domain ``Option &&
      range.getAppFn.constName? == some ``Option
  if concept == Ontology.probabilisticGame then
    return containsAnyConst type #[`RandomSystems.PDG,
      `RandomSystems.System.DDG]
  if concept == Ontology.monotoneCondition then
    return containsAnyConst type #[`RandomSystems.System.MonotoneCondition,
      `RandomSystems.System.MonotoneOutput,
      `RandomSystems.System.IsPrefixUpperSet] ||
      (containsConstName type ``Subtype &&
        containsConstName type ``List)
  return false

private def typePatternMatchesType (pattern : TypePattern)
    (concept : ConceptId) (type : Expr)
    (operands : Array ElaboratedOperand) : MetaM Bool := do
  let sortMatches ← match pattern.expectedSort with
    | .proposition => isProp type
    | .data => isDataType type
    | .anySort => pure true
  unless sortMatches && (← conceptMatchesType concept type) do return false
  if pattern.operandRoles.isEmpty then
    return pattern.builder.isAnonymous || pattern.builder == concept.name
  let some expectedType ← constructedPatternType? pattern operands
    | return false
  return ← isDefEqGuarded type expectedType

private def validateBindings (descriptor : SentenceDescriptor)
    (operands : Array ElaboratedOperand) (inputs : Array BindingInput)
    (before after : Array GoalSnapshot) : TacticM Unit := do
  unless bindingsMatchSchema descriptor.schema inputs do
    throwError "the sentence's produced names disagree with its registered binding roles"
  let some beforeMain := before[0]?
    | throwError "a controlled sentence requires an active goal"
  let some afterMain := after[0]?
    | if inputs.isEmpty then return else
        throwError "the sentence closed the goal instead of introducing its registered names"
  let added := afterMain.locals.extract beforeMain.locals.size afterMain.locals.size
  unless added.size == inputs.size do
    throwError "the sentence introduced a different number of local objects than its schema declares"
  for ((bindingSchema, input), localSnapshot) in
      (descriptor.schema.outputs.zip inputs).zip added do
    unless localSnapshot.userName == input.name do
      throwError m!"the sentence was required to introduce `{input.name}`, but introduced `{localSnapshot.userName}`"
    unless ← typePatternMatchesType bindingSchema.typePattern
        bindingSchema.concept localSnapshot.type operands do
      throwError m!"the introduced local `{input.name}` of type {localSnapshot.type} does not have the registered `{bindingSchema.concept.name}` class"
    if let some declaredType := input.declaredType? then
      afterMain.id.withContext do
        let expected ← elabTerm declaredType none
        unless ← isDefEq localSnapshot.type expected do
          throwError m!"the introduced local `{input.name}` does not have its stated type"

private def validateEffect (schema : EffectSchema) (expected : ExpectedEffect)
    (before after : Array GoalSnapshot) : TacticM Unit := do
  if before.isEmpty then
    throwError "a controlled sentence requires an active goal"
  match expected with
  | .closeMain =>
      unless after.size + 1 == before.size && preservedTail before after 0 do
        throwError "the sentence claims to close the current goal, but its backend produced a different goal transition"
  | .replaceMain count =>
      unless after.size + 1 == before.size + count &&
          preservedTail before after count do
        throwError "the sentence backend did not produce the declared number of residual obligations"
      unless ← residualsMatchSchema schema after do
        throwError "the sentence backend produced residual goals whose tags or propositions do not match the registered mathematical obligations"
  | .addLocals names =>
      let localsMatch := match before[0]?, after[0]? with
        | some beforeMain, some afterMain =>
            addedLocalsMatch beforeMain afterMain names
        | _, _ => false
      unless after.size == before.size && preservedTail before after 1 &&
          localsMatch do
        throwError "the sentence claims to introduce named local information, but its backend changed the goal structure"
  | .guardUnchanged =>
      unless after.size == before.size &&
          (before.zip after).all fun pair => sameGoalSnapshot pair.1 pair.2 do
        throwError "a goal announcement must leave the proof state unchanged"

private def elaborateOperands (inputs : Array OperandInput) : TacticM (Array ElaboratedOperand) :=
  withMainContext do
    inputs.mapM fun input => do
      if input.reference.term.raw.isNatLit?.isSome then
        throwError m!"operand `{input.role.name}` is an overloaded numeric literal; give it an explicit type so semantic metadata and backend checking cannot diverge"
      /- Operand classification is observational: it must not constrain the
      proof state's metavariables before the registered backend elaborates the
      same syntax against the exact expected relation. -/
      let (expr, type) ← withoutModifyingState do
        let local? ← match input.reference.term with
          | `(term| $identifier:ident) =>
              try
                pure (some (← getLocalDeclFromUserName identifier.getId))
              catch _ => pure none
          | _ => pure none
        match local? with
        | some declaration =>
            -- Preserve the already elaborated local declaration verbatim.
            -- Re-elaborating a higher-rank proof name without an expected
            -- type can instantiate its implicit binders with fresh
            -- metavariables even though the local context is fully checked.
            pure (mkFVar declaration.fvarId, ← instantiateMVars declaration.type)
        | none =>
            let expr ← instantiateMVars (← elabTerm input.reference.term none)
            let type ← instantiateMVars (← inferType expr)
            pure (expr, type)
      if expr.hasMVar || type.hasMVar then
        throwError m!"operand `{input.role.name}` contains unresolved metavariables\nexpression: {expr}\ntype: {type}"
      pure ⟨input.role, expr, type, input.reference.readerNote?⟩

private def residualGoalEvents (schema : EffectSchema)
    (after : Array GoalSnapshot) : Array ResidualGoalEvent :=
  match schema with
  | .replaceMain obligations _ =>
      (obligations.zip (after.extract 0 obligations.size)).map fun pair =>
        ⟨pair.1, pair.2.tag, pair.2.id, pair.2.target⟩
  | _ => #[]

private def addedLocalIds (before after : Array GoalSnapshot) : Array FVarId :=
  match before[0]?, after[0]? with
  | some beforeMain, some afterMain =>
      (afterMain.locals.extract beforeMain.locals.size afterMain.locals.size).map (·.id)
  | _, _ => #[]

private def elaboratedBindings (descriptor : SentenceDescriptor)
    (inputs : Array BindingInput) (before after : Array GoalSnapshot) :
    Array ElaboratedBinding :=
  match before[0]?, after[0]? with
  | some beforeMain, some afterMain =>
      let added := afterMain.locals.extract beforeMain.locals.size afterMain.locals.size
      ((descriptor.schema.outputs.zip inputs).zip added).map fun pair =>
        ⟨pair.1.1.role, pair.1.2.name, pair.2.id, pair.2.type⟩
  | _, _ => #[]

private def goalEffect (schema : EffectSchema) (expected : ExpectedEffect)
    (bindings : Array ElaboratedBinding) (after : Array GoalSnapshot) : GoalEffect :=
  match expected with
  | .closeMain => .closeMain
  | .replaceMain _ => .replaceMain (residualGoalEvents schema after)
  | .addLocals _ => .introduce bindings
  | .guardUnchanged => .guardUnchanged

private def effectiveSourceAttestations (descriptor : SentenceDescriptor) :
    TacticM (Corpus.Attestation × Array Corpus.Attestation ×
      Option ApplicationOccurrenceKey) := do
  let profile := (← getOptions).get `cryptoVerbose.applicationProfile ""
  let declaration? ← Lean.Elab.Term.getDeclName?
  let applicationAttestation? := declaration?.bind fun declaration =>
    Corpus.applicationAttestationFor? profile declaration
      descriptor.backendDeclaration descriptor.ruleId
  let primary := applicationAttestation?.getD descriptor.sourceAttestation
  unless primary.isPubliclyLicensed do
    throwError m!"the sentence `{descriptor.ruleId.layer}.{descriptor.ruleId.family}.{descriptor.ruleId.rule}` has no source license for public prose"
  if primary.source == .cr18Fallback && applicationAttestation?.isNone then
    throwError "CR18 fallback language is available only to an exact registered application occurrence"
  for support in descriptor.supportingSourceAttestations do
    unless support.isPubliclyLicensed do
      throwError "a supporting linguistic attestation is invalid or not publicly licensed"
  let applicationKey? := match declaration?, applicationAttestation? with
    | some declaration, some _ => some {
        profile
        declaration
        backendDeclaration := descriptor.backendDeclaration
        ruleId := descriptor.ruleId
      }
    | _, _ => none
  return (primary, descriptor.supportingSourceAttestations, applicationKey?)

private def emitEvent (source : Syntax) (descriptor : SentenceDescriptor)
    (assertion? : Option AssertionOccurrenceSummary)
    (intrinsicEffect outerEffect : GoalEffect)
    (operands : Array ElaboratedOperand)
    (bindingsAdded : Array ElaboratedBinding)
    (guidance : Array PresentationAnnotation)
    (before after : Array GoalSnapshot)
    (sourceAttestation : Corpus.Attestation)
    (supportingSourceAttestations : Array Corpus.Attestation)
    (applicationKey? : Option ApplicationOccurrenceKey) : TacticM Unit := do
  let declaration? ← Lean.Elab.Term.getDeclName?
  let locals := before[0]?.map (fun goal => goal.locals.map fun entity => {
    id := entity.id
    type := entity.type
    value? := entity.value?
  }) |>.getD #[]
  let event : SentenceEvent := {
    schemaVersion := 4
    formId := descriptor.formId
    ruleId := descriptor.ruleId
    act := descriptor.act
    invocation := ⟨descriptor.ruleId, operands⟩
    assertion?
    intrinsicEffect
    outerEffect
    goalsBefore := before
    goalsAfter := after
    residualGoals := match outerEffect with
      | .replaceMain obligations => obligations
      | _ => #[]
    localsAdded := addedLocalIds before after
    bindingsAdded
    sourceRange? := source.getRange?
    guidance := guidance
    sourceAttestation
    supportingSourceAttestations
    applicationKey?
    source := source
  }
  let factNonce? := (← getOptions).get? (α := Name) factNonceOption
  let authenticated : AuthenticatedSentenceEvent := { event, factNonce? }
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := source
    value := Dynamic.mk authenticated
  }
  if let some declaration := declaration? then
    modifyEnv fun environment => sentenceTraceRegistry.addEntry environment {
      declaration
      ruleId := descriptor.ruleId
      backendDeclaration := descriptor.backendDeclaration
      operandFingerprints := operands.map fun operand =>
        (operand.role,
          SignatureManifest.localExpressionFingerprint locals operand.expr,
          SignatureManifest.localExpressionFingerprint locals operand.type)
      exactConclusionHash? := assertion?.map fun occurrence =>
        SignatureManifest.localExpressionFingerprint locals occurrence.exactConclusion
      assertionDestination? := assertion?.map fun occurrence => occurrence.destination
      routineProducers := assertion?.map
        (fun occurrence => occurrence.evidenceAnchor.routineProducers) |>.getD #[]
      routineProofHashes := assertion?.map
        (fun occurrence => occurrence.evidenceAnchor.routineProofHashes) |>.getD #[]
      sourceAttestation
      supportingSourceAttestations
      applicationKey?
      sourceText := source.reprint.getD (toString source)
    }
  trace[CryptoLanguage.Verbose.sentence]
    "{descriptor.ruleId.layer}.{descriptor.ruleId.family}.{descriptor.ruleId.rule}"

private def withFactEnvelope {α : Type} (name : Name) (source : Syntax)
    (nonce : Name)
    (action : TacticM α) : TacticM α :=
  withOptions (fun options =>
    ((options.set factDestinationOption name).set factSourceOption source).set
      factNonceOption nonce) action

private def assertionEventSource (fallback : Syntax) : TacticM Syntax := do
  return (← getOptions).get factSourceOption fallback

private def requestedAssertionDestination : TacticM AssertionDestination := do
  match (← getOptions).get? (α := Name) factDestinationOption with
  | some name => return .localFact name
  | none => return .closeMain

private partial def routineEvidenceIn : InfoTree → Array RoutineEvidenceAnchor
  | .hole _ => #[]
  | .context _ child => routineEvidenceIn child
  | .node information children =>
      let here := match information with
        | .ofCustomInfo custom =>
            match custom.value.get? RoutineEvidenceAnchor with
            | some evidence => #[evidence]
            | none => #[]
        | _ => #[]
      children.toArray.foldl (fun result child => result ++ routineEvidenceIn child) here

private def pendingRoutineEvidence : TacticM (Array RoutineEvidenceAnchor) := do
  let state ← getInfoState
  return state.trees.toArray.foldl
    (fun result tree => result ++ routineEvidenceIn tree) #[]

private def newRoutineEvidence (beforeCount : Nat) : TacticM (Array RoutineEvidenceAnchor) := do
  let evidence ← pendingRoutineEvidence
  return evidence.extract beforeCount evidence.size

private def validateRoutineSupport (expected : Array Name)
    (support : Array RoutineEvidenceAnchor) : TacticM Unit := do
  let actual := support.map (·.producer)
  unless actual == expected do
    throwError m!"the assertion used routine producers {repr actual}, but its registered support is {repr expected}"
  for evidence in support do
    unless evidence.inferredType == evidence.proposition ||
        (← evidence.proofGoal.withContext <|
          isDefEqGuarded evidence.inferredType evidence.proposition) do
      throwError "a routine support proof does not have its recorded proposition"

private partial def containsExpression (root wanted : Expr) : Bool :=
  root == wanted || match root with
  | .app function argument =>
      containsExpression function wanted || containsExpression argument wanted
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsExpression domain wanted || containsExpression body wanted
  | .letE _ type value body _ =>
      containsExpression type wanted || containsExpression value wanted ||
        containsExpression body wanted
  | .mdata _ body | .proj _ _ body => containsExpression body wanted
  | _ => false

private def immediateApplicationArguments (expression : Expr) : Array Expr :=
  expression.consumeMData.getAppArgs

/- A supplied proof is authenticated only along a registered result-bearing
spine.  Recurse through a node only when that node itself is an explicitly
registered proof combinator.  This excludes valid-looking theorem
applications hidden in ignored arguments of unrelated opaque wrappers. -/
private partial def isImmediateArgumentOfRegisteredApplication
    (root wanted : Expr) (registered : Array Name) : Bool :=
  let root := root.consumeMData
  let rootDeclaration? := root.getAppFn.constName?
  let rootRegistered := rootDeclaration?.any registered.contains
  let here := rootRegistered && root.getAppArgs.contains wanted
  let registeredIffApplication :=
    root.getAppFn.constName? == some ``Iff.mpr &&
      root.getAppArgs.contains wanted &&
      root.getAppArgs.any fun argument =>
        registered.any (containsConstName argument)
  here || registeredIffApplication ||
    (rootRegistered && root.getAppArgs.any fun argument =>
      isImmediateArgumentOfRegisteredApplication argument wanted registered)

private partial def expressionDeclarations (expression : Expr)
    (result : Array Name := #[]) : Array Name :=
  match expression with
  | .const declaration _ =>
      if result.contains declaration then result else result.push declaration
  | .app function argument =>
      expressionDeclarations argument (expressionDeclarations function result)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      expressionDeclarations body (expressionDeclarations domain result)
  | .letE _ type value body _ =>
      expressionDeclarations body
        (expressionDeclarations value (expressionDeclarations type result))
  | .mdata _ body | .proj _ _ body => expressionDeclarations body result
  | _ => result

private partial def expressionDependsOnMVar (expression : Expr) (wanted : MVarId)
    (fuel : Nat) (visited : Array MVarId := #[]) : MetaM Bool := do
  if fuel == 0 then return false
  match expression with
  | .mvar id =>
      if id == wanted then return true
      if visited.contains id then return false
      let some assignment ← getExprMVarAssignment? id | return false
      expressionDependsOnMVar assignment wanted (fuel - 1) (visited.push id)
  | .app function argument =>
      if ← expressionDependsOnMVar function wanted (fuel - 1) visited then
        return true
      expressionDependsOnMVar argument wanted (fuel - 1) visited
  | .lam _ domain body _ | .forallE _ domain body _ =>
      if ← expressionDependsOnMVar domain wanted (fuel - 1) visited then
        return true
      expressionDependsOnMVar body wanted (fuel - 1) visited
  | .letE _ type value body _ =>
      if ← expressionDependsOnMVar type wanted (fuel - 1) visited then
        return true
      if ← expressionDependsOnMVar value wanted (fuel - 1) visited then
        return true
      expressionDependsOnMVar body wanted (fuel - 1) visited
  | .mdata _ body | .proj _ _ body =>
      expressionDependsOnMVar body wanted (fuel - 1) visited
  | _ => return false

private structure RoutineProducerContract where
  goalClass : Name
  requiredDeclarations : Array Name

private def appLast? (expression : Expr) (declaration : Name) : Option Expr := do
  guard (expression.getAppFn.constName? == some declaration)
  expression.getAppArgs.back?

private def appLastTwo? (expression : Expr) (declaration : Name) : Option (Expr × Expr) := do
  guard (expression.getAppFn.constName? == some declaration)
  let arguments := expression.getAppArgs
  guard (arguments.size >= 2)
  return (arguments[arguments.size - 2]!, arguments[arguments.size - 1]!)

private def projectedFirst? (expression : Expr) : Option Expr :=
  match expression.consumeMData with
  | .proj _ 0 source => some source
  | _ => appLast? expression `Subtype.val

private def restrictedEnhancedURFShape?
    (expression : Expr) : Option Expr := do
  let (budget, game) ← appLastTwo? expression `RandomSystems.Switching.limitGame
  let enhanced ← projectedFirst? game
  let (system, _condition) ← appLastTwo? enhanced `RandomSystems.PDS.adjoin
  guard (system.getAppFn.constName? == some `RandomSystems.PDS.urf)
  return budget

private def restrictedURPShape? (expression : Expr) : Option Expr := do
  let (budget, system) ← appLastTwo? expression `RandomSystems.Switching.limit
  guard (system.getAppFn.constName? == some `RandomSystems.PDS.urp)
  return budget

private def nonnegativeSubject? (expression : Expr) : Option Expr :=
  appLast? expression `Probability.Distribution.NonNeg

private def weightSubject? (expression : Expr) : Option Expr :=
  appLast? expression `Probability.Distribution.weight

/-- Exact producer-specific proposition matcher.  Orientation, constructor
nesting, and restriction arity are checked here; occurrence of the same
constants elsewhere in a proposition is not sufficient. -/
private def routineGoalMatches (producer : Name) (proposition : Expr) : Bool :=
  if producer ==
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURFNonnegative then
    (nonnegativeSubject? proposition).bind restrictedEnhancedURFShape? |>.isSome
  else if producer ==
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative then
    (nonnegativeSubject? proposition).bind restrictedURPShape? |>.isSome
  else if producer ==
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight then
    match proposition.eq? with
    | some (_, left, right) =>
        match (weightSubject? left).bind restrictedEnhancedURFShape?,
            (weightSubject? right).bind restrictedURPShape? with
        | some leftShape, some rightShape => leftShape == rightShape
        | _, _ => false
    | none => false
  else false

private def routineProducerContract? (producer : Name) : Option RoutineProducerContract :=
  if producer ==
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURFNonnegative then
    some {
      goalClass :=
        `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalNonnegativity
      requiredDeclarations := #[
        `RandomSystems.PDS.nonNeg_adjoin,
        `RandomSystems.PDS.isProbDist_urf,
        `Probability.Distribution.NonNeg.fTransform]
    }
  else if producer ==
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative then
    some {
      goalClass :=
        `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalNonnegativity
      requiredDeclarations := #[
        `RandomSystems.PDS.isProbDist_urp,
        `Probability.Distribution.NonNeg.fTransform]
    }
  else if producer ==
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight then
    some {
      goalClass := `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalWeight
      requiredDeclarations := #[
        `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURF_weight_eq_restrictedURP]
    }
  else none

/- Beta/zeta normalization used only to validate evidence reachability. It
does not unfold global declarations. In particular, an unused `let` cannot be
used to smuggle an operand or routine proof into a checked evidence root. -/
private partial def normalizeEvidence (raw : Expr) (fuel : Nat := 512)
    (visiting : Array FVarId := #[]) : MetaM Expr := do
  if fuel == 0 then return raw.consumeMData
  match raw.consumeMData with
  | .fvar id =>
      if visiting.contains id then return raw
      let some value ← id.getValue? | return raw
      normalizeEvidence value (fuel - 1) (visiting.push id)
  | .mvar id =>
      let some assignment ← getExprMVarAssignment? id | return raw
      normalizeEvidence assignment (fuel - 1) visiting
  | .app function argument =>
      let function ← normalizeEvidence function (fuel - 1) visiting
      let argument ← normalizeEvidence argument (fuel - 1) visiting
      match function.consumeMData with
      | .lam _ _ body _ =>
          normalizeEvidence (body.instantiate1 argument) (fuel - 1) visiting
      | _ => return .app function argument
  | .lam name domain body info =>
      return .lam name (
        ← normalizeEvidence domain (fuel - 1) visiting)
        (← normalizeEvidence body (fuel - 1) visiting) info
  | .forallE name domain body info =>
      return .forallE name
        (← normalizeEvidence domain (fuel - 1) visiting)
        (← normalizeEvidence body (fuel - 1) visiting) info
  | .letE _ _ value body _ =>
      normalizeEvidence (body.instantiate1 value) (fuel - 1) visiting
  | .proj typeName index expression =>
      return .proj typeName index
        (← normalizeEvidence expression (fuel - 1) visiting)
  | expression => return expression

/-- Constants in the beta/zeta-normalized proof expression. Routine producers
use the same computation as the core validator, so local abbreviations and
dead `let` bindings cannot make their receipts disagree. -/
def normalizedEvidenceDeclarations (expression : Expr) : MetaM (Array Name) := do
  return expressionDeclarations (← normalizeEvidence expression)

private def validateRoutineEvidence (evidence : RoutineEvidenceAnchor) : TacticM Unit := do
  let some contract := routineProducerContract? evidence.producer
    | throwError "an assertion emitted an unregistered routine producer"
  unless evidence.goalClass == contract.goalClass && evidence.cost == 1 do
    throwError "a routine receipt has the wrong producer class or cost"
  let proposition ← evidence.proofGoal.withContext <|
    instantiateMVars (← evidence.proofGoal.getType)
  let proof ← evidence.proofGoal.withContext do
    let some assignment ← getExprMVarAssignment? evidence.proofGoal
      | throwError "a routine receipt points to an unassigned proof goal"
    instantiateMVars assignment
  let inferredType ← evidence.proofGoal.withContext <|
    instantiateMVars (← inferType proof)
  unless proposition == evidence.proposition && proof == evidence.proof &&
      inferredType == evidence.inferredType &&
      (inferredType == proposition ||
        (← evidence.proofGoal.withContext <| isDefEqGuarded inferredType proposition)) do
    throwError "a routine receipt does not match its checked proof goal, proof, and proposition"
  let normalizedProof ← evidence.proofGoal.withContext <| normalizeEvidence proof
  let normalizedProposition ← evidence.proofGoal.withContext <|
    normalizeEvidence proposition
  let actualDeclarations := expressionDeclarations normalizedProof
  let expectedDeclarations := actualDeclarations.foldl
      (init := contract.requiredDeclarations) fun result declaration =>
    if result.contains declaration then result else result.push declaration
  unless actualDeclarations == evidence.proofDeclarations &&
      contract.requiredDeclarations.all actualDeclarations.contains &&
      evidence.declarations == expectedDeclarations do
    throwError "a routine receipt does not use the declarations required by its registered producer\nrequired: {repr contract.requiredDeclarations}\nactual proof: {repr actualDeclarations}\nrecorded proof: {repr evidence.proofDeclarations}\nrecorded union: {repr evidence.declarations}\nexpected union: {repr expectedDeclarations}"
  unless routineGoalMatches evidence.producer normalizedProposition do
    throwError m!"a routine receipt proposition is not the exact registered producer goal: {normalizedProposition}"

private def validateFixedEvidence (descriptor : SentenceDescriptor)
    (operands : Array ElaboratedOperand) (before after : Array GoalSnapshot)
    (bindings : Array ElaboratedBinding) : TacticM Unit := do
  let some mainBefore := before[0]?
    | throwError "a controlled sentence requires an active goal"
  let assignment? ← getExprMVarAssignment? mainBefore.id
  match descriptor.schema.effect with
  | .guardUnchanged =>
      for operand in operands do
        unless operand.expr == mainBefore.target ||
            (← mainBefore.id.withContext <|
              isDefEqGuarded operand.expr mainBefore.target) do
          throwError m!"announcement operand `{operand.role.name}` is not the complete current proposition"
  | _ =>
      let normalizedAssignment? ← assignment?.mapM fun assignment =>
        mainBefore.id.withContext <| normalizeEvidence assignment
      let normalizedAfter ← after.mapM fun goal =>
        goal.id.withContext <| normalizeEvidence goal.target
      let normalizedBindings ← match after[0]? with
        | some afterMain => bindings.mapM fun binding =>
            afterMain.id.withContext <| normalizeEvidence binding.type
        | none => pure #[]
      let roots := normalizedAfter ++ normalizedBindings ++ normalizedAssignment?.toArray
      for (input, operand) in descriptor.schema.inputs.zip operands do
        let normalizedOperand ← mainBefore.id.withContext <|
          normalizeEvidence operand.expr
        let characterizedDefinitionSupport :=
          descriptor.ruleId == Rules.rsDefineCharacterizedMBO &&
          operand.role == role `characterization &&
          operands.any fun other => other.role == role `assignment &&
            containsExpression operand.type other.expr
        -- `choose` and conjunction elimination change the local context by
        -- dependent elimination. Lean represents the old goal as the new
        -- metavariable under that context, so the source proof no longer
        -- occurs syntactically in a transition root. These two closed
        -- structural rules validate the source proposition and every
        -- produced binding in their dedicated backend before arriving here.
        let structuralEliminationSupport :=
          (descriptor.ruleId == Rules.structuralChoose &&
              operand.role == role `existence &&
              operand.type.getAppFn.constName? == some ``Exists) ||
          (descriptor.ruleId == Rules.structuralConjunction &&
              operand.role == role `conjunction &&
              operand.type.getAppFn.constName? == some ``And)
        let isProofOperand := input.concept == Ontology.proof
        let exactProofUse := isProofOperand && roots.contains normalizedOperand
        let registeredProofUse :=
          isProofOperand &&
          roots.any fun root => isImmediateArgumentOfRegisteredApplication
            root normalizedOperand descriptor.fixedProofCombinators
        let ordinaryUse := !isProofOperand &&
          roots.any (containsExpression · normalizedOperand)
        unless exactProofUse || registeredProofUse || ordinaryUse ||
            characterizedDefinitionSupport || structuralEliminationSupport do
          throwError m!"operand `{operand.role.name}` is not used by the checked fixed-effect transition\nnormalized transition roots: {roots}\nregistered proof combinators: {repr descriptor.fixedProofCombinators}"

private def checkedEvidenceRoot (proofGoal : MVarId) (invocation : RuleInvocation)
    (exactConclusion : Expr) (routineSupport : Array RoutineEvidenceAnchor)
    (proofOperandRoles : Array ArgumentRole)
    (fixedProofCombinators routineRootCombinators : Array Name) :
    TacticM CheckedEvidenceRoot := do
  unless ← proofGoal.isAssigned do
    throwError "an assertion backend did not assign its proof goal"
  let some rawProof ← getExprMVarAssignment? proofGoal
    | throwError "an assertion backend has no retrievable proof assignment"
  let proof ← instantiateMVars rawProof
  if proof.hasMVar then
    throwError "an assertion backend left unresolved metavariables in its proof"
  let inferredType ← instantiateMVars (← inferType proof)
  unless inferredType == exactConclusion ||
      (← isDefEqGuarded inferredType exactConclusion) do
    throwError "the assertion proof does not have the exact checked conclusion"
  let proofOperands := invocation.operands.filter fun operand =>
    proofOperandRoles.contains operand.role
  let exactProofOperands ← proofOperands.filterM fun operand =>
    return operand.type == exactConclusion ||
      (← isDefEqGuarded operand.type exactConclusion)
  if let some operand := exactProofOperands[0]? then
    if exactProofOperands.size == 1 then
      let normalizedProof ← proofGoal.withContext <| normalizeEvidence proof
      let normalizedOperand ← proofGoal.withContext <| normalizeEvidence operand.expr
      unless normalizedProof == normalizedOperand do
        throwError "the assertion evidence root is not the exact supplied proof"
  let normalizedRoot ← proofGoal.withContext <| normalizeEvidence proof
  for operand in invocation.operands do
    let normalizedOperand ← proofGoal.withContext <| normalizeEvidence operand.expr
    if proofOperandRoles.contains operand.role then
      unless normalizedRoot == normalizedOperand ||
          isImmediateArgumentOfRegisteredApplication normalizedRoot
            normalizedOperand fixedProofCombinators do
        throwError m!"proof operand `{operand.role.name}` is neither the exact evidence root nor an immediate premise of a registered proof combinator\nnormalized operand: {normalizedOperand}\nnormalized evidence root: {normalizedRoot}\nroot declaration: {repr normalizedRoot.getAppFn.constName?}\nregistered combinators: {repr fixedProofCombinators}"
    else
      unless containsExpression exactConclusion operand.expr ||
          containsExpression proof operand.expr do
        throwError m!"operand `{operand.role.name}` is not reachable from the assertion's checked conclusion or evidence root"
  if !routineSupport.isEmpty then
    let some rootDeclaration := normalizedRoot.getAppFn.constName?
      | throwError "an assertion with routine support has no registered root proof combinator"
    unless routineRootCombinators.contains rootDeclaration do
      throwError m!"routine support occurs under unregistered proof combinator {rootDeclaration}"
  for evidence in routineSupport do
    if evidence.proofGoal == proofGoal ||
        !(← expressionDependsOnMVar rawProof evidence.proofGoal 256) then
      throwError "a routine receipt is not a proper checked subgoal of the assertion proof"
    validateRoutineEvidence evidence
    let normalizedRoutineProof ← evidence.proofGoal.withContext <|
      normalizeEvidence evidence.proof
    unless (immediateApplicationArguments normalizedRoot).contains
        normalizedRoutineProof do
      throwError "a routine support receipt is not a direct checked premise of the assertion's registered proof combinator"
  return ⟨proof, inferredType, routineSupport⟩

private def assertionSummary (assertion : CheckedAssertion)
    (destination : AssertionDestination)
    (applicationKey? : Option ApplicationOccurrenceKey) : AssertionOccurrenceSummary := {
  invocation := assertion.invocation
  exactConclusion := assertion.exactConclusion
  destination
  evidenceAnchor := {
    proofHash := hash assertion.evidenceRoot.proof
    inferredTypeHash := hash assertion.evidenceRoot.inferredType
    routineProducers := assertion.evidenceRoot.routineSupport.map (·.producer)
    routineProofHashes := assertion.evidenceRoot.routineSupport.map (hash ·.proof)
  }
  applicationKey?
}

private def factBinding (before after : Array GoalSnapshot) (name : Name)
    (exactConclusion : Expr) : TacticM ElaboratedBinding := do
  let some beforeMain := before[0]?
    | throwError "a named assertion requires an active goal"
  let some afterMain := after[0]?
    | throwError "a named assertion unexpectedly closed the surrounding goal"
  let added := afterMain.locals.extract beforeMain.locals.size afterMain.locals.size
  let some localSnapshot := added[0]?
    | throwError "a named assertion did not introduce its local fact"
  unless added.size == 1 && localSnapshot.userName == name do
    throwError "a named assertion introduced a different local binding"
  afterMain.id.withContext do
    unless localSnapshot.type == exactConclusion ||
        (← isDefEqGuarded localSnapshot.type exactConclusion) do
      throwError "the named assertion's local type differs from its checked conclusion"
  return ⟨role `claim, name, localSnapshot.id, localSnapshot.type⟩

private def runBareAssertion (descriptor : SentenceDescriptor)
    (invocation : RuleInvocation)
    (backend : TacticM Unit)
    (before : Array GoalSnapshot) : TacticM (CheckedAssertion × Array GoalSnapshot) := do
  let some mainBefore := before[0]?
    | throwError "a controlled assertion requires an active goal"
  let routineCount := (← pendingRoutineEvidence).size
  backend
  let after ← snapshotGoals
  validateEffect .closeMain .closeMain before after
  let routineSupport ← newRoutineEvidence routineCount
  validateRoutineSupport descriptor.routineClosures routineSupport
  let proofOperandRoles := descriptor.schema.inputs.filterMap fun input =>
    if input.concept == Ontology.proof then some input.role else none
  let root ← checkedEvidenceRoot mainBefore.id invocation mainBefore.target
    routineSupport proofOperandRoles descriptor.fixedProofCombinators
      descriptor.routineRootCombinators
  return (⟨invocation, mainBefore.target, root⟩, after)

private def runNamedAssertion (descriptor : SentenceDescriptor)
    (invocation : RuleInvocation) (name : Name)
    (backend : TacticM Unit)
    (before : Array GoalSnapshot) : TacticM
      (CheckedAssertion × ElaboratedBinding × Array GoalSnapshot) := do
  let originalGoals ← getGoals
  let some originalMain := originalGoals.head?
    | throwError "a named assertion requires an active surrounding goal"
  originalMain.withContext do
    if (← getLCtx).decls.toList.reduceOption.any (·.userName == name) then
      throwError m!"the fact name `{name}` is already in use"
  let (claimType, proofExpression) ← withMainContext do
    let claimType ← mkFreshExprMVar (some (mkSort .zero))
    let proofExpression ← mkFreshExprMVar (some claimType)
    return (claimType, proofExpression)
  let proofGoal := proofExpression.mvarId!
  setGoals [proofGoal]
  let scratchBefore ← snapshotGoals
  let routineCount := (← pendingRoutineEvidence).size
  backend
  let scratchAfter ← snapshotGoals
  validateEffect .closeMain .closeMain scratchBefore scratchAfter
  let exactConclusion ← instantiateMVars claimType
  if exactConclusion.hasMVar then
    throwError "the wrapped assertion did not determine one exact proposition"
  let routineSupport ← newRoutineEvidence routineCount
  validateRoutineSupport descriptor.routineClosures routineSupport
  let proofOperandRoles := descriptor.schema.inputs.filterMap fun input =>
    if input.concept == Ontology.proof then some input.role else none
  let root ← checkedEvidenceRoot proofGoal invocation exactConclusion
    routineSupport proofOperandRoles descriptor.fixedProofCombinators
      descriptor.routineRootCombinators
  setGoals originalGoals
  let mainGoal := originalMain
  let (_, nextGoal) ← mainGoal.note name root.proof (some exactConclusion)
  setGoals (nextGoal :: originalGoals.tail)
  let after ← snapshotGoals
  validateEffect (.addLocalFact {
      role := role `claim
      concept := Ontology.proposition
      typePattern := { builder := Ontology.proposition.name }
    })
    (.addLocals #[name]) before after
  let binding ← factBinding before after name exactConclusion
  return (⟨invocation, exactConclusion, root⟩, binding, after)

/-- Execute a role-labelled mathematical act transactionally. -/
def runSentenceWithBindings (source : Syntax) (descriptor : SentenceDescriptor)
    (expected : ExpectedEffect) (inputs : Array OperandInput)
    (bindings : Array BindingInput)
    (guidance : Array PresentationAnnotation) (backend : BackendAction) : TacticM Unit := do
  let saved ← saveState
  let before ← snapshotGoals
  try
    unless descriptorIsConsistent descriptor do
      throwError "the registered sentence descriptor is internally inconsistent"
    let (sourceAttestation, supportingSourceAttestations, applicationKey?) ←
      effectiveSourceAttestations descriptor
    unless backend.declaration == descriptor.backendDeclaration do
      throwError "the parser selected a backend different from the registered backend declaration"
    unless operandsMatchSchema descriptor.schema inputs do
      throwError "the sentence elaborator's operand roles disagree with its registered rule schema"
    unless bindingsMatchSchema descriptor.schema bindings do
      throwError "the sentence elaborator's binding roles disagree with its registered rule schema"
    let operands ← elaborateOperands inputs
    validateOperandConcepts descriptor.schema operands
    let invocation : RuleInvocation := ⟨descriptor.ruleId, operands⟩
    match descriptor.effect with
    | .fixed effect =>
        if (← getOptions).contains factDestinationOption then
          throwError "`Fact NAME:` can wrap only a registered mathematical assertion"
        unless expectedMatchesSchema effect expected do
          throwError "the sentence elaborator's concrete goal effect disagrees with its registered schema"
        backend.execute
        let after ← snapshotGoals
        validateEffect effect expected before after
        validateBindings descriptor operands bindings before after
        let elaborated := elaboratedBindings descriptor bindings before after
        validateFixedEvidence descriptor operands before after elaborated
        let checkedEffect := goalEffect effect expected elaborated after
        emitEvent source descriptor none checkedEffect checkedEffect operands elaborated
          guidance before after sourceAttestation supportingSourceAttestations
          applicationKey?
    | .assertion =>
        unless expected == .closeMain && bindings.isEmpty do
          throwError "a reusable assertion intrinsically closes one isolated proposition and introduces no bindings"
        match ← requestedAssertionDestination with
        | .closeMain =>
            let (assertion, after) ←
              runBareAssertion descriptor invocation backend.execute before
            let summary := assertionSummary assertion .closeMain applicationKey?
            emitEvent (← assertionEventSource source) descriptor (some summary)
              .closeMain .closeMain operands #[]
              guidance before after sourceAttestation supportingSourceAttestations
              applicationKey?
        | .localFact name =>
            unless descriptor.supportsNamedFact do
              throwError "this assertion has no checked claim constructor for `Fact NAME:`; use it only as a closing step"
            let (assertion, binding, after) ←
              runNamedAssertion descriptor invocation name backend.execute before
            let summary := assertionSummary assertion (.localFact name) applicationKey?
            emitEvent (← assertionEventSource source) descriptor (some summary) .closeMain
              (.addLocalFact binding.role binding.name binding.type) operands #[binding]
              guidance before after sourceAttestation supportingSourceAttestations
              applicationKey?
  catch error =>
    trace[CryptoLanguage.Verbose.sentence]
      "rejected {descriptor.ruleId.layer}.{descriptor.ruleId.family}.{descriptor.ruleId.rule}: {error.toMessageData}"
    saved.restore (restoreInfo := true)
    let roles := descriptor.schema.inputs.map (·.role.name.toString)
    let roleText := if roles.isEmpty then "no explicit operands" else
      s!"explicit operands {String.intercalate ", " roles.toList}"
    throwErrorAt source m!"This sentence cannot establish the registered `{descriptor.schema.result.name}` relation from the current goal and {roleText}. Check that the named mathematical objects have the advertised roles and that the sentence matches the current proposition. The proof state and sentence metadata were restored. Details: {error.toMessageData}"

/-- Execute a sentence which does not introduce author-named bindings. -/
def runSentenceWith (source : Syntax) (descriptor : SentenceDescriptor)
    (expected : ExpectedEffect) (inputs : Array OperandInput)
    (guidance : Array PresentationAnnotation) (backend : BackendAction) : TacticM Unit :=
  runSentenceWithBindings source descriptor expected inputs #[] guidance backend

/-- Execute a sentence with no role-labelled term operands. -/
def runSentence (source : Syntax) (descriptor : SentenceDescriptor)
    (expected : ExpectedEffect) (backend : BackendAction) : TacticM Unit :=
  runSentenceWith source descriptor expected #[] #[] backend

private partial def authenticatedSentenceEventsIn :
    InfoTree → Array AuthenticatedSentenceEvent
  | .hole _ => #[]
  | .context _ child => authenticatedSentenceEventsIn child
  | .node information children =>
      let here := match information with
        | .ofCustomInfo custom =>
            match custom.value.get? AuthenticatedSentenceEvent with
            | some authenticated => #[authenticated]
            | none => #[]
        | _ => #[]
      children.toArray.foldl
        (fun result child => result ++ authenticatedSentenceEventsIn child) here

partial def sentenceEventsIn (tree : InfoTree) : Array SentenceEvent :=
  (authenticatedSentenceEventsIn tree).map (·.event)

private def authenticatedSentenceEventsInState (state : InfoState) :
    Array AuthenticatedSentenceEvent :=
  state.trees.toArray.foldl
    (fun result tree => result ++ authenticatedSentenceEventsIn tree) #[]

def sentenceEventsInState (state : InfoState) : Array SentenceEvent :=
  state.trees.toArray.foldl
    (fun result tree => result ++ sentenceEventsIn tree) #[]

def pendingSentenceEvents : TacticM (Array SentenceEvent) := do
  return sentenceEventsInState (← getInfoState)

/-- Apply the `Fact NAME:` destination to exactly one registered assertion.
The wrapped syntax cannot introduce a fact on its own or smuggle in a fixed-
effect tactic: success requires the assertion event emitted by the checked
lowering transaction. -/
def runFactEnvelope (source : Syntax) (name : Name)
    (assertionStep : TacticM Unit) : TacticM Unit := do
  let nonce ← liftMetaM mkFreshId
  let saved ← saveState
  let goalsBefore ← snapshotGoals
  let eventsBefore := authenticatedSentenceEventsInState (← getInfoState) |>.size
  try
    withFactEnvelope name source nonce assertionStep
    let goalsAfter ← snapshotGoals
    let eventsAfter := authenticatedSentenceEventsInState (← getInfoState)
    let newEvents := eventsAfter.extract eventsBefore eventsAfter.size
    unless newEvents.size == 1 do
      throwError "`Fact NAME:` must wrap exactly one registered mathematical assertion"
    let some authenticated := newEvents[0]?
      | throwError "`Fact NAME:` lost its checked assertion event"
    unless authenticated.factNonce? == some nonce do
      throwError "`Fact NAME:` received an event minted for a different envelope"
    let event := authenticated.event
    let some occurrence := event.assertion?
      | throwError "`Fact NAME:` cannot wrap a fixed-effect proof command"
    unless occurrence.destination == .localFact name do
      throwError "the wrapped assertion did not introduce the requested fact name"
    validateEffect (.addLocalFact {
        role := role `claim
        concept := Ontology.proposition
        typePattern := { builder := Ontology.proposition.name }
      })
      (.addLocals #[name]) goalsBefore goalsAfter
    let binding ← factBinding goalsBefore goalsAfter name occurrence.exactConclusion
    let intrinsicMatches := match event.intrinsicEffect with
      | .closeMain => true
      | _ => false
    let bindingEventMatches := match event.bindingsAdded[0]? with
      | some recorded => event.bindingsAdded.size == 1 &&
          recorded.fvarId == binding.fvarId && recorded.name == binding.name
      | none => false
    unless intrinsicMatches &&
        bindingEventMatches &&
        match event.outerEffect with
        | .addLocalFact bindingRole bindingName bindingType =>
            bindingRole == role `claim && bindingName == name &&
              (bindingType == binding.type)
        | _ => false do
      throwError "the wrapped assertion event does not describe the fact actually introduced"
    unless event.goalsBefore.size == goalsBefore.size &&
        (event.goalsBefore.zip goalsBefore).all fun pair =>
          sameGoalSnapshot pair.1 pair.2 do
      throwError "the wrapped assertion did not start from the `Fact` envelope's proof state"
    unless event.goalsAfter.size == goalsAfter.size &&
        (event.goalsAfter.zip goalsAfter).all fun pair =>
          sameGoalSnapshot pair.1 pair.2 do
      throwError "the wrapped assertion changed the proof state after introducing its checked fact"
  catch error =>
    saved.restore (restoreInfo := true)
    throwErrorAt source m!"Invalid named assertion: {error.toMessageData}"

/-- Execute an ordinary proof step unchanged while attaching reader-only
presentation guidance to its checked transition. -/
def runPresentation (source : Syntax) (guidance : Array PresentationAnnotation)
    (proofStep : TacticM Unit) : TacticM Unit := do
  let saved ← saveState
  let before ← snapshotGoals
  try
    proofStep
    let after ← snapshotGoals
    let event : PresentationEvent := {
      schemaVersion := 1
      goalsBefore := before
      goalsAfter := after
      sourceRange? := source.getRange?
      guidance := guidance
    }
    pushInfoLeaf <| Info.ofCustomInfo {
      stx := source
      value := Dynamic.mk event
    }
    trace[CryptoLanguage.Verbose.presentation] "reader guidance"
  catch error =>
    saved.restore (restoreInfo := true)
    throw error

def reference (term : Term) (readerNote? : Option String := none) : ReferenceSyntax :=
  ⟨term, readerNote?⟩

def operand (role : ArgumentRole) (term : Term)
    (readerNote? : Option String := none) : OperandInput :=
  ⟨role, reference term readerNote?⟩

/-- Assign the semantic tags declared by a typed multi-goal backend.  Core
validation subsequently checks both these tags and the residual propositions;
this helper alone is never an acceptance check. -/
def tagCurrentGoals (tags : Array Name) : TacticM Unit := do
  let goals := (← getGoals).toArray
  unless goals.size == tags.size do
    throwError "the typed backend exposed an unexpected number of obligations"
  for (goal, tag) in goals.zip tags do
    goal.setTag tag

def decodeReference (refStx : TSyntax `verboseReference) : TacticM ReferenceSyntax :=
  match refStx with
  | `(verboseReference| $term:term noted $note:str) =>
      pure ⟨term, some note.getString⟩
  | `(verboseReference| $term:term) => pure ⟨term, none⟩
  | _ => throwErrorAt refStx "invalid Verbose reference"

def form (family form : Name) : SentenceFormId := ⟨`en, family, form⟩

private def bindingWithPattern (binding : BindingSchema) : BindingSchema :=
  if binding.typePattern.builder.isAnonymous then
    { binding with typePattern := { builder := binding.concept.name } }
  else binding

private def outputsOfEffect : EffectSchema → Array BindingSchema
  | .addLocalFact binding => #[bindingWithPattern binding]
  | .introduce bindings => bindings.map bindingWithPattern
  | .replaceMain _ bindings => bindings.map bindingWithPattern
  | _ => #[]

def descriptor (family form : Name) (ruleId : RuleId) (act : SpeechAct)
    (effect : EffectSchema) (result : RelationId) (inputs : Array OperandSchema)
    (summary : String) (backendDeclaration : Name)
    (routineClosures : Array Name := #[]) : SentenceDescriptor :=
  let schema : RuleSchema := {
    id := ruleId
    act := act
    result := result
    inputs := inputs
    outputs := outputsOfEffect effect
    effect := effect
  }
  let sourceAttestation := (Corpus.attestationFor? ruleId).getD {
    source := .proposedPendingAttestation
    work := "source attestation required"
    locator := "unregistered controlled-language rule"
    construction := ruleId.layer ++ ruleId.family ++ ruleId.rule
    strength := .compositionalAdaptation
  }
  let suggestionPolicy := if inputs.all (·.concept == Ontology.proof) then
    SuggestionPolicy.exactGoal else SuggestionPolicy.selectionRequired
  { formId := Verbose.form family form
    ruleId, act, effect := .fixed effect, schema, summary, backendDeclaration,
    sourceAttestation,
    supportingSourceAttestations := Corpus.supportingAttestationsFor ruleId
    diagnosticId := ruleId.layer ++ ruleId.family ++ ruleId.rule
    suggestionPolicy, routineClosures, supportsNamedFact := false }

/-- Register one reusable mathematical assertion. Its deterministic backend
must close exactly one proposition. The surface envelope later chooses whether
that checked proposition closes the main goal or becomes `Fact NAME:`. -/
def assertionDescriptor (family form : Name) (ruleId : RuleId)
    (result : RelationId) (inputs : Array OperandSchema)
    (summary : String) (backendDeclaration : Name)
    (routineClosures : Array Name := #[]) : SentenceDescriptor :=
  let base := descriptor family form ruleId .assertion .closeMain result inputs
    summary backendDeclaration routineClosures
  { base with effect := .assertion }

/-- Register an assertion whose backend can construct its exact conclusion
from explicit operands in an isolated goal. Only these assertions may occur
inside `Fact NAME:`; other assertion backends remain closing steps. -/
def factAssertionDescriptor (family form : Name) (ruleId : RuleId)
    (result : RelationId) (inputs : Array OperandSchema)
    (summary : String) (backendDeclaration : Name)
    (routineClosures : Array Name := #[]) : SentenceDescriptor :=
  { assertionDescriptor family form ruleId result inputs summary
      backendDeclaration routineClosures with
    supportsNamedFact := true }

end CryptoLanguage.Verbose
