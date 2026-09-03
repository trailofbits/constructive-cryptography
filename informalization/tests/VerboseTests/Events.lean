import Verbose

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.Verbose
open CryptoLanguage.LanguageDesign.Ontology
open scoped CryptoVerbose

namespace CryptoLanguage.Verbose.Tests.Events

private def pendingSentenceEvents : TacticM (Array SentenceEvent) := do
  CryptoLanguage.Verbose.pendingSentenceEvents

private def currentSnapshots : TacticM (Array GoalSnapshot) := do
  (← getGoals).toArray.mapM fun goal => goal.withContext do
    let locals := (← getLCtx).decls.toList.reduceOption.toArray.map fun declaration => {
      id := declaration.fvarId
      userName := declaration.userName
      type := declaration.type
      value? := declaration.value? true
    }
    return ⟨goal, ← goal.getTag, ← goal.getType, locals⟩

structure RollbackMarker where
  value : Nat
deriving TypeName

private def testAttestation : CryptoLanguage.LanguageDesign.Corpus.Attestation := {
  source := .projectControlled
  work := "Verbose test harness"
  locator := "private regression descriptor"
  construction := `test.private.checkedSentence
  strength := .exactFormalRelation
}

private def licensedForTest (descriptor : SentenceDescriptor) : SentenceDescriptor :=
  { { descriptor with sourceAttestation := testAttestation } with
    supportingSourceAttestations := #[] }

def closePDSShape (_system proof : Term) : TacticM Unit :=
  Backend.closeFrom proof

private def pdsShapeContract := licensedForTest <| assertionDescriptor
  `test.assertion `pdsShape
  (CryptoLanguage.LanguageDesign.rule `test `assertion `pdsShape)
  Relations.equality #[
    explicitOperand (role `system) Ontology.pdsLaw,
    explicitOperand (role `proof) Ontology.proof]
  "test-only direct PDS carrier-shape assertion"
  `CryptoLanguage.Verbose.Tests.Events.closePDSShape

elab "test_pds_shape " system:term ", " proof:term : tactic => do
  runSentenceWith (← getRef) pdsShapeContract .closeMain #[
      operand (role `system) system, operand (role `proof) proof] #[] <|
    backendAction closePDSShape (system, proof)

def closeDependentPDSShape (_inputAlphabet _outputAlphabet _system proof : Term) :
    TacticM Unit :=
  Backend.closeFrom proof

private def dependentPDSShapeContract :=
  let systemSchema := {
    explicitOperand (role `system) Ontology.pdsLaw with
    typePattern := {
      builder := `RandomSystems.PDS
      operandRoles := #[role `inputAlphabet, role `outputAlphabet]
      expectedSort := .data
    }
  }
  licensedForTest <| assertionDescriptor
    `test.assertion `dependentPdsShape
    (CryptoLanguage.LanguageDesign.rule `test `assertion `dependentPdsShape)
    Relations.equality #[
      explicitOperand (role `inputAlphabet) Ontology.alphabet,
      explicitOperand (role `outputAlphabet) Ontology.alphabet,
      systemSchema,
      explicitOperand (role `proof) Ontology.proof]
    "test-only role-indexed PDS type-pattern assertion"
    `CryptoLanguage.Verbose.Tests.Events.closeDependentPDSShape

elab "test_dependent_pds_shape " inputAlphabet:term ", " outputAlphabet:term
    ", " system:term ", " proof:term : tactic => do
  runSentenceWith (← getRef) dependentPDSShapeContract .closeMain #[
      operand (role `inputAlphabet) inputAlphabet,
      operand (role `outputAlphabet) outputAlphabet,
      operand (role `system) system,
      operand (role `proof) proof] #[] <|
    backendAction closeDependentPDSShape
      (inputAlphabet, outputAlphabet, system, proof)

private def testAssertionContract := licensedForTest <|
  factAssertionDescriptor `test.assertion `fromProof
  (CryptoLanguage.LanguageDesign.rule `test `assertion `fromProof)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only reusable assertion" `CryptoLanguage.Verbose.Backend.closeFrom

private def falselySupportedAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `falselySupported
  (CryptoLanguage.LanguageDesign.rule `test `assertion `falselySupported)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only assertion with a false routine-support declaration"
    `CryptoLanguage.Verbose.Backend.closeFrom #[`test.nonexistentRoutineProducer]

private def closingOnlyAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `closingOnly
  (CryptoLanguage.LanguageDesign.rule `test `assertion `closingOnly)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only assertion without a named-claim constructor"
  `CryptoLanguage.Verbose.Backend.closeFrom

private def forgedRoutineAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `forgedRoutine
  (CryptoLanguage.LanguageDesign.rule `test `assertion `forgedRoutine)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only assertion with a forged root receipt"
  `CryptoLanguage.Verbose.Tests.Events.closeWithForgedRootReceipt
  #[`CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative]

private def deadRoutineAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `deadRoutine
  (CryptoLanguage.LanguageDesign.rule `test `assertion `deadRoutine)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only assertion with a genuine but dead routine child"
  `CryptoLanguage.Verbose.Tests.Events.closeWithDeadRoutineReceipt
  #[`CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative]

private def wrongRoutineGoalAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `wrongRoutineGoal
  (CryptoLanguage.LanguageDesign.rule `test `assertion `wrongRoutineGoal)
  Relations.proposition #[]
  "test-only assertion with the wrong routine producer goal"
  `CryptoLanguage.Verbose.Tests.Events.closeWithWrongRoutineGoalReceipt
  #[`CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative]

def closeWithForgedRootReceipt (proofTerm : Term) : TacticM Unit := do
  let goal ← getMainGoal
  Backend.closeFrom proofTerm
  let proof ← goal.withContext do
    let some assignment ← getExprMVarAssignment? goal
      | throwError "test backend lost its root assignment"
    instantiateMVars assignment
  let proposition ← goal.withContext <| instantiateMVars (← goal.getType)
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := ← getRef
    value := Dynamic.mk ({
      producer :=
        `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative
      goalClass :=
        `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalNonnegativity
      proofGoal := goal
      proposition
      proof
      inferredType := proposition
      declarations := #[]
      proofDeclarations := #[]
      cost := 1
    } : RoutineEvidenceAnchor)
  }

def closeWithDeadRoutineReceipt (X q proofTerm : Term) : TacticM Unit := do
  let originalGoals ← getGoals
  let root ← getMainGoal
  let rootType ← root.withContext <| instantiateMVars (← root.getType)
  let outerProof ← root.withContext <| elabTerm proofTerm (some rootType)
  let routineProposition ← root.withContext <| elabTerm (← `(term|
    (RandomSystems.Switching.limit $q
      (RandomSystems.PDS.urp $X)).NonNeg)) (some (mkSort .zero))
  let routineProof ← root.withContext <|
    mkFreshExprMVar (some routineProposition)
  setGoals [routineProof.mvarId!]
  CryptoLanguage.Verbose.RandomSystems.Routine.closeExpected (← getRef)
    .restrictedURPNonnegative
  root.assign (.letE `unused routineProposition routineProof outerProof true)
  setGoals originalGoals.tail

def closeWithWrongRoutineGoalReceipt : TacticM Unit := do
  let originalGoals ← getGoals
  let root ← getMainGoal
  let proposition ← root.withContext <| instantiateMVars (← root.getType)
  let child ← root.withContext <| mkFreshExprMVar (some proposition)
  let proof ← child.mvarId!.withContext <| elabTerm
    (← `(term| (RandomSystems.PDS.isProbDist_urp _).nonNeg))
    (some proposition)
  child.mvarId!.assign proof
  let inferredType ← child.mvarId!.withContext <|
    instantiateMVars (← inferType proof)
  let proofDeclarations ← child.mvarId!.withContext <|
    normalizedEvidenceDeclarations proof
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := ← getRef
    value := Dynamic.mk ({
      producer :=
        `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative
      goalClass :=
        `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalNonnegativity
      proofGoal := child.mvarId!
      proposition
      proof
      inferredType
      declarations := proofDeclarations
      proofDeclarations
      cost := 1
    } : RoutineEvidenceAnchor)
  }
  root.assign child
  setGoals originalGoals.tail

elab "test_false_routine_support " proof:term : tactic => do
  runSentenceWith (← getRef) falselySupportedAssertion .closeMain
    #[⟨role `proof, reference proof⟩] #[] <|
      backendAction Backend.closeFrom (proof)

elab "test_forged_root_routine " proof:term : tactic => do
  runSentenceWith (← getRef) forgedRoutineAssertion .closeMain
    #[⟨role `proof, reference proof⟩] #[] <|
      backendAction closeWithForgedRootReceipt (proof)

elab "test_dead_routine_receipt " X:term ", " q:term ", " proof:term : tactic => do
  runSentenceWith (← getRef) deadRoutineAssertion .closeMain
    #[operand (role `proof) proof] #[] <|
      backendAction closeWithDeadRoutineReceipt (X, q, proof)

elab "test_wrong_routine_goal_receipt" : tactic => do
  runSentence (← getRef) wrongRoutineGoalAssertion .closeMain <|
    backendAction closeWithWrongRoutineGoalReceipt ()

elab "test_same_backend_unrelated_proof " claimed:term ", " actual:term : tactic => do
  runSentenceWith (← getRef) testAssertionContract .closeMain
    #[⟨role `proof, reference claimed⟩] #[] <|
      backendAction Backend.closeFrom (actual)

elab "test_event_payload " name:ident ":" statement:term &"from"
    proof:verboseReference : tactic => do
  let proofRef ← decodeReference proof
  runFactEnvelope (← getRef) name.getId do
    runSentenceWith (← getRef) testAssertionContract .closeMain
      #[⟨role `proof, proofRef⟩] #[] <|
        backendAction Backend.closeFrom (proofRef.term)
  let some event := (← pendingSentenceEvents).back?
    | throwError "the successful sentence emitted no typed SentenceEvent"
  let some occurrence := event.assertion?
    | throwError "the reusable assertion event lost its assertion summary"
  let bindingMatches := match event.bindingsAdded[0]? with
    | some binding => binding.role == role `claim && binding.name == name.getId
    | none => false
  let outerMatches := match event.outerEffect with
    | .addLocalFact bindingRole bindingName _ =>
        bindingRole == role `claim && bindingName == name.getId
    | _ => false
  let expected ← withMainContext <| elabTerm statement none
  let checks := #[
    event.ruleId == CryptoLanguage.LanguageDesign.rule `test `assertion `fromProof,
    event.invocation.operands.map (·.role) == #[role `proof],
    occurrence.destination == .localFact name.getId,
    ← withMainContext <| isDefEqGuarded occurrence.exactConclusion expected,
    match event.intrinsicEffect with | .closeMain => true | _ => false,
    outerMatches,
    event.bindingsAdded.size == 1,
    bindingMatches,
    event.residualGoals.isEmpty]
  unless checks.all id do
    throwError "the typed SentenceEvent failed checks {repr checks}"

elab "test_replayed_public_fact_event " name:ident : tactic => do
  let some previous := (← pendingSentenceEvents).back?
    | throwError "replay test requires a prior genuine public sentence event"
  let source ← getRef
  runFactEnvelope source name.getId do
    let replay := { previous with
      outerEffect := .guardUnchanged
      sourceRange? := source.getRange?
      source }
    -- Public observations are deliberately not authentication capabilities.
    pushInfoLeaf <| Info.ofCustomInfo {
      stx := source
      value := Dynamic.mk replay
    }

elab "test_fact_state_mutation " name:ident &"from" proof:term : tactic => do
  runFactEnvelope (← getRef) name.getId do
    runSentenceWith (← getRef) testAssertionContract .closeMain
      #[⟨role `proof, reference proof⟩] #[] <|
        backendAction Backend.closeFrom (proof)
    evalTactic (← `(tactic| clear $name))

elab "test_fabricated_fact_event " name:ident : tactic => do
  let source ← getRef
  runFactEnvelope source name.getId do
    let snapshots ← currentSnapshots
    let some main := snapshots[0]?
      | throwError "fabricated-event test requires a goal"
    let invocation : RuleInvocation :=
      ⟨CryptoLanguage.LanguageDesign.rule `test `assertion `fabricated, #[]⟩
    let occurrence : AssertionOccurrenceSummary := {
      invocation
      exactConclusion := main.target
      destination := .localFact name.getId
      evidenceAnchor := { proofHash := 0, inferredTypeHash := 0 }
    }
    let event : SentenceEvent := {
      schemaVersion := 4
      formId := form `test.assertion `fabricated
      ruleId := invocation.ruleId
      act := .assertion
      invocation
      assertion? := some occurrence
      intrinsicEffect := .closeMain
      outerEffect := .addLocalFact (role `claim) name.getId main.target
      goalsBefore := snapshots
      goalsAfter := snapshots
      residualGoals := #[]
      localsAdded := #[]
      bindingsAdded := #[]
      sourceRange? := source.getRange?
      guidance := #[]
      sourceAttestation := testAttestation
      source
    }
    pushInfoLeaf <| Info.ofCustomInfo {
      stx := source
      value := Dynamic.mk event
    }

elab "test_fabricated_matching_fact_event " name:ident &"from" proof:term : tactic => do
  let source ← getRef
  runFactEnvelope source name.getId do
    let before ← currentSnapshots
    let some main := before[0]?
      | throwError "fabricated-event test requires a goal"
    let proofExpression ← withMainContext <| elabTerm proof (some main.target)
    let (_, next) ← main.id.note name.getId proofExpression (some main.target)
    setGoals (next :: (← getGoals).tail)
    let after ← currentSnapshots
    let some added := after[0]?.bind (·.locals.back?)
      | throwError "fabricated-event test did not introduce its local"
    let invocation : RuleInvocation :=
      ⟨CryptoLanguage.LanguageDesign.rule `test `assertion `fabricated, #[]⟩
    let occurrence : AssertionOccurrenceSummary := {
      invocation
      exactConclusion := main.target
      destination := .localFact name.getId
      evidenceAnchor := {
        proofHash := hash proofExpression
        inferredTypeHash := hash main.target
      }
    }
    let event : SentenceEvent := {
      schemaVersion := 4
      formId := form `test.assertion `fabricated
      ruleId := invocation.ruleId
      act := .assertion
      invocation
      assertion? := some occurrence
      intrinsicEffect := .closeMain
      outerEffect := .addLocalFact (role `claim) name.getId main.target
      goalsBefore := before
      goalsAfter := after
      residualGoals := #[]
      localsAdded := #[added.id]
      bindingsAdded := #[{
        role := role `claim
        name := name.getId
        fvarId := added.id
        type := added.type
      }]
      sourceRange? := source.getRange?
      guidance := #[]
      sourceAttestation := testAttestation
      source
    }
    pushInfoLeaf <| Info.ofCustomInfo { stx := source, value := Dynamic.mk event }

def ignoreFirstProof {P Q : Prop} (_claimed : P) (actual : Q) : Q := actual

opaque registeredToTrue {P : Prop} (_proof : P) : True := True.intro

def closeWithIgnoredRegisteredSubproof (claimed : Term) : TacticM Unit := do
  Backend.closeFrom (← `(term|
    ignoreFirstProof (registeredToTrue $claimed) True.intro))

private def ignoredRegisteredSubproofAssertion := licensedForTest <|
  { assertionDescriptor
    `test.assertion `ignoredRegisteredSubproof
    (CryptoLanguage.LanguageDesign.rule `test `assertion
      `ignoredRegisteredSubproof)
    Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
    "test-only assertion with registered evidence in an ignored subproof"
    `CryptoLanguage.Verbose.Tests.Events.closeWithIgnoredRegisteredSubproof with
    fixedProofCombinators := #[``registeredToTrue] }

elab "test_ignored_registered_subproof " claimed:term : tactic => do
  runSentenceWith (← getRef) ignoredRegisteredSubproofAssertion .closeMain
    #[⟨role `proof, reference claimed⟩] #[] <|
      backendAction closeWithIgnoredRegisteredSubproof (claimed)

private def emitForgedRoutineReceipt (producer goalClass : Name)
    (proofGoal : MVarId) (proposition proof inferredType : Expr)
    (required : Array Name) : TacticM Unit := do
  let proofDeclarations ← proofGoal.withContext <|
    normalizedEvidenceDeclarations proof
  let declarations := proofDeclarations.foldl (init := required)
    fun result declaration =>
      if result.contains declaration then result else result.push declaration
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := ← getRef
    value := Dynamic.mk ({
      producer
      goalClass
      proofGoal
      proposition
      proof
      inferredType
      declarations
      proofDeclarations
      cost := 1
    } : RoutineEvidenceAnchor)
  }

def closeWithReverseWeightReceipt (X q condition : Term) : TacticM Unit := do
  let originalGoals ← getGoals
  let root ← getMainGoal
  let proposition ← root.withContext <| elabTerm (← `(term|
    (RandomSystems.Switching.limit $q (RandomSystems.PDS.urp $X)).weight =
      (RandomSystems.Switching.limitGame $q
        (RandomSystems.PDS.adjoin (RandomSystems.PDS.urf $X $X) $condition).1).weight))
    (some (mkSort .zero))
  let child ← root.withContext <| mkFreshExprMVar (some proposition)
  let proof ← child.mvarId!.withContext <| elabTerm (← `(term|
    (CryptoLanguage.Verbose.RandomSystems.Routine.
      restrictedEnhancedURF_weight_eq_restrictedURP $X $q $condition).symm))
    (some proposition)
  child.mvarId!.assign proof
  let inferredType ← child.mvarId!.withContext <| instantiateMVars (← inferType proof)
  emitForgedRoutineReceipt
    `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight
    `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalWeight
    child.mvarId! proposition proof inferredType #[
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURF_weight_eq_restrictedURP]
  let rootProof ← root.withContext <|
    mkAppM ``ignoreFirstProof #[child, mkConst ``True.intro]
  root.assign rootProof
  setGoals originalGoals.tail

private def reverseWeightRoutineAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `reverseWeightRoutine
  (CryptoLanguage.LanguageDesign.rule `test `assertion `reverseWeightRoutine)
  Relations.proposition #[] "test-only reverse routine goal"
  `CryptoLanguage.Verbose.Tests.Events.closeWithReverseWeightReceipt
  #[`CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight]

elab "test_reverse_weight_routine " X:term ", " q:term ", " condition:term : tactic => do
  runSentence (← getRef) reverseWeightRoutineAssertion .closeMain <|
    backendAction closeWithReverseWeightReceipt (X, q, condition)

def closeWithNestedRestrictionReceipt (X q : Term) : TacticM Unit := do
  let originalGoals ← getGoals
  let root ← getMainGoal
  let proposition ← root.withContext <| elabTerm (← `(term|
    (RandomSystems.Switching.limit $q
      (RandomSystems.Switching.limit $q
        (RandomSystems.PDS.urp $X))).NonNeg)) (some (mkSort .zero))
  let child ← root.withContext <| mkFreshExprMVar (some proposition)
  let proof ← child.mvarId!.withContext <| elabTerm (← `(term|
    ((RandomSystems.PDS.isProbDist_urp $X).nonNeg.fTransform _).fTransform _))
    (some proposition)
  child.mvarId!.assign proof
  let inferredType ← child.mvarId!.withContext <| instantiateMVars (← inferType proof)
  emitForgedRoutineReceipt
    `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative
    `CryptoLanguage.Verbose.RandomSystems.Routine.canonicalNonnegativity
    child.mvarId! proposition proof inferredType #[
      `RandomSystems.PDS.isProbDist_urp,
      `Probability.Distribution.NonNeg.fTransform]
  let rootProof ← root.withContext <|
    mkAppM ``ignoreFirstProof #[child, mkConst ``True.intro]
  root.assign rootProof
  setGoals originalGoals.tail

private def nestedRestrictionRoutineAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `nestedRestrictionRoutine
  (CryptoLanguage.LanguageDesign.rule `test `assertion `nestedRestrictionRoutine)
  Relations.proposition #[] "test-only nested restriction routine goal"
  `CryptoLanguage.Verbose.Tests.Events.closeWithNestedRestrictionReceipt
  #[`CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative]

elab "test_nested_restriction_routine " X:term ", " q:term : tactic => do
  runSentence (← getRef) nestedRestrictionRoutineAssertion .closeMain <|
    backendAction closeWithNestedRestrictionReceipt (X, q)

def closeWithOpaqueWrapper (claimed actual : Term) : TacticM Unit := do
  let goal ← getMainGoal
  let target ← withMainContext <| instantiateMVars (← goal.getType)
  let actualProof ← withMainContext <| elabTerm actual (some target)
  let claimedProof ← withMainContext <| elabTerm claimed none
  let wrapped ← withMainContext <|
    mkAppM ``ignoreFirstProof #[claimedProof, actualProof]
  goal.assign wrapped
  setGoals (← getGoals).tail

private def opaqueAssertionContract := licensedForTest <| assertionDescriptor
  `test.assertion `opaqueWrapper
  (CryptoLanguage.LanguageDesign.rule `test `assertion `opaqueWrapper)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only assertion whose backend places the proof under an opaque wrapper"
  `CryptoLanguage.Verbose.Tests.Events.closeWithOpaqueWrapper

elab "test_same_backend_opaque_wrapper " claimed:term ", " actual:term : tactic => do
  runSentenceWith (← getRef) opaqueAssertionContract .closeMain
    #[⟨role `proof, reference claimed⟩] #[] <|
      backendAction closeWithOpaqueWrapper (claimed, actual)

def closeAndRetagTail (proof : Term) : TacticM Unit := do
  Backend.closeFrom proof
  tagCurrentGoals #[`retaggedTail]

private def tailMutatingAssertion := licensedForTest <| assertionDescriptor
  `test.assertion `retagTail
  (CryptoLanguage.LanguageDesign.rule `test `assertion `retagTail)
  Relations.proposition #[explicitOperand (role `proof) Ontology.proof]
  "test-only assertion that mutates a peer goal"
  `CryptoLanguage.Verbose.Tests.Events.closeAndRetagTail

elab "test_close_and_retag_tail " proof:term : tactic => do
  runSentenceWith (← getRef) tailMutatingAssertion .closeMain
    #[⟨role `proof, reference proof⟩] #[] <|
      backendAction closeAndRetagTail (proof)

elab "test_closing_only_fact " name:ident &"from" proof:term : tactic => do
  runFactEnvelope (← getRef) name.getId do
    runSentenceWith (← getRef) closingOnlyAssertion .closeMain
      #[⟨role `proof, reference proof⟩] #[] <|
        backendAction Backend.closeFrom (proof)

def noopAnnouncement (_statement : Term) : TacticM Unit := pure ()

def unrelatedReduction (_proof : Term) : TacticM Unit := do
  let main ← getMainGoal
  let residualType ← withMainContext <|
    elabTerm (← `(term| (0 : Nat) ≤ 0)) (some (mkSort .zero))
  let residual ← withMainContext <| mkFreshExprMVar (some residualType)
  main.assign (mkConst ``True.intro)
  setGoals [residual.mvarId!]
  tagCurrentGoals #[`distance]

def peerTypedReduction (subject _proof : Term) : TacticM Unit := do
  let main ← getMainGoal
  let residualType ← withMainContext <|
    elabTerm (← `(term| $subject ≤ $subject)) (some (mkSort .zero))
  let residual ← withMainContext <| mkFreshExprMVar (some residualType)
  main.assign (mkConst ``True.intro)
  setGoals [residual.mvarId!]
  tagCurrentGoals #[`distance]

def wrongResidualTarget : TacticM Unit := do
  evalTactic (← `(tactic| refine ?_))
  tagCurrentGoals #[`distance]

def wrongResidualTag : TacticM Unit := do
  evalTactic (← `(tactic| refine ?_))
  tagCurrentGoals #[`wrongDistance]

def infoRollbackBackend (name : Ident) : TacticM Unit := do
  pushInfoLeaf <| Info.ofCustomInfo {
    stx := ← getRef
    value := Dynamic.mk ({ value := 37 } : RollbackMarker)
  }
  Backend.introOne name

def badSentenceTransitionBackend : TacticM Unit :=
  Backend.introOne (mkIdent `introduced)

private def distanceContract := licensedForTest <| descriptor `test.effect `distance
  (CryptoLanguage.LanguageDesign.rule `test `effect `distance)
  .reduction (.replaceMain #[obligation `distance] #[])
  Relations.distanceBound #[] "test-only residual contract"
  `CryptoLanguage.Verbose.Tests.Events.wrongResidualTarget

private def wrongTagDistanceContract := licensedForTest <| descriptor
  `test.effect `wrongTagDistance
  (CryptoLanguage.LanguageDesign.rule `test `effect `wrongTagDistance)
  .reduction (.replaceMain #[obligation `distance] #[])
  Relations.distanceBound #[] "test-only wrong residual tag contract"
  `CryptoLanguage.Verbose.Tests.Events.wrongResidualTag

private def guardContract := licensedForTest <| descriptor `test.effect `guard
  (CryptoLanguage.LanguageDesign.rule `test `effect `guard)
  .announcement .guardUnchanged Relations.proofState #[]
  "test-only unchanged-state contract"
  `CryptoLanguage.Verbose.Backend.guardGoal

private def announcementContract := licensedForTest <|
  descriptor `test.effect `announcement
    (CryptoLanguage.LanguageDesign.rule `test `effect `announcement)
    .announcement .guardUnchanged Relations.proposition
    #[explicitOperand (role `proposition) Ontology.proposition]
    "test-only goal announcement contract"
    `CryptoLanguage.Verbose.Tests.Events.noopAnnouncement

private def reductionEvidenceContract := licensedForTest <|
  descriptor `test.effect `reductionEvidence
    (CryptoLanguage.LanguageDesign.rule `test `effect `reductionEvidence)
    .reduction (.replaceMain #[obligation `distance] #[])
    Relations.distanceBound #[
      explicitOperand (role `conditionalLaw) Ontology.proof]
    "test-only reduction evidence contract with a domain-named proof role"
    `CryptoLanguage.Verbose.Tests.Events.unrelatedReduction

private def peerReductionEvidenceContract := licensedForTest <|
  descriptor `test.effect `peerReductionEvidence
    (CryptoLanguage.LanguageDesign.rule `test `effect `peerReductionEvidence)
    .reduction (.replaceMain #[obligation `distance] #[])
    Relations.distanceBound #[
      explicitOperand (role `subject) Ontology.object,
      explicitOperand (role `proof) Ontology.proof]
    "test-only reduction with a peer-typed but unused proof"
    `CryptoLanguage.Verbose.Tests.Events.peerTypedReduction

private def rollbackContract := licensedForTest <| descriptor `test.effect `rollback
  (CryptoLanguage.LanguageDesign.rule `test `effect `rollback)
  .announcement .guardUnchanged Relations.proofState #[]
  "test-only backend that emits metadata before failing validation"
  `CryptoLanguage.Verbose.Tests.Events.infoRollbackBackend

private def badTransitionContract := licensedForTest <| descriptor
  `test.effect `badTransition
  (CryptoLanguage.LanguageDesign.rule `test `effect `badTransition)
  .announcement .guardUnchanged Relations.proofState #[]
  "test-only backend that mutates the local context"
  `CryptoLanguage.Verbose.Tests.Events.badSentenceTransitionBackend

elab "test_same_backend_noop_announcement " statement:term : tactic => do
  runSentenceWith (← getRef) announcementContract .guardUnchanged
    #[⟨role `proposition, reference statement⟩] #[] <|
      backendAction noopAnnouncement (statement)

elab "test_same_backend_unrelated_reduction " proof:term : tactic => do
  runSentenceWith (← getRef) reductionEvidenceContract (.replaceMain 1)
    #[⟨role `conditionalLaw, reference proof⟩] #[] <|
      backendAction unrelatedReduction (proof)

elab "test_same_backend_peer_typed_reduction " subject:term ", " proof:term : tactic => do
  runSentenceWith (← getRef) peerReductionEvidenceContract (.replaceMain 1)
    #[operand (role `subject) subject, operand (role `proof) proof] #[] <|
      backendAction peerTypedReduction (subject, proof)

elab "test_wrong_residual_target" : tactic => do
  runSentence (← getRef) distanceContract (.replaceMain 1) <|
    backendAction wrongResidualTarget ()

elab "test_wrong_residual_tag" : tactic => do
  runSentence (← getRef) wrongTagDistanceContract (.replaceMain 1) <|
    backendAction wrongResidualTag ()

private def propositionBindingContract := licensedForTest <| descriptor `test.effect `binding
  (CryptoLanguage.LanguageDesign.rule `test `effect `binding)
  .introduction (.introduce #[typedBinding (role `claim) Ontology.proposition])
  Relations.proofState #[] "test-only binding contract"
  `CryptoLanguage.Verbose.Backend.introOne

elab "test_wrong_binding_type " name:ident : tactic => do
  runSentenceWithBindings (← getRef) propositionBindingContract
      (.addLocals #[name.getId]) #[] #[⟨role `claim, name.getId, none⟩] #[] <|
    backendAction Backend.introOne (name)

elab "test_info_rollback " name:ident : tactic => do
  let treesBefore := (← getInfoState).trees.size
  try
    runSentence (← getRef) rollbackContract .guardUnchanged <|
      backendAction infoRollbackBackend (name)
  catch _ => pure ()
  unless (← getInfoState).trees.size == treesBefore do
    throwError "a failed sentence leaked InfoTree metadata"

/-- trace: [CryptoLanguage.Verbose.presentation] reader guidance -/
#guard_msgs in
set_option trace.CryptoLanguage.Verbose.presentation true in
example : True := by
  With presentation (label := "collision step", paragraphBefore := true) in
    exact True.intro

/- A mismatched backend mutates the goal before validation.  The `first`
fallback succeeds only if `runSentence` restores both the goal and context. -/
elab "test_bad_sentence_transition" : tactic => do
  runSentence (← getRef) badTransitionContract .guardUnchanged <|
    backendAction badSentenceTransitionBackend ()

example (P : Prop) : P → P := by
  first
  | test_bad_sentence_transition
  | exact fun proof => proof

example (proof : True) : True := by
  fail_if_success test_same_backend_noop_announcement False
  fail_if_success test_same_backend_unrelated_reduction proof
  exact proof

/- Ontology matching is about the direct carrier type. Merely containing a
PDS inside a collection or function type does not make the operand a PDS. -/
example (system : RandomSystems.PDS Nat Nat) (proof : system = system) :
    system = system := by
  test_pds_shape system, proof

example (system : RandomSystems.PDS Nat Nat) (proof : system = system) :
    system = system := by
  test_dependent_pds_shape Nat, Nat, system, proof

example (system : RandomSystems.PDS Nat Bool) (proof : system = system) :
    system = system := by
  fail_if_success test_dependent_pds_shape Nat, Nat, system, proof
  exact proof

example (systems : List (RandomSystems.PDS Nat Nat))
    (proof : systems = systems) : systems = systems := by
  fail_if_success test_pds_shape systems, proof
  exact proof

example (systems : Option (RandomSystems.PDS Nat Nat))
    (proof : systems = systems) : systems = systems := by
  fail_if_success test_pds_shape systems, proof
  exact proof

example (systems : RandomSystems.PDS Nat Nat × Nat)
    (proof : systems = systems) : systems = systems := by
  fail_if_success test_pds_shape systems, proof
  exact proof

example (systems : { system : RandomSystems.PDS Nat Nat // True })
    (proof : systems = systems) : systems = systems := by
  fail_if_success test_pds_shape systems, proof
  exact proof

example (systemFamily : Nat → RandomSystems.PDS Nat Nat)
    (proof : systemFamily = systemFamily) :
    systemFamily = systemFamily := by
  fail_if_success test_pds_shape systemFamily, proof
  exact proof

example (P : Prop) (proof : P) : P := by
  test_event_payload namedProof : P from proof
  fail_if_success test_replayed_public_fact_event replayedProof
  exact namedProof

/- `Fact` accepts only assertion forms with a checked isolated-claim
constructor, and the envelope rejects any mutation after that fact is added. -/
example (P : Prop) (proof : P) : P := by
  fail_if_success test_closing_only_fact namedProof from proof
  fail_if_success test_fact_state_mutation namedProof from proof
  fail_if_success test_fabricated_fact_event namedProof
  fail_if_success test_fabricated_matching_fact_event namedProof from proof
  exact proof

/- Descriptor metadata is enforced, rather than serving as documentation:
an assertion cannot claim routine support that its backend did not emit. -/
example (P : Prop) (proof : P) : P := by
  fail_if_success test_false_routine_support proof
  fail_if_success test_forged_root_routine proof
  exact proof

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) (proof : True) : True := by
  fail_if_success test_dead_routine_receipt X, q, proof
  fail_if_success test_reverse_weight_routine X, q,
    RandomSystems.Switching.collisionCondition
  fail_if_success test_nested_restriction_routine X, q
  exact proof

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] :
    (RandomSystems.PDS.urp X).NonNeg := by
  fail_if_success test_wrong_routine_goal_receipt
  exact (RandomSystems.PDS.isProbDist_urp X).nonNeg

/- A correctly named backend cannot ignore the sentence's claimed proof
operand and close the goal from unrelated evidence. -/
example (P Q : Prop) (proofP : P) (firstQ secondQ : Q) : Q := by
  fail_if_success test_same_backend_unrelated_proof proofP, secondQ
  fail_if_success test_same_backend_opaque_wrapper firstQ, secondQ
  exact secondQ

/- A registered theorem does not authenticate a claimed proof when its result
is merely supplied to an unrelated opaque function that ignores it. -/
example (P : Prop) (claimed : P) : True := by
  fail_if_success test_ignored_registered_subproof claimed
  trivial

example : True ∧ True := by
  constructor
  · fail_if_success test_close_and_retag_tail True.intro
    exact True.intro
  · exact True.intro

example (P Q : Prop) (proof : P ∧ Q) : P ∧ Q := by
  fail_if_success test_same_backend_noop_announcement P
  exact proof

example (subject : Nat) (peerProof : subject = subject) : True := by
  fail_if_success test_same_backend_peer_typed_reduction subject, peerProof
  trivial

example : True := by
  fail_if_success test_wrong_residual_target
  exact True.intro

example (n : Nat) : n ≤ n := by
  fail_if_success test_wrong_residual_tag
  exact le_rfl

example : Nat → True := by
  fail_if_success test_wrong_binding_type number
  exact fun _ => True.intro

set_option linter.unusedTactic false in
example (P : Prop) : P → P := by
  test_info_rollback proof
  exact fun proof => proof

set_option Elab.async false in
theorem fingerprintLocalDefinitionZero : True := by
  let irrelevant : Bool := true
  let relevant : Nat := 0
  have self : relevant = relevant := by
    It remains to prove relevant = relevant
    rfl
  trivial

set_option Elab.async false in
theorem fingerprintLocalDefinitionZeroReordered : True := by
  let relevant : Nat := 0
  let irrelevant : Bool := true
  have self : relevant = relevant := by
    It remains to prove relevant = relevant
    rfl
  trivial

set_option Elab.async false in
theorem fingerprintLocalDefinitionOne : True := by
  let irrelevant : Bool := true
  let relevant : Nat := 1
  have self : relevant = relevant := by
    It remains to prove relevant = relevant
    rfl
  trivial

run_cmd Lean.Elab.Command.liftTermElabM do
  let environment ← getEnv
  let fingerprint (declaration : Name) : TermElabM UInt64 := do
    let some entry := (sentenceTraceFor environment declaration)[0]?
      | throwError "the local-definition fingerprint fixture lost its sentence trace"
    let some (_, value, _) := entry.operandFingerprints[0]?
      | throwError "the local-definition fingerprint fixture lost its proposition operand"
    return value
  let zero ← fingerprint
    `CryptoLanguage.Verbose.Tests.Events.fingerprintLocalDefinitionZero
  let reordered ← fingerprint
    `CryptoLanguage.Verbose.Tests.Events.fingerprintLocalDefinitionZeroReordered
  let one ← fingerprint
    `CryptoLanguage.Verbose.Tests.Events.fingerprintLocalDefinitionOne
  unless zero == reordered && zero != one do
    throwError "local entity fingerprints must ignore independent-definition order and detect value mutation"

end CryptoLanguage.Verbose.Tests.Events
