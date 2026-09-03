import Verbose
import Verbose.English.Statements
import Verbose.English.Rewriting
import Verbose.RandomSystems
import Verbose.RandomSystems.Relations
import RandomSystems.Technique.Switching

open Probability
open RandomSystems
open Lean Elab Command Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.English.Statements
open scoped CryptoVerbose ENNReal

namespace CryptoLanguage.Verbose.Tests.Switching

private partial def containsConst (expression : Expr) (wanted : Name) : Bool :=
  match expression with
  | .const name _ => name == wanted
  | .app function argument =>
      containsConst function wanted || containsConst argument wanted
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsConst domain wanted || containsConst body wanted
  | .letE _ type value body _ =>
      containsConst type wanted || containsConst value wanted ||
        containsConst body wanted
  | .mdata _ body | .proj _ _ body => containsConst body wanted
  | _ => false

private def unusedRoutineAssertion := {
  assertionDescriptor
  `test.assertion `unusedRoutine
  (CryptoLanguage.LanguageDesign.rule `test `assertion `unusedRoutine)
  CryptoLanguage.LanguageDesign.Ontology.Relations.proposition
  #[CryptoLanguage.LanguageDesign.explicitOperand
    (CryptoLanguage.LanguageDesign.role `proof)
    CryptoLanguage.LanguageDesign.Ontology.proof]
  "test-only assertion with an unreachable routine receipt"
  `CryptoLanguage.Verbose.Tests.Switching.TestBackend.closeWithUnusedRoutine
  #[`CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight] with
  sourceAttestation := {
    source := .projectControlled
    work := "Verbose switching regression harness"
    locator := "private unreachable-receipt mutation"
    construction := `test.switching.unusedRoutineReceipt
    strength := .exactFormalRelation
  }
}

namespace TestBackend

def closeWithUnusedRoutine (X q proof : Term) : TacticM Unit := do
  let originalGoals ← getGoals
  let routineProposition ← withMainContext <| elabTerm (← `(term|
    (Switching.limit $q (PDS.urf $X $X)).weight =
      (Switching.limit $q (PDS.urp $X)).weight)) (some (mkSort .zero))
  let routineProof ← withMainContext <| mkFreshExprMVar (some routineProposition)
  setGoals [routineProof.mvarId!]
  CryptoLanguage.Verbose.RandomSystems.Routine.closeExpected (← getRef)
    .restrictedURFURPWeight
  setGoals originalGoals
  CryptoLanguage.Verbose.Backend.closeFrom proof

end TestBackend

elab "test_unused_routine_receipt " X:term ", " q:term ", " proof:term : tactic => do
  runSentenceWith (← getRef) unusedRoutineAssertion .closeMain
    #[⟨CryptoLanguage.LanguageDesign.role `proof, reference proof⟩] #[] <|
      backendAction TestBackend.closeWithUnusedRoutine (X, q, proof)

/- SWITCHING_VERBOSE_GOLDEN_BEGIN -/
set_option cryptoVerbose.applicationProfile "switching" in
Theorem urf_urp_switching "URF–URP switching"
  Given:
    a finite nonempty alphabet X
    Let q ∈ ℕ
  Conclusion:
    Adv⊥([q] URF(X), [q] URP(X)) ≤
      ENNReal.ofReal
        ((q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ)))
  Proof:
  classical
  Let restrictedURF be the system [q] URF(X)

  Let collisionMBO be the MBO given by
    (Switching.collisionCondition (X := X)), which is set on a query history
    exactly when two distinct queries in that history receive the same answer,
    as shown by
    (Switching.collisionCondition_functionEvaluator_mem_iff (X := X))

  let collisionGame : PDG X X := (PDS.adjoin URF(X) collisionMBO).1
  let restrictedCollisionGame := Switching.limitGame q collisionGame
  Let restrictedURP be the system [q] URP(X)

  Fact conditionalLaw: The game restrictedCollisionGame is conditionally
    equivalent to restrictedURP by
    (Switching.limit_urf_collision_condEquiv_limit_urp X q)

  Fact forgettingIdentity: Ignoring the MBO of restrictedCollisionGame yields
    restrictedURF by
    (Switching.forget_limitGame_adjoin q (PDS.urf X X) collisionMBO)

  calc
    Adv⊥(restrictedURF, restrictedURP) =
        Adv⊥(forget(restrictedCollisionGame), restrictedURP) := by
      Replacing forget(restrictedCollisionGame) by restrictedURF using
        forgettingIdentity yields Adv⊥(restrictedURF, restrictedURP)
    _ ≤ νᴺᴬ[restrictedCollisionGame] := by
      The conditional equivalence in conditionalLaw gives
        Adv⊥(forget(restrictedCollisionGame), restrictedURP) ≤
          νᴺᴬ[restrictedCollisionGame]
    _ ≤ ENNReal.ofReal
        ((q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ))) := by
      The supremum of the winning probabilities achievable by non-adaptive
        strategies against restrictedCollisionGame is at most
          (ENNReal.ofReal
            ((q : ℝ) * ((q : ℝ) - 1) /
              (2 * (Fintype.card X : ℝ)))) by
            (Switching.blindSupWinProb_limit_urf_collision_le X q)
  QED
/- SWITCHING_VERBOSE_GOLDEN_END -/

/- The comparison grammar exposes both occurrences of the game as checked
operands.  A cosmetically plausible sentence with a different winning game
therefore fails closed. -/
example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    Adv⊥(forget(Switching.limitGame q
        (PDS.adjoin URF(X) Switching.collisionCondition).1), [q] URP(X)) ≤
      νᴺᴬ[Switching.limitGame q
        (PDS.adjoin URF(X) Switching.collisionCondition).1] := by
  classical
  let game := Switching.limitGame q
    (PDS.adjoin URF(X) Switching.collisionCondition).1
  let otherGame := Switching.limitGame (q + 1)
    (PDS.adjoin URF(X) Switching.collisionCondition).1
  let ideal := [q] URP(X)
  have conditionalLaw : PDG.CondEquiv game ideal :=
    Switching.limit_urf_collision_condEquiv_limit_urp X q
  change Adv⊥(forget(game), ideal) ≤ νᴺᴬ[game]
  fail_if_success
    The conditional equivalence in conditionalLaw gives
      Adv⊥(forget(game), ideal) ≤ νᴺᴬ[otherGame]
  exact PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
    (by
      dsimp [game, Switching.limitGame]
      exact (PDS.nonNeg_adjoin (PDS.isProbDist_urf X X).nonNeg
        Switching.collisionCondition).fTransform _)
    (by
      dsimp [ideal, Switching.limit]
      exact (PDS.isProbDist_urp X).nonNeg.fTransform _)
    (by
      dsimp [game, ideal, Switching.limitGame, Switching.limit]
      simp only [Distribution.weight_fTransform]
      rw [PDS.isProbDist_urf X X |>.weight_eq,
        PDS.isProbDist_urp X |>.weight_eq])
    conditionalLaw

run_cmd Lean.Elab.Command.liftTermElabM do
  let declaration :=
    `CryptoLanguage.Verbose.Tests.Switching.urf_urp_switching
  let some presentation := theoremPresentation? (← getEnv) declaration
    | throwError "the switching theorem lost its presentation record"
  let some declarationInfo := (← getEnv).find? declaration
    | throwError "the switching theorem is absent from the environment"
  let libraryType := (← getConstInfo
    ``RandomSystems.Switching.urf_urp_switching).type
  let sameLibraryEndpoint ← isDefEqGuarded presentation.exactType libraryType
  unless presentation.title == "URF–URP switching" &&
      presentation.exactType == declarationInfo.type &&
      sameLibraryEndpoint &&
      presentation.givens.size == 2 && presentation.binders.size == 5 &&
      presentation.assumptionCount == 0 &&
      containsConst presentation.conclusion ``RandomSystems.PDS.advFullyDefined &&
      containsConst presentation.conclusion ``ENNReal.ofReal do
    throwError m!"the switching passage changed its title, telescope, or exact library endpoint: title={presentation.title}, givens={presentation.givens.size}, binders={presentation.binders.size}, assumptions={presentation.assumptionCount}, metadataType={presentation.exactType == declarationInfo.type}, libraryEndpoint={sameLibraryEndpoint}, advantage={containsConst presentation.conclusion ``RandomSystems.PDS.advFullyDefined}, ofReal={containsConst presentation.conclusion ``ENNReal.ofReal}"
  let expectedRules := #[
    rsBindSystem,
    rsDefineCharacterizedMBO,
    rsBindSystem,
    rsConditionalLaw,
    rsForgetGame,
    proofRewriting,
    rsConditionalBlindComparison,
    rsBlindWinningBound]
  unless presentation.sentenceRules == expectedRules do
    throwError "the switching passage changed its semantic event sequence: {repr presentation.sentenceRules}"
  let expectedDestinations : Array AssertionDestination := #[
    .localFact `conditionalLaw,
    .localFact `forgettingIdentity,
    .closeMain,
    .closeMain,
    .closeMain]
  unless presentation.assertionDestinations == expectedDestinations do
    throwError "the switching passage changed its Fact/assertion occurrence structure"
  let expectedRoutineProducers := #[
    `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURFNonnegative,
    `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative,
    `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight]
  unless presentation.routineProducers == expectedRoutineProducers do
    throwError "the switching passage changed its checked routine-support graph"
  let entries := presentation.sentenceTrace
  unless entries.size == expectedRules.size do
    throwError "the switching passage lost detailed sentence-trace entries"
  let expectedBackends := #[
    `CryptoLanguage.Verbose.RandomSystems.Definitions.Backend.systemBinder,
    `CryptoLanguage.Verbose.RandomSystems.Definitions.Backend.characterizedMBO,
    `CryptoLanguage.Verbose.RandomSystems.Definitions.Backend.systemBinder,
    `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw,
    `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.forgetGame,
    `CryptoLanguage.Verbose.Backend.replaceInClaim,
    `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalBlindComparison,
    `CryptoLanguage.Verbose.RandomSystems.Backend.blindWinningBound]
  unless entries.map (·.backendDeclaration) == expectedBackends do
    throwError "the switching passage changed its checked backend sequence"
  let expectedConditionalKey : ApplicationOccurrenceKey := {
    profile := "switching"
    declaration
    backendDeclaration :=
      `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw
    ruleId := rsConditionalLaw
  }
  unless entries[3]?.bind (·.applicationKey?) == some expectedConditionalKey do
    throwError "the actual conditional-law event lost its exact application occurrence key"
  let expectedOperandFingerprints :
      Array (Array (CryptoLanguage.LanguageDesign.ArgumentRole × UInt64 × UInt64)) := #[
    #[(role `value, 4800529727614759686, 18000756170829816554)],
    #[(role `assignment, 13919521993507224307, 11218800119039645406),
      (role `characterization, 13002266911722231693, 15822454966045910312)],
    #[(role `value, 361431180999170579, 18000756170829816554)],
    #[(role `game, 7828697281008806374, 5382546231620454189),
      (role `system, 2215086225017496947, 18000756170829816554),
      (role `proof, 1500042708148396704, 9977726372933473343)],
    #[(role `game, 7828697281008806374, 5382546231620454189),
      (role `system, 16477100625456452231, 18000756170829816554),
      (role `proof, 16669587359861237457, 15873070668558447571)],
    #[(role `old, 6970412099997955887, 18000756170829816554),
      (role `new, 8759650492627353259, 18000756170829816554),
      (role `equation, 7657589408011003252, 13579007895265433593),
      (role `result, 273763828663494420, 18297551606480182804)],
    #[(role `conditionalLaw, 17644878951346928088, 4405415382176173972),
      (role `game, 14557541346037146450, 5382546231620454189),
      (role `system, 5023720560454013323, 18000756170829816554),
      (role `winningGame, 14557541346037146450, 5382546231620454189)],
    #[(role `game, 14557541346037146450, 5382546231620454189),
      (role `bound, 1667853133175369629, 18297551606480182804),
      (role `proof, 8511778181156705782, 11483070493749301787)]]
  unless entries.map (·.operandFingerprints) == expectedOperandFingerprints do
    throwError "the switching passage changed an alpha-stable operand or operand-type fingerprint\nactual: {repr (entries.map (·.operandFingerprints))}"
  let expectedConclusionFingerprints : Array (Option UInt64) := #[
    none, none, none, some 10595526372359717701,
    some 5263269683156620682, some 285175575572128204,
    some 7174340373481410615, some 3088134144877902755]
  unless entries.map (·.exactConclusionHash?) == expectedConclusionFingerprints do
    throwError "the switching passage changed an alpha-stable assertion conclusion fingerprint\nactual: {repr (entries.map (·.exactConclusionHash?))}"
  unless entries[1]!.operandFingerprints.map (fun item => item.1) ==
      #[CryptoLanguage.LanguageDesign.role `assignment,
        CryptoLanguage.LanguageDesign.role `characterization] &&
      entries[1]!.sourceText.contains "collisionCondition_functionEvaluator_mem_iff" do
    throwError m!"the switching MBO definition lost its exact assignment, characterization, or canonical punctuation: roles={repr (entries[1]!.operandFingerprints.map (fun item => item.1))}, source={entries[1]!.sourceText}"
  let fixture ← IO.FS.readFile "tests/VerboseTests/Switching.lean"
  let golden ← IO.FS.readFile "tests/Fixtures/Switching.verbose.lean.txt"
  let beginMarker := "/- SWITCHING_VERBOSE_" ++ "GOLDEN_BEGIN -/\n"
  let endMarker := "/- SWITCHING_VERBOSE_" ++ "GOLDEN_END -/"
  let actual ← match fixture.splitOn beginMarker with
    | [_, rest] =>
        match rest.splitOn endMarker with
        | [passage, _] => pure passage
        | _ => throwError "the switching fixture must contain exactly one closing golden marker"
    | _ => throwError "the switching fixture must contain exactly one opening golden marker"
  unless actual == golden do
    throwError "the exactly delimited switching source form changed"
  let expectedSources : Array CryptoLanguage.LanguageDesign.Corpus.Source := #[
    .projectControlled, .projectControlled, .projectControlled,
    .cr18Fallback, .cr18Fallback, .projectControlled, .cr18Fallback,
    .projectControlled]
  unless entries.map (fun entry => entry.sourceAttestation.source) == expectedSources do
    throwError "the switching passage lost its application-scoped source licenses"
  unless entries[1]!.supportingSourceAttestations.map (·.source) ==
      #[.primaryJost, .primaryLiuMau20] do
    throwError "the characterized-MBO sentence lost its Jost ontology and Liu–Maurer discourse provenance"
  unless entries[6]!.routineProofHashes.size == 3 &&
      entries[6]!.routineProofHashes.all (· != 0) do
    throwError "the blind-comparison step lost its exact routine-proof receipts"

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) (P : Prop) (proof : P) : P := by
  fail_if_success test_unused_routine_receipt X, q, proof
  exact proof

end CryptoLanguage.Verbose.Tests.Switching
