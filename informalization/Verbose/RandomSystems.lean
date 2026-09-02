import Verbose.Core
import Verbose.RandomSystems.Routine
import RandomSystems.Technique.BlindWinning

/-!
# Random Systems sentences

This first vertical slice covers exact conditional laws, domain filtering,
reduction to blind winning, and the universal non-adaptive step. CBC-specific
theorem names do not occur in grammar dispatch. The common-domain
data-processing sentence remains pending while the live carrier migration is
completed upstream.
-/

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems

def conditionalLaw :=
  { factAssertionDescriptor `rs.conditionalEquivalence `fromProof
      rsConditionalLaw
      Relations.conditionalEquivalence #[
        explicitOperand (role `game) Ontology.game,
        explicitOperand (role `system) Ontology.system,
        explicitOperand (role `proof) Ontology.proof]
      "establish the exact game-to-system conditional law"
      `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalLaw with
    fixedProofCombinators := #[``id] }

def filterConditionalLaw :=
  { factAssertionDescriptor `rs.conditionalEquivalence `filterDomain
      rsFilterConditionalLaw
      Relations.conditionalEquivalence #[
        explicitOperand (role `predicate) Ontology.predicate,
        explicitOperand (role `prefixClosed) Ontology.proof,
        explicitOperand (role `gameNeverRefuses) Ontology.proof,
        explicitOperand (role `systemNeverRefuses) Ontology.proof,
        explicitOperand (role `conditionalLaw) Ontology.proof]
      "preserve conditional equivalence under the same prefix-closed domain filter"
      `CryptoLanguage.Verbose.RandomSystems.Backend.filterConditionalLaw with
    fixedProofCombinators := #[`RandomSystems.PDG.condEquiv_filterDom] }

def reduceToBlind :=
  { descriptor `rs.conditionalEquivalence `reduceToBlind
      rsConditionalBlindBound .reduction
        (.replaceMain #[obligation `blindWinning] #[])
      Relations.advantageBound #[explicitOperand (role `game) Ontology.game,
        explicitOperand (role `bound) Ontology.bound,
        explicitOperand (role `conditionalLaw) Ontology.proof,
        explicitOperand (role `gameNonnegative) Ontology.proof,
        explicitOperand (role `idealNonnegative) Ontology.proof,
        explicitOperand (role `equalWeight) Ontology.proof]
      "reduce fully-defined advantage to one blind-winning bound"
      `CryptoLanguage.Verbose.RandomSystems.Backend.reduceToBlind with
    fixedProofCombinators := #[
      `LE.le.trans,
      `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv] }

def conditionalBlindComparison :=
  { assertionDescriptor `rs.conditionalEquivalence `blindComparison
    rsConditionalBlindComparison Relations.advantageBound #[
      explicitOperand (role `conditionalLaw) Ontology.proof,
      explicitOperand (role `game) Ontology.game,
      explicitOperand (role `system) Ontology.pdsLaw,
      explicitOperand (role `winningGame) Ontology.game]
    "derive the exact blind-winning comparison from conditional equivalence"
    `CryptoLanguage.Verbose.RandomSystems.Backend.conditionalBlindComparison #[
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedEnhancedURFNonnegative,
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURPNonnegative,
      `CryptoLanguage.Verbose.RandomSystems.Routine.restrictedURFURPWeight] with
    routineRootCombinators := #[
      `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv]
    fixedProofCombinators := #[
      `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv] }

def blindUniversal := descriptor `rs.winning `blindUniversal
  rsBlindUniversal .reduction (.replaceMain #[obligation `fixedEnvironment] #[
    typedBinding (role `environment) Ontology.environment,
    typedBinding (role `nonadaptive) Ontology.proposition,
    typedBinding (role `rounds) Ontology.horizon])
  Relations.winningBound #[explicitOperand (role `game) Ontology.game]
  "fix one non-adaptive environment and interaction horizon"
  `CryptoLanguage.Verbose.RandomSystems.Backend.blindUniversal

def blindWinningBound :=
  { assertionDescriptor `rs.winning `blindBound rsBlindWinningBound
      Relations.winningBound #[
        explicitOperand (role `game) Ontology.game,
        explicitOperand (role `bound) Ontology.bound,
        explicitOperand (role `proof) Ontology.proof]
      "bound the supremum of non-adaptive winning probabilities"
      `CryptoLanguage.Verbose.RandomSystems.Backend.blindWinningBound with
    fixedProofCombinators := #[`ENNReal.ofReal_le_ofReal] }

namespace Backend

def conditionalLaw (game system fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic| change RandomSystems.PDG.CondEquiv $game $system))
  evalTactic (← `(tactic| exact $fact))

def filterConditionalLaw (predicate prefixClosed gameNeverRefuses
    systemNeverRefuses conditionalLaw : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact RandomSystems.PDG.condEquiv_filterDom $predicate $prefixClosed
      $gameNeverRefuses $systemNeverRefuses $conditionalLaw))

def reduceToBlind (game bound conditionalLaw gameNonnegative
    idealNonnegative equalWeight : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    refine (RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
      $gameNonnegative $idealNonnegative $equalWeight $conditionalLaw).trans ?_))
  evalTactic (← `(tactic|
    change ENNReal.ofReal (RandomSystems.PDG.blindSupWinProb $game) ≤ $bound))
  tagCurrentGoals #[`blindWinning]

def conditionalBlindComparison (conditionalLaw game system winningGame : Term) :
    TacticM Unit := do
  withMainContext do
    let gameExpression ← instantiateMVars (← elabTerm game none)
    let winningGameExpression ← instantiateMVars (← elabTerm winningGame none)
    unless gameExpression == winningGameExpression do
      throwError "the game inside the advantage must be the game inside the winning quantity"
    let claimExpression ← elabTerm (← `(term|
      RandomSystems.PDS.advFullyDefined
          (RandomSystems.PDG.forget $game) $system ≤
        ENNReal.ofReal
          (RandomSystems.PDG.blindSupWinProb $winningGame))) (some (mkSort .zero))
    let target ← instantiateMVars (← getMainTarget)
    unless target == claimExpression do
      throwError "the displayed comparison is not the current proposition"
  evalTactic (← `(tactic|
    refine RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
      ?_ ?_ ?_ $conditionalLaw))
  let source ← getRef
  Routine.closeExpected source .restrictedEnhancedURFNonnegative
  Routine.closeExpected source .restrictedURPNonnegative
  Routine.closeExpected source .restrictedURFURPWeight

def blindUniversal (game property : Term) (environment nonadaptive rounds : Ident) :
    TacticM Unit := do
  evalTactic (← `(tactic|
    refine RandomSystems.PDG.blindSupWinProb_le_of_forall (G := $game) ?_))
  for name in #[environment, nonadaptive, rounds] do
    withMainContext do
      let (_, next) ← (← getMainGoal).intro name.getId
      replaceMainGoal [next]
  withMainContext do
    let expected ← elabTerm property none
    let declaration ← getLocalDeclFromUserName nonadaptive.getId
    unless ← isDefEq declaration.type expected do
      throwError "the non-adaptivity witness does not have its stated proposition"
  tagCurrentGoals #[`fixedEnvironment]

def blindWinningBound (game bound proof : Term) : TacticM Unit := do
  withMainContext do
    let goalsBefore ← getGoals
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let expected ← elabTerm (← `(term|
      ENNReal.ofReal (RandomSystems.PDG.blindSupWinProb $game) ≤ $bound)) none
    unless target == expected do
      throwError "the current goal is not the displayed blind-winning bound"
    let proofExpression ← elabTerm proof none
    let proofType ← instantiateMVars (← inferType proofExpression)
    let finalProof ← if proofType == target || (← isDefEqGuarded proofType target) then
      pure proofExpression
    else
      elabTerm (← `(term| ENNReal.ofReal_le_ofReal $proof)) (some target)
    let finalType ← instantiateMVars (← inferType finalProof)
    unless finalType == target || (← isDefEqGuarded finalType target) do
      throwError "the supplied theorem proves neither the displayed bound nor its real-valued precursor"
    goal.assign finalProof
    replaceMainGoal goalsBefore.tail

end Backend
end CryptoLanguage.Verbose.RandomSystems

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems

private def runConditionalSentence (source : Syntax)
    (game system fact : TSyntax `verboseReference) : TacticM Unit := do
  let gameRef ← decodeReference game
  let systemRef ← decodeReference system
  let factRef ← decodeReference fact
  runSentenceWith source conditionalLaw .closeMain
      #[⟨role `game, gameRef⟩, ⟨role `system, systemRef⟩, ⟨role `proof, factRef⟩] #[] <|
    backendAction Backend.conditionalLaw
      (gameRef.term, systemRef.term, factRef.term)

elab (name := internalConditional) "crypto_verbose_rs_conditional "
    game:verboseReference ", " system:verboseReference &"using"
    fact:verboseReference : tactic => do
  runConditionalSentence (← getRef) game system fact

elab "crypto_verbose_rs_conditional_fact " name:ident ", "
    game:verboseReference ", " system:verboseReference &"using"
    fact:verboseReference : tactic => do
  let source ← getRef
  runFactEnvelope source name.getId <|
    runConditionalSentence source game system fact

private def runFilterSentence (source : Syntax)
    (predicate prefixClosed gameNeverRefuses systemNeverRefuses conditionalLaw :
      TSyntax `verboseReference) : TacticM Unit := do
  let predicateRef ← decodeReference predicate
  let prefixClosedRef ← decodeReference prefixClosed
  let gameNeverRefusesRef ← decodeReference gameNeverRefuses
  let systemNeverRefusesRef ← decodeReference systemNeverRefuses
  let conditionalLawRef ← decodeReference conditionalLaw
  runSentenceWith source filterConditionalLaw .closeMain
      #[⟨role `predicate, predicateRef⟩, ⟨role `prefixClosed, prefixClosedRef⟩,
        ⟨role `gameNeverRefuses, gameNeverRefusesRef⟩,
        ⟨role `systemNeverRefuses, systemNeverRefusesRef⟩,
        ⟨role `conditionalLaw, conditionalLawRef⟩] #[] <|
    backendAction Backend.filterConditionalLaw
      (predicateRef.term, prefixClosedRef.term, gameNeverRefusesRef.term,
        systemNeverRefusesRef.term, conditionalLawRef.term)

elab (name := internalFilter) "crypto_verbose_rs_filter "
    predicate:verboseReference &"using" prefixClosed:verboseReference ", "
    gameNeverRefuses:verboseReference ", " systemNeverRefuses:verboseReference
    ", " conditionalLaw:verboseReference : tactic => do
  runFilterSentence (← getRef) predicate prefixClosed gameNeverRefuses
    systemNeverRefuses conditionalLaw

elab "crypto_verbose_rs_filter_fact " name:ident ", "
    predicate:verboseReference &"using" prefixClosed:verboseReference ", "
    gameNeverRefuses:verboseReference ", " systemNeverRefuses:verboseReference
    ", " conditionalLaw:verboseReference : tactic => do
  let source ← getRef
  runFactEnvelope source name.getId <|
    runFilterSentence source predicate prefixClosed gameNeverRefuses
      systemNeverRefuses conditionalLaw

elab (name := internalReduceBlind) "crypto_verbose_rs_reduce_blind "
    game:verboseReference &"to" bound:verboseReference &"using"
    conditionalLaw:verboseReference ", " gameNonnegative:verboseReference ", "
    idealNonnegative:verboseReference ", " equalWeight:verboseReference : tactic => do
  let gameRef ← decodeReference game
  let boundRef ← decodeReference bound
  let conditionalLawRef ← decodeReference conditionalLaw
  let gameNonnegativeRef ← decodeReference gameNonnegative
  let idealNonnegativeRef ← decodeReference idealNonnegative
  let equalWeightRef ← decodeReference equalWeight
  runSentenceWith (← getRef) reduceToBlind (.replaceMain 1)
      #[⟨role `game, gameRef⟩, ⟨role `bound, boundRef⟩,
        ⟨role `conditionalLaw, conditionalLawRef⟩,
        ⟨role `gameNonnegative, gameNonnegativeRef⟩,
        ⟨role `idealNonnegative, idealNonnegativeRef⟩,
        ⟨role `equalWeight, equalWeightRef⟩] #[] <|
    backendAction Backend.reduceToBlind
      (gameRef.term, boundRef.term, conditionalLawRef.term,
        gameNonnegativeRef.term, idealNonnegativeRef.term, equalWeightRef.term)

elab "crypto_verbose_rs_conditional_blind_comparison "
    conditionalLaw:verboseReference ", " game:verboseReference ", "
    system:verboseReference ", " winningGame:verboseReference : tactic => do
  let conditionalLawRef ← decodeReference conditionalLaw
  let gameRef ← decodeReference game
  let systemRef ← decodeReference system
  let winningGameRef ← decodeReference winningGame
  runSentenceWith (← getRef) conditionalBlindComparison .closeMain #[
      ⟨role `conditionalLaw, conditionalLawRef⟩,
      ⟨role `game, gameRef⟩,
      ⟨role `system, systemRef⟩,
      ⟨role `winningGame, winningGameRef⟩] #[] <|
    backendAction Backend.conditionalBlindComparison
      (conditionalLawRef.term, gameRef.term, systemRef.term, winningGameRef.term)

elab (name := internalBlindUniversal) "crypto_verbose_rs_blind_universal "
    game:verboseReference &"with" environment:ident ", " nonadaptive:ident ":"
    property:term:max ", " rounds:ident : tactic => do
  let gameRef ← decodeReference game
  runSentenceWithBindings (← getRef) blindUniversal (.replaceMain 1)
      #[⟨role `game, gameRef⟩] #[
        ⟨role `environment, environment.getId, none⟩,
        ⟨role `nonadaptive, nonadaptive.getId, some property⟩,
        ⟨role `rounds, rounds.getId, none⟩] #[] <|
    backendAction Backend.blindUniversal
      (gameRef.term, property, environment, nonadaptive, rounds)

elab "crypto_verbose_rs_blind_bound " game:verboseReference " <= "
    bound:verboseReference &"using" proof:verboseReference : tactic => do
  let gameRef ← decodeReference game
  let boundRef ← decodeReference bound
  let proofRef ← decodeReference proof
  runSentenceWith (← getRef) blindWinningBound .closeMain #[
      ⟨role `game, gameRef⟩, ⟨role `bound, boundRef⟩,
      ⟨role `proof, proofRef⟩] #[] <|
    backendAction Backend.blindWinningBound
      (gameRef.term, boundRef.term, proofRef.term)

namespace CryptoVerbose

scoped macro &"Fact" name:ident ":" &"The" &"game"
    game:verboseReference &"is" &"conditionally" &"equivalent" &"to"
    system:verboseReference &"by" fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_conditional_fact $name, $game, $system using $fact)

scoped macro &"Fact" name:ident ":" &"Filtering" &"both" &"sides"
    &"by" predicate:verboseReference &"preserves" &"conditional"
    &"equivalence" &"using" prefixClosed:verboseReference ","
    gameNeverRefuses:verboseReference "," systemNeverRefuses:verboseReference
    "," &"and" conditionalLaw:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_filter_fact $name, $predicate using $prefixClosed,
    $gameNeverRefuses, $systemNeverRefuses, $conditionalLaw)

scoped macro &"The" &"game" game:verboseReference &"is" &"conditionally"
    &"equivalent" &"to" system:verboseReference &"by" fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_conditional $game, $system using $fact)

scoped macro &"Filtering" &"both" &"sides" &"by" predicate:verboseReference
    &"preserves" &"conditional" &"equivalence" &"using"
    prefixClosed:verboseReference "," gameNeverRefuses:verboseReference ","
    systemNeverRefuses:verboseReference "," &"and"
    conditionalLaw:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_filter $predicate using $prefixClosed,
    $gameNeverRefuses, $systemNeverRefuses, $conditionalLaw)

scoped macro &"Using" conditionalLaw:verboseReference ","
    gameNonnegative:verboseReference "," idealNonnegative:verboseReference ","
    &"and" equalWeight:verboseReference "," &"it"
    &"suffices" &"to" &"prove" &"the" &"blind" &"winning" &"probability"
    &"of" game:verboseReference &"is" &"at" &"most"
    bound:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_reduce_blind $game to $bound using
    $conditionalLaw, $gameNonnegative, $idealNonnegative, $equalWeight)

scoped macro &"The" &"conditional" &"equivalence" &"in"
    conditionalLaw:verboseReference &"gives"
    &"Adv⊥(" &"forget(" game:verboseReference ")" ","
    system:verboseReference ")" "≤" &"νᴺᴬ["
    winningGame:verboseReference "]" : tactic =>
  `(tactic| crypto_verbose_rs_conditional_blind_comparison
    $conditionalLaw, $game, $system, $winningGame)

scoped macro &"To" &"bound" &"the" &"blind" &"winning" &"probability" &"of"
    game:verboseReference "," &"fix" environment:ident &"with"
    nonadaptive:ident ":" property:term "," &"and"
    &"horizon" rounds:ident : tactic =>
  `(tactic| crypto_verbose_rs_blind_universal $game with $environment,
    $nonadaptive : $property, $rounds)

scoped macro &"The" &"supremum" &"of" &"the" &"winning" &"probabilities"
    &"achievable" &"by" &"non" "-" &"adaptive" &"strategies" &"against"
    game:verboseReference &"is" &"at" &"most" bound:verboseReference &"by"
    proof:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_blind_bound $game <= $bound using $proof)

end CryptoVerbose
