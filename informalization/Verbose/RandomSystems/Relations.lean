import Verbose.RandomSystems
import RandomSystems.RandomSystem
import RandomSystems.System.ProbabilisticSystem

/-!
# Exact Random Systems relation sentences

Each form checks the named systems or game appearing in its prose.  A proof of
an unrelated but type-correct proposition cannot be relabelled as one of these
domain relations.
-/

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems.Relations

def pdsEquivalent := assertionDescriptor `rs.systemRelation `pdsEquivalent
  rsPdsEquivalent Relations.equality #[
    explicitOperand (role `left) Ontology.pdsLaw,
    explicitOperand (role `right) Ontology.pdsLaw,
    explicitOperand (role `proof) Ontology.proof]
  "establish strict observational equivalence of two fully-defined laws"
  `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.pdsEquivalent

@[crypto_verbose_sentence] def gameEquivalent := assertionDescriptor `rs.gameRelation `equivalentAsGames
  rsGameEquivalent Relations.equality #[
    explicitOperand (role `left) Ontology.game,
    explicitOperand (role `right) Ontology.game,
    explicitOperand (role `proof) Ontology.proof]
  "establish equality of the not-won laws of two games"
  `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.gameEquivalent

def forgetGame := factAssertionDescriptor `rs.gameRelation `forget
  rsForgetGame Relations.equality #[
    explicitOperand (role `game) Ontology.game,
    explicitOperand (role `system) Ontology.pdsLaw,
    explicitOperand (role `proof) Ontology.proof]
  "identify the PDS law obtained by ignoring a game's MBO"
  `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.forgetGame

def enhanceWithMBO := assertionDescriptor `rs.gameRelation `enhanceWithMBO
  rsEnhanceWithMBO Relations.equality #[
    explicitOperand (role `condition) Ontology.monotoneCondition,
    explicitOperand (role `system) Ontology.pdsLaw,
    explicitOperand (role `game) Ontology.game,
    explicitOperand (role `proof) Ontology.proof]
  "identify the game obtained by enhancing a system with the MBO defined by an explicit monotone condition"
  `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.enhanceWithMBO

def filterQueries :=
  { assertionDescriptor `rs.conditionalEquivalence `filterQueries
      rsFilterQueriesConditionalLaw Relations.conditionalEquivalence #[
        explicitOperand (role `queryBudget) Ontology.horizon,
        explicitOperand (role `gameNeverRefuses) Ontology.proof,
        explicitOperand (role `systemNeverRefuses) Ontology.proof,
        explicitOperand (role `conditionalLaw) Ontology.proof]
      "preserve conditional equivalence under the common query restriction"
      `CryptoLanguage.Verbose.RandomSystems.Relations.Backend.filterQueries with
    fixedProofCombinators := #[`RandomSystems.PDG.condEquiv_filterQueries] }

namespace Backend

def pdsEquivalent (left right fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact (show RandomSystems.PDS.Equivalent $left $right from $fact)))

def gameEquivalent (left right fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact (show RandomSystems.PDG.EquivalentAsGames $left $right from $fact)))

def forgetGame (game system fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact (show RandomSystems.PDG.forget $game = $system from $fact)))

def enhanceWithMBO (condition system game fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact (show (RandomSystems.PDS.adjoin $system $condition).1 = $game from $fact)))

def filterQueries (budget gameNeverRefuses systemNeverRefuses
    conditionalLaw : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact RandomSystems.PDG.condEquiv_filterQueries $budget
      $gameNeverRefuses $systemNeverRefuses $conditionalLaw))

end Backend
end CryptoLanguage.Verbose.RandomSystems.Relations

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems.Relations

private inductive ExactRelationBackend
  | pds
  | game

private def exactRelation (source : Syntax) (entry : SentenceDescriptor)
    (left right fact : TSyntax `verboseReference)
    (backend : ExactRelationBackend) : TacticM Unit := do
  let leftRef ← decodeReference left
  let rightRef ← decodeReference right
  let factRef ← decodeReference fact
  let inputs := #[
      ⟨role `left, leftRef⟩, ⟨role `right, rightRef⟩,
      ⟨role `proof, factRef⟩]
  match backend with
  | .pds =>
      runSentenceWith source entry .closeMain inputs #[] <|
        backendAction Backend.pdsEquivalent
          (leftRef.term, rightRef.term, factRef.term)
  | .game =>
      runSentenceWith source entry .closeMain inputs #[] <|
        backendAction Backend.gameEquivalent
          (leftRef.term, rightRef.term, factRef.term)

elab "crypto_verbose_rs_pds_equivalent " left:verboseReference ", "
    right:verboseReference &"using" fact:verboseReference : tactic => do
  exactRelation (← getRef) pdsEquivalent left right fact
    .pds

elab "crypto_verbose_rs_game_equivalent " left:verboseReference ", "
    right:verboseReference &"using" fact:verboseReference : tactic => do
  exactRelation (← getRef) gameEquivalent left right fact
    .game

private def runForgetSentence (source : Syntax)
    (game system fact : TSyntax `verboseReference) : TacticM Unit := do
  let gameRef ← decodeReference game
  let systemRef ← decodeReference system
  let factRef ← decodeReference fact
  runSentenceWith source forgetGame .closeMain #[
      ⟨role `game, gameRef⟩, ⟨role `system, systemRef⟩,
      ⟨role `proof, factRef⟩] #[] <|
    backendAction Backend.forgetGame (gameRef.term, systemRef.term, factRef.term)

elab "crypto_verbose_rs_forget " game:verboseReference ", "
    system:verboseReference &"using" fact:verboseReference : tactic => do
  runForgetSentence (← getRef) game system fact

elab "crypto_verbose_rs_forget_fact " name:ident ", "
    game:verboseReference ", " system:verboseReference &"using"
    fact:verboseReference : tactic => do
  let source ← getRef
  runFactEnvelope source name.getId <|
    runForgetSentence source game system fact

elab "crypto_verbose_rs_enhance_mbo " condition:verboseReference ", "
    system:verboseReference ", " game:verboseReference &"using"
    fact:verboseReference : tactic => do
  let conditionRef ← decodeReference condition
  let systemRef ← decodeReference system
  let gameRef ← decodeReference game
  let factRef ← decodeReference fact
  runSentenceWith (← getRef) enhanceWithMBO .closeMain #[
      ⟨role `condition, conditionRef⟩, ⟨role `system, systemRef⟩,
      ⟨role `game, gameRef⟩, ⟨role `proof, factRef⟩] #[] <|
    backendAction Backend.enhanceWithMBO
      (conditionRef.term, systemRef.term, gameRef.term, factRef.term)

elab "crypto_verbose_rs_filter_queries " budget:verboseReference &"using"
    gameNeverRefuses:verboseReference ", " systemNeverRefuses:verboseReference
    ", " conditionalLaw:verboseReference : tactic => do
  let budgetRef ← decodeReference budget
  let gameNeverRefusesRef ← decodeReference gameNeverRefuses
  let systemNeverRefusesRef ← decodeReference systemNeverRefuses
  let conditionalLawRef ← decodeReference conditionalLaw
  runSentenceWith (← getRef) filterQueries .closeMain #[
      ⟨role `queryBudget, budgetRef⟩,
      ⟨role `gameNeverRefuses, gameNeverRefusesRef⟩,
      ⟨role `systemNeverRefuses, systemNeverRefusesRef⟩,
      ⟨role `conditionalLaw, conditionalLawRef⟩] #[] <|
    backendAction Backend.filterQueries
      (budgetRef.term, gameNeverRefusesRef.term, systemNeverRefusesRef.term,
        conditionalLawRef.term)

namespace CryptoVerbose

scoped macro &"Fact" name:ident ":" &"Ignoring" &"the" &"MBO" &"of"
    game:verboseReference &"yields" system:verboseReference &"by"
    fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_forget_fact $name, $game, $system using $fact)

scoped macro &"The" &"PDS" &"laws" left:verboseReference &"and"
    right:verboseReference &"are" &"observationally" &"equivalent" &"by"
    fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_pds_equivalent $left, $right using $fact)

scoped macro &"The" &"games" left:verboseReference &"and"
    right:verboseReference &"are" &"equivalent" &"by"
    fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_game_equivalent $left, $right using $fact)

scoped macro &"Ignoring" &"the" &"MBO" &"of" game:verboseReference
    &"yields" system:verboseReference &"by" fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_forget $game, $system using $fact)

scoped macro &"The" &"game" &"obtained" &"by" &"enhancing"
    system:verboseReference &"with" &"the" &"MBO" &"defined" &"by"
    condition:verboseReference &"is" game:verboseReference &"by"
    fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_enhance_mbo $condition, $system, $game using $fact)

scoped macro &"Restricting" &"both" &"sides" &"to"
    budget:verboseReference &"queries" &"preserves" &"conditional"
    &"equivalence" &"using" gameNeverRefuses:verboseReference ","
    systemNeverRefuses:verboseReference "," &"and"
    conditionalLaw:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_filter_queries $budget using $gameNeverRefuses,
    $systemNeverRefuses, $conditionalLaw)

end CryptoVerbose
