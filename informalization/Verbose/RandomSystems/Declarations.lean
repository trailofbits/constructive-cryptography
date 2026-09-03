import Verbose.Core
import RandomSystems.System.Game
import RandomSystems.System.RandomObjects

/-!
# Quarantined Random Systems declaration prototype

This module is not imported by `Verbose`. Its old English declaration forms
are retained temporarily as migration evidence, have pending attestations,
and are rejected by public rendering/help. Standard URF/URP restrictions use
the standalone notation in `Verbose.RandomSystems.Notation`.
-/

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems.Declarations

def restrictedURF :=
  descriptor `rs.declaration `restrictedURF rsDeclareRestrictedURF
    .introduction
    (.introduce #[typedBinding (role `system) Ontology.probabilisticSystem])
    Relations.definition #[
      explicitOperand (role `alphabet) Ontology.alphabet,
      explicitOperand (role `queryBudget) Ontology.horizon]
    "introduce the query restriction of a uniform random function"
    `CryptoLanguage.Verbose.RandomSystems.Declarations.Backend.restrictedURF

def enhancedURFGame :=
  descriptor `rs.declaration `enhancedURFGame rsDeclareEnhancedURFGame
    .introduction
    (.introduce #[typedBinding (role `game) Ontology.probabilisticGame])
    Relations.definition #[
      explicitOperand (role `alphabet) Ontology.alphabet,
      explicitOperand (role `condition) Ontology.monotoneCondition]
    "introduce the game obtained by enhancing a uniform random function with an explicit MBO"
    `CryptoLanguage.Verbose.RandomSystems.Declarations.Backend.enhancedURFGame

def restrictedGame :=
  descriptor `rs.declaration `restrictedGame rsDeclareRestrictedGame
    .introduction
    (.introduce #[typedBinding (role `restrictedGame) Ontology.probabilisticGame])
    Relations.definition #[
      explicitOperand (role `game) Ontology.probabilisticGame,
      explicitOperand (role `queryBudget) Ontology.horizon]
    "introduce the query restriction of an explicit game"
    `CryptoLanguage.Verbose.RandomSystems.Declarations.Backend.restrictedGame

def restrictedURP :=
  descriptor `rs.declaration `restrictedURP rsDeclareRestrictedURP
    .introduction
    (.introduce #[typedBinding (role `system) Ontology.probabilisticSystem])
    Relations.definition #[
      explicitOperand (role `alphabet) Ontology.alphabet,
      explicitOperand (role `queryBudget) Ontology.horizon]
    "introduce the query restriction of a uniform random permutation"
    `CryptoLanguage.Verbose.RandomSystems.Declarations.Backend.restrictedURP

namespace Backend

def restrictedURF (name : Ident) (alphabet budget : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    let $name := Probability.Distribution.fTransform
      (RandomSystems.System.filterQueries $budget)
      (RandomSystems.PDS.urf $alphabet $alphabet)))

def enhancedURFGame (name : Ident) (alphabet condition : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    let $name :=
      (RandomSystems.PDS.adjoin
        (RandomSystems.PDS.urf $alphabet $alphabet) $condition).1))

def restrictedGame (name : Ident) (game budget : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    let $name := Probability.Distribution.fTransform
      (fun gamma =>
        (RandomSystems.System.filterQueries $budget gamma.1, gamma.2)) $game))

def restrictedURP (name : Ident) (alphabet budget : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    let $name := Probability.Distribution.fTransform
      (RandomSystems.System.filterQueries $budget)
      (RandomSystems.PDS.urp $alphabet)))

end Backend
end CryptoLanguage.Verbose.RandomSystems.Declarations

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems.Declarations

elab "crypto_verbose_rs_declare_restricted_urf " name:ident ", "
    alphabet:verboseReference ", " budget:verboseReference : tactic => do
  let alphabetRef ← decodeReference alphabet
  let budgetRef ← decodeReference budget
  runSentenceWithBindings (← getRef) restrictedURF (.addLocals #[name.getId]) #[
      ⟨role `alphabet, alphabetRef⟩,
      ⟨role `queryBudget, budgetRef⟩] #[
      ⟨role `system, name.getId, none⟩] #[] <|
    backendAction Backend.restrictedURF
      (name, alphabetRef.term, budgetRef.term)

elab "crypto_verbose_rs_declare_enhanced_urf_game " name:ident ", "
    alphabet:verboseReference ", " condition:verboseReference : tactic => do
  let alphabetRef ← decodeReference alphabet
  let conditionRef ← decodeReference condition
  runSentenceWithBindings (← getRef) enhancedURFGame (.addLocals #[name.getId]) #[
      ⟨role `alphabet, alphabetRef⟩,
      ⟨role `condition, conditionRef⟩] #[
      ⟨role `game, name.getId, none⟩] #[] <|
    backendAction Backend.enhancedURFGame
      (name, alphabetRef.term, conditionRef.term)

elab "crypto_verbose_rs_declare_restricted_game " name:ident ", "
    game:verboseReference ", " budget:verboseReference : tactic => do
  let gameRef ← decodeReference game
  let budgetRef ← decodeReference budget
  runSentenceWithBindings (← getRef) restrictedGame (.addLocals #[name.getId]) #[
      ⟨role `game, gameRef⟩,
      ⟨role `queryBudget, budgetRef⟩] #[
      ⟨role `restrictedGame, name.getId, none⟩] #[] <|
    backendAction Backend.restrictedGame (name, gameRef.term, budgetRef.term)

elab "crypto_verbose_rs_declare_restricted_urp " name:ident ", "
    alphabet:verboseReference ", " budget:verboseReference : tactic => do
  let alphabetRef ← decodeReference alphabet
  let budgetRef ← decodeReference budget
  runSentenceWithBindings (← getRef) restrictedURP (.addLocals #[name.getId]) #[
      ⟨role `alphabet, alphabetRef⟩,
      ⟨role `queryBudget, budgetRef⟩] #[
      ⟨role `system, name.getId, none⟩] #[] <|
    backendAction Backend.restrictedURP
      (name, alphabetRef.term, budgetRef.term)

namespace CryptoVerbose

scoped macro &"Let" name:ident &"be" &"the" &"restriction" &"of" &"the"
    &"uniform" &"random" &"function" &"on" alphabet:verboseReference
    &"to" budget:verboseReference &"queries" : tactic =>
  `(tactic|
    crypto_verbose_rs_declare_restricted_urf $name, $alphabet, $budget)

scoped macro &"Let" name:ident &"be" &"the" &"game" &"obtained" &"by"
    &"enhancing" &"the" &"uniform" &"random" &"function" &"on"
    alphabet:verboseReference &"with" &"the" &"MBO" &"defined" &"by"
    condition:verboseReference : tactic =>
  `(tactic|
    crypto_verbose_rs_declare_enhanced_urf_game $name, $alphabet, $condition)

scoped macro &"Let" name:ident &"be" &"the" &"restriction" &"of"
    game:verboseReference &"to" budget:verboseReference &"queries" : tactic =>
  `(tactic|
    crypto_verbose_rs_declare_restricted_game $name, $game, $budget)

scoped macro &"Let" name:ident &"be" &"the" &"restriction" &"of" &"the"
    &"uniform" &"random" &"permutation" &"on" alphabet:verboseReference
    &"to" budget:verboseReference &"queries" : tactic =>
  `(tactic|
    crypto_verbose_rs_declare_restricted_urp $name, $alphabet, $budget)

end CryptoVerbose
