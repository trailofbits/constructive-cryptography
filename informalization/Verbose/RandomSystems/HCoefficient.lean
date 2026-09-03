import Verbose.RandomSystems.Relations
import RandomSystems.Technique.HCoefficient

/-! A deterministic opening sentence for the public H-coefficient theorem. -/

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems.HCoefficient

def applyTheorem :=
  { descriptor `rs.distance `hCoefficient
      rsHCoefficient .reduction
        (.replaceMain #[obligation `goodRatio, obligation `idealBadMass] #[])
      Relations.advantageBound #[
        explicitOperand (role `real) Ontology.pdsLaw,
        explicitOperand (role `ideal) Ontology.pdsLaw,
        explicitOperand (role `badPredicate) Ontology.predicate,
        explicitOperand (role `ratioLoss) Ontology.bound,
        explicitOperand (role `badMassLoss) Ontology.bound,
        explicitOperand (role `realNonnegative) Ontology.proof,
        explicitOperand (role `idealNonnegative) Ontology.proof,
        explicitOperand (role `equalWeight) Ontology.proof,
        explicitOperand (role `idealWeightAtMostOne) Ontology.proof]
      "fix the H-coefficient route and expose its good-ratio and ideal-bad-mass obligations"
      `CryptoLanguage.Verbose.RandomSystems.HCoefficient.Backend.applyTheorem with
    fixedProofCombinators := #[`RandomSystems.PDS.h_coefficient_theorem] }

namespace Backend

def applyTheorem (real ideal badPredicate ratioLoss badMassLoss
    realNonnegative idealNonnegative equalWeight idealWeightAtMostOne : Term) :
    TacticM Unit := do
  evalTactic (← `(tactic|
    refine RandomSystems.PDS.h_coefficient_theorem
      (S := $real) (T := $ideal) (Bad := $badPredicate)
      (eps := $ratioLoss) (δb := $badMassLoss)
      $realNonnegative $idealNonnegative $equalWeight
      $idealWeightAtMostOne ?_ ?_))
  tagCurrentGoals #[`goodRatio, `idealBadMass]

end Backend
end CryptoLanguage.Verbose.RandomSystems.HCoefficient

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems.HCoefficient

elab "crypto_verbose_rs_h_coefficient " real:verboseReference ", "
    ideal:verboseReference ", " badPredicate:verboseReference ", "
    ratioLoss:verboseReference ", " badMassLoss:verboseReference &"using"
    realNonnegative:verboseReference ", " idealNonnegative:verboseReference ", "
    equalWeight:verboseReference ", " idealWeightAtMostOne:verboseReference : tactic => do
  let realRef ← decodeReference real
  let idealRef ← decodeReference ideal
  let badPredicateRef ← decodeReference badPredicate
  let ratioLossRef ← decodeReference ratioLoss
  let badMassLossRef ← decodeReference badMassLoss
  let realNonnegativeRef ← decodeReference realNonnegative
  let idealNonnegativeRef ← decodeReference idealNonnegative
  let equalWeightRef ← decodeReference equalWeight
  let idealWeightAtMostOneRef ← decodeReference idealWeightAtMostOne
  runSentenceWith (← getRef) applyTheorem (.replaceMain 2) #[
      ⟨role `real, realRef⟩, ⟨role `ideal, idealRef⟩,
      ⟨role `badPredicate, badPredicateRef⟩,
      ⟨role `ratioLoss, ratioLossRef⟩,
      ⟨role `badMassLoss, badMassLossRef⟩,
      ⟨role `realNonnegative, realNonnegativeRef⟩,
      ⟨role `idealNonnegative, idealNonnegativeRef⟩,
      ⟨role `equalWeight, equalWeightRef⟩,
      ⟨role `idealWeightAtMostOne, idealWeightAtMostOneRef⟩] #[] <|
    backendAction Backend.applyTheorem
      (realRef.term, idealRef.term, badPredicateRef.term, ratioLossRef.term,
        badMassLossRef.term, realNonnegativeRef.term, idealNonnegativeRef.term,
        equalWeightRef.term, idealWeightAtMostOneRef.term)

namespace CryptoVerbose

scoped macro &"Apply" &"the" &"H" "-" &"coefficient" &"theorem" &"to"
    real:verboseReference &"and" ideal:verboseReference &"with" &"bad"
    &"predicate" badPredicate:verboseReference "," &"ratio" &"loss"
    ratioLoss:verboseReference "," &"and" &"bad" "-" &"mass" &"loss"
    badMassLoss:verboseReference &"using" realNonnegative:verboseReference ","
    idealNonnegative:verboseReference "," equalWeight:verboseReference ","
    &"and" idealWeightAtMostOne:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_h_coefficient $real, $ideal, $badPredicate,
    $ratioLoss, $badMassLoss using $realNonnegative, $idealNonnegative,
    $equalWeight, $idealWeightAtMostOne)

end CryptoVerbose
