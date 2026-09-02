import Verbose
import Verbose.RandomSystems.HCoefficient

open Probability
open RandomSystems
open scoped CryptoVerbose ENNReal NNReal

namespace CryptoLanguage.Verbose.Tests.HCoefficient

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.Verbose

private partial def sentenceEvents : InfoTree → Array SentenceEvent
  | .hole _ => #[]
  | .context _ child => sentenceEvents child
  | .node information children =>
      let here := match information with
        | .ofCustomInfo custom =>
            match custom.value.get? SentenceEvent with
            | some event => #[event]
            | none => #[]
        | _ => #[]
      children.toArray.foldl (fun result child => result ++ sentenceEvents child) here

elab "test_h_residual_event " real:verboseReference ", " ideal:verboseReference
    ", " badPredicate:verboseReference ", " ratioLoss:verboseReference ", "
    badMassLoss:verboseReference &"using" realNonnegative:verboseReference ", "
    idealNonnegative:verboseReference ", " equalWeight:verboseReference ", "
    idealWeightAtMostOne:verboseReference : tactic => do
  let realRef ← decodeReference real
  let idealRef ← decodeReference ideal
  let badPredicateRef ← decodeReference badPredicate
  let ratioLossRef ← decodeReference ratioLoss
  let badMassLossRef ← decodeReference badMassLoss
  let realNonnegativeRef ← decodeReference realNonnegative
  let idealNonnegativeRef ← decodeReference idealNonnegative
  let equalWeightRef ← decodeReference equalWeight
  let idealWeightAtMostOneRef ← decodeReference idealWeightAtMostOne
  let descriptor := {
    CryptoLanguage.Verbose.RandomSystems.HCoefficient.applyTheorem with
    sourceAttestation := {
      source := .projectControlled
      work := "Verbose H-coefficient regression harness"
      locator := "private residual-goal event test"
      construction := `test.hCoefficient.residualEvent
      strength := .exactFormalRelation
    }
  }
  runSentenceWith (← getRef) descriptor (.replaceMain 2) #[
      ⟨role `real, realRef⟩, ⟨role `ideal, idealRef⟩,
      ⟨role `badPredicate, badPredicateRef⟩,
      ⟨role `ratioLoss, ratioLossRef⟩,
      ⟨role `badMassLoss, badMassLossRef⟩,
      ⟨role `realNonnegative, realNonnegativeRef⟩,
      ⟨role `idealNonnegative, idealNonnegativeRef⟩,
      ⟨role `equalWeight, equalWeightRef⟩,
      ⟨role `idealWeightAtMostOne, idealWeightAtMostOneRef⟩] #[] <|
    backendAction
      CryptoLanguage.Verbose.RandomSystems.HCoefficient.Backend.applyTheorem
      (realRef.term, idealRef.term, badPredicateRef.term, ratioLossRef.term,
        badMassLossRef.term, realNonnegativeRef.term, idealNonnegativeRef.term,
        equalWeightRef.term, idealWeightAtMostOneRef.term)
  let events ← CryptoLanguage.Verbose.pendingSentenceEvents
  let some event := events.findRev? (·.ruleId == rsHCoefficient)
    | throwError "the H-coefficient sentence emitted no SentenceEvent"
  unless event.residualGoals.map (·.role) ==
      #[obligation `goodRatio, obligation `idealBadMass] &&
      event.residualGoals.map (·.tag) == #[`goodRatio, `idealBadMass] do
    throwError "the H-coefficient event lost its semantic residual roles"

universe u v

variable {X : Type u} {Y : Type v}

example (real ideal : PDS X Y)
    (Bad : List (X × Option Y) → Prop) (eps delta : ℝ≥0)
    (realNonnegative : real.NonNeg) (idealNonnegative : ideal.NonNeg)
    (equalWeight : real.weight = ideal.weight)
    (idealWeightAtMostOne : ideal.weight ≤ 1)
    (goodRatio : ∀ transcript, ¬ Bad transcript →
      (1 - eps) * PDS.transcriptSystemFactor ideal transcript ≤
        PDS.transcriptSystemFactor real transcript)
    (idealBadMass : ∀ (environment : System.DDE.Total Y X) (rounds : ℕ),
      Probability.probBad (PDS.trLawFullyDefined environment rounds ideal) Bad ≤ delta) :
    PDS.advFullyDefined real ideal ≤ (delta + eps : ℝ≥0) := by
  fail_if_success
    Apply the H-coefficient theorem to ideal and real with bad predicate Bad,
      ratio loss eps, and bad-mass loss delta using realNonnegative,
      idealNonnegative, equalWeight, and idealWeightAtMostOne
  fail_if_success
    Apply the H-coefficient theorem to real and ideal with bad predicate Bad,
      ratio loss eps, and bad-mass loss delta using realNonnegative,
      idealNonnegative, idealWeightAtMostOne, and equalWeight
  test_h_residual_event real, ideal, Bad, eps, delta using realNonnegative,
    idealNonnegative, equalWeight, idealWeightAtMostOne
  case goodRatio => exact goodRatio
  case idealBadMass => exact idealBadMass

end CryptoLanguage.Verbose.Tests.HCoefficient
