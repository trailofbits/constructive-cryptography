import Verbose
import Verbose.RandomSystems.ProofSpine

open Probability
open RandomSystems
open scoped CryptoVerbose ENNReal

namespace CryptoLanguage.Verbose.Tests.ProofSpine

universe u v w z
variable {X : Type u} {Y : Type v} {U : Type w} {V : Type z}

example {X2 Y2 : Type*}
    (systemTransform : System.DDS X Y → System.DDS X2 Y2)
    (gameTransform : System.DDG X Y → System.DDG X2 Y2)
    (game : PDG X Y) (system : PDS X Y)
    (absorption : ∀ queries2 : List X2, ∃ (queries : List X)
      (pushTranscript : List (X × Option Y) → List (X2 × Option Y2)),
        (∀ realization ∈ game.support,
          (System.Won (gameTransform realization)
              (System.DDE.Total.playQueries queries2) queries2.length ↔
            System.Won realization (System.DDE.Total.playQueries queries)
              queries.length) ∧
          System.DDE.Total.transcript (gameTransform realization).1
              (System.DDE.Total.playQueries queries2) queries2.length =
            pushTranscript (System.DDE.Total.transcript realization.1
              (System.DDE.Total.playQueries queries) queries.length)) ∧
        ∀ realization ∈ system.support,
          System.DDE.Total.transcript (systemTransform realization)
              (System.DDE.Total.playQueries queries2) queries2.length =
            pushTranscript (System.DDE.Total.transcript realization
              (System.DDE.Total.playQueries queries) queries.length))
    (conditionalLaw : PDG.CondEquiv game system) :
    PDG.CondEquiv (Distribution.fTransform gameTransform game)
      (Distribution.fTransform systemTransform system) := by
  fail_if_success
    Transforming the system by systemTransform and the game by gameTransform
      preserves conditional equivalence using absorption and conditionalLaw
  exact PDG.condEquiv_fTransform systemTransform gameTransform absorption
    conditionalLaw

set_option linter.unusedVariables false in
example (environment : System.DDE.Total Y X)
    (nonadaptive : System.DDE.Total.NonAdaptive environment)
    (rounds : ℕ) (referenceSystem : System.DDS X Y) (queries : List X)
    (inducedQueries : System.transcriptInputs
      (System.DDE.Total.transcript referenceSystem environment rounds) = queries)
    (predicate : List X → Prop) [DecidablePred predicate]
    (filteredQueries : List X)
    (filtering : PDG.Plumbing.filterAdmit predicate queries = filteredQueries)
    (law : Distribution Bool) (collisionEvent : Bool → List X → Prop)
    (game : PDG X Y)
    (identity : PDG.winningMass environment rounds game =
      law.mass (fun outcome => collisionEvent outcome filteredQueries)) :
    PDG.winningMass environment rounds game =
      law.mass (fun outcome => collisionEvent outcome filteredQueries) := by
  exact identity

example (queries : List X) (law : Distribution Bool)
    (collisionEvent : Bool → List X → Prop) (bound : ℝ)
    (massBound : law.mass (fun outcome => collisionEvent outcome queries) ≤ bound) :
    law.mass (fun outcome => collisionEvent outcome queries) ≤ bound := by
  fail_if_success
    For queries, under law, the collision event collisionEvent has mass at most
      bound by massBound
  exact massBound

/- A query-dependent arithmetic expression is not a collision event mass. -/
set_option linter.unusedVariables false in
example (queries : List X) (law : Distribution Bool)
    (collisionEvent : Bool → List X → Prop) (bound : ℝ)
    (notMass : (queries.length : ℝ) ≤ bound) : (queries.length : ℝ) ≤ bound := by
  fail_if_success
    For queries, under law, the collision event collisionEvent has mass at most
      bound by notMass
  exact notMass

/- Even an exact event-mass inequality cannot call a non-list index a query
list. -/
set_option linter.unusedVariables false in
example (queries : Nat) (law : Distribution Bool)
    (collisionEvent : Bool → Nat → Prop) (bound : ℝ)
    (massBound : law.mass (fun outcome => collisionEvent outcome queries) ≤ bound) :
    law.mass (fun outcome => collisionEvent outcome queries) ≤ bound := by
  fail_if_success
    For queries, under law, the collision event collisionEvent has mass at most
      bound by massBound
  exact massBound

/- A mixed conditional-equivalence proof: restriction, Condition C, and the
non-adaptive universal step occur in one proof rather than isolated demos. -/
example (predicate : List X → Prop) [DecidablePred predicate]
    (prefixClosed : PrefixClosed predicate)
    (game : PDG X Y) (system : PDS X Y)
    (gameNeverRefuses :
      ∀ realization ∈ game.support, ∀ (history : List X) (query : X),
        System.answer realization.1 history query ≠ none)
    (systemNeverRefuses :
      ∀ realization ∈ system.support, ∀ (history : List X) (query : X),
        System.answer realization history query ≠ none)
    (baseLaw : PDG.CondEquiv game system)
    (gameNonnegative :
      (Distribution.fTransform
        (fun realization : System.DDG X Y =>
          ((System.filterDom predicate prefixClosed realization.1,
            realization.2) : System.DDG X Y)) game).NonNeg)
    (idealNonnegative :
      (Distribution.fTransform (System.filterDom predicate prefixClosed)
        system).NonNeg)
    (equalWeight :
      (Distribution.fTransform
        (fun realization : System.DDG X Y =>
          ((System.filterDom predicate prefixClosed realization.1,
            realization.2) : System.DDG X Y)) game).weight =
      (Distribution.fTransform (System.filterDom predicate prefixClosed)
        system).weight)
    (bound : ℝ)
    (fixedBound : ∀ (environment : System.DDE.Total Y X),
      System.DDE.Total.NonAdaptive environment → ∀ rounds : ℕ,
        PDG.winningMass environment rounds
          (Distribution.fTransform
            (fun realization : System.DDG X Y =>
              ((System.filterDom predicate prefixClosed realization.1,
                realization.2) : System.DDG X Y)) game) ≤ bound) :
    PDS.advFullyDefined
      (PDG.forget (Distribution.fTransform
        (fun realization : System.DDG X Y =>
          ((System.filterDom predicate prefixClosed realization.1,
            realization.2) : System.DDG X Y)) game))
      (Distribution.fTransform (System.filterDom predicate prefixClosed) system) ≤
        ENNReal.ofReal bound := by
  let restrictedGame := Distribution.fTransform
    (fun realization : System.DDG X Y =>
      ((System.filterDom predicate prefixClosed realization.1,
        realization.2) : System.DDG X Y)) game
  let restrictedIdeal :=
    Distribution.fTransform (System.filterDom predicate prefixClosed) system

  have restrictedLaw : PDG.CondEquiv restrictedGame restrictedIdeal :=
    PDG.condEquiv_filterDom predicate prefixClosed gameNeverRefuses
      systemNeverRefuses baseLaw
  change PDS.advFullyDefined (PDG.forget restrictedGame) restrictedIdeal ≤ _
  refine (PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
    gameNonnegative idealNonnegative equalWeight restrictedLaw).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact PDG.blindSupWinProb_le_of_forall fixedBound

end CryptoLanguage.Verbose.Tests.ProofSpine
