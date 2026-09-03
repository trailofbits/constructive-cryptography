import Verbose
import Verbose.RandomSystems
import Verbose.RandomSystems.Relations
import RandomSystems.Technique.Switching

open Probability
open RandomSystems
open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.Verbose
open scoped CryptoVerbose ENNReal

namespace CryptoLanguage.Verbose.Tests.RandomSystems

universe u v w z

variable {X : Type u} {Y : Type v} {U : Type w} {V : Type z}

private def testReduceToBlindDescriptor : SentenceDescriptor := {
  CryptoLanguage.Verbose.RandomSystems.reduceToBlind with
  sourceAttestation := {
    source := .projectControlled
    work := "Verbose reduction regression harness"
    locator := "private overloaded-operand test"
    construction := `test.randomSystems.reduceToBlind
    strength := .exactFormalRelation
  }
}

elab "test_reduce_to_blind " game:term " to " bound:term " using "
    conditionalLaw:term ", " gameNonnegative:term ", " idealNonnegative:term
    ", " equalWeight:term : tactic => do
  runSentenceWith (← getRef) testReduceToBlindDescriptor (.replaceMain 1) #[
      operand (role `game) game, operand (role `bound) bound,
      operand (role `conditionalLaw) conditionalLaw,
      operand (role `gameNonnegative) gameNonnegative,
      operand (role `idealNonnegative) idealNonnegative,
      operand (role `equalWeight) equalWeight] #[] <|
    backendAction CryptoLanguage.Verbose.RandomSystems.Backend.reduceToBlind
      (game, bound, conditionalLaw, gameNonnegative, idealNonnegative,
        equalWeight)

/- Standard RS objects use standalone mathematical notation whose expansion is
an exact constructor term. -/
example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) : True := by
  classical
  let restrictedFunction := [q] URF(X)
  let collisionGame : PDG X X :=
    (PDS.adjoin URF(X) Switching.collisionCondition).1
  let restrictedCollisionGame := Switching.limitGame q collisionGame
  let restrictedPermutation := [q] URP(X)
  have gameNonnegative : restrictedCollisionGame.NonNeg := by
    dsimp [restrictedCollisionGame, collisionGame, Switching.limitGame]
    exact (PDS.nonNeg_adjoin
      (PDS.isProbDist_urf X X).nonNeg Switching.collisionCondition).fTransform _
  have functionDefinition :
      restrictedFunction = Switching.limit q (PDS.urf X X) := rfl
  have gameDefinition :
      collisionGame =
        (PDS.adjoin (PDS.urf X X) Switching.collisionCondition).1 := rfl
  have restrictedGameDefinition :
      restrictedCollisionGame = Switching.limitGame q collisionGame := rfl
  have permutationDefinition :
      restrictedPermutation = Switching.limit q (PDS.urp X) := rfl
  have nonnegativityDefinition : restrictedCollisionGame.NonNeg :=
    gameNonnegative
  trivial

/- The notation elaborates through the typed constructor and rejects invalid
restriction operands or budgets. -/
example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] : True := by
  classical
  fail_if_success
    let heterogeneousRestriction := [0] URF(X, Bool)
  fail_if_success
    let badBudget := [X] URF(X)
  trivial

/- Checked-library metadata does not license generic prose, including under a
`Fact` envelope. -/
example (game : PDG X Y) (system : PDS X Y)
    (conditionalLaw : PDG.CondEquiv game system) : True := by
  fail_if_success
    Fact checkedLaw: The game game is conditionally equivalent to system by
      conditionalLaw
  trivial

example (left right : PDS X Y) (fact : PDS.Equivalent left right) :
    PDS.Equivalent left right := by
  fail_if_success
    The PDS laws left and right are observationally equivalent by fact
  exact fact

example (left right : PDG X Y) (fact : PDG.EquivalentAsGames left right) :
    PDG.EquivalentAsGames left right := by
  The games left and right are equivalent by fact

/- The systems named in the sentence are genuine operands, not decoration. -/
example (left right : PDS X Y) (fact : PDS.Equivalent left right) :
    PDS.Equivalent left right := by
  fail_if_success
    The PDS laws right and left are observationally equivalent by fact
  exact fact

example (game : PDG X Y) (system : PDS X Y)
    (fact : PDG.forget game = system) : PDG.forget game = system := by
  fail_if_success
    Ignoring the MBO of game yields system by fact
  exact fact

example (system : PDS X Y)
    (condition : System.DDS X Y → System.MonotoneCondition X)
    (game : PDG X Y) (fact : (PDS.adjoin system condition).1 = game) :
    (PDS.adjoin system condition).1 = game := by
  fail_if_success
    The game obtained by enhancing system with the MBO defined by condition is
      game by fact
  exact fact

example (game : PDG X Y) (system : PDS X Y)
    (conditionalLaw : PDG.CondEquiv game system) :
    PDG.CondEquiv game system := by
  fail_if_success
    The game game is conditionally equivalent to system by conditionalLaw
  exact conditionalLaw

example (predicate : List X → Prop) [DecidablePred predicate]
    (prefixClosed : PrefixClosed predicate)
    (game : PDG X Y) (system : PDS X Y)
    (gameNeverRefuses :
      ∀ γ ∈ game.support, ∀ (l : List X) (x : X), System.answer γ.1 l x ≠ none)
    (systemNeverRefuses :
      ∀ s ∈ system.support, ∀ (l : List X) (x : X), System.answer s l x ≠ none)
    (conditionalLaw : PDG.CondEquiv game system) :
    PDG.CondEquiv
      (Distribution.fTransform
        (fun γ : System.DDG X Y =>
          ((System.filterDom predicate prefixClosed γ.1, γ.2) : System.DDG X Y)) game)
      (Distribution.fTransform (System.filterDom predicate prefixClosed) system) := by
  fail_if_success
    Filtering both sides by predicate preserves conditional equivalence using
      prefixClosed, gameNeverRefuses, systemNeverRefuses, and conditionalLaw
  exact PDG.condEquiv_filterDom predicate prefixClosed gameNeverRefuses
    systemNeverRefuses conditionalLaw

example (queryBudget : ℕ) (game : PDG X Y) (system : PDS X Y)
    (gameNeverRefuses :
      ∀ γ ∈ game.support, ∀ (l : List X) (x : X), System.answer γ.1 l x ≠ none)
    (systemNeverRefuses :
      ∀ s ∈ system.support, ∀ (l : List X) (x : X), System.answer s l x ≠ none)
    (conditionalLaw : PDG.CondEquiv game system) :
    PDG.CondEquiv
      (Distribution.fTransform
        (fun γ : System.DDG X Y =>
          ((System.filterQueries queryBudget γ.1, γ.2) : System.DDG X Y)) game)
      (Distribution.fTransform (System.filterQueries queryBudget) system) := by
  fail_if_success
    Restricting both sides to queryBudget queries preserves conditional
      equivalence using gameNeverRefuses, systemNeverRefuses, and conditionalLaw
  exact PDG.condEquiv_filterQueries queryBudget gameNeverRefuses
    systemNeverRefuses conditionalLaw

example (game : PDG X Y) (system : PDS X Y) (bound : ENNReal)
    (gameNonnegative : game.NonNeg) (idealNonnegative : system.NonNeg)
    (equalWeight : game.weight = system.weight)
    (conditionalLaw : PDG.CondEquiv game system)
    (blindBound : ENNReal.ofReal (PDG.blindSupWinProb game) ≤ bound) :
    PDS.advFullyDefined (PDG.forget game) system ≤ bound := by
  fail_if_success
    Using conditionalLaw, idealNonnegative, gameNonnegative, and equalWeight,
      it suffices to prove the blind winning probability of game is at most bound
  fail_if_success
    Using conditionalLaw, gameNonnegative, idealNonnegative, and equalWeight,
      it suffices to prove the blind winning probability of game is at most bound
  exact (PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
    gameNonnegative idealNonnegative equalWeight conditionalLaw).trans blindBound

/- Compound overloaded notation is rejected before a reduction can record it
as `Nat` while its backend consumes it as `ENNReal`. -/
example (game : PDG X Y) (system : PDS X Y)
    (gameNonnegative : game.NonNeg) (idealNonnegative : system.NonNeg)
    (equalWeight : game.weight = system.weight)
    (conditionalLaw : PDG.CondEquiv game system)
    (blindBound : ENNReal.ofReal (PDG.blindSupWinProb game) ≤ (0 : ENNReal)) :
    PDS.advFullyDefined (PDG.forget game) system ≤ (0 : ENNReal) := by
  fail_if_success
    test_reduce_to_blind game to (0 + 0) using conditionalLaw,
      gameNonnegative, idealNonnegative, equalWeight
  exact (PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
    gameNonnegative idealNonnegative equalWeight conditionalLaw).trans blindBound

example (game : PDG X Y) (bound : ℝ)
    (fixedBound : ∀ (environment : System.DDE.Total Y X),
      System.DDE.Total.NonAdaptive environment → ∀ rounds : ℕ,
        PDG.winningMass environment rounds game ≤ bound) :
    PDG.blindSupWinProb game ≤ bound := by
  fail_if_success
    To bound the blind winning probability of game,
      fix environment with nonadaptive : True, and horizon rounds
  fail_if_success
    To bound the blind winning probability of game,
      fix environment with nonadaptive :
        System.DDE.Total.NonAdaptive environment, and horizon rounds
  exact PDG.blindSupWinProb_le_of_forall fixedBound

/- A wrong route remains rejected: conditional equivalence cannot close an
unrelated proposition. -/
/- error: This sentence cannot establish -/
#guard_msgs (substring := true) in
example (game : PDG X Y) (system : PDS X Y)
    (conditionalLaw : PDG.CondEquiv game system) : True := by
  The game game is conditionally equivalent to system by conditionalLaw

example (game : PDG X Y) (system : PDS X Y)
    (conditionalLaw : PDG.CondEquiv game system) :
    PDG.CondEquiv game system := by
  fail_if_success
    The game game is conditionally equivalent to system by conditionalLaw
  exact conditionalLaw

end CryptoLanguage.Verbose.Tests.RandomSystems
