import RandomSystems.Observation

set_option autoImplicit false

/-!
# Random-system games

Lanzenberger, Definitions 2.20--2.22 (printed pp. 16--17): a deterministic
game is a system paired with a monotone condition on query histories, and a
probabilistic game is a distribution over those pairs. The condition is not
visible during interaction.
-/

noncomputable section

namespace RandomSystems

open Classical
open Probability

universe u v

namespace System

variable {X : Type u} {Y : Type v}

/-- Lanzenberger, Definition 2.20: a Boolean condition that remains true under
extension of the query history. -/
abbrev MC (X : Type u) : Type u :=
  {condition : List X → Bool //
    ∀ ⦃initial final : List X⦄, initial <+: final →
      condition initial = true → condition final = true}

/-- Lanzenberger, Definition 2.20: a deterministic discrete game is a system
paired with a monotone condition. -/
structure DDG (X : Type u) (Y : Type v) where
  system : DDS X Y
  condition : MC X

/-- Lanzenberger, Definition 2.25: a winner is a deterministic environment.
The environment sees system answers, but not the game's condition. -/
abbrev Winner (X : Type u) (Y : Type v) := DDE Y X

/-- Lanzenberger, Definition 2.21: the ordinary transcript together with the
condition evaluated on its query history. -/
def gameTr (game : DDG X Y) (winner : Winner X Y) :
    Part (Transcript X Y × Bool) :=
  (tr winner game.system).map fun transcript =>
    (transcript, game.condition.1 (transcript.map Prod.fst))

/-- Lanzenberger, Definition 2.25: a winner wins when the condition is true at
the end of its interaction with the game. -/
def Wins (winner : Winner X Y) (game : DDG X Y) : Prop :=
  ∃ transcript : Transcript X Y, (transcript, true) ∈ gameTr game winner

end System

/-- Lanzenberger, Definition 2.22: a probabilistic discrete game is a
distribution over deterministic discrete games. -/
abbrev PDG (X : Type u) (Y : Type v) : Type (max u v) :=
  Distribution (System.DDG X Y)

namespace PDG

variable {X : Type u} {Y : Type v}

/-- Lanzenberger, Definition 2.20: every deterministic game in the law has
the same system domain. -/
def HasDomain (game : PDG X Y) (domain : Set (List X)) : Prop :=
  ∀ deterministic ∈ game.support,
    System.dom deterministic.system = domain

/-- The PDS obtained by forgetting the condition of every deterministic
game. -/
def underlying (game : PDG X Y) : PDS X Y :=
  Distribution.fTransform System.DDG.system game

/-- Forgetting the condition preserves a probability law. -/
lemma isProbDist_underlying {game : PDG X Y}
    (probability : game.isProbDist) : game.underlying.isProbDist :=
  Distribution.fTransform_isProbDist _ probability

/-- Forgetting the condition preserves the common deterministic domain. -/
lemma hasDomain_underlying (game : PDG X Y) (domain : Set (List X))
    (hasDomain : HasDomain game domain) :
    PDS.HasDomain game.underlying domain := by
  intro system supported
  obtain ⟨deterministic, deterministicSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      System.DDG.system game supported
  exact hasDomain deterministic deterministicSupported

/-- The law of Lanzenberger's game transcript under a deterministic winner. -/
def gameTrLaw (winner : System.Winner X Y) (game : PDG X Y) :
    Distribution (Option (System.Transcript X Y × Bool)) :=
  Distribution.fTransform
    (fun deterministic => (System.gameTr deterministic winner).toOption) game

end PDG

end RandomSystems
