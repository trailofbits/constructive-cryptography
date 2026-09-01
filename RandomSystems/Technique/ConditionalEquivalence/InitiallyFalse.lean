import RandomSystems.Game

set_option autoImplicit false

/-!
# Initially false game conditions

Lanzenberger's monotone-condition carrier permits either Boolean value on the
empty query history. CR18's initially-false MBO convention is an additional
hypothesis of the conditional-equivalence technique.
-/

noncomputable section

namespace RandomSystems

open Probability

universe u v w

namespace System.DDG

variable {X : Type u} {Y : Type v}

/-- CR18 says that the monotone game bit “is initially set to 0” before
Definition 3.22 (printed p. 71). Lean represents that initial value by
`false`. -/
def InitiallyFalse (game : DDG X Y) : Prop :=
  game.condition.1 [] = false

end System.DDG

namespace PDG

variable {A : Type w} {X : Type u} {Y : Type v}

/-- Every deterministic game in the law has a condition that is false before
the first query. -/
def InitiallyFalse (game : PDG X Y) : Prop :=
  ∀ deterministic ∈ game.support, deterministic.InitiallyFalse

/-- A pushforward is initially false when every supported source value maps
to an initially false deterministic game. -/
lemma initiallyFalse_fTransform (source : Distribution A)
    (toGame : A → System.DDG X Y)
    (initiallyFalse : ∀ value ∈ source.support,
      (toGame value).InitiallyFalse) :
    PDG.InitiallyFalse (Distribution.fTransform toGame source) := by
  intro deterministic supported
  obtain ⟨value, valueSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      toGame source supported
  exact initiallyFalse value valueSupported

end PDG

end RandomSystems
