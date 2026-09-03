import Verbose

open Probability
open RandomSystems
open scoped CryptoVerbose ENNReal

namespace CryptoLanguage.Verbose.Tests.Notation

example (q : Nat) : ([q] : List Nat) = List.singleton q := rfl

example (X Y : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    URF(X, Y) = PDS.urf X Y := rfl

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) :
    [q] URF(X) = Switching.limit q (PDS.urf X X) := rfl

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) :
    [q] URP(X) = Switching.limit q (PDS.urp X) := rfl

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q r : Nat) :
    [q] ([r] URF(X)) =
      Switching.limit q (Switching.limit r (PDS.urf X X)) := rfl

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) :
    id ([q] URF(X)) = Switching.limit q (PDS.urf X X) := rfl

example (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) :
    Adv⊥([q] URF(X), [q] URP(X)) =
      PDS.advFullyDefined (Switching.limit q (PDS.urf X X))
        (Switching.limit q (PDS.urp X)) := rfl

end CryptoLanguage.Verbose.Tests.Notation
