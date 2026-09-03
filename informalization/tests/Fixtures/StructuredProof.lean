import Init

/- A dependency-free stand-in for the topology vocabulary used by the optional
Rudin adapter.  The fixture deliberately uses the conventional declaration
names because the adapter is keyed by elaborated constants, not source text. -/
class TopologicalSpace (X : Type) : Type where
  marker : True

def IsOpen {X : Type} [TopologicalSpace X] (_set : X → Prop) : Prop := True

namespace RandomSystems

abbrev PDS (_X _Y : Type) := Nat

namespace PDS

def advFullyDefined {X Y : Type} (S T : RandomSystems.PDS X Y) : Nat :=
  S - S + (T - T)

end PDS

end RandomSystems

namespace Fixtures

def Related (P Q : Prop) : Prop := P → Q

theorem structured (P Q R : Prop) (hp : P) (hpq : P → Q) (hqr : Q → R) : P ∧ R := by
  constructor
  · exact hp
  · have hq : Q := hpq hp
    exact hqr hq

theorem configuredLanguage (P Q : Prop) (h : P → Q) : Related P Q := by
  exact h

theorem calculated (a b c : Nat) (hab : a = b) (hbc : b = c) : a = c := by
  calc
    a = b := hab
    _ = c := hbc

theorem arithmeticBound (q N : Nat) (h : q ≤ N) : q ≤ N := by
  exact h

theorem configuredAdvantage {X Y : Type} (S T : RandomSystems.PDS X Y) (ε : Nat)
    (h : RandomSystems.PDS.advFullyDefined S T ≤ ε) :
    RandomSystems.PDS.advFullyDefined S T ≤ ε := by
  exact h

/-- Negative fixture: a list is not a transcript merely because its carrier is
`List`. -/
theorem ordinaryList (values : List Nat) : values = values := by
  rfl

/-- Negative fixture: a predicate is not a cryptographic bad event merely
because its local name is `Bad`. -/
theorem arbitraryBadName (Bad : Nat → Prop) (value : Nat) (h : ¬ Bad value) :
    ¬ Bad value := by
  exact h

theorem topologyVocabulary (X : Type) [TopologicalSpace X] (U : X → Prop)
    (hU : IsOpen U) : IsOpen U := by
  exact hU

end Fixtures
