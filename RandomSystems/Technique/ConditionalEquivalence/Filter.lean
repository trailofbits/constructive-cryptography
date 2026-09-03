/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Game.Filter
import RandomSystems.Technique.ConditionalEquivalence

set_option autoImplicit false

/-!
# Conditional equivalence under a common domain restriction
-/

noncomputable section

namespace RandomSystems

open Probability

universe u v

variable {X : Type u} {Y : Type v}

namespace System.DDG

/-- Restricting the visible domain preserves the initial value of the MBO. -/
lemma initiallyFalse_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (game : DDG X Y) (initiallyFalse : game.InitiallyFalse) :
    (game.filterDom P hP).InitiallyFalse :=
  initiallyFalse

end System.DDG

namespace PDG

/-- A common domain restriction preserves an initially-false game law. -/
lemma initiallyFalse_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (game : PDG X Y) (initiallyFalse : game.InitiallyFalse) :
    (PDG.filterDom P hP game).InitiallyFalse := by
  apply PDG.initiallyFalse_fTransform
  intro deterministic supported
  exact deterministic.initiallyFalse_filterDom P hP
    (initiallyFalse deterministic supported)

end PDG

namespace ConditionalEquivalence

/-- Applying the same prefix-closed domain restriction to a game and its
target preserves conditional equivalence. -/
lemma ConditionallyEquivalent.filterDom
    {game : PDG X Y} {target : PDS X Y}
    (equivalent : game |≡ target)
    (P : List X → Prop) (hP : PrefixClosed P) :
    PDG.filterDom P hP game |≡ PDS.filterDom P hP target := by
  refine ⟨PDG.initiallyFalse_filterDom P hP game
    equivalent.initiallyFalse, ?_⟩
  intro transcript nonempty gameNotWon targetDefined
  by_cases admitted : P (transcript.map Prod.fst)
  · have massAfalseEqual :
        massAfalse (PDG.filterDom P hP game)
            (transcript.map Prod.fst) =
          massAfalse game (transcript.map Prod.fst) := by
      unfold massAfalse PDG.filterDom
      rw [Distribution.mass_fTransform]
      apply Distribution.mass_congr
      intro deterministic
      constructor
      · rintro ⟨historyAdmitted, conditionFalse⟩
        exact ⟨historyAdmitted.1, conditionFalse⟩
      · rintro ⟨historyAdmitted, conditionFalse⟩
        exact ⟨⟨historyAdmitted, admitted⟩, conditionFalse⟩
    have massDomEqual :
        massDom (PDS.filterDom P hP target)
            (transcript.map Prod.fst) =
          massDom target (transcript.map Prod.fst) := by
      unfold massDom PDS.filterDom
      rw [Distribution.mass_fTransform]
      apply Distribution.mass_congr
      intro deterministic
      constructor
      · exact fun historyAdmitted => historyAdmitted.1
      · exact fun historyAdmitted => ⟨historyAdmitted, admitted⟩
    have massYAfalseEqual :
        massYAfalse (PDG.filterDom P hP game) transcript =
          massYAfalse game transcript := by
      unfold massYAfalse PDG.filterDom
      rw [Distribution.mass_fTransform]
      apply Distribution.mass_congr
      intro deterministic
      constructor
      · rintro ⟨consistent, conditionFalse⟩
        exact ⟨((System.systemConsistent_filterDom_iff
          P hP deterministic.system transcript nonempty).mp consistent).1,
          conditionFalse⟩
      · rintro ⟨consistent, conditionFalse⟩
        exact ⟨(System.systemConsistent_filterDom_iff
          P hP deterministic.system transcript nonempty).mpr
            ⟨consistent, admitted⟩, conditionFalse⟩
    have transcriptSystemFactorEqual :
        PDS.transcriptSystemFactor (PDS.filterDom P hP target) transcript =
          PDS.transcriptSystemFactor target transcript := by
      unfold PDS.transcriptSystemFactor PDS.filterDom
      rw [Distribution.mass_fTransform]
      apply Distribution.mass_congr
      intro deterministic
      exact (System.systemConsistent_filterDom_iff
        P hP deterministic transcript nonempty).trans
          ⟨fun consistent => consistent.1,
            fun consistent => ⟨consistent, admitted⟩⟩
    have originalEquality := equivalent.mass_eq transcript nonempty
      (massAfalseEqual ▸ gameNotWon) (massDomEqual ▸ targetDefined)
    rw [massYAfalseEqual, massDomEqual, transcriptSystemFactorEqual,
      massAfalseEqual]
    exact originalEquality
  · have massAfalseZero :
        massAfalse (PDG.filterDom P hP game)
            (transcript.map Prod.fst) = 0 := by
      unfold massAfalse PDG.filterDom
      rw [Distribution.mass_fTransform]
      apply Distribution.mass_eq_zero_of_forall_not
      intro deterministic notWon
      exact admitted notWon.1.2
    exact (gameNotWon massAfalseZero).elim

/-- Applying one bundled domain restriction to a game and its target preserves
conditional equivalence. -/
lemma ConditionallyEquivalent.domain_filter
    {game : PDG X Y} {target : PDS X Y}
    (equivalent : game |≡ target) (restriction : DomainFilter X) :
    restriction • game |≡ restriction • target :=
  equivalent.filterDom restriction.predicate restriction.prefixClosed

end ConditionalEquivalence

end RandomSystems
