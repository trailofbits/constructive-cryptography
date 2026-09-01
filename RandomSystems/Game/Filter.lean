/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Filter
import RandomSystems.Game

set_option autoImplicit false

/-!
# Domain-filtered games

A common domain restriction changes the visible system of a game and leaves
its monotone condition unchanged.
-/

noncomputable section

namespace RandomSystems

open Probability

universe u v

namespace System.DDG

variable {X : Type u} {Y : Type v}

/-- Restrict a deterministic game's visible system by a prefix-closed history
predicate. -/
def filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (game : DDG X Y) : DDG X Y where
  system := System.filterDom P hP game.system
  condition := game.condition

end System.DDG

namespace PDG

variable {X : Type u} {Y : Type v}

/-- Apply one prefix-closed domain restriction to every deterministic game. -/
def filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (game : PDG X Y) : PDG X Y :=
  Distribution.fTransform (System.DDG.filterDom P hP) game

/-- Forgetting the condition commutes with a common domain restriction. -/
lemma underlying_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (game : PDG X Y) :
    underlying (filterDom P hP game) =
      PDS.filterDom P hP (underlying game) := by
  calc
    underlying (filterDom P hP game) =
        Distribution.fTransform
          (System.DDG.system ∘ System.DDG.filterDom P hP) game :=
      Distribution.fTransform_fTransform
        System.DDG.system (System.DDG.filterDom P hP) game
    _ = Distribution.fTransform
        (System.filterDom P hP ∘ System.DDG.system) game := by
      apply Distribution.fTransform_congr
      intro deterministic _
      rfl
    _ = Distribution.fTransform (System.filterDom P hP)
        (Distribution.fTransform System.DDG.system game) :=
      (Distribution.fTransform_fTransform
        (System.filterDom P hP) System.DDG.system game).symm
    _ = PDS.filterDom P hP (underlying game) := by
      change Distribution.fTransform (System.filterDom P hP)
          (Distribution.fTransform System.DDG.system game) =
        Distribution.fTransform (System.filterDom P hP) (underlying game)
      rfl

/-- Restriction preserves a probability law on games. -/
lemma isProbDist_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    {game : PDG X Y} (probability : game.isProbDist) :
    (filterDom P hP game).isProbDist :=
  Distribution.fTransform_isProbDist _ probability

/-- Restriction intersects a common game domain with its admission
predicate. -/
lemma hasDomain_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (game : PDG X Y) (domain : Set (List X))
    (hasDomain : HasDomain game domain) :
    HasDomain (filterDom P hP game)
      {history | history ∈ domain ∧ P history} := by
  intro restricted supported
  obtain ⟨original, originalSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      (System.DDG.filterDom P hP) game supported
  ext history
  change history ∈
      System.dom (System.filterDom P hP original.system) ↔ _
  rw [System.mem_dom_filterDom, hasDomain original originalSupported]
  rfl

end PDG

end RandomSystems
