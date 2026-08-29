/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem
import RandomSystems.Distance

set_option autoImplicit false

namespace RandomSystems

/-!
# Ordered parallel composition of fixed-interface random systems

Lanzenberger, Definition 2.13 (printed p. 14): “The parallel composition of a
family of `(Xᵢ, Yᵢ)`-systems” routes each tagged query to its corresponding
component.  This module specializes that definition to an ordered binary sum.

The presentation-level congruence and fibrewise distance bounds are Lean
consequences of this deterministic routing law.  The construction uses only
the complete finite-history functions underlying DDSs and DDEs.
-/

noncomputable section

open Classical
open Probability (Distribution)
open scoped ENNReal

universe u₁ v₁ u₂ v₂

open RandomSystems.System

variable {X₁ : Type u₁} {Y₁ : Type v₁}
variable {X₂ : Type u₂} {Y₂ : Type v₂}

private def leftQueries : List (X₁ ⊕ X₂) → List X₁ :=
  List.filterMap fun
    | Sum.inl query => some query
    | Sum.inr _ => none

private def rightQueries : List (X₁ ⊕ X₂) → List X₂ :=
  List.filterMap fun
    | Sum.inl _ => none
    | Sum.inr query => some query

private theorem leftQueries_prefix {first second : List (X₁ ⊕ X₂)}
    (hprefix : first <+: second) :
    leftQueries first <+: leftQueries second := by
  obtain ⟨tail, rfl⟩ := hprefix
  exact ⟨leftQueries tail, by simp [leftQueries, List.filterMap_append]⟩

private theorem rightQueries_prefix {first second : List (X₁ ⊕ X₂)}
    (hprefix : first <+: second) :
    rightQueries first <+: rightQueries second := by
  obtain ⟨tail, rfl⟩ := hprefix
  exact ⟨rightQueries tail, by simp [rightQueries, List.filterMap_append]⟩

private theorem leftQueries_nonempty_of_getLast?_inl
    (history : List (X₁ ⊕ X₂)) (query : X₁)
    (lastEqual : history.getLast? = some (Sum.inl query)) :
    leftQueries history ≠ [] := by
  intro empty
  have member : query ∈ leftQueries history := by
    rw [leftQueries, List.mem_filterMap]
    obtain ⟨prior, rfl⟩ := List.getLast?_eq_some_iff.mp lastEqual
    exact ⟨Sum.inl query, by simp, rfl⟩
  simp [empty] at member

private theorem rightQueries_nonempty_of_getLast?_inr
    (history : List (X₁ ⊕ X₂)) (query : X₂)
    (lastEqual : history.getLast? = some (Sum.inr query)) :
    rightQueries history ≠ [] := by
  intro empty
  have member : query ∈ rightQueries history := by
    rw [rightQueries, List.mem_filterMap]
    obtain ⟨prior, rfl⟩ := List.getLast?_eq_some_iff.mp lastEqual
    exact ⟨Sum.inr query, by simp, rfl⟩
  simp [empty] at member

private theorem leftQueries_nonempty_of_mem_inl
    (history : List (X₁ ⊕ X₂)) (query : X₁)
    (member : Sum.inl query ∈ history) :
    leftQueries history ≠ [] := by
  intro empty
  have kept : query ∈ leftQueries history := by
    rw [leftQueries, List.mem_filterMap]
    exact ⟨Sum.inl query, member, rfl⟩
  simp [empty] at kept

private theorem rightQueries_nonempty_of_mem_inr
    (history : List (X₁ ⊕ X₂)) (query : X₂)
    (member : Sum.inr query ∈ history) :
    rightQueries history ≠ [] := by
  intro empty
  have kept : query ∈ rightQueries history := by
    rw [rightQueries, List.mem_filterMap]
    exact ⟨Sum.inr query, member, rfl⟩
  simp [empty] at kept

private def parallelOutput (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂)
    (history : List (X₁ ⊕ X₂))
    (defined : history ≠ [] ∧
      (leftQueries history = [] ∨
        leftQueries history ∈ RandomSystems.System.dom left) ∧
      (rightQueries history = [] ∨
        rightQueries history ∈ RandomSystems.System.dom right))
    (last : X₁ ⊕ X₂) (lastMem : last ∈ history) : Y₁ ⊕ Y₂ :=
  match last with
  | Sum.inl query =>
      Sum.inl (RandomSystems.System.output left (leftQueries history) (by
        rcases defined.2.1 with empty | admitted
        · exact False.elim
            (leftQueries_nonempty_of_mem_inl history query lastMem empty)
        · exact admitted))
  | Sum.inr query =>
      Sum.inr (RandomSystems.System.output right (rightQueries history) (by
        rcases defined.2.2 with empty | admitted
        · exact False.elim
            (rightQueries_nonempty_of_mem_inr history query lastMem empty)
        · exact admitted))

private theorem parallelOutput_congr_last
    (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂)
    (history : List (X₁ ⊕ X₂))
    (defined : history ≠ [] ∧
      (leftQueries history = [] ∨
        leftQueries history ∈ RandomSystems.System.dom left) ∧
      (rightQueries history = [] ∨
        rightQueries history ∈ RandomSystems.System.dom right))
    {first second : X₁ ⊕ X₂} (equal : first = second)
    (firstMem : first ∈ history) (secondMem : second ∈ history) :
    parallelOutput left right history defined first firstMem =
      parallelOutput left right history defined second secondMem := by
  subst second
  rfl

private def parallelRaw (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂) :
    RandomSystems.System.Raw (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  fun history =>
    { Dom := history ≠ [] ∧
        (leftQueries history = [] ∨
          leftQueries history ∈ RandomSystems.System.dom left) ∧
        (rightQueries history = [] ∨
          rightQueries history ∈ RandomSystems.System.dom right)
      get := fun defined =>
        parallelOutput left right history defined
          (history.getLast defined.1) (List.getLast_mem defined.1) }

private def parallel (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂) :
    RandomSystems.System.DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  ⟨parallelRaw left right, by
    constructor
    · simp [parallelRaw]
    · intro first second hprefix firstNonempty secondDefined
      refine ⟨firstNonempty, ?_, ?_⟩
      · rcases secondDefined.2.1 with empty | admitted
        · left
          exact List.eq_nil_of_prefix_nil
            (empty ▸ leftQueries_prefix (X₁ := X₁) (X₂ := X₂) hprefix)
        · by_cases firstEmpty : leftQueries first = []
          · exact Or.inl firstEmpty
          · exact Or.inr (RandomSystems.System.prefix_closed left
              (leftQueries_prefix hprefix)
              firstEmpty admitted)
      · rcases secondDefined.2.2 with empty | admitted
        · left
          exact List.eq_nil_of_prefix_nil
            (empty ▸ rightQueries_prefix (X₁ := X₁) (X₂ := X₂) hprefix)
        · by_cases firstEmpty : rightQueries first = []
          · exact Or.inl firstEmpty
          · exact Or.inr (RandomSystems.System.prefix_closed right
              (rightQueries_prefix hprefix)
              firstEmpty admitted)⟩

@[simp]
private theorem dom_parallel (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂) :
    RandomSystems.System.dom (parallel left right) =
      {history | history ≠ [] ∧
        (leftQueries history = [] ∨
          leftQueries history ∈ RandomSystems.System.dom left) ∧
        (rightQueries history = [] ∨
          rightQueries history ∈ RandomSystems.System.dom right)} :=
  rfl

@[simp]
private theorem leftQueries_append_inl (history : List (X₁ ⊕ X₂)) (query : X₁) :
    leftQueries (history ++ [Sum.inl query]) = leftQueries history ++ [query] := by
  simp [leftQueries, List.filterMap_append]

@[simp]
private theorem leftQueries_append_inr (history : List (X₁ ⊕ X₂)) (query : X₂) :
    leftQueries (history ++ [Sum.inr query]) = leftQueries history := by
  simp [leftQueries, List.filterMap_append]

@[simp]
private theorem rightQueries_append_inl (history : List (X₁ ⊕ X₂)) (query : X₁) :
    rightQueries (history ++ [Sum.inl query]) = rightQueries history := by
  simp [rightQueries, List.filterMap_append]

@[simp]
private theorem rightQueries_append_inr (history : List (X₁ ⊕ X₂)) (query : X₂) :
    rightQueries (history ++ [Sum.inr query]) = rightQueries history ++ [query] := by
  simp [rightQueries, List.filterMap_append]

private theorem output_parallel_left (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂) (history : List (X₁ ⊕ X₂))
    (query : X₁)
    (defined : history ++ [Sum.inl query] ∈
      RandomSystems.System.dom (parallel left right)) :
    RandomSystems.System.output (parallel left right)
        (history ++ [Sum.inl query]) defined =
      Sum.inl (RandomSystems.System.output left
        (leftQueries history ++ [query]) (by
          have component := (dom_parallel left right ▸ defined).2.1
          simpa using component.resolve_left (by simp))) := by
  change (parallelRaw left right (history ++ [Sum.inl query])).get defined = _
  unfold parallelRaw
  dsimp
  calc
    parallelOutput left right (history ++ [Sum.inl query]) defined
        ((history ++ [Sum.inl query]).getLast (by simp)) _ =
      parallelOutput left right (history ++ [Sum.inl query]) defined
        (Sum.inl query) (by simp) :=
          parallelOutput_congr_last left right _ defined
            (List.getLast_append_singleton history) _ _
    _ = _ := by simp [parallelOutput]

private theorem output_parallel_right (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂) (history : List (X₁ ⊕ X₂))
    (query : X₂)
    (defined : history ++ [Sum.inr query] ∈
      RandomSystems.System.dom (parallel left right)) :
    RandomSystems.System.output (parallel left right)
        (history ++ [Sum.inr query]) defined =
      Sum.inr (RandomSystems.System.output right
        (rightQueries history ++ [query]) (by
          have component := (dom_parallel left right ▸ defined).2.2
          simpa using component.resolve_left (by simp))) := by
  change (parallelRaw left right (history ++ [Sum.inr query])).get defined = _
  unfold parallelRaw
  dsimp
  calc
    parallelOutput left right (history ++ [Sum.inr query]) defined
        ((history ++ [Sum.inr query]).getLast (by simp)) _ =
      parallelOutput left right (history ++ [Sum.inr query]) defined
        (Sum.inr query) (by simp) :=
          parallelOutput_congr_last left right _ defined
            (List.getLast_append_singleton history) _ _
    _ = _ := by simp [parallelOutput]

private def EnvConsistent {X : Type*} {Y : Type*}
    (environment : DDE Y X) (transcript : Transcript X Y) : Prop :=
  ∀ k, (hk : k < transcript.length) →
    ∃ hdom : (transcript.take k).map Prod.snd ∈ environment.1.Dom,
      (environment.1 ((transcript.take k).map Prod.snd)).get hdom = transcript[k].1

private def SystemConsistent {X : Type*} {Y : Type*}
    (system : DDS X Y) (transcript : Transcript X Y) : Prop :=
  ∀ k, (hk : k < transcript.length) →
    ∃ hdom : (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈ dom system,
      output system ((transcript.take k).map Prod.fst ++ [transcript[k].1]) hdom =
        transcript[k].2

private def FinalAt {X : Type*} {Y : Type*}
    (environment : DDE Y X) (rounds : Nat) (transcript : Transcript X Y) : Prop :=
  transcript.length = rounds ∨
    (transcript.length < rounds ∧ transcript.map Prod.snd ∉ environment.1.Dom)

private theorem systemConsistent_snoc_iff {X : Type*} {Y : Type*}
    (system : DDS X Y) (transcript : Transcript X Y) (event : X × Y) :
    SystemConsistent system (transcript ++ [event]) ↔
      SystemConsistent system transcript ∧
        ∃ hdom : transcript.map Prod.fst ++ [event.1] ∈ dom system,
          output system (transcript.map Prod.fst ++ [event.1]) hdom = event.2 := by
  constructor
  · intro consistent
    constructor
    · intro k hk
      have hk' : k < (transcript ++ [event]).length := by simp; omega
      have row := consistent k hk'
      simpa only [List.take_append_of_le_length (Nat.le_of_lt hk),
        List.getElem_append_left hk] using row
    · have row := consistent transcript.length (by simp)
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero] using row
  · rintro ⟨prior, last⟩ k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k transcript.length with earlier | atLast
    · have row := prior k earlier
      simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier),
        List.getElem_append_left earlier] using row
    · have equal : k = transcript.length := by omega
      subst equal
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero] using last

private abbrev Dialogue (X₁ : Type u₁) (Y₁ : Type v₁)
    (X₂ : Type u₂) (Y₂ : Type v₂) :=
  List ((X₁ × Y₁) ⊕ (X₂ × Y₂))

private def taggedPair : ((X₁ × Y₁) ⊕ (X₂ × Y₂)) →
    (X₁ ⊕ X₂) × (Y₁ ⊕ Y₂)
  | Sum.inl pair => (Sum.inl pair.1, Sum.inl pair.2)
  | Sum.inr pair => (Sum.inr pair.1, Sum.inr pair.2)

private def dialogueTranscript (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    RandomSystems.System.Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  dialogue.map taggedPair

private def leftTranscript (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    RandomSystems.System.Transcript X₁ Y₁ :=
  dialogue.filterMap fun
    | Sum.inl pair => some pair
    | Sum.inr _ => none

private def rightTranscript (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    RandomSystems.System.Transcript X₂ Y₂ :=
  dialogue.filterMap fun
    | Sum.inl _ => none
    | Sum.inr pair => some pair

private def LeftRealizes (left : RandomSystems.System.DDS X₁ Y₁)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) : Prop :=
  ∀ k, (hk : k < dialogue.length) →
    match dialogue[k] with
    | Sum.inl pair =>
        ∃ hdom : leftQueries ((dialogue.take k).map (taggedPair · |>.1)) ++
            [pair.1] ∈ RandomSystems.System.dom left,
          RandomSystems.System.output left
            (leftQueries ((dialogue.take k).map (taggedPair · |>.1)) ++
              [pair.1]) hdom = pair.2
    | Sum.inr _ => True

private def RightRealizes (right : RandomSystems.System.DDS X₂ Y₂)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) : Prop :=
  ∀ k, (hk : k < dialogue.length) →
    match dialogue[k] with
    | Sum.inl _ => True
    | Sum.inr pair =>
        ∃ hdom : rightQueries ((dialogue.take k).map (taggedPair · |>.1)) ++
            [pair.1] ∈ RandomSystems.System.dom right,
          RandomSystems.System.output right
            (rightQueries ((dialogue.take k).map (taggedPair · |>.1)) ++
              [pair.1]) hdom = pair.2

private theorem leftRealizes_take_early
    (left : RandomSystems.System.DDS X₁ Y₁)
    {dialogue : Dialogue X₁ Y₁ X₂ Y₂}
    (realizes : LeftRealizes left dialogue) (n : Nat) :
    LeftRealizes left (dialogue.take n) := by
  intro k hk
  have kDialogue : k < dialogue.length := by
    rw [List.length_take] at hk
    omega
  have base := realizes k kDialogue
  have kLe : k ≤ n := by
    rw [List.length_take] at hk
    omega
  simpa only [List.getElem_take, List.take_take, min_eq_left kLe] using base

private theorem rightRealizes_take_early
    (right : RandomSystems.System.DDS X₂ Y₂)
    {dialogue : Dialogue X₁ Y₁ X₂ Y₂}
    (realizes : RightRealizes right dialogue) (n : Nat) :
    RightRealizes right (dialogue.take n) := by
  intro k hk
  have kDialogue : k < dialogue.length := by
    rw [List.length_take] at hk
    omega
  have base := realizes k kDialogue
  have kLe : k ≤ n := by
    rw [List.length_take] at hk
    omega
  simpa only [List.getElem_take, List.take_take, min_eq_left kLe] using base

private theorem leftTranscript_inputs (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    (leftTranscript dialogue).map Prod.fst =
      leftQueries (dialogue.map (taggedPair · |>.1)) := by
  rw [leftTranscript, leftQueries, List.map_filterMap, List.filterMap_map]
  apply List.filterMap_congr
  intro event _
  cases event <;> rfl

private theorem rightTranscript_inputs (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    (rightTranscript dialogue).map Prod.fst =
      rightQueries (dialogue.map (taggedPair · |>.1)) := by
  rw [rightTranscript, rightQueries, List.map_filterMap, List.filterMap_map]
  apply List.filterMap_congr
  intro event _
  cases event <;> rfl

private theorem leftRealizes_snoc_inl_iff
    (left : RandomSystems.System.DDS X₁ Y₁)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) (pair : X₁ × Y₁) :
    LeftRealizes left (dialogue ++ [Sum.inl pair]) ↔
      LeftRealizes left dialogue ∧
        ∃ hdom : leftQueries (dialogue.map (taggedPair · |>.1)) ++
            [pair.1] ∈ RandomSystems.System.dom left,
          RandomSystems.System.output left
            (leftQueries (dialogue.map (taggedPair · |>.1)) ++ [pair.1]) hdom =
              pair.2 := by
  constructor
  · intro realizes
    constructor
    · simpa only [List.take_append_of_le_length le_rfl, List.take_length] using
        leftRealizes_take_early left realizes dialogue.length
    · have row := realizes dialogue.length (by simp)
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero] using row
  · rintro ⟨prior, last⟩ k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k dialogue.length with earlier | atLast
    · have row := prior k earlier
      simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier),
        List.getElem_append_left earlier] using row
    · have equal : k = dialogue.length := by omega
      subst equal
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero] using last

private theorem leftRealizes_snoc_inr_iff
    (left : RandomSystems.System.DDS X₁ Y₁)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) (pair : X₂ × Y₂) :
    LeftRealizes left (dialogue ++ [Sum.inr pair]) ↔
      LeftRealizes left dialogue := by
  constructor
  · intro realizes
    simpa only [List.take_append_of_le_length le_rfl, List.take_length] using
      leftRealizes_take_early left realizes dialogue.length
  · intro prior k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k dialogue.length with earlier | atLast
    · have row := prior k earlier
      simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier),
        List.getElem_append_left earlier] using row
    · have equal : k = dialogue.length := by omega
      subst equal
      simp

private theorem rightRealizes_snoc_inl_iff
    (right : RandomSystems.System.DDS X₂ Y₂)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) (pair : X₁ × Y₁) :
    RightRealizes right (dialogue ++ [Sum.inl pair]) ↔
      RightRealizes right dialogue := by
  constructor
  · intro realizes
    simpa only [List.take_append_of_le_length le_rfl, List.take_length] using
      rightRealizes_take_early right realizes dialogue.length
  · intro prior k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k dialogue.length with earlier | atLast
    · have row := prior k earlier
      simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier),
        List.getElem_append_left earlier] using row
    · have equal : k = dialogue.length := by omega
      subst equal
      simp

private theorem rightRealizes_snoc_inr_iff
    (right : RandomSystems.System.DDS X₂ Y₂)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) (pair : X₂ × Y₂) :
    RightRealizes right (dialogue ++ [Sum.inr pair]) ↔
      RightRealizes right dialogue ∧
        ∃ hdom : rightQueries (dialogue.map (taggedPair · |>.1)) ++
            [pair.1] ∈ RandomSystems.System.dom right,
          RandomSystems.System.output right
            (rightQueries (dialogue.map (taggedPair · |>.1)) ++ [pair.1]) hdom =
              pair.2 := by
  constructor
  · intro realizes
    constructor
    · simpa only [List.take_append_of_le_length le_rfl, List.take_length] using
        rightRealizes_take_early right realizes dialogue.length
    · have row := realizes dialogue.length (by simp)
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero] using row
  · rintro ⟨prior, last⟩ k hk
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k dialogue.length with earlier | atLast
    · have row := prior k earlier
      simpa only [List.take_append_of_le_length (Nat.le_of_lt earlier),
        List.getElem_append_left earlier] using row
    · have equal : k = dialogue.length := by omega
      subst equal
      simpa only [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl, Nat.sub_self,
        List.getElem_cons_zero] using last

private theorem leftRealizes_iff_systemConsistent
    (left : RandomSystems.System.DDS X₁ Y₁) :
    ∀ dialogue : Dialogue X₁ Y₁ X₂ Y₂,
      LeftRealizes left dialogue ↔
        SystemConsistent left (leftTranscript dialogue) := by
  intro dialogue
  induction dialogue using List.reverseRecOn with
  | nil => simp [LeftRealizes, SystemConsistent, leftTranscript]
  | append_singleton prior event inductionHypothesis =>
      cases event with
      | inl pair =>
          rw [leftRealizes_snoc_inl_iff,
            show leftTranscript (prior ++ [Sum.inl pair]) =
                leftTranscript prior ++ [pair] by
              simp [leftTranscript, List.filterMap_append],
            systemConsistent_snoc_iff, inductionHypothesis,
            leftTranscript_inputs]
      | inr pair =>
          rw [leftRealizes_snoc_inr_iff,
            show leftTranscript (prior ++ [Sum.inr pair]) =
                leftTranscript prior by
              simp [leftTranscript, List.filterMap_append],
            inductionHypothesis]

private theorem rightRealizes_iff_systemConsistent
    (right : RandomSystems.System.DDS X₂ Y₂) :
    ∀ dialogue : Dialogue X₁ Y₁ X₂ Y₂,
      RightRealizes right dialogue ↔
        SystemConsistent right (rightTranscript dialogue) := by
  intro dialogue
  induction dialogue using List.reverseRecOn with
  | nil => simp [RightRealizes, SystemConsistent, rightTranscript]
  | append_singleton prior event inductionHypothesis =>
      cases event with
      | inl pair =>
          rw [rightRealizes_snoc_inl_iff,
            show rightTranscript (prior ++ [Sum.inl pair]) =
                rightTranscript prior by
              simp [rightTranscript, List.filterMap_append],
            inductionHypothesis]
      | inr pair =>
          rw [rightRealizes_snoc_inr_iff,
            show rightTranscript (prior ++ [Sum.inr pair]) =
                rightTranscript prior ++ [pair] by
              simp [rightTranscript, List.filterMap_append],
            systemConsistent_snoc_iff, inductionHypothesis,
            rightTranscript_inputs]

private theorem leftRealizes_take (left : RandomSystems.System.DDS X₁ Y₁)
    {dialogue : Dialogue X₁ Y₁ X₂ Y₂}
    (realizes : LeftRealizes left dialogue) (n : Nat) :
    LeftRealizes left (dialogue.take n) := by
  intro k hk
  have kDialogue : k < dialogue.length := by
    rw [List.length_take] at hk
    omega
  have base := realizes k kDialogue
  have kLe : k ≤ n := by
    rw [List.length_take] at hk
    omega
  simpa only [List.getElem_take, List.take_take, min_eq_left kLe] using base

private theorem rightRealizes_take (right : RandomSystems.System.DDS X₂ Y₂)
    {dialogue : Dialogue X₁ Y₁ X₂ Y₂}
    (realizes : RightRealizes right dialogue) (n : Nat) :
    RightRealizes right (dialogue.take n) := by
  intro k hk
  have kDialogue : k < dialogue.length := by
    rw [List.length_take] at hk
    omega
  have base := realizes k kDialogue
  have kLe : k ≤ n := by
    rw [List.length_take] at hk
    omega
  simpa only [List.getElem_take, List.take_take, min_eq_left kLe] using base

private theorem leftRealizes_domain (left : RandomSystems.System.DDS X₁ Y₁) :
    ∀ {dialogue : Dialogue X₁ Y₁ X₂ Y₂}, LeftRealizes left dialogue →
      leftQueries (dialogue.map (taggedPair · |>.1)) = [] ∨
        leftQueries (dialogue.map (taggedPair · |>.1)) ∈
          RandomSystems.System.dom left := by
  intro dialogue realizes
  induction dialogue using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton prior event inductionHypothesis =>
      cases event with
      | inl pair =>
          right
          have last := realizes prior.length (by simp)
          have last' : ∃ hdom :
              leftQueries (prior.map (taggedPair · |>.1)) ++ [pair.1] ∈
                RandomSystems.System.dom left,
              RandomSystems.System.output left
                  (leftQueries (prior.map (taggedPair · |>.1)) ++ [pair.1]) hdom =
                pair.2 := by
            simpa only [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl, Nat.sub_self,
              List.getElem_cons_zero] using last
          simpa only [List.map_append, List.map_singleton, taggedPair,
            leftQueries_append_inl] using last'.choose
      | inr pair =>
          have priorRealizes : LeftRealizes left prior := by
            simpa only [List.take_append_of_le_length le_rfl, List.take_length] using
              leftRealizes_take left realizes prior.length
          simpa only [List.map_append, List.map_singleton, taggedPair,
            leftQueries_append_inr] using inductionHypothesis priorRealizes

private theorem rightRealizes_domain (right : RandomSystems.System.DDS X₂ Y₂) :
    ∀ {dialogue : Dialogue X₁ Y₁ X₂ Y₂}, RightRealizes right dialogue →
      rightQueries (dialogue.map (taggedPair · |>.1)) = [] ∨
        rightQueries (dialogue.map (taggedPair · |>.1)) ∈
          RandomSystems.System.dom right := by
  intro dialogue realizes
  induction dialogue using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton prior event inductionHypothesis =>
      cases event with
      | inl pair =>
          have priorRealizes : RightRealizes right prior := by
            simpa only [List.take_append_of_le_length le_rfl, List.take_length] using
              rightRealizes_take right realizes prior.length
          simpa only [List.map_append, List.map_singleton, taggedPair,
            rightQueries_append_inl] using inductionHypothesis priorRealizes
      | inr pair =>
          right
          have last := realizes prior.length (by simp)
          have last' : ∃ hdom :
              rightQueries (prior.map (taggedPair · |>.1)) ++ [pair.1] ∈
                RandomSystems.System.dom right,
              RandomSystems.System.output right
                  (rightQueries (prior.map (taggedPair · |>.1)) ++ [pair.1]) hdom =
                pair.2 := by
            simpa only [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl, Nat.sub_self,
              List.getElem_cons_zero] using last
          simpa only [List.map_append, List.map_singleton, taggedPair,
            rightQueries_append_inr] using last'.choose

private theorem systemConsistent_parallel_iff
    (left : RandomSystems.System.DDS X₁ Y₁)
    (right : RandomSystems.System.DDS X₂ Y₂)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    SystemConsistent (parallel left right) (dialogueTranscript dialogue) ↔
      LeftRealizes left dialogue ∧ RightRealizes right dialogue := by
  constructor
  -- Project joint consistency onto each tagged component.
  · intro joint
    constructor
    -- Every left-tagged event is admitted and answered by the left DDS.
    · intro k hk
      have mappedLength : k < (dialogueTranscript dialogue).length := by
        simpa only [dialogueTranscript, List.length_map] using hk
      obtain ⟨jointDomain, jointOutput⟩ := joint k mappedLength
      cases eventEqual : dialogue[k] with
      | inl pair =>
          -- Rewrite the joint history as the tagged left history at this event.
          let prior := (dialogue.take k).map (taggedPair · |>.1)
          have historyEqual :
              ((dialogueTranscript dialogue).take k).map Prod.fst ++
                  [(dialogueTranscript dialogue)[k].1] =
                prior ++ [Sum.inl pair.1] := by
            simp [prior, dialogueTranscript, List.map_map, Function.comp_def,
              eventEqual, taggedPair]
          have targetDomain : prior ++ [Sum.inl pair.1] ∈
              RandomSystems.System.dom (parallel left right) :=
            historyEqual ▸ jointDomain
          -- Joint consistency supplies the tagged left answer.
          have targetOutput :
              RandomSystems.System.output (parallel left right)
                  (prior ++ [Sum.inl pair.1]) targetDomain = Sum.inl pair.2 := by
            calc
              _ = RandomSystems.System.output (parallel left right)
                    (((dialogueTranscript dialogue).take k).map Prod.fst ++
                      [(dialogueTranscript dialogue)[k].1]) jointDomain :=
                RandomSystems.System.output_congr _ historyEqual.symm _ _
              _ = (dialogueTranscript dialogue)[k].2 := jointOutput
              _ = Sum.inl pair.2 := by
                simp [dialogueTranscript, eventEqual, taggedPair]
          -- The parallel-domain law projects admission to the left component.
          have leftDomain :
              leftQueries ((dialogue.take k).map (taggedPair · |>.1)) ++
                  [pair.1] ∈ RandomSystems.System.dom left := by
            have component := (dom_parallel left right ▸ targetDomain).2.1
            simpa only [prior, leftQueries_append_inl] using
              component.resolve_left (by simp)
          -- The parallel-output law projects the recorded answer to the left DDS.
          exact ⟨leftDomain, by
            have equation := output_parallel_left left right
              ((dialogue.take k).map (taggedPair · |>.1)) pair.1 targetDomain
            rw [equation] at targetOutput
            exact Sum.inl.inj targetOutput⟩
      | inr pair => trivial
    -- The right component is symmetric, using right-tagged events.
    · intro k hk
      have mappedLength : k < (dialogueTranscript dialogue).length := by
        simpa only [dialogueTranscript, List.length_map] using hk
      obtain ⟨jointDomain, jointOutput⟩ := joint k mappedLength
      cases eventEqual : dialogue[k] with
      | inl pair => trivial
      | inr pair =>
          -- Rewrite the joint history as the tagged right history at this event.
          let prior := (dialogue.take k).map (taggedPair · |>.1)
          have historyEqual :
              ((dialogueTranscript dialogue).take k).map Prod.fst ++
                  [(dialogueTranscript dialogue)[k].1] =
                prior ++ [Sum.inr pair.1] := by
            simp [prior, dialogueTranscript, List.map_map, Function.comp_def,
              eventEqual, taggedPair]
          have targetDomain : prior ++ [Sum.inr pair.1] ∈
              RandomSystems.System.dom (parallel left right) :=
            historyEqual ▸ jointDomain
          -- Joint consistency supplies the tagged right answer.
          have targetOutput :
              RandomSystems.System.output (parallel left right)
                  (prior ++ [Sum.inr pair.1]) targetDomain = Sum.inr pair.2 := by
            calc
              _ = RandomSystems.System.output (parallel left right)
                    (((dialogueTranscript dialogue).take k).map Prod.fst ++
                      [(dialogueTranscript dialogue)[k].1]) jointDomain :=
                RandomSystems.System.output_congr _ historyEqual.symm _ _
              _ = (dialogueTranscript dialogue)[k].2 := jointOutput
              _ = Sum.inr pair.2 := by
                simp [dialogueTranscript, eventEqual, taggedPair]
          -- The parallel-domain law projects admission to the right component.
          have rightDomain :
              rightQueries ((dialogue.take k).map (taggedPair · |>.1)) ++
                  [pair.1] ∈ RandomSystems.System.dom right := by
            have component := (dom_parallel left right ▸ targetDomain).2.2
            simpa only [prior, rightQueries_append_inr] using
              component.resolve_left (by simp)
          -- The parallel-output law projects the recorded answer to the right DDS.
          exact ⟨rightDomain, by
            have equation := output_parallel_right left right
              ((dialogue.take k).map (taggedPair · |>.1)) pair.1 targetDomain
            rw [equation] at targetOutput
            exact Sum.inr.inj targetOutput⟩
  -- Conversely, component realization supplies joint admission and output.
  · rintro ⟨leftRealizes, rightRealizes⟩ k hk
    have hkDialogue : k < dialogue.length := by
      simpa only [dialogueTranscript, List.length_map] using hk
    cases eventEqual : dialogue[k] with
    | inl pair =>
        -- Left realization supplies the active component's domain and answer.
        have leftAt := leftRealizes k hkDialogue
        simp only [eventEqual] at leftAt
        obtain ⟨leftDomain, leftOutput⟩ := leftAt
        let prior := (dialogue.take k).map (taggedPair · |>.1)
        -- The inactive right prefix and active left query give joint admission.
        have jointDomain :
            prior ++ [Sum.inl pair.1] ∈
              RandomSystems.System.dom (parallel left right) := by
          rw [dom_parallel]
          refine ⟨by simp, Or.inr ?_, ?_⟩
          · simpa only [prior, leftQueries_append_inl] using leftDomain
          · simpa only [prior, rightQueries_append_inl] using rightRealizes_domain right
              (rightRealizes_take right rightRealizes k)
        -- Routing embeds the left answer in the joint output alphabet.
        have jointOutput :
            RandomSystems.System.output (parallel left right)
                (prior ++ [Sum.inl pair.1]) jointDomain = Sum.inl pair.2 := by
          rw [output_parallel_left]
          exact congrArg Sum.inl leftOutput
        have historyEqual :
            ((dialogueTranscript dialogue).take k).map Prod.fst ++
                [(dialogueTranscript dialogue)[k].1] =
              prior ++ [Sum.inl pair.1] := by
          simp [prior, dialogueTranscript, List.map_map, Function.comp_def,
            eventEqual, taggedPair]
        -- Return from the tagged history to the transcript-prefix history.
        have sourceDomain :
            ((dialogueTranscript dialogue).take k).map Prod.fst ++
                [(dialogueTranscript dialogue)[k].1] ∈
              RandomSystems.System.dom (parallel left right) :=
          historyEqual.symm ▸ jointDomain
        refine ⟨sourceDomain, ?_⟩
        calc
          _ = RandomSystems.System.output (parallel left right)
                (prior ++ [Sum.inl pair.1]) jointDomain :=
            RandomSystems.System.output_congr _ historyEqual _ _
          _ = Sum.inl pair.2 := jointOutput
          _ = (dialogueTranscript dialogue)[k].2 := by
            simp [dialogueTranscript, eventEqual, taggedPair]
    | inr pair =>
        -- Right realization supplies the active component's domain and answer.
        have rightAt := rightRealizes k hkDialogue
        simp only [eventEqual] at rightAt
        obtain ⟨rightDomain, rightOutput⟩ := rightAt
        let prior := (dialogue.take k).map (taggedPair · |>.1)
        -- The inactive left prefix and active right query give joint admission.
        have jointDomain :
            prior ++ [Sum.inr pair.1] ∈
              RandomSystems.System.dom (parallel left right) := by
          rw [dom_parallel]
          refine ⟨by simp, ?_, Or.inr ?_⟩
          · simpa only [prior, leftQueries_append_inr] using leftRealizes_domain left
              (leftRealizes_take left leftRealizes k)
          · simpa only [prior, rightQueries_append_inr] using rightDomain
        -- Routing embeds the right answer in the joint output alphabet.
        have jointOutput :
            RandomSystems.System.output (parallel left right)
                (prior ++ [Sum.inr pair.1]) jointDomain = Sum.inr pair.2 := by
          rw [output_parallel_right]
          exact congrArg Sum.inr rightOutput
        have historyEqual :
            ((dialogueTranscript dialogue).take k).map Prod.fst ++
                [(dialogueTranscript dialogue)[k].1] =
              prior ++ [Sum.inr pair.1] := by
          simp [prior, dialogueTranscript, List.map_map, Function.comp_def,
            eventEqual, taggedPair]
        -- Return from the tagged history to the transcript-prefix history.
        have sourceDomain :
            ((dialogueTranscript dialogue).take k).map Prod.fst ++
                [(dialogueTranscript dialogue)[k].1] ∈
              RandomSystems.System.dom (parallel left right) :=
          historyEqual.symm ▸ jointDomain
        refine ⟨sourceDomain, ?_⟩
        calc
          _ = RandomSystems.System.output (parallel left right)
                (prior ++ [Sum.inr pair.1]) jointDomain :=
            RandomSystems.System.output_congr _ historyEqual _ _
          _ = Sum.inr pair.2 := jointOutput
          _ = (dialogueTranscript dialogue)[k].2 := by
            simp [dialogueTranscript, eventEqual, taggedPair]

private theorem trN_consistent_of_compatible {X : Type*} {Y : Type*}
    (system : DDS X Y) (environment : DDE Y X)
    (compatible : Compatible environment system) (rounds : Nat) :
    EnvConsistent environment (trN environment system rounds) ∧
      FinalAt environment rounds (trN environment system rounds) ∧
      SystemConsistent system (trN environment system rounds) := by
  induction rounds with
  | zero =>
      refine ⟨fun k hk => (by simp [trN] at hk), Or.inl rfl,
        fun k hk => (by simp [trN] at hk)⟩
  | succ rounds inductionHypothesis =>
      obtain ⟨environmentConsistent, finalAt, systemConsistent⟩ :=
        inductionHypothesis
      by_cases environmentDomain :
          (trN environment system rounds).map Prod.snd ∈ environment.1.Dom
      · have queryMem := Part.get_mem environmentDomain
        have systemDomain := compatible rounds _ queryMem
        rw [trN_succ_of_query environmentDomain systemDomain]
        refine ⟨?_, Or.inl (by
          rcases finalAt with lengthEqual | ⟨_, stopped⟩
          · simp [lengthEqual]
          · exact absurd environmentDomain stopped), ?_⟩
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (trN environment system rounds).length with
            earlier | last
          · rw [List.take_append_of_le_length (le_of_lt earlier),
              List.getElem_append_left earlier]
            exact environmentConsistent k earlier
          · have kEqual : k = (trN environment system rounds).length := by omega
            subst kEqual
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            exact ⟨environmentDomain, by simp⟩
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (trN environment system rounds).length with
            earlier | last
          · rw [List.take_append_of_le_length (le_of_lt earlier),
              List.getElem_append_left earlier]
            exact systemConsistent k earlier
          · have kEqual : k = (trN environment system rounds).length := by omega
            subst kEqual
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            simpa only [Nat.sub_self, List.getElem_cons_zero] using
              (show ∃ hdom, output system
                  ((trN environment system rounds).map Prod.fst ++
                    [(environment.1
                      ((trN environment system rounds).map Prod.snd)).get
                        environmentDomain]) hdom =
                    output system
                      ((trN environment system rounds).map Prod.fst ++
                        [(environment.1
                          ((trN environment system rounds).map Prod.snd)).get
                            environmentDomain]) systemDomain from
                ⟨systemDomain, rfl⟩)
      · rw [trN_succ_of_stop environmentDomain]
        refine ⟨environmentConsistent, Or.inr ⟨?_, environmentDomain⟩,
          systemConsistent⟩
        rcases finalAt with lengthEqual | ⟨lengthLess, _⟩ <;> omega

private theorem trN_eq_of_consistent {X : Type*} {Y : Type*}
    (system : DDS X Y) (environment : DDE Y X) :
    ∀ (rounds : Nat) (transcript : Transcript X Y),
      EnvConsistent environment transcript →
      FinalAt environment rounds transcript →
      SystemConsistent system transcript →
      trN environment system rounds = transcript := by
  intro rounds
  induction rounds with
  | zero =>
      intro transcript _ finalAt _
      rcases finalAt with lengthEqual | ⟨lengthLess, _⟩
      · simpa [trN] using (List.eq_nil_of_length_eq_zero lengthEqual).symm
      · omega
  | succ rounds inductionHypothesis =>
      intro transcript environmentConsistent finalAt systemConsistent
      rcases finalAt with lengthEqual | ⟨lengthLess, stopped⟩
      · have roundsLess : rounds < transcript.length := by omega
        have prefixEqual : trN environment system rounds = transcript.take rounds := by
          apply inductionHypothesis
          · intro k hk
            rw [List.length_take] at hk
            have kLess : k < transcript.length := by omega
            have kRounds : k ≤ rounds :=
              Nat.le_of_lt (lt_of_lt_of_le hk (min_le_left _ _))
            simpa only [List.take_take, min_eq_left kRounds,
              List.getElem_take] using environmentConsistent k kLess
          · exact Or.inl (by
              simp [List.length_take, show rounds ≤ transcript.length by omega])
          · intro k hk
            rw [List.length_take] at hk
            have kLess : k < transcript.length := by omega
            have kRounds : k ≤ rounds :=
              Nat.le_of_lt (lt_of_lt_of_le hk (min_le_left _ _))
            simpa only [List.take_take, min_eq_left kRounds,
              List.getElem_take] using systemConsistent k kLess
        obtain ⟨environmentDomain, queryEqual⟩ :=
          environmentConsistent rounds roundsLess
        obtain ⟨systemDomain, answerEqual⟩ := systemConsistent rounds roundsLess
        have environmentDomain' :
            (trN environment system rounds).map Prod.snd ∈ environment.1.Dom := by
          rwa [prefixEqual]
        have queryEqual' :
            (environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain' = transcript[rounds].1 := by
          apply Part.get_eq_of_mem
          rw [prefixEqual]
          exact queryEqual ▸ Part.get_mem environmentDomain
        have systemDomain' :
            (trN environment system rounds).map Prod.fst ++
              [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain'] ∈ dom system := by
          rw [queryEqual']
          simpa only [prefixEqual] using systemDomain
        have answerEqual' :
            output system ((trN environment system rounds).map Prod.fst ++
              [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain']) systemDomain' = transcript[rounds].2 := by
          calc
            _ = output system ((transcript.take rounds).map Prod.fst ++
                [transcript[rounds].1]) systemDomain :=
              output_congr system (by rw [queryEqual', prefixEqual]) _ _
            _ = transcript[rounds].2 := answerEqual
        have pairEqual :
            ((environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain',
              output system ((trN environment system rounds).map Prod.fst ++
                [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                  environmentDomain']) systemDomain') = transcript[rounds] := by
          apply Prod.ext
          · exact queryEqual'
          · exact answerEqual'
        rw [trN_succ_of_query environmentDomain' systemDomain', pairEqual, prefixEqual]
        conv_rhs => rw [← List.take_length (l := transcript), lengthEqual]
        rw [List.take_add_one, List.getElem?_eq_getElem roundsLess]
        simp
      · have prefixEqual : trN environment system rounds = transcript := by
          apply inductionHypothesis transcript environmentConsistent
          · rcases Nat.lt_or_ge transcript.length rounds with less | greater
            · exact Or.inr ⟨less, stopped⟩
            · exact Or.inl (by omega)
          · exact systemConsistent
        rw [trN_succ_of_stop (by rwa [prefixEqual]), prefixEqual]

private theorem stopped_consistent_of_toOption_eq_some {X : Type*} {Y : Type*}
    {environment : DDE Y X} {system : DDS X Y}
    (compatible : Compatible environment system)
    {transcript : Transcript X Y}
    (equal : (tr environment system).toOption = some transcript) :
    EnvConsistent environment transcript ∧
      transcript.map Prod.snd ∉ environment.1.Dom ∧
      SystemConsistent system transcript := by
  rw [Part.toOption_eq_some_iff] at equal
  obtain ⟨stops, valueEqual⟩ := equal
  have stable := Nat.find_spec stops
  have transcriptEqual : trN environment system (Nat.find stops) = transcript := by
    rw [← tr_get_eq_trN stops stable, valueEqual]
  have consistent := trN_consistent_of_compatible system environment compatible
    (Nat.find stops)
  refine ⟨transcriptEqual ▸ consistent.1, ?_, transcriptEqual ▸ consistent.2.2⟩
  have stopped := (trN_succ_eq_iff_of_compatible compatible (Nat.find stops)).1 stable
  rwa [transcriptEqual] at stopped

private theorem toOption_eq_some_iff_systemConsistent {X : Type*} {Y : Type*}
    {environment : DDE Y X} {system : DDS X Y}
    (compatible : Compatible environment system)
    {transcript : Transcript X Y}
    (environmentConsistent : EnvConsistent environment transcript)
    (terminal : transcript.map Prod.snd ∉ environment.1.Dom) :
    (tr environment system).toOption = some transcript ↔
      SystemConsistent system transcript := by
  constructor
  · intro equal
    exact (stopped_consistent_of_toOption_eq_some compatible equal).2.2
  · intro systemConsistent
    have transcriptAtLength :
        trN environment system transcript.length = transcript :=
      trN_eq_of_consistent system environment transcript.length transcript
        environmentConsistent (Or.inl rfl) systemConsistent
    have stable : trN environment system (transcript.length + 1) =
        trN environment system transcript.length := by
      apply trN_succ_of_stop
      rwa [transcriptAtLength]
    rw [Part.toOption_eq_some_iff]
    let stops : Stops environment system := ⟨transcript.length, stable⟩
    exact ⟨stops, (tr_get_eq_trN stops stable).trans transcriptAtLength⟩

private def fixedQueries {X : Type*} {Y : Type*}
    (queries : List X) : DDE Y X :=
  ⟨(fun answers : List Y =>
      (⟨answers.length < queries.length,
        fun h => queries[answers.length]⟩ : Part X)),
    by
      intro first second hprefix secondDomain
      exact lt_of_le_of_lt hprefix.length_le secondDomain⟩

@[simp]
private theorem fixedQueries_dom {X : Type*} {Y : Type*}
    (queries : List X) (answers : List Y) :
    answers ∈ (fixedQueries (Y := Y) queries).1.Dom ↔
      answers.length < queries.length :=
  Iff.rfl

private theorem fixedQueries_get {X : Type*} {Y : Type*}
    (queries : List X) (answers : List Y)
    (domain : answers ∈ (fixedQueries (Y := Y) queries).1.Dom) :
    ((fixedQueries (Y := Y) queries).1 answers).get domain =
      queries[answers.length] :=
  rfl

private theorem trN_fixedQueries {X : Type*} {Y : Type*}
    (system : DDS X Y) (queries : List X)
    (admitted : queries = [] ∨ queries ∈ dom system) :
    ∀ rounds,
      (trN (fixedQueries (Y := Y) queries) system rounds).length =
          min rounds queries.length ∧
        (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.fst =
          queries.take rounds := by
  intro rounds
  induction rounds with
  | zero => simp [trN]
  | succ rounds inductionHypothesis =>
      obtain ⟨lengthEqual, inputsEqual⟩ := inductionHypothesis
      by_cases beforeEnd : rounds < queries.length
      · have environmentDomain :
            (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd ∈
              (fixedQueries (Y := Y) queries).1.Dom := by
          exact (fixedQueries_dom queries _).2 (by
            simpa [lengthEqual] using beforeEnd)
        have queryEqual :
            ((fixedQueries (Y := Y) queries).1
              ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).get
                environmentDomain = queries[rounds] := by
          have answerLengthEqual :
              ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd).length =
                rounds := by
            rw [List.length_map, lengthEqual,
              min_eq_left (Nat.le_of_lt beforeEnd)]
          simp only [fixedQueries_get, answerLengthEqual]
        have nextPrefix : queries.take (rounds + 1) ∈ dom system := by
          rcases admitted with empty | fullDomain
          · subst queries
            simp at beforeEnd
          · apply prefix_closed system (List.take_prefix _ _) (by
              intro empty
              have positive : 0 < (queries.take (rounds + 1)).length := by
                rw [List.length_take]
                omega
              rw [empty] at positive
              simp at positive)
              fullDomain
        have systemDomain :
            (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.fst ++
                [((fixedQueries (Y := Y) queries).1
                  ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).get
                    environmentDomain] ∈ dom system := by
          rw [inputsEqual, queryEqual]
          have takeEqual : queries.take (rounds + 1) =
              queries.take rounds ++ [queries[rounds]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem beforeEnd,
              Option.toList_some]
          exact takeEqual ▸ nextPrefix
        rw [trN_succ_of_query environmentDomain systemDomain]
        constructor
        · simp only [List.length_append, List.length_singleton, lengthEqual]
          omega
        · simp only [List.map_append, inputsEqual, queryEqual, List.map_singleton]
          rw [List.take_add_one, List.getElem?_eq_getElem beforeEnd,
            Option.toList_some]
      · have atEnd : queries.length ≤ rounds := Nat.le_of_not_gt beforeEnd
        have environmentStopped :
            (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd ∉
              (fixedQueries (Y := Y) queries).1.Dom := by
          rw [fixedQueries_dom, List.length_map, lengthEqual,
            min_eq_right atEnd]
          omega
        rw [trN_succ_of_stop environmentStopped]
        constructor
        · rw [lengthEqual]
          omega
        · rw [inputsEqual, List.take_of_length_le atEnd,
            List.take_of_length_le (atEnd.trans (Nat.le_succ _))]

private theorem fixedQueries_compatible {X : Type*} {Y : Type*}
    (system : DDS X Y) (queries : List X)
    (admitted : queries = [] ∨ queries ∈ dom system) :
    Compatible (fixedQueries (Y := Y) queries) system := by
  intro rounds query queryMem
  have invariant := trN_fixedQueries system queries admitted rounds
  have environmentDomain :
      (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd ∈
        (fixedQueries (Y := Y) queries).1.Dom :=
    Part.dom_iff_mem.mpr ⟨query, queryMem⟩
  have beforeEnd :
      (trN (fixedQueries (Y := Y) queries) system rounds).length < queries.length := by
    simpa only [List.length_map] using
      (fixedQueries_dom queries
        ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).1
          environmentDomain
  have indexEqual :
      (trN (fixedQueries (Y := Y) queries) system rounds).length = rounds := by
    rw [invariant.1]
    omega
  have queryEqual : query = queries[rounds] := by
    have getIsQuery := Part.get_eq_of_mem queryMem environmentDomain
    have getIsFixed :
        ((fixedQueries (Y := Y) queries).1
          ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).get
            environmentDomain = queries[rounds] := by
      simp only [fixedQueries_get, List.length_map, indexEqual]
    exact getIsQuery.symm.trans getIsFixed
  rw [invariant.2, queryEqual]
  rcases admitted with empty | fullDomain
  · subst queries
    simp at beforeEnd
  · have nextPrefix := prefix_closed system
      (List.take_prefix (rounds + 1) queries) (by
        intro empty
        have positive : 0 < (queries.take (rounds + 1)).length := by
          rw [List.length_take]
          omega
        rw [empty] at positive
        simp at positive) fullDomain
    have takeEqual : queries.take (rounds + 1) =
        queries.take rounds ++ [queries[rounds]] := by
      rw [List.take_add_one,
        List.getElem?_eq_getElem (indexEqual ▸ beforeEnd), Option.toList_some]
    exact takeEqual ▸ nextPrefix

private theorem fixedQueries_halts {X : Type*} {Y : Type*}
    (queries : List X) : DDE.Halts (fixedQueries (Y := Y) queries) := by
  refine ⟨queries.length, ?_⟩
  intro answers lengthAtLeast domain
  exact Nat.not_lt_of_ge lengthAtLeast
    ((fixedQueries_dom queries answers).1 domain)

private theorem fixedQueries_stops {X : Type*} {Y : Type*}
    (system : DDS X Y) (queries : List X) :
    Stops (fixedQueries (Y := Y) queries) system :=
  stops_of_halts (fixedQueries_halts (Y := Y) queries) system

private theorem fixedQueries_envConsistent {X : Type*} {Y : Type*}
    (transcript : Transcript X Y) :
    EnvConsistent (fixedQueries (Y := Y) (transcript.map Prod.fst))
      transcript := by
  intro k hk
  have domain : (transcript.take k).map Prod.snd ∈
      (fixedQueries (Y := Y) (transcript.map Prod.fst)).1.Dom := by
    rw [fixedQueries_dom, List.length_map, List.length_take,
      List.length_map]
    omega
  refine ⟨domain, ?_⟩
  have indexEqual : ((transcript.take k).map Prod.snd).length = k := by
    rw [List.length_map, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have hkMap : k < (transcript.map Prod.fst).length := by simpa using hk
  calc
    ((fixedQueries (Y := Y) (transcript.map Prod.fst)).1
        ((transcript.take k).map Prod.snd)).get domain =
        (transcript.map Prod.fst)[k]'hkMap := by
          simp only [fixedQueries_get, indexEqual]
    _ = transcript[k].1 := by simp

private theorem fixedQueries_terminal {X : Type*} {Y : Type*}
    (transcript : Transcript X Y) :
    transcript.map Prod.snd ∉
      (fixedQueries (Y := Y) (transcript.map Prod.fst)).1.Dom := by
  rw [fixedQueries_dom, List.length_map, List.length_map]
  exact Nat.not_lt_of_ge le_rfl

private theorem systemConsistent_queries_admitted {X : Type*} {Y : Type*}
    (system : DDS X Y) (transcript : Transcript X Y)
    (consistent : SystemConsistent system transcript) :
    transcript.map Prod.fst = [] ∨ transcript.map Prod.fst ∈ dom system := by
  induction transcript using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton prior event =>
      right
      have last := (systemConsistent_snoc_iff system prior event).1 consistent |>.2
      simpa only [List.map_append, List.map_singleton] using last.choose

private theorem mass_systemConsistent_eq_of_equivalent {X : Type*} {Y : Type*}
    (left right : CommonDomain.ProbabilityPresentation X Y)
    (equivalent : CommonDomain.ProbabilityPresentation.Equivalent left right)
    (transcript : Transcript X Y) :
    left.law.1.mass (fun system => SystemConsistent system transcript) =
      right.law.1.mass (fun system => SystemConsistent system transcript) := by
  let queries := transcript.map Prod.fst
  by_cases admitted : queries = [] ∨ queries ∈ left.domain
  · have admittedRight : queries = [] ∨ queries ∈ right.domain := by
      rwa [← equivalent.1]
    let environment := fixedQueries (Y := Y) queries
    have leftAdmissible : PDS.Compatible environment left.law.1 ∧
        PDS.Stops environment left.law.1 := by
      constructor
      · intro system supported
        apply fixedQueries_compatible system queries
        rcases admitted with empty | inDomain
        · exact Or.inl empty
        · exact Or.inr (by
            rw [left.hasDomain system supported]
            exact inDomain)
      · intro system _
        exact fixedQueries_stops system queries
    have rightAdmissible : PDS.Compatible environment right.law.1 ∧
        PDS.Stops environment right.law.1 := by
      constructor
      · intro system supported
        apply fixedQueries_compatible system queries
        rcases admittedRight with empty | inDomain
        · exact Or.inl empty
        · exact Or.inr (by
            rw [right.hasDomain system supported]
            exact inDomain)
      · intro system _
        exact fixedQueries_stops system queries
    have lawEqual := equivalent.2 environment
      ⟨leftAdmissible, rightAdmissible⟩
    have coefficientEqual := congrArg (fun law => law (some transcript)) lawEqual
    change PDS.trLaw environment left.law.1 (some transcript) =
      PDS.trLaw environment right.law.1 (some transcript) at coefficientEqual
    unfold PDS.trLaw at coefficientEqual
    rw [Distribution.fTransform_apply_eq_mass,
      Distribution.fTransform_apply_eq_mass] at coefficientEqual
    calc
      left.law.1.mass (fun system => SystemConsistent system transcript) =
          left.law.1.mass (fun system =>
            (tr environment system).toOption = some transcript) := by
        apply Distribution.mass_congr_of_support
        intro system supported
        exact (toOption_eq_some_iff_systemConsistent
          (leftAdmissible.1 system supported)
          (fixedQueries_envConsistent transcript)
          (fixedQueries_terminal transcript)).symm
      _ = right.law.1.mass (fun system =>
            (tr environment system).toOption = some transcript) := coefficientEqual
      _ = right.law.1.mass (fun system => SystemConsistent system transcript) := by
        apply Distribution.mass_congr_of_support
        intro system supported
        exact toOption_eq_some_iff_systemConsistent
          (rightAdmissible.1 system supported)
          (fixedQueries_envConsistent transcript)
          (fixedQueries_terminal transcript)
  · have admittedRight : ¬ (queries = [] ∨ queries ∈ right.domain) := by
      simpa only [equivalent.1] using admitted
    have leftZero :
        left.law.1.mass (fun system => SystemConsistent system transcript) = 0 := by
      calc
        _ = left.law.1.mass (fun _ => False) := by
          apply Distribution.mass_congr_of_support
          intro system supported
          constructor
          · intro consistent
            exact False.elim (admitted (by
              simpa only [queries, left.hasDomain system supported] using
                systemConsistent_queries_admitted system transcript consistent))
          · intro false
            exact false.elim
        _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)
    have rightZero :
        right.law.1.mass (fun system => SystemConsistent system transcript) = 0 := by
      calc
        _ = right.law.1.mass (fun _ => False) := by
          apply Distribution.mass_congr_of_support
          intro system supported
          constructor
          · intro consistent
            exact False.elim (admittedRight (by
              simpa only [queries, right.hasDomain system supported] using
                systemConsistent_queries_admitted system transcript consistent))
          · intro false
            exact false.elim
        _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)
    exact leftZero.trans rightZero.symm

private def MatchingEvent
    (event : (X₁ ⊕ X₂) × (Y₁ ⊕ Y₂)) : Prop :=
  match event with
  | (Sum.inl _, Sum.inl _) => True
  | (Sum.inr _, Sum.inr _) => True
  | _ => False

private def Matching
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) : Prop :=
  ∀ event ∈ transcript, MatchingEvent event

private theorem systemConsistent_parallel_matching
    (left : DDS X₁ Y₁) (right : DDS X₂ Y₂) :
    ∀ transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂),
      SystemConsistent (parallel left right) transcript → Matching transcript := by
  intro transcript consistent
  induction transcript using List.reverseRecOn with
  | nil => intro event member; simp at member
  | append_singleton prior event inductionHypothesis =>
      have split :=
        (systemConsistent_snoc_iff (parallel left right) prior event).1 consistent
      have priorMatching := inductionHypothesis split.1
      have eventMatching : MatchingEvent event := by
        rcases event with ⟨query, answer⟩
        rcases query with query | query <;> rcases answer with answer | answer
        · trivial
        · exfalso
          obtain ⟨domain, outputEqual⟩ := split.2
          have routed := output_parallel_left left right
            (prior.map Prod.fst) query domain
          rw [routed] at outputEqual
          cases outputEqual
        · exfalso
          obtain ⟨domain, outputEqual⟩ := split.2
          have routed := output_parallel_right left right
            (prior.map Prod.fst) query domain
          rw [routed] at outputEqual
          cases outputEqual
        · trivial
      intro candidate member
      rcases List.mem_append.mp member with inPrior | inLast
      · exact priorMatching candidate inPrior
      · have equal : candidate = event := by simpa using inLast
        subst candidate
        exact eventMatching

private theorem matching_exists_dialogue
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (matching : Matching transcript) :
    ∃ dialogue : Dialogue X₁ Y₁ X₂ Y₂,
      dialogueTranscript dialogue = transcript := by
  -- Reconstruct the component dialogue one matching tagged pair at a time.
  induction transcript with
  | nil => exact ⟨[], rfl⟩
  | cons event transcript inductionHypothesis =>
      have eventMatching := matching event (by simp)
      have tailMatching : Matching transcript := by
        intro candidate member
        exact matching candidate (by simp [member])
      obtain ⟨dialogue, dialogueEqual⟩ := inductionHypothesis tailMatching
      rcases event with ⟨query, answer⟩
      rcases query with query | query <;> rcases answer with answer | answer
      -- Matching tags determine whether the event belongs to the left or right.
      · exact ⟨Sum.inl (query, answer) :: dialogue, by
          change (Sum.inl query, Sum.inl answer) :: dialogueTranscript dialogue = _
          rw [dialogueEqual]⟩
      · exact eventMatching.elim
      · exact eventMatching.elim
      · exact ⟨Sum.inr (query, answer) :: dialogue, by
          change (Sum.inr query, Sum.inr answer) :: dialogueTranscript dialogue = _
          rw [dialogueEqual]⟩

private noncomputable def parallelLaw
    (left : PDS X₁ Y₁) (right : PDS X₂ Y₂) :
    PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  Distribution.fTransform (fun systems => parallel systems.1 systems.2)
    (Distribution.prod left right)

private theorem mass_parallelLaw_systemConsistent
    (left : PDS X₁ Y₁) (right : PDS X₂ Y₂)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    (parallelLaw left right).mass (fun system =>
        SystemConsistent system (dialogueTranscript dialogue)) =
      left.mass (fun system => SystemConsistent system (leftTranscript dialogue)) *
        right.mass (fun system =>
          SystemConsistent system (rightTranscript dialogue)) := by
  rw [parallelLaw, Distribution.mass_fTransform]
  calc
    (Distribution.prod left right).mass (fun systems =>
        SystemConsistent (parallel systems.1 systems.2)
          (dialogueTranscript dialogue)) =
      (Distribution.prod left right).mass (fun systems =>
        SystemConsistent systems.1 (leftTranscript dialogue) ∧
          SystemConsistent systems.2 (rightTranscript dialogue)) := by
        apply Distribution.mass_congr
        intro systems
        rw [systemConsistent_parallel_iff,
          leftRealizes_iff_systemConsistent,
          rightRealizes_iff_systemConsistent]
    _ = _ := Distribution.mass_prod_and left right
      (fun system => SystemConsistent system (leftTranscript dialogue))
      (fun system => SystemConsistent system (rightTranscript dialogue))

private theorem mass_parallelLaw_systemConsistent_eq
    (left left' : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right right' : CommonDomain.ProbabilityPresentation X₂ Y₂)
    (leftEquivalent :
      CommonDomain.ProbabilityPresentation.Equivalent left left')
    (rightEquivalent :
      CommonDomain.ProbabilityPresentation.Equivalent right right')
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    (parallelLaw left.law.1 right.law.1).mass
        (fun system => SystemConsistent system transcript) =
      (parallelLaw left'.law.1 right'.law.1).mass
        (fun system => SystemConsistent system transcript) := by
  by_cases matching : Matching transcript
  -- A matching transcript reconstructs a dialogue and its mass factors.
  · obtain ⟨dialogue, equal⟩ := matching_exists_dialogue transcript matching
    subst transcript
    rw [mass_parallelLaw_systemConsistent,
      mass_parallelLaw_systemConsistent,
      mass_systemConsistent_eq_of_equivalent left left' leftEquivalent,
      mass_systemConsistent_eq_of_equivalent right right' rightEquivalent]
  -- A tag-mismatched transcript is inconsistent with every parallel DDS.
  · have leftZero :
        (parallelLaw left.law.1 right.law.1).mass
          (fun system => SystemConsistent system transcript) = 0 := by
      rw [parallelLaw, Distribution.mass_fTransform]
      apply Distribution.mass_eq_zero_of_forall_not
      intro systems consistent
      exact matching
        (systemConsistent_parallel_matching systems.1 systems.2 transcript consistent)
    -- The same inconsistency makes the primed parallel mass zero.
    have rightZero :
        (parallelLaw left'.law.1 right'.law.1).mass
          (fun system => SystemConsistent system transcript) = 0 := by
      rw [parallelLaw, Distribution.mass_fTransform]
      apply Distribution.mass_eq_zero_of_forall_not
      intro systems consistent
      exact matching
        (systemConsistent_parallel_matching systems.1 systems.2 transcript consistent)
    exact leftZero.trans rightZero.symm

private theorem trLaw_none {X : Type*} {Y : Type*}
    (law : PDS X Y) (environment : DDE Y X)
    (stops : PDS.Stops environment law) :
    PDS.trLaw environment law none = 0 := by
  rw [PDS.trLaw, Distribution.fTransform_apply_eq_mass]
  calc
    law.mass (fun system => (tr environment system).toOption = none) =
        law.mass (fun _ => False) := by
      apply Distribution.mass_congr_of_support
      intro system supported
      constructor
      · intro equal
        exact (Part.toOption_eq_none_iff.mp equal) (stops system supported)
      · intro false
        exact false.elim
    _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)

private theorem trLaw_eq_of_systemConsistent_mass_eq {X : Type*} {Y : Type*}
    (first second : PDS X Y) (environment : DDE Y X)
    (admissible :
      (PDS.Compatible environment first ∧ PDS.Stops environment first) ∧
        (PDS.Compatible environment second ∧ PDS.Stops environment second))
    (massEqual : ∀ transcript : Transcript X Y,
      first.mass (fun system => SystemConsistent system transcript) =
        second.mass (fun system => SystemConsistent system transcript)) :
    PDS.trLaw environment first = PDS.trLaw environment second := by
  apply Finsupp.ext
  intro value
  cases value with
  | none =>
      rw [trLaw_none first environment admissible.1.2,
        trLaw_none second environment admissible.2.2]
  | some transcript =>
      by_cases witness : ∃ system,
          (system ∈ first.support ∨ system ∈ second.support) ∧
            (tr environment system).toOption = some transcript
      · obtain ⟨system, inFirstOrSecond, observed⟩ := witness
        have environmentConsistent : EnvConsistent environment transcript := by
          rcases inFirstOrSecond with inFirst | inSecond
          · exact (stopped_consistent_of_toOption_eq_some
              (admissible.1.1 system inFirst) observed).1
          · exact (stopped_consistent_of_toOption_eq_some
              (admissible.2.1 system inSecond) observed).1
        have terminal : transcript.map Prod.snd ∉ environment.1.Dom := by
          rcases inFirstOrSecond with inFirst | inSecond
          · exact (stopped_consistent_of_toOption_eq_some
              (admissible.1.1 system inFirst) observed).2.1
          · exact (stopped_consistent_of_toOption_eq_some
              (admissible.2.1 system inSecond) observed).2.1
        unfold PDS.trLaw
        rw [Distribution.fTransform_apply_eq_mass,
          Distribution.fTransform_apply_eq_mass]
        calc
          first.mass (fun system =>
              (tr environment system).toOption = some transcript) =
            first.mass (fun system => SystemConsistent system transcript) := by
              apply Distribution.mass_congr_of_support
              intro deterministic supported
              exact toOption_eq_some_iff_systemConsistent
                (admissible.1.1 deterministic supported)
                environmentConsistent terminal
          _ = second.mass (fun system => SystemConsistent system transcript) :=
            massEqual transcript
          _ = second.mass (fun system =>
              (tr environment system).toOption = some transcript) := by
              apply Distribution.mass_congr_of_support
              intro deterministic supported
              exact (toOption_eq_some_iff_systemConsistent
                (admissible.2.1 deterministic supported)
                environmentConsistent terminal).symm
      · unfold PDS.trLaw
        rw [Distribution.fTransform_apply_eq_mass,
          Distribution.fTransform_apply_eq_mass]
        have firstZero : first.mass (fun system =>
            (tr environment system).toOption = some transcript) = 0 := by
          calc
            _ = first.mass (fun _ => False) := by
              apply Distribution.mass_congr_of_support
              intro deterministic supported
              constructor
              · intro equal
                exact witness ⟨deterministic, Or.inl supported, equal⟩
              · intro false
                exact false.elim
            _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)
        have secondZero : second.mass (fun system =>
            (tr environment system).toOption = some transcript) = 0 := by
          calc
            _ = second.mass (fun _ => False) := by
              apply Distribution.mass_congr_of_support
              intro deterministic supported
              constructor
              · intro equal
                exact witness ⟨deterministic, Or.inr supported, equal⟩
              · intro false
                exact false.elim
            _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)
        exact firstZero.trans secondZero.symm

private def parallelDomain (left : Set (List X₁)) (right : Set (List X₂)) :
    Set (List (X₁ ⊕ X₂)) :=
  {history | history ≠ [] ∧
    (leftQueries history = [] ∨ leftQueries history ∈ left) ∧
    (rightQueries history = [] ∨ rightQueries history ∈ right)}

private theorem parallelLaw_hasDomain
    (left : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right : CommonDomain.ProbabilityPresentation X₂ Y₂) :
    PDS.HasDomain (parallelLaw left.law.1 right.law.1)
      (parallelDomain left.domain right.domain) := by
  intro output supported
  obtain ⟨systems, systemsSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      (fun systems : DDS X₁ Y₁ × DDS X₂ Y₂ =>
        parallel systems.1 systems.2)
      (Distribution.prod left.law.1 right.law.1) supported
  have componentSupported :=
    Distribution.support_prod_subset left.law.1 right.law.1 systemsSupported
  obtain ⟨leftSupported, rightSupported⟩ :=
    Finset.mem_product.mp componentSupported
  rw [dom_parallel, left.hasDomain systems.1 leftSupported,
    right.hasDomain systems.2 rightSupported]
  rfl

private noncomputable def parallelPresentation
    (left : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right : CommonDomain.ProbabilityPresentation X₂ Y₂) :
    CommonDomain.ProbabilityPresentation (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) where
  law := ⟨parallelLaw left.law.1 right.law.1,
    Distribution.fTransform_isProbDist _
      (Distribution.prod_isProbDist left.law.1 right.law.1
        left.law.2 right.law.2)⟩
  fixedDomain := ⟨parallelDomain left.domain right.domain,
    parallelLaw_hasDomain left right⟩

private theorem probDist_support_nonempty {A : Type*}
    (law : Distribution.ProbDist A) : ∃ a, a ∈ law.1.support := by
  apply Finsupp.support_nonempty_iff.mpr
  intro equalZero
  have weightZero : law.1.weight = 0 := by rw [equalZero]; simp [Distribution.weight]
  rw [law.2.weight_eq] at weightZero
  norm_num at weightZero

private theorem parallelPresentation_domain
    (left : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right : CommonDomain.ProbabilityPresentation X₂ Y₂) :
    (parallelPresentation left right).domain =
      parallelDomain left.domain right.domain := by
  obtain ⟨system, supported⟩ :=
    probDist_support_nonempty (parallelPresentation left right).law
  exact ((parallelPresentation left right).hasDomain system supported).symm.trans
    (parallelLaw_hasDomain left right system supported)

private theorem parallelPresentation_equivalent
    {left left' : CommonDomain.ProbabilityPresentation X₁ Y₁}
    {right right' : CommonDomain.ProbabilityPresentation X₂ Y₂}
    (leftEquivalent :
      CommonDomain.ProbabilityPresentation.Equivalent left left')
    (rightEquivalent :
      CommonDomain.ProbabilityPresentation.Equivalent right right') :
    CommonDomain.ProbabilityPresentation.Equivalent
      (parallelPresentation left right) (parallelPresentation left' right') := by
  constructor
  -- Component equivalence identifies the two component domains.
  · rw [parallelPresentation_domain, parallelPresentation_domain,
      leftEquivalent.1, rightEquivalent.1]
  -- Transcript-cell masses factor through component consistency masses.
  · intro environment admissible
    change PDS.trLaw environment (parallelLaw left.law.1 right.law.1) =
      PDS.trLaw environment (parallelLaw left'.law.1 right'.law.1)
    exact trLaw_eq_of_systemConsistent_mass_eq _ _ environment admissible
      (mass_parallelLaw_systemConsistent_eq left left' right right'
        leftEquivalent rightEquivalent)

private noncomputable def parallelRandomSystem :
    CommonDomain.ProbabilityRandomSystem X₁ Y₁ →
      CommonDomain.ProbabilityRandomSystem X₂ Y₂ →
      CommonDomain.ProbabilityRandomSystem (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  Quotient.lift₂
    (fun left right =>
      CommonDomain.ProbabilityRandomSystem.ofPresentation
        (parallelPresentation left right))
    (fun _ _ _ _ leftEquivalent rightEquivalent =>
      CommonDomain.ProbabilityRandomSystem.ofPresentation_eq_iff.mpr
        (parallelPresentation_equivalent leftEquivalent rightEquivalent))

@[simp]
private theorem parallelRandomSystem_ofPresentation
    (left : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right : CommonDomain.ProbabilityPresentation X₂ Y₂) :
    parallelRandomSystem
        (CommonDomain.ProbabilityRandomSystem.ofPresentation left)
        (CommonDomain.ProbabilityRandomSystem.ofPresentation right) =
      CommonDomain.ProbabilityRandomSystem.ofPresentation
        (parallelPresentation left right) :=
  rfl

private theorem advantageOnDomain_congr
    {X : Type*} {Y : Type*} {D : Set (List X)}
    {left left' right right' :
      CommonDomain.ProbabilityPresentation X Y}
    (leftDomain : left.domain = D) (leftDomain' : left'.domain = D)
    (rightDomain : right.domain = D) (rightDomain' : right'.domain = D)
    (leftEquivalent :
      CommonDomain.ProbabilityPresentation.Equivalent left left')
    (rightEquivalent :
      CommonDomain.ProbabilityPresentation.Equivalent right right') :
    PDS.advantageOnDomain D left.law.1 right.law.1 =
      PDS.advantageOnDomain D left'.law.1 right'.law.1 := by
  have observedLeft : ∀ environment :
      {e : DDE Y X // CompatibleD e D ∧ DDE.Halts e},
      PDS.trLaw environment.1 left.law.1 =
        PDS.trLaw environment.1 left'.law.1 := by
    intro environment
    apply leftEquivalent.2 environment.1
    constructor
    · constructor
      · apply PDS.compatible_of_compatibleD environment.2.1
        exact leftDomain ▸ left.hasDomain
      · exact PDS.stops_of_halts environment.2.2 left.law.1
    · constructor
      · apply PDS.compatible_of_compatibleD environment.2.1
        exact leftDomain' ▸ left'.hasDomain
      · exact PDS.stops_of_halts environment.2.2 left'.law.1
  have observedRight : ∀ environment :
      {e : DDE Y X // CompatibleD e D ∧ DDE.Halts e},
      PDS.trLaw environment.1 right.law.1 =
        PDS.trLaw environment.1 right'.law.1 := by
    intro environment
    apply rightEquivalent.2 environment.1
    constructor
    · constructor
      · apply PDS.compatible_of_compatibleD environment.2.1
        exact rightDomain ▸ right.hasDomain
      · exact PDS.stops_of_halts environment.2.2 right.law.1
    · constructor
      · apply PDS.compatible_of_compatibleD environment.2.1
        exact rightDomain' ▸ right'.hasDomain
      · exact PDS.stops_of_halts environment.2.2 right'.law.1
  unfold PDS.advantageOnDomain
  apply congrArg iSup
  funext environment
  rw [observedLeft environment, observedRight environment]

/- The component observer is defined only from functions.  For a supplied
left-answer history, `overrideDDS` gives those answers to the first left
queries and then falls back to one fixed system with the required domain. -/
private def overrideDDS (base : DDS X₁ Y₁) (answers : List Y₁) : DDS X₁ Y₁ :=
  ⟨(fun history =>
      (⟨history ∈ dom base, fun admitted =>
        if before : history.length - 1 < answers.length then
          answers[history.length - 1]
        else output base history admitted⟩ : Part Y₁)),
    ⟨empty_not_mem base, by
      intro first second hprefix firstNonempty secondDomain
      exact prefix_closed base hprefix firstNonempty secondDomain⟩⟩

@[simp]
private theorem dom_overrideDDS (base : DDS X₁ Y₁) (answers : List Y₁) :
    dom (overrideDDS base answers) = dom base :=
  rfl

private theorem output_overrideDDS_of_lt
    (base : DDS X₁ Y₁) (answers : List Y₁) (history : List X₁)
    (admitted : history ∈ dom (overrideDDS base answers))
    (before : history.length - 1 < answers.length) :
    output (overrideDDS base answers) history admitted =
      answers[history.length - 1] := by
  simp [output, overrideDDS, before]

private theorem systemConsistent_override
    (base source : DDS X₁ Y₁) (answers : List Y₁)
    (transcript : Transcript X₁ Y₁)
    (sameDomain : dom base = dom source)
    (consistent : SystemConsistent source transcript)
    (answerPrefix : transcript.map Prod.snd <+: answers) :
    SystemConsistent (overrideDDS base answers) transcript := by
  intro k hk
  obtain ⟨sourceDomain, _⟩ := consistent k hk
  have baseDomain :
      (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈ dom base := by
    rw [sameDomain]
    exact sourceDomain
  have overrideDomain :
      (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈
        dom (overrideDDS base answers) := by
    rwa [dom_overrideDDS]
  refine ⟨overrideDomain, ?_⟩
  have answerLength : transcript.length ≤ answers.length := by
    simpa using answerPrefix.length_le
  have answerIndex : k < answers.length := lt_of_lt_of_le hk answerLength
  have before :
      ((transcript.take k).map Prod.fst ++ [transcript[k].1]).length - 1 <
        answers.length := by
    rw [List.length_append, List.length_singleton, List.length_map,
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    simpa using answerIndex
  rw [output_overrideDDS_of_lt base answers _ overrideDomain before]
  have projectedIndex : k < (transcript.map Prod.snd).length := by
    simpa using hk
  calc
    answers[((transcript.take k).map Prod.fst ++
        [transcript[k].1]).length - 1] = answers[k] := by
          congr 1
          simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    _ = (transcript.map Prod.snd)[k] :=
      (answerPrefix.getElem projectedIndex).symm
    _ = transcript[k].2 := by simp

private theorem trN_prefix_of_le {X : Type*} {Y : Type*}
    (environment : DDE Y X) (system : DDS X Y) {first second : Nat}
    (le : first ≤ second) :
    trN environment system first <+: trN environment system second := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  induction extra with
  | zero => exact List.prefix_refl _
  | succ extra inductionHypothesis =>
      have prior := inductionHypothesis (by omega)
      apply prior.trans
      show trN environment system (first + extra) <+:
        trExtend environment system (trN environment system (first + extra))
      rcases trExtend_eq_or_append environment system
          (trN environment system (first + extra)) with unchanged | ⟨pair, appended⟩
      · rw [unchanged]
      · rw [appended]
        exact List.prefix_append _ _

private theorem envConsistent_take {X : Type*} {Y : Type*}
    (environment : DDE Y X) (transcript : Transcript X Y)
    (consistent : EnvConsistent environment transcript) (rounds : Nat) :
    EnvConsistent environment (transcript.take rounds) := by
  intro k hk
  have kTranscript : k < transcript.length := by
    rw [List.length_take] at hk
    omega
  have row := consistent k kTranscript
  have kRounds : k ≤ rounds := by
    rw [List.length_take] at hk
    omega
  simpa only [List.take_take, min_eq_left kRounds,
    List.getElem_take] using row

private theorem systemConsistent_take {X : Type*} {Y : Type*}
    (system : DDS X Y) (transcript : Transcript X Y)
    (consistent : SystemConsistent system transcript) (rounds : Nat) :
    SystemConsistent system (transcript.take rounds) := by
  intro k hk
  have kTranscript : k < transcript.length := by
    rw [List.length_take] at hk
    omega
  have row := consistent k kTranscript
  have kRounds : k ≤ rounds := by
    rw [List.length_take] at hk
    omega
  simpa only [List.take_take, min_eq_left kRounds,
    List.getElem_take] using row

private theorem compatible_of_consistent_complete {X : Type*} {Y : Type*}
    (system : DDS X Y) (environment : DDE Y X) (rounds : Nat)
    (transcript : Transcript X Y)
    (environmentConsistent : EnvConsistent environment transcript)
    (finalAt : FinalAt environment rounds transcript)
    (systemConsistent : SystemConsistent system transcript)
    (haltsAt : ∀ answers : List Y, rounds ≤ answers.length →
      answers ∉ environment.1.Dom) :
    Compatible environment system := by
  intro n query queryMember
  by_cases beforeBound : n < rounds
  · by_cases beforeEnd : n < transcript.length
    · have transcriptPrefix :
          trN environment system n = transcript.take n :=
        trN_eq_of_consistent system environment n (transcript.take n)
          (envConsistent_take environment transcript environmentConsistent n)
          (Or.inl (by simp [List.length_take, Nat.min_eq_left
            (Nat.le_of_lt beforeEnd)]))
          (systemConsistent_take system transcript systemConsistent n)
      obtain ⟨environmentDomain, environmentQuery⟩ :=
        environmentConsistent n beforeEnd
      obtain ⟨systemDomain, _⟩ := systemConsistent n beforeEnd
      have queryMember' :
          query ∈ environment.1 ((transcript.take n).map Prod.snd) := by
        rwa [transcriptPrefix] at queryMember
      have expectedMember :
          transcript[n].1 ∈ environment.1 ((transcript.take n).map Prod.snd) :=
        environmentQuery ▸ Part.get_mem environmentDomain
      have queryEqual : query = transcript[n].1 :=
        Part.mem_unique queryMember' expectedMember
      rwa [transcriptPrefix, queryEqual]
    · have endLe : transcript.length ≤ n := Nat.le_of_not_gt beforeEnd
      obtain ⟨endLess, stopped⟩ :
          transcript.length < rounds ∧
            transcript.map Prod.snd ∉ environment.1.Dom := by
        rcases finalAt with equal | stopped
        · omega
        · exact stopped
      have transcriptAtEnd :
          trN environment system transcript.length = transcript :=
        trN_eq_of_consistent system environment transcript.length transcript
          environmentConsistent (Or.inl rfl) systemConsistent
      have stable :
          trN environment system (transcript.length + 1) =
            trN environment system transcript.length := by
        apply trN_succ_of_stop
        rwa [transcriptAtEnd]
      have transcriptAtN : trN environment system n = transcript := by
        calc
          _ = trN environment system transcript.length :=
            trN_eq_of_le stable n endLe
          _ = transcript := transcriptAtEnd
      rw [transcriptAtN] at queryMember
      exact (stopped queryMember.choose).elim
  · have boundLe : rounds ≤ n := Nat.le_of_not_gt beforeBound
    have transcriptAtBound : trN environment system rounds = transcript :=
      trN_eq_of_consistent system environment rounds transcript
        environmentConsistent finalAt systemConsistent
    have stopped : transcript.map Prod.snd ∉ environment.1.Dom := by
      rcases finalAt with equal | stopped
      · apply haltsAt
        simp [equal]
      · exact stopped.2
    have stable :
        trN environment system (rounds + 1) =
          trN environment system rounds := by
      apply trN_succ_of_stop
      rwa [transcriptAtBound]
    have transcriptAtN : trN environment system n = transcript := by
      calc
        _ = trN environment system rounds := trN_eq_of_le stable n boundLe
        _ = transcript := transcriptAtBound
    rw [transcriptAtN] at queryMember
    exact (stopped queryMember.choose).elim

private def leftPairs
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    Transcript X₁ Y₁ :=
  transcript.filterMap fun
    | (Sum.inl query, Sum.inl answer) => some (query, answer)
    | _ => none

private theorem leftPairs_length_le
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    (leftPairs transcript).length ≤ transcript.length := by
  exact List.length_filterMap_le _ _

@[simp]
private theorem leftPairs_dialogueTranscript
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    leftPairs (dialogueTranscript dialogue) = leftTranscript dialogue := by
  rw [leftPairs, dialogueTranscript, leftTranscript, List.filterMap_map]
  apply congrArg (fun transform => List.filterMap transform dialogue)
  funext event
  cases event with
  | inl pair => cases pair; rfl
  | inr pair => cases pair; rfl

private def leftAnswers (dialogue : Dialogue X₁ Y₁ X₂ Y₂) :
    List Y₁ :=
  (leftTranscript dialogue).map Prod.snd

private theorem exists_next_left_event
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂)
    (answers : List Y₁) (answerPrefix : answers <+: leftAnswers dialogue)
    (strict : answers.length < (leftTranscript dialogue).length) :
    ∃ before pair after,
      dialogue = before ++ Sum.inl pair :: after ∧
      leftAnswers before = answers := by
  induction dialogue generalizing answers with
  | nil => simp [leftTranscript] at strict
  | cons event dialogue inductionHypothesis =>
      cases event with
      | inl pair =>
          cases answers with
          | nil =>
              exact ⟨[], pair, dialogue, by simp, rfl⟩
          | cons answer answers =>
              have prefixSplit :
                  answer = pair.2 ∧ answers <+: leftAnswers dialogue := by
                simpa [leftAnswers, leftTranscript] using answerPrefix
              have prefixTail : answers <+: leftAnswers dialogue := by
                exact prefixSplit.2
              have answerEqual : answer = pair.2 := prefixSplit.1
              have strictTail :
                  answers.length < (leftTranscript dialogue).length := by
                simpa [leftTranscript] using strict
              obtain ⟨before, nextPair, after, dialogueEqual, beforeAnswers⟩ :=
                inductionHypothesis answers prefixTail strictTail
              refine ⟨Sum.inl pair :: before, nextPair, after, ?_, ?_⟩
              · simp [dialogueEqual]
              · change pair.2 :: leftAnswers before = answer :: answers
                simp [answerEqual, beforeAnswers]
      | inr pair =>
          have prefixTail : answers <+: leftAnswers dialogue := by
            simpa [leftAnswers, leftTranscript] using answerPrefix
          have strictTail :
              answers.length < (leftTranscript dialogue).length := by
            simpa [leftTranscript] using strict
          obtain ⟨before, nextPair, after, dialogueEqual, beforeAnswers⟩ :=
            inductionHypothesis answers prefixTail strictTail
          refine ⟨Sum.inr pair :: before, nextPair, after, ?_, ?_⟩
          · simp [dialogueEqual]
          · simpa [leftAnswers, leftTranscript] using beforeAnswers

/- At a left-answer history `answers`, probe the outer DDE with a DDS that
replays those answers.  Requiring the probe to expose a next left query at
every prefix makes prefix closure part of the function table itself. -/
private def inducedLeftBounded
    (base : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat) :
    DDE Y₁ X₁ :=
  ⟨(fun answers =>
      (⟨∀ candidate, candidate <+: answers →
          candidate.length <
            (leftPairs (trN environment
              (parallel (overrideDDS base candidate) right) rounds)).length,
        fun admitted =>
          let current := admitted answers (List.prefix_refl answers)
          ((leftPairs (trN environment
            (parallel (overrideDDS base answers) right) rounds))[answers.length]).1⟩ : Part X₁)),
    by
      intro first second firstPrefix secondAdmitted candidate candidatePrefix
      exact secondAdmitted candidate (candidatePrefix.trans firstPrefix)⟩

private theorem nextLeftProbe
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (sameDomain : dom base = dom left)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂)
    (environmentConsistent :
      EnvConsistent environment (dialogueTranscript dialogue))
    (systemConsistent :
      SystemConsistent (parallel left right) (dialogueTranscript dialogue))
    (roundBound : dialogue.length ≤ rounds)
    (answers : List Y₁) (answerPrefix : answers <+: leftAnswers dialogue)
    (strict : answers.length < (leftTranscript dialogue).length) :
    answers.length <
        (leftPairs (trN environment
          (parallel (overrideDDS base answers) right) rounds)).length ∧
      ((leftPairs (trN environment
        (parallel (overrideDDS base answers) right) rounds))[answers.length]?).map
          Prod.fst = ((leftTranscript dialogue)[answers.length]?).map Prod.fst := by
  obtain ⟨before, pair, after, dialogueEqual, beforeAnswers⟩ :=
    exists_next_left_event dialogue answers answerPrefix strict
  have takeEqual :
      (dialogueTranscript dialogue).take before.length =
        dialogueTranscript before := by
    simp [dialogueEqual, dialogueTranscript, List.map_append]
  have beforeEnvironment :
      EnvConsistent environment (dialogueTranscript before) := by
    rw [← takeEqual]
    exact envConsistent_take environment (dialogueTranscript dialogue)
      environmentConsistent before.length
  have realizes :=
    (systemConsistent_parallel_iff left right dialogue).1 systemConsistent
  have beforeLeft : LeftRealizes left before := by
    have restricted := leftRealizes_take_early left realizes.1 before.length
    simpa [dialogueEqual] using restricted
  have beforeRight : RightRealizes right before := by
    have restricted := rightRealizes_take_early right realizes.2 before.length
    simpa [dialogueEqual] using restricted
  have beforeSource : SystemConsistent left (leftTranscript before) :=
    (leftRealizes_iff_systemConsistent left before).1 beforeLeft
  have beforeAnswerPrefix :
      (leftTranscript before).map Prod.snd <+: answers := by
    change leftAnswers before <+: answers
    rw [beforeAnswers]
  have beforeOverride :
      SystemConsistent (overrideDDS base answers) (leftTranscript before) :=
    systemConsistent_override base left answers (leftTranscript before)
      sameDomain beforeSource beforeAnswerPrefix
  have beforeProbe :
      SystemConsistent (parallel (overrideDDS base answers) right)
        (dialogueTranscript before) :=
    (systemConsistent_parallel_iff (overrideDDS base answers) right before).2
      ⟨(leftRealizes_iff_systemConsistent (overrideDDS base answers) before).2
          beforeOverride,
        beforeRight⟩
  have probePrefix :
      trN environment (parallel (overrideDDS base answers) right)
          before.length = dialogueTranscript before :=
    trN_eq_of_consistent (parallel (overrideDDS base answers) right)
      environment before.length (dialogueTranscript before)
      beforeEnvironment (Or.inl (by simp [dialogueTranscript])) beforeProbe
  have nextIndex : before.length < (dialogueTranscript dialogue).length := by
    simp [dialogueEqual, dialogueTranscript]
  have nextEvent :
      (dialogueTranscript dialogue)[before.length] =
        (Sum.inl pair.1, Sum.inl pair.2) := by
    simp [dialogueEqual, dialogueTranscript, taggedPair]
  obtain ⟨outerDomain, outerQuery⟩ :=
    environmentConsistent before.length nextIndex
  have probeEnvironmentDomain :
      (trN environment (parallel (overrideDDS base answers) right)
          before.length).map Prod.snd ∈ environment.1.Dom := by
    rwa [probePrefix, ← takeEqual]
  have probeQuery :
      (environment.1
        ((trN environment (parallel (overrideDDS base answers) right)
          before.length).map Prod.snd)).get probeEnvironmentDomain =
        Sum.inl pair.1 := by
    have outerQueryValue :
        (environment.1
          ((dialogueTranscript dialogue).take before.length |>.map Prod.snd)).get
            outerDomain = Sum.inl pair.1 :=
      outerQuery.trans (congrArg Prod.fst nextEvent)
    have queryMember :
        Sum.inl pair.1 ∈
          environment.1 ((dialogueTranscript dialogue).take before.length |>.map
            Prod.snd) :=
      outerQueryValue ▸ Part.get_mem outerDomain
    apply Part.get_eq_of_mem
    simpa only [probePrefix, ← takeEqual] using queryMember
  obtain ⟨outerSystemDomain, _⟩ := systemConsistent before.length nextIndex
  have fullHistoryEqual :
      ((dialogueTranscript dialogue).take before.length).map Prod.fst ++
          [(dialogueTranscript dialogue)[before.length].1] =
        (dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1] := by
    rw [takeEqual, nextEvent]
  have originalDomain :
      (dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1] ∈
        dom (parallel left right) :=
    fullHistoryEqual ▸ outerSystemDomain
  have parallelDomainEqual :
      dom (parallel (overrideDDS base answers) right) =
        dom (parallel left right) := by
    rw [dom_parallel, dom_parallel, dom_overrideDDS, sameDomain]
  have probeHistoryEqual :
      (trN environment (parallel (overrideDDS base answers) right)
          before.length).map Prod.fst ++
        [(environment.1
          ((trN environment (parallel (overrideDDS base answers) right)
            before.length).map Prod.snd)).get probeEnvironmentDomain] =
      (dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1] := by
    exact congrArg₂
      (fun (history : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
          (query : X₁ ⊕ X₂) => history.map Prod.fst ++ [query])
      probePrefix probeQuery
  have probeSystemDomain :
      (trN environment (parallel (overrideDDS base answers) right)
          before.length).map Prod.fst ++
        [(environment.1
          ((trN environment (parallel (overrideDDS base answers) right)
            before.length).map Prod.snd)).get probeEnvironmentDomain] ∈
          dom (parallel (overrideDDS base answers) right) := by
    rw [parallelDomainEqual]
    exact probeHistoryEqual.symm ▸ originalDomain
  have concreteDomain :
      (dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1] ∈
        dom (parallel (overrideDDS base answers) right) :=
    probeHistoryEqual ▸ probeSystemDomain
  have nextStep := trN_succ_of_query probeEnvironmentDomain probeSystemDomain
  have pairEqual :
      ((environment.1
          ((trN environment (parallel (overrideDDS base answers) right)
            before.length).map Prod.snd)).get probeEnvironmentDomain,
        output (parallel (overrideDDS base answers) right)
          ((trN environment (parallel (overrideDDS base answers) right)
            before.length).map Prod.fst ++
            [(environment.1
              ((trN environment (parallel (overrideDDS base answers) right)
                before.length).map Prod.snd)).get probeEnvironmentDomain])
          probeSystemDomain) =
        (Sum.inl pair.1,
          output (parallel (overrideDDS base answers) right)
            ((dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1])
            concreteDomain) := by
    apply Prod.ext
    · exact probeQuery
    · change output (parallel (overrideDDS base answers) right)
          ((trN environment (parallel (overrideDDS base answers) right)
            before.length).map Prod.fst ++
            [(environment.1
              ((trN environment (parallel (overrideDDS base answers) right)
                before.length).map Prod.snd)).get probeEnvironmentDomain])
          probeSystemDomain =
        output (parallel (overrideDDS base answers) right)
          ((dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1])
          concreteDomain
      exact output_congr _ probeHistoryEqual _ _
  have nextStepClean :
      trN environment (parallel (overrideDDS base answers) right)
          (before.length + 1) =
        dialogueTranscript before ++
          [(Sum.inl pair.1,
            output (parallel (overrideDDS base answers) right)
              ((dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1])
              concreteDomain)] := by
    calc
      _ = trN environment (parallel (overrideDDS base answers) right)
            before.length ++
          [((environment.1
              ((trN environment (parallel (overrideDDS base answers) right)
                before.length).map Prod.snd)).get probeEnvironmentDomain,
            output (parallel (overrideDDS base answers) right)
              ((trN environment (parallel (overrideDDS base answers) right)
                before.length).map Prod.fst ++
                [(environment.1
                  ((trN environment (parallel (overrideDDS base answers) right)
                    before.length).map Prod.snd)).get probeEnvironmentDomain])
              probeSystemDomain)] := nextStep
      _ = trN environment (parallel (overrideDDS base answers) right)
            before.length ++
          [(Sum.inl pair.1,
            output (parallel (overrideDDS base answers) right)
              ((dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1])
              concreteDomain)] := congrArg (fun event =>
                trN environment (parallel (overrideDDS base answers) right)
                  before.length ++ [event]) pairEqual
      _ = _ := congrArg (fun transcript => transcript ++
          [(Sum.inl pair.1,
            output (parallel (overrideDDS base answers) right)
              ((dialogueTranscript before).map Prod.fst ++ [Sum.inl pair.1])
              concreteDomain)]) probePrefix
  have beforeSuccLe : before.length + 1 ≤ rounds := by
    have : before.length + 1 ≤ dialogue.length := by
      simp [dialogueEqual]
    omega
  have stagePrefix := trN_prefix_of_le environment
    (parallel (overrideDDS base answers) right) beforeSuccLe
  rw [nextStepClean] at stagePrefix
  have routedOutput := output_parallel_left
    (overrideDDS base answers) right
    ((dialogueTranscript before).map Prod.fst) pair.1 concreteDomain
  rw [routedOutput] at stagePrefix
  have projectedPrefix := stagePrefix.filterMap (fun
    | (Sum.inl query, Sum.inl answer) => some (query, answer)
    | _ => none)
  change leftPairs
      (dialogueTranscript before ++
        [(Sum.inl pair.1,
          Sum.inl (output (overrideDDS base answers)
            (leftQueries ((dialogueTranscript before).map Prod.fst) ++ [pair.1]) _))]) <+:
      leftPairs (trN environment
        (parallel (overrideDDS base answers) right) rounds) at projectedPrefix
  have projectionEqual := leftPairs_dialogueTranscript before
  unfold leftPairs at projectionEqual
  rw [leftPairs, List.filterMap_append, projectionEqual] at projectedPrefix
  simp [leftPairs] at projectedPrefix
  have leftConcreteDomain :
      leftQueries ((dialogueTranscript before).map Prod.fst) ++ [pair.1] ∈
        dom (overrideDDS base answers) := by
    have component :=
      (dom_parallel (overrideDDS base answers) right ▸ concreteDomain).2.1
    simpa only [leftQueries_append_inl] using
      component.resolve_left (by simp)
  let probeAnswer := output (overrideDDS base answers)
    (leftQueries ((dialogueTranscript before).map Prod.fst) ++ [pair.1])
    leftConcreteDomain
  change leftTranscript before ++ [(pair.1, probeAnswer)] <+:
      leftPairs (trN environment
        (parallel (overrideDDS base answers) right) rounds) at projectedPrefix
  have beforeLength : (leftTranscript before).length = answers.length := by
    simpa [leftAnswers] using congrArg List.length beforeAnswers
  have finalIndex : answers.length <
      (leftPairs (trN environment
        (parallel (overrideDDS base answers) right) rounds)).length := by
    have projectedLength := projectedPrefix.length_le
    simp [beforeLength] at projectedLength
    omega
  have sourceIndex : answers.length <
      (leftTranscript before ++ [(pair.1, probeAnswer)]).length := by
    simp [beforeLength]
  have row := projectedPrefix.getElem sourceIndex
  have sourceQuery :
      (leftTranscript before ++ [(pair.1, probeAnswer)])[answers.length].1 =
        pair.1 := by
    have atLast :
        ((leftTranscript before ++ [(pair.1, probeAnswer)])[(leftTranscript before).length]).1 =
          pair.1 := by simp
    simpa only [beforeLength] using atLast
  have finalQuery :
      (leftPairs (trN environment
        (parallel (overrideDDS base answers) right) rounds))[answers.length].1 =
        pair.1 :=
    (congrArg Prod.fst row).symm.trans sourceQuery
  have targetQuery :
      (leftTranscript dialogue)[answers.length].1 = pair.1 := by
    have atNext :
        (leftTranscript dialogue)[(leftTranscript before).length].1 = pair.1 := by
      simp [dialogueEqual, leftTranscript]
    simpa only [beforeLength] using atNext
  refine ⟨finalIndex, ?_⟩
  rw [List.getElem?_eq_getElem finalIndex,
    List.getElem?_eq_getElem strict]
  simp only [Option.map_some]
  rw [finalQuery, targetQuery]

private theorem inducedLeftBounded_accepts
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (sameDomain : dom base = dom left)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂)
    (environmentConsistent :
      EnvConsistent environment (dialogueTranscript dialogue))
    (systemConsistent :
      SystemConsistent (parallel left right) (dialogueTranscript dialogue))
    (roundBound : dialogue.length ≤ rounds)
    (answers : List Y₁) (answerPrefix : answers <+: leftAnswers dialogue)
    (strict : answers.length < (leftTranscript dialogue).length) :
    ∃ admitted : answers ∈
        (inducedLeftBounded base right environment rounds).1.Dom,
      ((inducedLeftBounded base right environment rounds).1 answers).get
          admitted = (leftTranscript dialogue)[answers.length].1 := by
  have admitted : answers ∈
      (inducedLeftBounded base right environment rounds).1.Dom := by
    intro candidate candidatePrefix
    have candidateFull : candidate <+: leftAnswers dialogue :=
      candidatePrefix.trans answerPrefix
    have candidateStrict :
        candidate.length < (leftTranscript dialogue).length :=
      lt_of_le_of_lt candidatePrefix.length_le strict
    exact (nextLeftProbe base left right sameDomain environment rounds dialogue
      environmentConsistent systemConsistent roundBound candidate candidateFull
      candidateStrict).1
  refine ⟨admitted, ?_⟩
  have current : answers.length <
      (leftPairs (trN environment
        (parallel (overrideDDS base answers) right) rounds)).length :=
    admitted answers (List.prefix_refl answers)
  change ((leftPairs (trN environment
      (parallel (overrideDDS base answers) right) rounds))[answers.length]'current).1 = _
  obtain ⟨nextIndex, nextEqual⟩ :=
    (nextLeftProbe base left right sameDomain environment rounds dialogue
    environmentConsistent systemConsistent roundBound answers answerPrefix strict)
  rw [List.getElem?_eq_getElem nextIndex,
    List.getElem?_eq_getElem strict] at nextEqual
  simpa only [Option.map_some, Option.some.injEq] using nextEqual

private theorem fullLeftProbe_eq
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (sameDomain : dom base = dom left)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂)
    (environmentConsistent :
      EnvConsistent environment (dialogueTranscript dialogue))
    (finalAt : FinalAt environment rounds (dialogueTranscript dialogue))
    (systemConsistent :
      SystemConsistent (parallel left right) (dialogueTranscript dialogue)) :
    trN environment
        (parallel (overrideDDS base (leftAnswers dialogue)) right) rounds =
      dialogueTranscript dialogue := by
  have realizes :=
    (systemConsistent_parallel_iff left right dialogue).1 systemConsistent
  have leftSource : SystemConsistent left (leftTranscript dialogue) :=
    (leftRealizes_iff_systemConsistent left dialogue).1 realizes.1
  have leftOverride :
      SystemConsistent (overrideDDS base (leftAnswers dialogue))
        (leftTranscript dialogue) :=
    systemConsistent_override base left (leftAnswers dialogue)
      (leftTranscript dialogue) sameDomain leftSource (List.prefix_refl _)
  have probeConsistent :
      SystemConsistent
        (parallel (overrideDDS base (leftAnswers dialogue)) right)
        (dialogueTranscript dialogue) :=
    (systemConsistent_parallel_iff
      (overrideDDS base (leftAnswers dialogue)) right dialogue).2
      ⟨(leftRealizes_iff_systemConsistent
          (overrideDDS base (leftAnswers dialogue)) dialogue).2 leftOverride,
        realizes.2⟩
  exact trN_eq_of_consistent
    (parallel (overrideDDS base (leftAnswers dialogue)) right)
    environment rounds (dialogueTranscript dialogue)
    environmentConsistent finalAt probeConsistent

private theorem inducedLeftBounded_follows
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (sameDomain : dom base = dom left)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat)
    (dialogue : Dialogue X₁ Y₁ X₂ Y₂)
    (environmentConsistent :
      EnvConsistent environment (dialogueTranscript dialogue))
    (finalAt : FinalAt environment rounds (dialogueTranscript dialogue))
    (systemConsistent :
      SystemConsistent (parallel left right) (dialogueTranscript dialogue))
    (roundBound : dialogue.length ≤ rounds) :
    EnvConsistent (inducedLeftBounded base right environment rounds)
        (leftTranscript dialogue) ∧
      FinalAt (inducedLeftBounded base right environment rounds) rounds
        (leftTranscript dialogue) ∧
      SystemConsistent left (leftTranscript dialogue) := by
  have realizes :=
    (systemConsistent_parallel_iff left right dialogue).1 systemConsistent
  have leftSystem : SystemConsistent left (leftTranscript dialogue) :=
    (leftRealizes_iff_systemConsistent left dialogue).1 realizes.1
  have inducedConsistent :
      EnvConsistent (inducedLeftBounded base right environment rounds)
        (leftTranscript dialogue) := by
    intro k hk
    let answers := ((leftTranscript dialogue).take k).map Prod.snd
    have answerPrefix : answers <+: leftAnswers dialogue := by
      exact (List.take_prefix k (leftTranscript dialogue)).map Prod.snd
    have answerLength : answers.length = k := by
      simp [answers, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    have strict : answers.length < (leftTranscript dialogue).length := by
      simpa [answerLength] using hk
    obtain ⟨admitted, queryEqual⟩ := inducedLeftBounded_accepts
      base left right sameDomain environment rounds dialogue
      environmentConsistent systemConsistent roundBound answers answerPrefix strict
    refine ⟨admitted, ?_⟩
    have kLe : k ≤ (leftTranscript dialogue).length := Nat.le_of_lt hk
    simpa only [answers, List.length_map, List.length_take,
      Nat.min_eq_left kLe] using queryEqual
  have leftLength : (leftTranscript dialogue).length ≤ rounds := by
    exact le_trans (List.length_filterMap_le _ _) roundBound
  have inducedFinal :
      FinalAt (inducedLeftBounded base right environment rounds) rounds
        (leftTranscript dialogue) := by
    rcases eq_or_lt_of_le leftLength with equal | less
    · exact Or.inl equal
    · refine Or.inr ⟨less, ?_⟩
      intro admitted
      have exposesAnother := admitted (leftAnswers dialogue)
        (List.prefix_refl _)
      have probeEqual := fullLeftProbe_eq base left right sameDomain
        environment rounds dialogue environmentConsistent finalAt systemConsistent
      rw [probeEqual, leftPairs_dialogueTranscript] at exposesAnother
      simp [leftAnswers] at exposesAnother
  exact ⟨inducedConsistent, inducedFinal, leftSystem⟩

private theorem inducedLeftBounded_factorization
    (leftDomain : Set (List X₁)) (rightDomain : Set (List X₂))
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (baseHasDomain : dom base = leftDomain)
    (leftHasDomain : dom left = leftDomain)
    (rightHasDomain : dom right = rightDomain)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (environmentCompatible : CompatibleD environment
      (parallelDomain leftDomain rightDomain))
    (rounds : Nat) :
    Compatible (inducedLeftBounded base right environment rounds) left ∧
      trN (inducedLeftBounded base right environment rounds) left rounds =
        leftPairs (trN environment (parallel left right) rounds) := by
  have jointDomain :
      dom (parallel left right) = parallelDomain leftDomain rightDomain := by
    rw [dom_parallel, leftHasDomain, rightHasDomain]
    rfl
  have outerCompatible : Compatible environment (parallel left right) :=
    environmentCompatible (parallel left right) jointDomain
  obtain ⟨outerEnvironment, outerFinal, outerSystem⟩ :=
    trN_consistent_of_compatible (parallel left right) environment
      outerCompatible rounds
  have outerMatching := systemConsistent_parallel_matching left right
    (trN environment (parallel left right) rounds) outerSystem
  obtain ⟨dialogue, dialogueEqual⟩ := matching_exists_dialogue
    (trN environment (parallel left right) rounds) outerMatching
  have environmentConsistent :
      EnvConsistent environment (dialogueTranscript dialogue) := by
    rw [dialogueEqual]
    exact outerEnvironment
  have finalAt : FinalAt environment rounds (dialogueTranscript dialogue) := by
    rw [dialogueEqual]
    exact outerFinal
  have systemConsistent :
      SystemConsistent (parallel left right) (dialogueTranscript dialogue) := by
    rw [dialogueEqual]
    exact outerSystem
  have roundBound : dialogue.length ≤ rounds := by
    have transcriptBound := trN_length_le environment (parallel left right) rounds
    simpa [← dialogueEqual, dialogueTranscript] using transcriptBound
  have sameDomain : dom base = dom left := baseHasDomain.trans leftHasDomain.symm
  obtain ⟨inducedEnvironment, inducedFinal, inducedSystem⟩ :=
    inducedLeftBounded_follows base left right sameDomain environment rounds
      dialogue environmentConsistent finalAt systemConsistent roundBound
  have haltsAt : ∀ answers : List Y₁, rounds ≤ answers.length →
      answers ∉ (inducedLeftBounded base right environment rounds).1.Dom :=
    by
      intro answers lengthAtLeast admitted
      have current := admitted answers (List.prefix_refl answers)
      have projectedBound := leftPairs_length_le
        (trN environment (parallel (overrideDDS base answers) right) rounds)
      have transcriptBound := trN_length_le environment
        (parallel (overrideDDS base answers) right) rounds
      omega
  have compatible :
      Compatible (inducedLeftBounded base right environment rounds) left :=
    compatible_of_consistent_complete left
      (inducedLeftBounded base right environment rounds) rounds
      (leftTranscript dialogue) inducedEnvironment inducedFinal inducedSystem haltsAt
  constructor
  · exact compatible
  · calc
      trN (inducedLeftBounded base right environment rounds) left rounds =
          leftTranscript dialogue :=
        trN_eq_of_consistent left
          (inducedLeftBounded base right environment rounds) rounds
          (leftTranscript dialogue) inducedEnvironment inducedFinal inducedSystem
      _ = leftPairs (dialogueTranscript dialogue) :=
        (leftPairs_dialogueTranscript dialogue).symm
      _ = leftPairs (trN environment (parallel left right) rounds) := by
        rw [dialogueEqual]

private theorem stoppedTranscriptAt {X : Type*} {Y : Type*}
    (environment : DDE Y X) (system : DDS X Y) (rounds : Nat)
    (haltsAt : ∀ answers : List Y, rounds ≤ answers.length →
      answers ∉ environment.1.Dom) :
    (tr environment system).toOption = some (trN environment system rounds) := by
  have stable := trN_succ_eq_of_halts_bound haltsAt system
  let stops : Stops environment system := ⟨rounds, stable⟩
  rw [Part.toOption_eq_some_iff]
  exact ⟨stops, tr_get_eq_trN stops stable⟩

private def reconstructLeft
    (base : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat) :
    Option (Transcript X₁ Y₁) →
      Option (Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
  | none => none
  | some transcript => some (trN environment
      (parallel (overrideDDS base (transcript.map Prod.snd)) right) rounds)

private theorem fullLeftProbe_of_trN
    (leftDomain : Set (List X₁)) (rightDomain : Set (List X₂))
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (baseHasDomain : dom base = leftDomain)
    (leftHasDomain : dom left = leftDomain)
    (rightHasDomain : dom right = rightDomain)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (environmentCompatible : CompatibleD environment
      (parallelDomain leftDomain rightDomain))
    (rounds : Nat) :
    trN environment
        (parallel (overrideDDS base
          ((leftPairs (trN environment (parallel left right) rounds)).map Prod.snd))
          right) rounds =
      trN environment (parallel left right) rounds := by
  have jointDomain :
      dom (parallel left right) = parallelDomain leftDomain rightDomain := by
    rw [dom_parallel, leftHasDomain, rightHasDomain]
    rfl
  have compatible : Compatible environment (parallel left right) :=
    environmentCompatible (parallel left right) jointDomain
  obtain ⟨environmentConsistent, finalAt, systemConsistent⟩ :=
    trN_consistent_of_compatible (parallel left right) environment compatible rounds
  obtain ⟨dialogue, dialogueEqual⟩ := matching_exists_dialogue
    (trN environment (parallel left right) rounds)
    (systemConsistent_parallel_matching left right _ systemConsistent)
  have sameDomain : dom base = dom left := baseHasDomain.trans leftHasDomain.symm
  have probeEqual := fullLeftProbe_eq base left right sameDomain environment rounds
    dialogue (by simpa [dialogueEqual] using environmentConsistent)
    (by simpa [dialogueEqual] using finalAt)
    (by simpa [dialogueEqual] using systemConsistent)
  have answerEqual :
      leftAnswers dialogue =
        (leftPairs (trN environment (parallel left right) rounds)).map Prod.snd := by
    rw [← dialogueEqual, leftPairs_dialogueTranscript]
    rfl
  rw [← answerEqual, probeEqual, dialogueEqual]

private theorem reconstructLeft_transcript
    (leftDomain : Set (List X₁)) (rightDomain : Set (List X₂))
    (base left : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (baseHasDomain : dom base = leftDomain)
    (leftHasDomain : dom left = leftDomain)
    (rightHasDomain : dom right = rightDomain)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (environmentCompatible : CompatibleD environment
      (parallelDomain leftDomain rightDomain))
    (environmentHalts : DDE.Halts environment) :
    reconstructLeft base right environment environmentHalts.choose
        (tr (inducedLeftBounded base right environment environmentHalts.choose)
          left).toOption =
      (tr environment (parallel left right)).toOption := by
  let rounds := environmentHalts.choose
  have outerHalts := environmentHalts.choose_spec
  have innerHalts : ∀ answers : List Y₁, rounds ≤ answers.length →
      answers ∉ (inducedLeftBounded base right environment rounds).1.Dom := by
    intro answers lengthAtLeast admitted
    have current := admitted answers (List.prefix_refl answers)
    have projectedBound := leftPairs_length_le
      (trN environment (parallel (overrideDDS base answers) right) rounds)
    have transcriptBound := trN_length_le environment
      (parallel (overrideDDS base answers) right) rounds
    omega
  rw [stoppedTranscriptAt
      (inducedLeftBounded base right environment rounds) left rounds innerHalts,
    stoppedTranscriptAt environment (parallel left right) rounds outerHalts]
  simp only [reconstructLeft]
  have factor := inducedLeftBounded_factorization leftDomain rightDomain
    base left right baseHasDomain leftHasDomain rightHasDomain environment
    environmentCompatible rounds
  rw [factor.2]
  exact congrArg some (fullLeftProbe_of_trN leftDomain rightDomain
    base left right baseHasDomain leftHasDomain rightHasDomain environment
    environmentCompatible rounds)

private noncomputable def fixedRightLaw
    (left : PDS X₁ Y₁) (right : DDS X₂ Y₂) :
    PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  Distribution.fTransform (fun system => parallel system right) left

private theorem trLaw_fixedRightLaw
    (leftDomain : Set (List X₁)) (rightDomain : Set (List X₂))
    (base : DDS X₁ Y₁) (left : PDS X₁ Y₁) (right : DDS X₂ Y₂)
    (baseHasDomain : dom base = leftDomain)
    (leftHasDomain : PDS.HasDomain left leftDomain)
    (rightHasDomain : dom right = rightDomain)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (environmentCompatible : CompatibleD environment
      (parallelDomain leftDomain rightDomain))
    (environmentHalts : DDE.Halts environment) :
    PDS.trLaw environment (fixedRightLaw left right) =
      Distribution.fTransform
        (reconstructLeft base right environment environmentHalts.choose)
        (PDS.trLaw
          (inducedLeftBounded base right environment environmentHalts.choose)
          left) := by
  unfold PDS.trLaw fixedRightLaw
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro system supported
  exact (reconstructLeft_transcript leftDomain rightDomain base system right
    baseHasDomain (leftHasDomain system supported) rightHasDomain environment
    environmentCompatible environmentHalts).symm

private theorem fixedRight_observation_le_advantageOnDomain
    (leftDomain : Set (List X₁)) (rightDomain : Set (List X₂))
    (base : DDS X₁ Y₁) (left left' : PDS X₁ Y₁)
    (right : DDS X₂ Y₂)
    (baseHasDomain : dom base = leftDomain)
    (leftHasDomain : PDS.HasDomain left leftDomain)
    (leftHasDomain' : PDS.HasDomain left' leftDomain)
    (rightHasDomain : dom right = rightDomain)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (environmentCompatible : CompatibleD environment
      (parallelDomain leftDomain rightDomain))
    (environmentHalts : DDE.Halts environment) :
    ENNReal.ofReal (Probability.statDist
      (PDS.trLaw environment (fixedRightLaw left right))
      (PDS.trLaw environment (fixedRightLaw left' right))) ≤
      PDS.advantageOnDomain leftDomain left left' := by
  rw [trLaw_fixedRightLaw leftDomain rightDomain base left right
      baseHasDomain leftHasDomain rightHasDomain environment
      environmentCompatible environmentHalts,
    trLaw_fixedRightLaw leftDomain rightDomain base left' right
      baseHasDomain leftHasDomain' rightHasDomain environment
      environmentCompatible environmentHalts]
  let componentEnvironment :=
    inducedLeftBounded base right environment environmentHalts.choose
  have componentHalts : DDE.Halts componentEnvironment := by
    refine ⟨environmentHalts.choose, ?_⟩
    intro answers lengthAtLeast admitted
    have current := admitted answers (List.prefix_refl answers)
    have projectedBound := leftPairs_length_le
      (trN environment (parallel (overrideDDS base answers) right)
        environmentHalts.choose)
    have transcriptBound := trN_length_le environment
      (parallel (overrideDDS base answers) right) environmentHalts.choose
    omega
  have componentCompatible : CompatibleD componentEnvironment leftDomain := by
    intro system systemDomain
    exact (inducedLeftBounded_factorization leftDomain rightDomain
      base system right baseHasDomain systemDomain rightHasDomain environment
      environmentCompatible environmentHalts.choose).1
  calc
    ENNReal.ofReal (Probability.statDist
        (Distribution.fTransform
          (reconstructLeft base right environment environmentHalts.choose)
          (PDS.trLaw componentEnvironment left))
        (Distribution.fTransform
          (reconstructLeft base right environment environmentHalts.choose)
          (PDS.trLaw componentEnvironment left'))) ≤
      ENNReal.ofReal (Probability.statDist
        (PDS.trLaw componentEnvironment left)
        (PDS.trLaw componentEnvironment left')) :=
      ENNReal.ofReal_le_ofReal (Probability.statDist_fTransform_le _ _ _)
    _ ≤ PDS.advantageOnDomain leftDomain left left' :=
      le_iSup_of_le
        (⟨componentEnvironment, componentCompatible, componentHalts⟩ :
          {e : DDE Y₁ X₁ // CompatibleD e leftDomain ∧ DDE.Halts e})
        le_rfl

private theorem parallelLaw_eq_sum_right
    (left : PDS X₁ Y₁) (right : PDS X₂ Y₂) :
    parallelLaw left right =
      ∑ system ∈ right.support, right system • fixedRightLaw left system := by
  rw [parallelLaw, Distribution.prod_eq_sum_right,
    Distribution.fTransform_sum]
  apply Finset.sum_congr rfl
  intro system _
  rw [Distribution.fTransform_smul, fixedRightLaw,
    Distribution.fTransform_fTransform]
  apply congrArg (fun law => right system • law)
  apply Distribution.fTransform_congr
  intro deterministic _
  rfl

private theorem support_nonempty_of_probability
    (system : CommonDomain.ProbabilityPresentation X₁ Y₁) :
    system.law.1.support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro lawZero
  have normalized := system.law.2.weight_eq
  rw [lawZero] at normalized
  simp [Distribution.weight] at normalized

private theorem parallel_left_observation_le_advantageOnDomain
    (left left' : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right : CommonDomain.ProbabilityPresentation X₂ Y₂)
    (sameDomain : left'.domain = left.domain)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (environmentCompatible : CompatibleD environment
      (parallelDomain left.domain right.domain))
    (environmentHalts : DDE.Halts environment) :
    ENNReal.ofReal (Probability.statDist
      (PDS.trLaw environment (parallelLaw left.law.1 right.law.1))
      (PDS.trLaw environment (parallelLaw left'.law.1 right.law.1))) ≤
      PDS.advantageOnDomain left.domain left.law.1 left'.law.1 := by
  obtain ⟨base, baseSupported⟩ := support_nonempty_of_probability left
  have baseDomain := left.hasDomain base baseSupported
  unfold PDS.trLaw
  rw [parallelLaw_eq_sum_right, parallelLaw_eq_sum_right,
    Distribution.fTransform_sum, Distribution.fTransform_sum]
  simp_rw [Distribution.fTransform_smul]
  have weightSum :
      ∑ system ∈ right.law.1.support,
          ENNReal.ofReal (right.law.1 system) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun system supported => right.law.2.nonNeg system)]
    have normalized :
        ∑ system ∈ right.law.1.support, right.law.1 system = 1 := by
      rw [← Distribution.weight_eq_sum_of_support_subset right.law.1
        Finset.Subset.rfl]
      exact right.law.2.weight_eq
    rw [normalized, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (Probability.statDist
        (∑ system ∈ right.law.1.support, right.law.1 system •
          Distribution.fTransform (fun deterministic =>
            (tr environment deterministic).toOption)
            (fixedRightLaw left.law.1 system))
        (∑ system ∈ right.law.1.support, right.law.1 system •
          Distribution.fTransform (fun deterministic =>
            (tr environment deterministic).toOption)
            (fixedRightLaw left'.law.1 system))) ≤
      ENNReal.ofReal (∑ system ∈ right.law.1.support,
        right.law.1 system * Probability.statDist
          (PDS.trLaw environment (fixedRightLaw left.law.1 system))
          (PDS.trLaw environment (fixedRightLaw left'.law.1 system))) :=
      ENNReal.ofReal_le_ofReal
        (Probability.statDist_sum_le right.law.1.support right.law.1 _ _
          (fun system _ => right.law.2.nonNeg system))
    _ = ∑ system ∈ right.law.1.support,
        ENNReal.ofReal (right.law.1 system * Probability.statDist
          (PDS.trLaw environment (fixedRightLaw left.law.1 system))
          (PDS.trLaw environment (fixedRightLaw left'.law.1 system))) :=
      ENNReal.ofReal_sum_of_nonneg fun system supported =>
        mul_nonneg (right.law.2.nonNeg system)
          (Probability.statDist_nonneg _ _)
    _ ≤ ∑ system ∈ right.law.1.support,
        ENNReal.ofReal (right.law.1 system) *
          PDS.advantageOnDomain left.domain left.law.1 left'.law.1 := by
      refine Finset.sum_le_sum fun system supported => ?_
      rw [ENNReal.ofReal_mul (right.law.2.nonNeg system)]
      exact mul_le_mul' le_rfl
        (fixedRight_observation_le_advantageOnDomain left.domain right.domain base
          left.law.1 left'.law.1 system baseDomain left.hasDomain
          (sameDomain.symm ▸ left'.hasDomain) (right.hasDomain system supported)
          environment environmentCompatible environmentHalts)
    _ = PDS.advantageOnDomain left.domain left.law.1 left'.law.1 := by
      rw [← Finset.sum_mul, weightSum, one_mul]

private theorem advantageOnDomain_parallel_left_le
    (left left' : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right : CommonDomain.ProbabilityPresentation X₂ Y₂)
    (sameDomain : left'.domain = left.domain) :
    PDS.advantageOnDomain (parallelDomain left.domain right.domain)
        (parallelLaw left.law.1 right.law.1)
        (parallelLaw left'.law.1 right.law.1) ≤
      PDS.advantageOnDomain left.domain left.law.1 left'.law.1 := by
  -- Bound each compatible parallel observation by its induced left observation.
  refine iSup_le fun environment => ?_
  exact parallel_left_observation_le_advantageOnDomain left left' right sameDomain
    environment.1 environment.2.1 environment.2.2

private def swapTranscript
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    Transcript (X₂ ⊕ X₁) (Y₂ ⊕ Y₁) :=
  transcript.map fun pair => (Sum.swap pair.1, Sum.swap pair.2)

private def swapDDS (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    DDS (X₂ ⊕ X₁) (Y₂ ⊕ Y₁) :=
  ⟨fun history => (system.1 (history.map Sum.swap)).map Sum.swap, by
    constructor
    · exact system.2.1
    · intro first second hprefix firstNonempty secondDefined
      exact system.2.2 (hprefix.map Sum.swap)
        (fun mappedEmpty => firstNonempty (List.map_eq_nil_iff.mp mappedEmpty))
        secondDefined⟩

private def swapDDE
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) :
    DDE (Y₂ ⊕ Y₁) (X₂ ⊕ X₁) :=
  ⟨fun history => (environment.1 (history.map Sum.swap)).map Sum.swap, by
    intro first second hprefix secondDefined
    exact environment.2 (hprefix.map Sum.swap) secondDefined⟩

@[simp]
private theorem swapTranscript_nil :
    swapTranscript ([] : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) = [] :=
  rfl

@[simp]
private theorem swapTranscript_append
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (query : X₁ ⊕ X₂) (answer : Y₁ ⊕ Y₂) :
    swapTranscript (transcript ++ [(query, answer)]) =
      swapTranscript transcript ++ [(Sum.swap query, Sum.swap answer)] := by
  simp [swapTranscript]

@[simp]
private theorem swapTranscript_map_fst
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    (swapTranscript transcript).map Prod.fst =
      (transcript.map Prod.fst).map Sum.swap := by
  simp [swapTranscript, List.map_map]

@[simp]
private theorem swapTranscript_map_snd
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    (swapTranscript transcript).map Prod.snd =
      (transcript.map Prod.snd).map Sum.swap := by
  simp [swapTranscript, List.map_map]

@[simp]
private theorem dom_swapDDS
    (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (history : List (X₂ ⊕ X₁)) :
    history ∈ dom (swapDDS system) ↔ history.map Sum.swap ∈ dom system :=
  Iff.rfl

@[simp]
private theorem output_swapDDS
    (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (history : List (X₂ ⊕ X₁))
    (defined : history ∈ dom (swapDDS system)) :
    output (swapDDS system) history defined =
      Sum.swap (output system (history.map Sum.swap) defined) :=
  rfl

@[simp]
private theorem swapDDE_dom
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (history : List (Y₂ ⊕ Y₁)) :
    history ∈ (swapDDE environment).1.Dom ↔
      history.map Sum.swap ∈ environment.1.Dom :=
  Iff.rfl

@[simp]
private theorem swapDDE_get
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (history : List (Y₂ ⊕ Y₁))
    (defined : history ∈ (swapDDE environment).1.Dom) :
    ((swapDDE environment).1 history).get defined =
      Sum.swap ((environment.1 (history.map Sum.swap)).get defined) :=
  rfl

@[simp]
private theorem map_swap_swap (history : List (X₁ ⊕ X₂)) :
    (history.map Sum.swap).map Sum.swap = history := by
  simp [List.map_map]

private theorem trN_swap
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) (rounds : Nat) :
    trN (swapDDE environment) (swapDDS system) rounds =
      swapTranscript (trN environment system rounds) := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [trN, trN, inductionHypothesis]
      unfold trExtend
      simp only [swapTranscript_map_snd, swapDDE_dom, swapDDE_get,
        swapTranscript_map_fst, List.map_append, List.map_singleton,
        dom_swapDDS, map_swap_swap]
      by_cases environmentDefined :
          (trN environment system rounds).map Prod.snd ∈ environment.1.Dom
      · rw [dif_pos environmentDefined, dif_pos environmentDefined]
        simp only [Sum.swap_swap]
        by_cases systemDefined :
            (trN environment system rounds).map Prod.fst ++
                [(environment.1
                  ((trN environment system rounds).map Prod.snd)).get
                    environmentDefined] ∈ dom system
        · rw [dif_pos systemDefined, dif_pos systemDefined]
          simp [swapTranscript, List.map_map, Function.comp_def]
        · rw [dif_neg systemDefined, dif_neg systemDefined]
      · rw [dif_neg environmentDefined, dif_neg environmentDefined]

@[simp]
private theorem leftQueries_map_swap (history : List (X₂ ⊕ X₁)) :
    leftQueries (history.map Sum.swap) = rightQueries history := by
  unfold leftQueries rightQueries
  rw [List.filterMap_map]
  congr 1
  funext query
  cases query <;> rfl

@[simp]
private theorem rightQueries_map_swap (history : List (X₂ ⊕ X₁)) :
    rightQueries (history.map Sum.swap) = leftQueries history := by
  unfold leftQueries rightQueries
  rw [List.filterMap_map]
  congr 1
  funext query
  cases query <;> rfl

private theorem swapDDS_parallel (left : DDS X₁ Y₁) (right : DDS X₂ Y₂) :
    swapDDS (parallel left right) = parallel right left := by
  apply Subtype.ext
  funext history
  apply Part.ext'
  · change
      (history.map Sum.swap ≠ [] ∧
        (leftQueries (history.map Sum.swap) = [] ∨
          leftQueries (history.map Sum.swap) ∈ dom left) ∧
        (rightQueries (history.map Sum.swap) = [] ∨
          rightQueries (history.map Sum.swap) ∈ dom right)) ↔
      (history ≠ [] ∧
        (leftQueries history = [] ∨ leftQueries history ∈ dom right) ∧
        (rightQueries history = [] ∨ rightQueries history ∈ dom left))
    simp only [leftQueries_map_swap, rightQueries_map_swap]
    constructor
    · intro defined
      exact ⟨fun historyEmpty => defined.1 (by simp [historyEmpty]),
        defined.2.2, defined.2.1⟩
    · intro defined
      exact ⟨fun mappedEmpty =>
          defined.1 (List.map_eq_nil_iff.mp mappedEmpty),
        defined.2.2, defined.2.1⟩
  · intro swappedDefined directDefined
    have historyNonempty : history ≠ [] := by
      exact directDefined.1
    change output (swapDDS (parallel left right)) history swappedDefined =
      output (parallel right left) history directDefined
    rw [output_swapDDS]
    change Sum.swap (parallelOutput left right (history.map Sum.swap)
        swappedDefined ((history.map Sum.swap).getLast _) _) =
      parallelOutput right left history directDefined
        (history.getLast historyNonempty) _
    let last := history.getLast historyNonempty
    have lastMem : last ∈ history := List.getLast_mem historyNonempty
    have swappedLastMem : Sum.swap last ∈ history.map Sum.swap := by
      exact List.mem_map.mpr ⟨last, lastMem, rfl⟩
    have mappedLast : (history.map Sum.swap).getLast (by simp [historyNonempty]) =
        Sum.swap last := by
      simp [last, List.getLast_map]
    have outputCase : ∀ (candidate : X₂ ⊕ X₁)
        (candidateMem : candidate ∈ history)
        (swappedMem : Sum.swap candidate ∈ history.map Sum.swap),
        Sum.swap (parallelOutput left right (history.map Sum.swap)
          swappedDefined (Sum.swap candidate) swappedMem) =
        parallelOutput right left history directDefined candidate candidateMem := by
      intro candidate candidateMem swappedMem
      cases candidate <;>
        simp [parallelOutput, leftQueries_map_swap, rightQueries_map_swap]
    calc
      Sum.swap (parallelOutput left right (history.map Sum.swap)
          swappedDefined ((history.map Sum.swap).getLast _) _) =
        Sum.swap (parallelOutput left right (history.map Sum.swap)
          swappedDefined (Sum.swap last) swappedLastMem) :=
            congrArg Sum.swap (parallelOutput_congr_last left right _ _
              mappedLast _ _)
      _ = parallelOutput right left history directDefined last lastMem :=
        outputCase last lastMem swappedLastMem
      _ = parallelOutput right left history directDefined
          (history.getLast historyNonempty) _ :=
        parallelOutput_congr_last right left _ _ (by rfl) _ _

private theorem inducedLeftBounded_halts
    (base : DDS X₁ Y₁) (right : DDS X₂ Y₂)
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) (rounds : Nat) :
    DDE.Halts (inducedLeftBounded base right environment rounds) := by
  refine ⟨rounds, ?_⟩
  intro answers lengthAtLeast admitted
  have current := admitted answers (List.prefix_refl answers)
  have projectedBound := leftPairs_length_le
    (trN environment (parallel (overrideDDS base answers) right) rounds)
  have transcriptBound := trN_length_le environment
    (parallel (overrideDDS base answers) right) rounds
  omega

private def swapDomain
    (domain : Set (List (X₁ ⊕ X₂))) : Set (List (X₂ ⊕ X₁)) :=
  {history | history.map Sum.swap ∈ domain}

@[simp]
private theorem swapTranscript_involution
    (transcript : Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    swapTranscript (swapTranscript transcript) = transcript := by
  simp [swapTranscript, List.map_map, Function.comp_def]

@[simp]
private theorem swapDDS_involution
    (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    swapDDS (swapDDS system) = system := by
  apply Subtype.ext
  funext history
  apply Part.ext'
  · change ((history.map Sum.swap).map Sum.swap ∈ dom system) ↔
      history ∈ dom system
    simp [List.map_map, Function.comp_def]
  · intro _ _
    change Sum.swap (Sum.swap (output system
      ((history.map Sum.swap).map Sum.swap) _)) = output system history _
    simpa only [Sum.swap_swap, List.map_map, Function.comp_def]
      using output_congr system (by simp) _ _

@[simp]
private theorem swapDDE_involution
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂)) :
    swapDDE (swapDDE environment) = environment := by
  apply Subtype.ext
  funext history
  change Part.map Sum.swap
      (Part.map Sum.swap
        (environment.1 ((history.map Sum.swap).map Sum.swap))) =
    environment.1 history
  have inputSwap :
      (Sum.swap ∘ Sum.swap : Y₁ ⊕ Y₂ → Y₁ ⊕ Y₂) = id := by
    funext value
    exact Sum.swap_swap value
  have outputSwap :
      (Sum.swap ∘ Sum.swap : X₁ ⊕ X₂ → X₁ ⊕ X₂) = id := by
    funext value
    exact Sum.swap_swap value
  rw [Part.map_map, List.map_map, inputSwap, outputSwap]
  simp only [List.map_id]
  exact Part.map_id' (fun value : X₁ ⊕ X₂ => rfl)
    (environment.1 history)

private theorem compatible_swap
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (compatible : Compatible environment system) :
    Compatible (swapDDE environment) (swapDDS system) := by
  intro rounds query responds
  rw [trN_swap] at responds ⊢
  simp only [swapTranscript_map_snd, swapDDE, map_swap_swap] at responds
  obtain ⟨oldQuery, oldResponds, queryEqual⟩ :=
    (Part.mem_map_iff Sum.swap).mp responds
  have oldAdmitted := compatible rounds oldQuery oldResponds
  have swappedQuery : Sum.swap query = oldQuery := by
    rw [← queryEqual, Sum.swap_swap]
  rw [← swappedQuery] at oldAdmitted
  simpa only [swapTranscript_map_fst, List.map_append,
    List.map_singleton, Sum.swap_swap, dom_swapDDS,
    map_swap_swap] using oldAdmitted

private theorem compatibleD_swap
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (domain : Set (List (X₁ ⊕ X₂)))
    (compatible : CompatibleD environment domain) :
    CompatibleD (swapDDE environment) (swapDomain domain) := by
  intro system systemDomain
  have originalDomain : dom (swapDDS system) = domain := by
    ext history
    change history.map Sum.swap ∈ dom system ↔ history ∈ domain
    rw [systemDomain]
    change (history.map Sum.swap).map Sum.swap ∈ domain ↔ _
    simp [List.map_map, Function.comp_def]
  have originalCompatible := compatible (swapDDS system) originalDomain
  have swappedCompatible := compatible_swap environment (swapDDS system)
    originalCompatible
  simpa only [swapDDS_involution] using swappedCompatible

private theorem halts_swap
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (halts : DDE.Halts environment) :
    DDE.Halts (swapDDE environment) := by
  obtain ⟨rounds, bound⟩ := halts
  refine ⟨rounds, ?_⟩
  intro answers lengthAtLeast admitted
  exact bound (answers.map Sum.swap) (by simpa using lengthAtLeast) admitted

private theorem tr_toOption_swap
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (system : DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (halts : DDE.Halts environment) :
    (tr (swapDDE environment) (swapDDS system)).toOption =
      (tr environment system).toOption.map swapTranscript := by
  let rounds := halts.choose
  have originalBound := halts.choose_spec
  have swappedBound : ∀ answers : List (Y₂ ⊕ Y₁),
      rounds ≤ answers.length →
        answers ∉ (swapDDE environment).1.Dom := by
    intro answers lengthAtLeast admitted
    exact originalBound (answers.map Sum.swap)
      (by simpa [rounds] using lengthAtLeast) admitted
  rw [stoppedTranscriptAt (swapDDE environment) (swapDDS system)
      rounds swappedBound,
    stoppedTranscriptAt environment system rounds originalBound,
    trN_swap]
  rfl

@[simp]
private theorem swapDomain_involution
    (domain : Set (List (X₁ ⊕ X₂))) :
    swapDomain (swapDomain domain) = domain := by
  ext history
  change (history.map Sum.swap).map Sum.swap ∈ domain ↔ history ∈ domain
  simp [List.map_map, Function.comp_def]

private noncomputable def swapLaw
    (law : PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    PDS (X₂ ⊕ X₁) (Y₂ ⊕ Y₁) :=
  Distribution.fTransform swapDDS law

@[simp]
private theorem swapLaw_involution
    (law : PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    swapLaw (swapLaw law) = law := by
  rw [swapLaw, swapLaw, Distribution.fTransform_fTransform]
  calc
    Distribution.fTransform (swapDDS ∘ swapDDS) law =
        Distribution.fTransform id law := by
      apply Distribution.fTransform_congr
      intro system _
      exact swapDDS_involution system
    _ = law := Distribution.fTransform_id law

private theorem trLaw_swap
    (environment : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂))
    (law : PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂))
    (halts : DDE.Halts environment) :
    PDS.trLaw (swapDDE environment) (swapLaw law) =
      Distribution.fTransform (Option.map swapTranscript)
        (PDS.trLaw environment law) := by
  unfold PDS.trLaw swapLaw
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro system _
  exact tr_toOption_swap environment system halts

private theorem option_swapTranscript_injective :
    Function.Injective
      (Option.map swapTranscript :
        Option (Transcript (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) →
          Option (Transcript (X₂ ⊕ X₁) (Y₂ ⊕ Y₁))) := by
  apply Option.map_injective
  intro left right equal
  have mapped := congrArg swapTranscript equal
  simpa only [swapTranscript_involution] using mapped

private theorem swapDomain_parallelDomain
    (left : Set (List X₁)) (right : Set (List X₂)) :
    swapDomain (parallelDomain left right) = parallelDomain right left := by
  ext history
  simp [swapDomain, parallelDomain, leftQueries_map_swap,
    rightQueries_map_swap, and_comm]

private theorem swapLaw_parallelLaw
    (left : PDS X₁ Y₁) (right : PDS X₂ Y₂) :
    swapLaw (parallelLaw left right) = parallelLaw right left := by
  unfold swapLaw parallelLaw
  rw [Distribution.fTransform_fTransform,
    ← Distribution.fTransform_swap_prod left right,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro systems _
  exact swapDDS_parallel systems.1 systems.2

private theorem advantageOnDomain_swap_le
    (domain : Set (List (X₁ ⊕ X₂)))
    (left right : PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    PDS.advantageOnDomain (swapDomain domain) (swapLaw left) (swapLaw right) ≤
      PDS.advantageOnDomain domain left right := by
  refine iSup_le fun environment => ?_
  have swappedHalts : DDE.Halts (swapDDE environment.1) :=
    halts_swap environment.1 environment.2.2
  have swappedCompatible : CompatibleD (swapDDE environment.1) domain := by
    have twice := compatibleD_swap environment.1 (swapDomain domain)
      environment.2.1
    simpa only [swapDomain_involution] using twice
  have leftLaw := trLaw_swap (swapDDE environment.1) left swappedHalts
  have rightLaw := trLaw_swap (swapDDE environment.1) right swappedHalts
  simp only [swapDDE_involution] at leftLaw rightLaw
  calc
    ENNReal.ofReal (Probability.statDist
        (PDS.trLaw environment.1 (swapLaw left))
        (PDS.trLaw environment.1 (swapLaw right))) =
      ENNReal.ofReal (Probability.statDist
        (Distribution.fTransform (Option.map swapTranscript)
          (PDS.trLaw (swapDDE environment.1) left))
        (Distribution.fTransform (Option.map swapTranscript)
          (PDS.trLaw (swapDDE environment.1) right))) := by
      rw [leftLaw, rightLaw]
    _ = ENNReal.ofReal (Probability.statDist
        (PDS.trLaw (swapDDE environment.1) left)
        (PDS.trLaw (swapDDE environment.1) right)) := by
      congr 1
      exact Probability.statDist_fTransform_injective _ _ _
        option_swapTranscript_injective
    _ ≤ PDS.advantageOnDomain domain left right :=
      le_iSup_of_le
        (⟨swapDDE environment.1, swappedCompatible, swappedHalts⟩ :
          {e : DDE (Y₁ ⊕ Y₂) (X₁ ⊕ X₂) //
            CompatibleD e domain ∧ DDE.Halts e})
        le_rfl

private theorem advantageOnDomain_swap_eq
    (domain : Set (List (X₁ ⊕ X₂)))
    (left right : PDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂)) :
    PDS.advantageOnDomain (swapDomain domain) (swapLaw left) (swapLaw right) =
      PDS.advantageOnDomain domain left right := by
  apply le_antisymm
  · exact advantageOnDomain_swap_le domain left right
  · have reverse := advantageOnDomain_swap_le (swapDomain domain)
      (swapLaw left) (swapLaw right)
    simpa only [swapDomain_involution, swapLaw_involution] using reverse

private theorem advantageOnDomain_parallel_right_le
    (left : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right right' : CommonDomain.ProbabilityPresentation X₂ Y₂)
    (sameDomain : right'.domain = right.domain) :
    PDS.advantageOnDomain (parallelDomain left.domain right.domain)
        (parallelLaw left.law.1 right.law.1)
        (parallelLaw left.law.1 right'.law.1) ≤
      PDS.advantageOnDomain right.domain right.law.1 right'.law.1 := by
  -- Swap the ordered components, apply the left bound, and swap back.
  calc
    PDS.advantageOnDomain (parallelDomain left.domain right.domain)
        (parallelLaw left.law.1 right.law.1)
        (parallelLaw left.law.1 right'.law.1) =
      PDS.advantageOnDomain (swapDomain (parallelDomain left.domain right.domain))
        (swapLaw (parallelLaw left.law.1 right.law.1))
        (swapLaw (parallelLaw left.law.1 right'.law.1)) :=
      (advantageOnDomain_swap_eq (parallelDomain left.domain right.domain)
        (parallelLaw left.law.1 right.law.1)
        (parallelLaw left.law.1 right'.law.1)).symm
    _ = PDS.advantageOnDomain (parallelDomain right.domain left.domain)
        (parallelLaw right.law.1 left.law.1)
        (parallelLaw right'.law.1 left.law.1) := by
      rw [swapDomain_parallelDomain, swapLaw_parallelLaw,
        swapLaw_parallelLaw]
    _ ≤ PDS.advantageOnDomain right.domain right.law.1 right'.law.1 :=
      advantageOnDomain_parallel_left_le right right' left sameDomain

private theorem advantageOnDomain_parallel_le
    (left left' : CommonDomain.ProbabilityPresentation X₁ Y₁)
    (right right' : CommonDomain.ProbabilityPresentation X₂ Y₂)
    (leftDomain : left'.domain = left.domain)
    (rightDomain : right'.domain = right.domain) :
    PDS.advantageOnDomain (parallelDomain left.domain right.domain)
        (parallelLaw left.law.1 right.law.1)
        (parallelLaw left'.law.1 right'.law.1) ≤
      PDS.advantageOnDomain left.domain left.law.1 left'.law.1 +
      PDS.advantageOnDomain right.domain right.law.1 right'.law.1 := by
  -- First change the left component while holding the right fixed.
  have leftBound := advantageOnDomain_parallel_left_le left left' right leftDomain
  -- Then change the right component while holding the new left fixed.
  have rightBound :
      PDS.advantageOnDomain (parallelDomain left.domain right.domain)
          (parallelLaw left'.law.1 right.law.1)
          (parallelLaw left'.law.1 right'.law.1) ≤
        PDS.advantageOnDomain right.domain right.law.1 right'.law.1 := by
    simpa only [leftDomain] using
      advantageOnDomain_parallel_right_le left' right right' rightDomain
  -- The triangle inequality joins the two one-component changes.
  exact
    (PDS.advantageOnDomain_triangle (parallelDomain left.domain right.domain)
      (parallelLaw left.law.1 right.law.1)
      (parallelLaw left'.law.1 right.law.1)
      (parallelLaw left'.law.1 right'.law.1)).trans
      (add_le_add leftBound rightBound)

namespace CommonDomain

/-- Left-component projection of a tagged query history. -/
def leftQueries (history : List (X₁ ⊕ X₂)) : List X₁ :=
  RandomSystems.leftQueries history

/-- Right-component projection of a tagged query history. -/
def rightQueries (history : List (X₁ ⊕ X₂)) : List X₂ :=
  RandomSystems.rightQueries history

/-- Lanzenberger, Definition 2.13 (printed p. 14): “The parallel composition of
a family of `(Xᵢ, Yᵢ)`-systems.”  Binary ordered sums implement the source's
component tags. -/
def parallelDDS (left : System.DDS X₁ Y₁) (right : System.DDS X₂ Y₂) :
    System.DDS (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  parallel left right

@[simp]
theorem dom_parallelDDS (left : System.DDS X₁ Y₁)
    (right : System.DDS X₂ Y₂) :
    System.dom (parallelDDS left right) =
      {history | history ≠ [] ∧
        (leftQueries history = [] ∨ leftQueries history ∈ System.dom left) ∧
        (rightQueries history = [] ∨
          rightQueries history ∈ System.dom right)} :=
  dom_parallel left right

/-- Exact left-component evaluation of binary ordered parallel. -/
theorem output_parallelDDS_left (left : System.DDS X₁ Y₁)
    (right : System.DDS X₂ Y₂) (history : List (X₁ ⊕ X₂))
    (query : X₁)
    (defined : history ++ [Sum.inl query] ∈
      System.dom (parallelDDS left right)) :
    System.output (parallelDDS left right)
        (history ++ [Sum.inl query]) defined =
      Sum.inl (System.output left (leftQueries history ++ [query]) (by
        have component := (dom_parallelDDS left right ▸ defined).2.1
        rcases component with empty | admitted
        · simp [leftQueries] at empty
        · simpa [leftQueries] using admitted)) :=
  output_parallel_left left right history query defined

/-- Exact right-component evaluation of binary ordered parallel. -/
theorem output_parallelDDS_right (left : System.DDS X₁ Y₁)
    (right : System.DDS X₂ Y₂) (history : List (X₁ ⊕ X₂))
    (query : X₂)
    (defined : history ++ [Sum.inr query] ∈
      System.dom (parallelDDS left right)) :
    System.output (parallelDDS left right)
        (history ++ [Sum.inr query]) defined =
      Sum.inr (System.output right (rightQueries history ++ [query]) (by
        have component := (dom_parallelDDS left right ▸ defined).2.2
        rcases component with empty | admitted
        · simp [rightQueries] at empty
        · simpa [rightQueries] using admitted)) :=
  output_parallel_right left right history query defined

/-- Binary ordered parallel depends only on the two component domains. -/
theorem parallelDDS_dom_congr
    {left left' : System.DDS X₁ Y₁}
    {right right' : System.DDS X₂ Y₂}
    (leftDomain : System.dom left = System.dom left')
    (rightDomain : System.dom right = System.dom right') :
    System.dom (parallelDDS left right) =
      System.dom (parallelDDS left' right') := by
  rw [parallelDDS, parallelDDS, dom_parallel, dom_parallel,
    leftDomain, rightDomain]

end CommonDomain

namespace CommonDomain.ProbabilityPresentation

/-- Independent ordered parallel preserves normalization and the common-domain
condition. -/
noncomputable def parallel
    (left : ProbabilityPresentation X₁ Y₁)
    (right : ProbabilityPresentation X₂ Y₂) :
    ProbabilityPresentation (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  parallelPresentation left right

@[simp]
theorem parallel_law
    (left : ProbabilityPresentation X₁ Y₁)
    (right : ProbabilityPresentation X₂ Y₂) :
    (parallel left right).law.1 = parallelLaw left.law.1 right.law.1 :=
  rfl

@[simp]
theorem parallel_domain
    (left : ProbabilityPresentation X₁ Y₁)
    (right : ProbabilityPresentation X₂ Y₂) :
    (parallel left right).domain =
      parallelDomain left.domain right.domain :=
  parallelPresentation_domain left right

/-- Ordered parallel is independent of the selected normalized
presentatives. -/
theorem equivalent_parallel
    {left left' : ProbabilityPresentation X₁ Y₁}
    {right right' : ProbabilityPresentation X₂ Y₂}
    (leftEquivalent : Equivalent left left')
    (rightEquivalent : Equivalent right right') :
    Equivalent (parallel left right) (parallel left' right') :=
  parallelPresentation_equivalent leftEquivalent rightEquivalent

/-- Changing only the left component is nonexpanding within its common-domain
fibre. -/
theorem advantageOnDomain_parallel_left_le
    (left left' : ProbabilityPresentation X₁ Y₁)
    (right : ProbabilityPresentation X₂ Y₂)
    (sameDomain : left'.domain = left.domain) :
    PDS.advantageOnDomain (parallel left right).domain
        (parallel left right).law.1 (parallel left' right).law.1 ≤
      PDS.advantageOnDomain left.domain left.law.1 left'.law.1 := by
  rw [parallel_domain]
  exact RandomSystems.advantageOnDomain_parallel_left_le left left' right sameDomain

/-- Changing only the right component is nonexpanding within its common-domain
fibre. -/
theorem advantageOnDomain_parallel_right_le
    (left : ProbabilityPresentation X₁ Y₁)
    (right right' : ProbabilityPresentation X₂ Y₂)
    (sameDomain : right'.domain = right.domain) :
    PDS.advantageOnDomain (parallel left right).domain
        (parallel left right).law.1 (parallel left right').law.1 ≤
      PDS.advantageOnDomain right.domain right.law.1 right'.law.1 := by
  rw [parallel_domain]
  exact RandomSystems.advantageOnDomain_parallel_right_le left right right' sameDomain

/-- Independent ordered parallel is jointly nonexpanding within the two fixed
common-domain fibres. -/
theorem advantageOnDomain_parallel_le
    (left left' : ProbabilityPresentation X₁ Y₁)
    (right right' : ProbabilityPresentation X₂ Y₂)
    (leftDomain : left'.domain = left.domain)
    (rightDomain : right'.domain = right.domain) :
    PDS.advantageOnDomain (parallel left right).domain
        (parallel left right).law.1 (parallel left' right').law.1 ≤
      PDS.advantageOnDomain left.domain left.law.1 left'.law.1 +
        PDS.advantageOnDomain right.domain right.law.1 right'.law.1 := by
  rw [parallel_domain]
  exact RandomSystems.advantageOnDomain_parallel_le left left' right right'
    leftDomain rightDomain

end CommonDomain.ProbabilityPresentation

namespace CommonDomain.ProbabilityRandomSystem

/-- Independent ordered parallel on normalized common-domain random systems. -/
noncomputable def parallel :
    ProbabilityRandomSystem X₁ Y₁ → ProbabilityRandomSystem X₂ Y₂ →
      ProbabilityRandomSystem (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) :=
  parallelRandomSystem

@[simp]
theorem parallel_ofPresentation
    (left : ProbabilityPresentation X₁ Y₁)
    (right : ProbabilityPresentation X₂ Y₂) :
    parallel (ofPresentation left) (ofPresentation right) =
      ofPresentation (ProbabilityPresentation.parallel left right) :=
  parallelRandomSystem_ofPresentation left right

end CommonDomain.ProbabilityRandomSystem

end

end RandomSystems
