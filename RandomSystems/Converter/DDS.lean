/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Interface
import Mathlib.Data.List.Basic

set_option autoImplicit false

/-!
# Deterministic discrete systems at addressed interfaces

A history is a nonempty finite list of attempted queries.  A deterministic
discrete system is the mathematical function which assigns an optional answer
in the fibre selected by the final attempted query.  Rejection is therefore an
ordinary value and remains part of the argument to all later evaluations.

Ordered parallel projects the complete tagged query history to the component
selected by the final tag.  The definitions below are native to this model;
they do not pass through a second system representation.

Maurer--Renner 2016 leaves the resource carrier abstract. Jost and
Liu--Maurer use probabilistic random systems. Lanzenberger's literal partial
DDS is owned by the fixed-interface `RandomSystems.DDS`; this optional-answer
attempted-history DDS is the deterministic ambient specialization used for
query-indexed DDC attachment.
-/

namespace RandomSystems.Ambient

universe u v w z

/-- A nonempty finite history of attempted queries at an interface. -/
structure History (A : Interface.{u, v}) where
  queries : List A.query
  nonempty : queries ≠ []

namespace History

/-- The one-query history. -/
def singleton {A : Interface.{u, v}} (query : A.query) : History A where
  queries := [query]
  nonempty := by simp

/-- Append one attempted query. -/
def snoc {A : Interface.{u, v}} (history : History A)
    (query : A.query) : History A where
  queries := history.queries ++ [query]
  nonempty := by simp

/-- The first query of a nonempty attempted-query history. -/
def head {A : Interface.{u, v}} (history : History A) : A.query :=
  history.queries.head history.nonempty

/-- The attempted queries strictly after the first query. -/
def tail {A : Interface.{u, v}} (history : History A) : List A.query :=
  history.queries.tail

@[simp]
theorem coe_snoc {A : Interface.{u, v}} (history : History A)
    (query : A.query) :
    (snoc history query).queries = history.queries ++ [query] :=
  rfl

/-- The final attempted query. -/
def last {A : Interface.{u, v}} (history : History A) : A.query :=
  history.queries.getLast history.nonempty

/-- Pointwise mapping of an attempted-query history. -/
def map {A : Interface.{u, v}} {B : Interface.{w, z}}
    (function : A.query → B.query)
    (history : History A) : History B where
  queries := history.queries.map function
  nonempty := by simpa using history.nonempty

@[ext]
theorem ext {A : Interface.{u, v}} {left right : History A}
    (equal : left.queries = right.queries) : left = right := by
  cases left
  cases right
  cases equal
  rfl

@[simp]
theorem last_singleton {A : Interface.{u, v}} (query : A.query) :
    (singleton query).last = query := by
  simp [last, singleton]

@[simp]
theorem last_snoc {A : Interface.{u, v}} (history : History A)
    (query : A.query) : (snoc history query).last = query := by
  simp [last, snoc]

@[simp]
theorem map_singleton {A : Interface.{u, v}} {B : Interface.{w, z}}
    (function : A.query → B.query) (query : A.query) :
    map function (singleton query) = singleton (function query) :=
  rfl

@[simp]
theorem map_snoc {A : Interface.{u, v}} {B : Interface.{w, z}}
    (function : A.query → B.query) (history : History A)
    (query : A.query) :
    map function (snoc history query) = snoc (map function history)
      (function query) := by
  apply ext
  simp [map, snoc]

@[simp]
theorem map_id {A : Interface.{u, v}} (history : History A) :
    map id history = history := by
  apply ext
  simp [map]

theorem map_comp {A B C : Interface.{u, v}}
    (second : B.query → C.query) (first : A.query → B.query)
    (history : History A) :
    map second (map first history) = map (second ∘ first) history := by
  apply ext
  simp [map, Function.comp_def]

@[simp]
theorem last_map {A : Interface.{u, v}} {B : Interface.{w, z}}
    (function : A.query → B.query) (history : History A) :
    (map function history).last = function history.last := by
  simp [last, map, List.getLast_map]

end History

/-- A deterministic discrete system with query-selected answers. -/
abbrev DDS (A : Interface.{u, v}) :=
  (history : History A) → Option (A.answer history.last)

namespace DDS

@[ext]
theorem ext {A : Interface.{u, v}} {left right : DDS A}
    (equal : ∀ history, left history = right history) : left = right :=
  funext equal

/-- The DDS induced by an ordinary total function. Its answer depends only on
the last attempted query. -/
def ofFunction {A : Interface.{u, v}}
    (function : (query : A.query) → A.answer query) : DDS A :=
  fun history => some (function history.last)

@[simp]
theorem ofFunction_apply {A : Interface.{u, v}}
    (function : (query : A.query) → A.answer query) (history : History A) :
    ofFunction function history = some (function history.last) :=
  rfl

abbrev PackedAnswer (A : Interface.{u, v}) :=
  Σ query, Option (A.answer query)

def pack {A : Interface.{u, v}} (system : DDS A)
    (history : History A) : PackedAnswer A :=
  ⟨history.last, system history⟩

theorem pack_injective {A : Interface.{u, v}}
    (history : History A) :
    Function.Injective (fun answer =>
      (⟨history.last, answer⟩ : PackedAnswer A)) := by
  intro left right equal
  cases equal
  rfl

def mapPackedAnswer {A B : Interface.{u, v}}
    (equivalence : A.Equiv B) : PackedAnswer A → PackedAnswer B
  | ⟨query, answer⟩ =>
      ⟨equivalence.queries query, answer.map (equivalence.answers query)⟩

@[simp]
theorem mapPackedAnswer_refl {A : Interface.{u, v}}
    (answer : PackedAnswer A) :
    mapPackedAnswer (.refl A) answer = answer := by
  rcases answer with ⟨query, answer⟩
  cases answer <;> rfl

theorem mapPackedAnswer_trans {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C)
    (answer : PackedAnswer A) :
    mapPackedAnswer second (mapPackedAnswer first answer) =
      mapPackedAnswer (first.trans second) answer := by
  rcases answer with ⟨query, answer⟩
  cases answer <;> rfl

/-- Relabel a DDS along an equivalence of addressed interfaces. -/
noncomputable def relabel {A B : Interface.{u, v}}
    (equivalence : A.Equiv B) (system : DDS A) : DDS B := by
  classical
  intro history
  let source := History.map equivalence.queries.symm history
  let mapped : Option (B.answer (equivalence.queries source.last)) :=
    (system source).map (equivalence.answers source.last)
  have selected : equivalence.queries source.last = history.last := by
    simp [source]
  exact cast (congrArg (fun query => Option (B.answer query)) selected) mapped

theorem pack_relabel {A B : Interface.{u, v}}
    (equivalence : A.Equiv B) (system : DDS A) (history : History B) :
    pack (relabel equivalence system) history =
      mapPackedAnswer equivalence
        (pack system (History.map equivalence.queries.symm history)) := by
  classical
  unfold pack mapPackedAnswer relabel
  dsimp only
  let source := History.map equivalence.queries.symm history
  have selected : equivalence.queries source.last = history.last := by
    simp [source]
  apply Sigma.ext selected.symm
  exact cast_heq
    (congrArg (fun query => Option (B.answer query)) selected)
    ((system source).map (equivalence.answers source.last))

@[simp]
theorem relabel_refl {A : Interface.{u, v}} (system : DDS A) :
    relabel (.refl A) system = system := by
  apply ext
  intro history
  apply pack_injective history
  calc
    pack (relabel (.refl A) system) history =
        mapPackedAnswer (.refl A)
          (pack system (History.map id history)) :=
      pack_relabel (.refl A) system history
    _ = mapPackedAnswer (.refl A) (pack system history) := by
      rw [History.map_id]
    _ = pack system history := mapPackedAnswer_refl _

theorem relabel_trans {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) (system : DDS A) :
    relabel second (relabel first system) =
      relabel (first.trans second) system := by
  apply ext
  intro history
  have historiesEqual :
      History.map first.queries.symm
          (History.map second.queries.symm history) =
        History.map (first.trans second).queries.symm history := by
    apply History.ext
    change (history.queries.map second.queries.symm).map
        first.queries.symm =
      history.queries.map (first.trans second).queries.symm
    simp [Interface.Equiv.trans]
  apply pack_injective history
  calc
    pack (relabel second (relabel first system)) history =
        mapPackedAnswer second
          (pack (relabel first system)
            (History.map second.queries.symm history)) :=
      pack_relabel second (relabel first system) history
    _ = mapPackedAnswer second
          (mapPackedAnswer first
            (pack system
              (History.map first.queries.symm
                (History.map second.queries.symm history)))) := by
      rw [pack_relabel]
    _ = mapPackedAnswer second
          (mapPackedAnswer first
            (pack system
              (History.map (first.trans second).queries.symm history))) := by
      rw [historiesEqual]
    _ = mapPackedAnswer (first.trans second)
          (pack system
            (History.map (first.trans second).queries.symm history)) :=
      mapPackedAnswer_trans first second _
    _ = pack (relabel (first.trans second) system) history :=
      (pack_relabel (first.trans second) system history).symm

def leftQueries {A B : Interface.{u, v}}
    (queries : List (Interface.parallel A B).query) : List A.query :=
  queries.filterMap fun
    | Sum.inl query => some query
    | Sum.inr _ => none

def rightQueries {A B : Interface.{u, v}}
    (queries : List (Interface.parallel A B).query) : List B.query :=
  queries.filterMap fun
    | Sum.inl _ => none
    | Sum.inr query => some query

theorem leftQueries_append_inl {A B : Interface.{u, v}}
    (queries : List (A.query ⊕ B.query)) (query : A.query) :
    leftQueries (queries ++ [Sum.inl query]) =
      leftQueries queries ++ [query] := by
  induction queries with
  | nil => rfl
  | cons tagged remaining inductionHypothesis =>
      cases tagged with
      | inl current =>
          change current :: leftQueries (remaining ++ [Sum.inl query]) =
            current :: (leftQueries remaining ++ [query])
          exact congrArg (List.cons current) inductionHypothesis
      | inr current =>
          change leftQueries (remaining ++ [Sum.inl query]) =
            leftQueries remaining ++ [query]
          exact inductionHypothesis

theorem rightQueries_append_inr {A B : Interface.{u, v}}
    (queries : List (A.query ⊕ B.query)) (query : B.query) :
    rightQueries (queries ++ [Sum.inr query]) =
      rightQueries queries ++ [query] := by
  induction queries with
  | nil => rfl
  | cons tagged remaining inductionHypothesis =>
      cases tagged with
      | inl current =>
          change rightQueries (remaining ++ [Sum.inr query]) =
            rightQueries remaining ++ [query]
          exact inductionHypothesis
      | inr current =>
          change current :: rightQueries (remaining ++ [Sum.inr query]) =
            current :: (rightQueries remaining ++ [query])
          exact congrArg (List.cons current) inductionHypothesis

theorem leftQueries_nonempty_of_last {A B : Interface.{u, v}}
    (history : History (Interface.parallel A B)) (query : A.query)
    (lastEqual : history.last = Sum.inl query) :
    leftQueries history.queries ≠ [] := by
  intro empty
  have member : query ∈ leftQueries history.queries := by
    rw [leftQueries, List.mem_filterMap]
    exact ⟨Sum.inl query,
      lastEqual ▸ List.getLast_mem history.nonempty, rfl⟩
  rw [empty] at member
  simp at member

theorem rightQueries_nonempty_of_last {A B : Interface.{u, v}}
    (history : History (Interface.parallel A B)) (query : B.query)
    (lastEqual : history.last = Sum.inr query) :
    rightQueries history.queries ≠ [] := by
  intro empty
  have member : query ∈ rightQueries history.queries := by
    rw [rightQueries, List.mem_filterMap]
    exact ⟨Sum.inr query,
      lastEqual ▸ List.getLast_mem history.nonempty, rfl⟩
  rw [empty] at member
  simp at member

/-- Complete attempted-query history projected to the left component. -/
def leftHistory {A B : Interface.{u, v}}
    (history : History (Interface.parallel A B)) (query : A.query)
    (lastEqual : history.last = Sum.inl query) : History A where
  queries := leftQueries history.queries
  nonempty := leftQueries_nonempty_of_last history query lastEqual

/-- Complete attempted-query history projected to the right component. -/
def rightHistory {A B : Interface.{u, v}}
    (history : History (Interface.parallel A B)) (query : B.query)
    (lastEqual : history.last = Sum.inr query) : History B where
  queries := rightQueries history.queries
  nonempty := rightQueries_nonempty_of_last history query lastEqual

@[simp]
theorem last_leftHistory {A B : Interface.{u, v}}
    (history : History (Interface.parallel A B)) (query : A.query)
    (lastEqual : history.last = Sum.inl query) :
    (leftHistory history query lastEqual).last = query := by
  have decomposition :
      (show List (A.query ⊕ B.query) from history.queries).dropLast ++
          ([Sum.inl query] : List (A.query ⊕ B.query)) = history.queries := by
    rw [← lastEqual]
    exact List.dropLast_append_getLast history.nonempty
  have projectionEqual : leftQueries history.queries =
      leftQueries history.queries.dropLast ++ [query] := calc
    leftQueries history.queries =
        leftQueries
          ((show List (A.query ⊕ B.query) from history.queries).dropLast ++
            ([Sum.inl query] : List (A.query ⊕ B.query))) :=
      congrArg (leftQueries (A := A) (B := B)) decomposition.symm
    _ = leftQueries history.queries.dropLast ++ [query] := by
      exact leftQueries_append_inl history.queries.dropLast query
  let expected : History A :=
    ⟨leftQueries history.queries.dropLast ++ [query], by simp⟩
  have historyEqual : leftHistory history query lastEqual = expected := by
    apply History.ext
    exact projectionEqual
  rw [historyEqual]
  simp [History.last, expected]

@[simp]
theorem last_rightHistory {A B : Interface.{u, v}}
    (history : History (Interface.parallel A B)) (query : B.query)
    (lastEqual : history.last = Sum.inr query) :
    (rightHistory history query lastEqual).last = query := by
  have decomposition :
      (show List (A.query ⊕ B.query) from history.queries).dropLast ++
          ([Sum.inr query] : List (A.query ⊕ B.query)) = history.queries := by
    rw [← lastEqual]
    exact List.dropLast_append_getLast history.nonempty
  have projectionEqual : rightQueries history.queries =
      rightQueries history.queries.dropLast ++ [query] := calc
    rightQueries history.queries =
        rightQueries
          ((show List (A.query ⊕ B.query) from history.queries).dropLast ++
            ([Sum.inr query] : List (A.query ⊕ B.query))) :=
      congrArg (rightQueries (A := A) (B := B)) decomposition.symm
    _ = rightQueries history.queries.dropLast ++ [query] := by
      exact rightQueries_append_inr history.queries.dropLast query
  let expected : History B :=
    ⟨rightQueries history.queries.dropLast ++ [query], by simp⟩
  have historyEqual : rightHistory history query lastEqual = expected := by
    apply History.ext
    exact projectionEqual
  rw [historyEqual]
  simp [History.last, expected]

/-- Evaluate the left component in the fibre selected by the final query. -/
def leftAnswer {A B : Interface.{u, v}} (system : DDS A)
    (history : History (Interface.parallel A B)) (query : A.query)
    (lastEqual : history.last = Sum.inl query) : Option (A.answer query) :=
  cast (congrArg (fun selected => Option (A.answer selected))
    (last_leftHistory history query lastEqual))
    (system (leftHistory history query lastEqual))

/-- Evaluate the right component in the fibre selected by the final query. -/
def rightAnswer {A B : Interface.{u, v}} (system : DDS B)
    (history : History (Interface.parallel A B)) (query : B.query)
    (lastEqual : history.last = Sum.inr query) : Option (B.answer query) :=
  cast (congrArg (fun selected => Option (B.answer selected))
    (last_rightHistory history query lastEqual))
    (system (rightHistory history query lastEqual))

/-- Ordered parallel of deterministic discrete systems. -/
def parallel {A B : Interface.{u, v}} (left : DDS A) (right : DDS B) :
    DDS (Interface.parallel A B) :=
  fun history =>
    match lastEqual : history.last with
    | Sum.inl query =>
        leftAnswer left history query lastEqual
    | Sum.inr query =>
        rightAnswer right history query lastEqual

theorem cast_dependent_sum_left {A B : Interface.{u, v}}
    {P : (Interface.parallel A B).query → Sort*}
    (selected : (Interface.parallel A B).query)
    (left : ∀ query, selected = Sum.inl query → P (Sum.inl query))
    (right : ∀ query, selected = Sum.inr query → P (Sum.inr query))
    (query : A.query) (equal : selected = Sum.inl query) :
    cast (congrArg P equal)
        (@DDS.parallel.match_1 A B P selected left right) =
      left query equal := by
  subst selected
  have reduction := DDS.parallel.match_1.eq_1
    (motive := P) query left right
  rw [reduction, cast_eq]

theorem cast_dependent_sum_right {A B : Interface.{u, v}}
    {P : (Interface.parallel A B).query → Sort*}
    (selected : (Interface.parallel A B).query)
    (left : ∀ query, selected = Sum.inl query → P (Sum.inl query))
    (right : ∀ query, selected = Sum.inr query → P (Sum.inr query))
    (query : B.query) (equal : selected = Sum.inr query) :
    cast (congrArg P equal)
        (@DDS.parallel.match_1 A B P selected left right) =
      right query equal := by
  subst selected
  have reduction := DDS.parallel.match_1.eq_2
    (motive := P) query left right
  rw [reduction, cast_eq]

/-- Exact evaluation equation for the left component of ordered parallel. -/
theorem parallel_apply_left {A B : Interface.{u, v}}
    (left : DDS A) (right : DDS B)
    (history : History (Interface.parallel A B)) (query : A.query)
    (lastEqual : history.last = Sum.inl query) :
    cast (congrArg (fun selected =>
      Option ((Interface.parallel A B).answer selected)) lastEqual)
        (parallel left right history) =
      leftAnswer left history query lastEqual := by
  unfold parallel
  exact cast_dependent_sum_left
    (P := fun selected =>
      Option ((Interface.parallel A B).answer selected)) history.last
    (fun query equal => leftAnswer left history query equal)
    (fun query equal => rightAnswer right history query equal)
    query lastEqual

/-- Exact evaluation equation for the right component of ordered parallel. -/
theorem parallel_apply_right {A B : Interface.{u, v}}
    (left : DDS A) (right : DDS B)
    (history : History (Interface.parallel A B)) (query : B.query)
    (lastEqual : history.last = Sum.inr query) :
    cast (congrArg (fun selected =>
      Option ((Interface.parallel A B).answer selected)) lastEqual)
        (parallel left right history) =
      rightAnswer right history query lastEqual := by
  unfold parallel
  exact cast_dependent_sum_right
    (P := fun selected =>
      Option ((Interface.parallel A B).answer selected)) history.last
    (fun query equal => leftAnswer left history query equal)
    (fun query equal => rightAnswer right history query equal)
    query lastEqual

theorem pack_parallel_left {A B : Interface.{u, v}}
    (left : DDS A) (right : DDS B)
    (history : History (Interface.parallel A B)) (query : A.query)
    (lastEqual : history.last = Sum.inl query) :
    pack (parallel left right) history =
      (⟨Sum.inl query, leftAnswer left history query lastEqual⟩ :
        PackedAnswer (Interface.parallel A B)) := by
  apply Sigma.ext lastEqual
  exact (cast_heq (congrArg (fun selected =>
      Option ((Interface.parallel A B).answer selected)) lastEqual)
      (parallel left right history)).symm.trans
    (heq_of_eq (parallel_apply_left left right history query lastEqual))

theorem pack_parallel_right {A B : Interface.{u, v}}
    (left : DDS A) (right : DDS B)
    (history : History (Interface.parallel A B)) (query : B.query)
    (lastEqual : history.last = Sum.inr query) :
    pack (parallel left right) history =
      (⟨Sum.inr query, rightAnswer right history query lastEqual⟩ :
        PackedAnswer (Interface.parallel A B)) := by
  apply Sigma.ext lastEqual
  exact (cast_heq (congrArg (fun selected =>
      Option ((Interface.parallel A B).answer selected)) lastEqual)
      (parallel left right history)).symm.trans
    (heq_of_eq (parallel_apply_right left right history query lastEqual))

theorem leftQueries_map_inl {A B : Interface.{u, v}}
    (queries : List A.query) :
    leftQueries
        (queries.map (Sum.inl : A.query → A.query ⊕ B.query)) =
      queries := by
  induction queries with
  | nil => rfl
  | cons query remaining inductionHypothesis =>
      change query :: leftQueries
          (remaining.map (Sum.inl : A.query → A.query ⊕ B.query)) =
        query :: remaining
      exact congrArg (List.cons query) inductionHypothesis

theorem rightQueries_map_inr {A B : Interface.{u, v}}
    (queries : List B.query) :
    rightQueries
        (queries.map (Sum.inr : B.query → A.query ⊕ B.query)) =
      queries := by
  induction queries with
  | nil => rfl
  | cons query remaining inductionHypothesis =>
      change query :: rightQueries
          (remaining.map (Sum.inr : B.query → A.query ⊕ B.query)) =
        query :: remaining
      exact congrArg (List.cons query) inductionHypothesis

theorem leftHistory_map_inl {A B : Interface.{u, v}}
    (history : History A) :
    leftHistory
        (History.map (B := Interface.parallel A B) Sum.inl history)
        history.last
        (History.last_map (B := Interface.parallel A B) Sum.inl history) =
      history := by
  apply History.ext
  exact leftQueries_map_inl history.queries

theorem rightHistory_map_inr {A B : Interface.{u, v}}
    (history : History B) :
    rightHistory
        (History.map (B := Interface.parallel A B) Sum.inr history)
        history.last
        (History.last_map (B := Interface.parallel A B) Sum.inr history) =
      history := by
  apply History.ext
  exact rightQueries_map_inr history.queries

theorem apply_heq_of_history_eq {A : Interface.{u, v}}
    (system : DDS A) {left right : History A} (equal : left = right) :
    system left ≍ system right := by
  subst right
  rfl

theorem leftAnswer_map_inl {A B : Interface.{u, v}}
    (system : DDS A) (history : History A) :
    leftAnswer system
        (History.map (B := Interface.parallel A B) Sum.inl history)
        history.last
        (History.last_map (B := Interface.parallel A B) Sum.inl history) =
      system history := by
  unfold leftAnswer
  apply eq_of_heq
  exact (cast_heq _ _).trans
    (apply_heq_of_history_eq system
      (leftHistory_map_inl (B := B) history))

theorem rightAnswer_map_inr {A B : Interface.{u, v}}
    (system : DDS B) (history : History B) :
    rightAnswer system
        (History.map (B := Interface.parallel A B) Sum.inr history)
        history.last
        (History.last_map (B := Interface.parallel A B) Sum.inr history) =
      system history := by
  unfold rightAnswer
  apply eq_of_heq
  exact (cast_heq _ _).trans
    (apply_heq_of_history_eq system
      (rightHistory_map_inr (A := A) history))

/-- The unique DDS on the empty interface. -/
def empty : DDS Interface.empty :=
  fun history => PEmpty.elim history.last

/-- Empty is the left unit of ordered parallel after interface relabeling. -/
@[simp]
theorem relabel_parallel_empty_left {A : Interface.{u, v}}
    (system : DDS A) :
    relabel (Interface.Equiv.parallelEmptyLeft A)
        (parallel empty system) = system := by
  apply ext
  intro history
  apply pack_injective history
  let source := History.map
    (Interface.Equiv.parallelEmptyLeft A).queries.symm history
  have sourceEqual : source =
      History.map (B := Interface.parallel Interface.empty A)
        Sum.inr history := by
    rfl
  have sourceLast : source.last = Sum.inr history.last := by
    exact congrArg History.last sourceEqual |>.trans
      (History.last_map (B := Interface.parallel Interface.empty A)
        Sum.inr history)
  calc
    pack (relabel (Interface.Equiv.parallelEmptyLeft A)
        (parallel empty system)) history =
        mapPackedAnswer (Interface.Equiv.parallelEmptyLeft A)
          (pack (parallel empty system) source) :=
      pack_relabel (Interface.Equiv.parallelEmptyLeft A)
        (parallel empty system) history
    _ = mapPackedAnswer (Interface.Equiv.parallelEmptyLeft A)
          ⟨Sum.inr history.last,
            rightAnswer system source history.last sourceLast⟩ := by
      rw [pack_parallel_right empty system source history.last sourceLast]
    _ = pack system history := by
      have answerEqual :
          rightAnswer system source history.last sourceLast =
            system history := by
        subst source
        exact rightAnswer_map_inr (A := Interface.empty) system history
      rw [answerEqual]
      unfold mapPackedAnswer pack
      cases system history <;> rfl

/-- Empty is the right unit of ordered parallel after interface relabeling. -/
@[simp]
theorem relabel_parallel_empty_right {A : Interface.{u, v}}
    (system : DDS A) :
    relabel (Interface.Equiv.parallelEmptyRight A)
        (parallel system empty) = system := by
  apply ext
  intro history
  apply pack_injective history
  let source := History.map
    (Interface.Equiv.parallelEmptyRight A).queries.symm history
  have sourceEqual : source =
      History.map (B := Interface.parallel A Interface.empty)
        Sum.inl history := by
    rfl
  have sourceLast : source.last = Sum.inl history.last := by
    exact congrArg History.last sourceEqual |>.trans
      (History.last_map (B := Interface.parallel A Interface.empty)
        Sum.inl history)
  calc
    pack (relabel (Interface.Equiv.parallelEmptyRight A)
        (parallel system empty)) history =
        mapPackedAnswer (Interface.Equiv.parallelEmptyRight A)
          (pack (parallel system empty) source) :=
      pack_relabel (Interface.Equiv.parallelEmptyRight A)
        (parallel system empty) history
    _ = mapPackedAnswer (Interface.Equiv.parallelEmptyRight A)
          ⟨Sum.inl history.last,
            leftAnswer system source history.last sourceLast⟩ := by
      rw [pack_parallel_left system empty source history.last sourceLast]
    _ = pack system history := by
      have answerEqual :
          leftAnswer system source history.last sourceLast =
            system history := by
        subst source
        exact leftAnswer_map_inl (B := Interface.empty) system history
      rw [answerEqual]
      unfold mapPackedAnswer pack
      cases system history <;> rfl

theorem assoc_left_left_queries {A B C : Interface.{u, v}}
    (queries : List (A.query ⊕ (B.query ⊕ C.query))) :
    leftQueries (A := A) (B := B)
        (leftQueries (A := Interface.parallel A B) (B := C)
          (queries.map
            (Interface.Equiv.parallelAssoc A B C).queries.symm)) =
      leftQueries (A := A) (B := Interface.parallel B C) queries := by
  induction queries with
  | nil => rfl
  | cons tagged remaining inductionHypothesis =>
      rcases tagged with query | tagged
      · change query :: leftQueries (A := A) (B := B)
            (leftQueries (A := Interface.parallel A B) (B := C)
              (remaining.map
                (Interface.Equiv.parallelAssoc A B C).queries.symm)) =
          query :: leftQueries (A := A) (B := Interface.parallel B C)
            remaining
        exact congrArg (List.cons query) inductionHypothesis
      · rcases tagged with query | query
        · exact inductionHypothesis
        · exact inductionHypothesis

theorem assoc_left_right_queries {A B C : Interface.{u, v}}
    (queries : List (A.query ⊕ (B.query ⊕ C.query))) :
    rightQueries (A := A) (B := B)
        (leftQueries (A := Interface.parallel A B) (B := C)
          (queries.map
            (Interface.Equiv.parallelAssoc A B C).queries.symm)) =
      leftQueries (A := B) (B := C)
        (rightQueries (A := A) (B := Interface.parallel B C) queries) := by
  induction queries with
  | nil => rfl
  | cons tagged remaining inductionHypothesis =>
      rcases tagged with query | tagged
      · exact inductionHypothesis
      · rcases tagged with query | query
        · change query :: rightQueries (A := A) (B := B)
              (leftQueries (A := Interface.parallel A B) (B := C)
                (remaining.map
                  (Interface.Equiv.parallelAssoc A B C).queries.symm)) =
            query :: leftQueries (A := B) (B := C)
              (rightQueries (A := A) (B := Interface.parallel B C)
                remaining)
          exact congrArg (List.cons query) inductionHypothesis
        · exact inductionHypothesis

theorem assoc_right_queries {A B C : Interface.{u, v}}
    (queries : List (A.query ⊕ (B.query ⊕ C.query))) :
    rightQueries (A := Interface.parallel A B) (B := C)
        (queries.map
          (Interface.Equiv.parallelAssoc A B C).queries.symm) =
      rightQueries (A := B) (B := C)
        (rightQueries (A := A) (B := Interface.parallel B C) queries) := by
  induction queries with
  | nil => rfl
  | cons tagged remaining inductionHypothesis =>
      rcases tagged with query | tagged
      · exact inductionHypothesis
      · rcases tagged with query | query
        · exact inductionHypothesis
        · change query :: rightQueries
              (remaining.map
                (Interface.Equiv.parallelAssoc A B C).queries.symm) =
            query :: rightQueries (rightQueries remaining)
          exact congrArg (List.cons query) inductionHypothesis

theorem nested_left_left {A B C : Interface.{u, v}}
    (first : DDS A) (second : DDS B)
    (history : History (Interface.parallel (Interface.parallel A B) C))
    (query : A.query) (lastEqual : history.last = Sum.inl (Sum.inl query)) :
    leftAnswer (parallel first second) history (Sum.inl query) lastEqual ≍
      first (leftHistory
        (leftHistory history (Sum.inl query) lastEqual) query
        (last_leftHistory history (Sum.inl query) lastEqual)) := by
  let innerHistory := leftHistory history (Sum.inl query) lastEqual
  have innerLast : innerHistory.last = Sum.inl query :=
    last_leftHistory history (Sum.inl query) lastEqual
  unfold leftAnswer
  refine (cast_heq _ _).trans ?_
  have evaluated := parallel_apply_left first second innerHistory query innerLast
  refine ((cast_heq _ _).symm.trans (heq_of_eq evaluated)).trans ?_
  unfold leftAnswer
  exact cast_heq _ _

theorem nested_left_right {A B C : Interface.{u, v}}
    (first : DDS A) (second : DDS B)
    (history : History (Interface.parallel (Interface.parallel A B) C))
    (query : B.query) (lastEqual : history.last = Sum.inl (Sum.inr query)) :
    leftAnswer (parallel first second) history (Sum.inr query) lastEqual ≍
      second (rightHistory
        (leftHistory history (Sum.inr query) lastEqual) query
        (last_leftHistory history (Sum.inr query) lastEqual)) := by
  let innerHistory := leftHistory history (Sum.inr query) lastEqual
  have innerLast : innerHistory.last = Sum.inr query :=
    last_leftHistory history (Sum.inr query) lastEqual
  unfold leftAnswer
  refine (cast_heq _ _).trans ?_
  have evaluated := parallel_apply_right first second innerHistory query innerLast
  refine ((cast_heq _ _).symm.trans (heq_of_eq evaluated)).trans ?_
  unfold rightAnswer
  exact cast_heq _ _

theorem nested_right_left {A B C : Interface.{u, v}}
    (second : DDS B) (third : DDS C)
    (history : History (Interface.parallel A (Interface.parallel B C)))
    (query : B.query) (lastEqual : history.last = Sum.inr (Sum.inl query)) :
    rightAnswer (parallel second third) history (Sum.inl query) lastEqual ≍
      second (leftHistory
        (rightHistory history (Sum.inl query) lastEqual) query
        (last_rightHistory history (Sum.inl query) lastEqual)) := by
  let innerHistory := rightHistory history (Sum.inl query) lastEqual
  have innerLast : innerHistory.last = Sum.inl query :=
    last_rightHistory history (Sum.inl query) lastEqual
  unfold rightAnswer
  refine (cast_heq _ _).trans ?_
  have evaluated := parallel_apply_left second third innerHistory query innerLast
  refine ((cast_heq _ _).symm.trans (heq_of_eq evaluated)).trans ?_
  unfold leftAnswer
  exact cast_heq _ _

theorem nested_right_right {A B C : Interface.{u, v}}
    (second : DDS B) (third : DDS C)
    (history : History (Interface.parallel A (Interface.parallel B C)))
    (query : C.query) (lastEqual : history.last = Sum.inr (Sum.inr query)) :
    rightAnswer (parallel second third) history (Sum.inr query) lastEqual ≍
      third (rightHistory
        (rightHistory history (Sum.inr query) lastEqual) query
        (last_rightHistory history (Sum.inr query) lastEqual)) := by
  let innerHistory := rightHistory history (Sum.inr query) lastEqual
  have innerLast : innerHistory.last = Sum.inr query :=
    last_rightHistory history (Sum.inr query) lastEqual
  unfold rightAnswer
  refine (cast_heq _ _).trans ?_
  have evaluated := parallel_apply_right second third innerHistory query innerLast
  refine ((cast_heq _ _).symm.trans (heq_of_eq evaluated)).trans ?_
  unfold rightAnswer
  exact cast_heq _ _

theorem map_assoc_left {A B C : Interface.{u, v}}
    (query : A.query)
    (left : Option (A.answer query)) (right : Option (A.answer query))
    (equal : left ≍ right) :
    mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
        ⟨Sum.inl (Sum.inl query), left⟩ =
      (⟨Sum.inl query, right⟩ :
        PackedAnswer (Interface.parallel A (Interface.parallel B C))) := by
  have valueEqual : left = right := eq_of_heq equal
  subst right
  cases left <;> rfl

theorem map_assoc_middle {A B C : Interface.{u, v}}
    (query : B.query)
    (left : Option (B.answer query)) (right : Option (B.answer query))
    (equal : left ≍ right) :
    mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
        ⟨Sum.inl (Sum.inr query), left⟩ =
      (⟨Sum.inr (Sum.inl query), right⟩ :
        PackedAnswer (Interface.parallel A (Interface.parallel B C))) := by
  have valueEqual : left = right := eq_of_heq equal
  subst right
  cases left <;> rfl

theorem map_assoc_right {A B C : Interface.{u, v}}
    (query : C.query)
    (left : Option (C.answer query)) (right : Option (C.answer query))
    (equal : left ≍ right) :
    mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
        ⟨Sum.inr query, left⟩ =
      (⟨Sum.inr (Sum.inr query), right⟩ :
        PackedAnswer (Interface.parallel A (Interface.parallel B C))) := by
  have valueEqual : left = right := eq_of_heq equal
  subst right
  cases left <;> rfl

/-- Ordered parallel is associative after canonical interface reassociation. -/
theorem relabel_parallel_assoc {A B C : Interface.{u, v}}
    (first : DDS A) (second : DDS B) (third : DDS C) :
    relabel (Interface.Equiv.parallelAssoc A B C)
        (parallel (parallel first second) third) =
      parallel first (parallel second third) := by
  apply ext
  intro history
  apply pack_injective history
  change pack
      (relabel (Interface.Equiv.parallelAssoc A B C)
        (parallel (parallel first second) third)) history =
    pack (parallel first (parallel second third)) history
  let source := History.map
    (Interface.Equiv.parallelAssoc A B C).queries.symm history
  rw [pack_relabel]
  cases lastEqual : history.last with
  | inl query =>
      have sourceLast : source.last = Sum.inl (Sum.inl query) := by
        simp only [source, History.last_map, lastEqual]
        rfl
      have outerPacked := pack_parallel_left
        (parallel first second) third source (Sum.inl query) sourceLast
      have targetPacked := pack_parallel_left
        first (parallel second third) history query lastEqual
      let sourceAB := leftHistory source (Sum.inl query) sourceLast
      let sourceA := leftHistory sourceAB query
        (last_leftHistory source (Sum.inl query) sourceLast)
      let targetA := leftHistory history query lastEqual
      have componentHistoryEqual : sourceA = targetA := by
        apply History.ext
        exact assoc_left_left_queries history.queries
      have answerEqual :
          leftAnswer (parallel first second) source (Sum.inl query)
              sourceLast ≍
            leftAnswer first history query lastEqual := by
        refine (nested_left_left first second source query sourceLast).trans ?_
        refine (apply_heq_of_history_eq first componentHistoryEqual).trans ?_
        unfold targetA leftAnswer
        exact (cast_heq _ _).symm
      calc
        mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
            (pack (parallel (parallel first second) third) source) =
            mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
              ⟨Sum.inl (Sum.inl query),
                leftAnswer (parallel first second) source
                  (Sum.inl query) sourceLast⟩ :=
          congrArg (mapPackedAnswer
            (Interface.Equiv.parallelAssoc A B C)) outerPacked
        _ = ⟨Sum.inl query,
              leftAnswer first history query lastEqual⟩ :=
          map_assoc_left query _ _ answerEqual
        _ = pack (parallel first (parallel second third)) history :=
          targetPacked.symm
  | inr tagged =>
      cases tagged with
      | inl query =>
          have sourceLast : source.last = Sum.inl (Sum.inr query) := by
            simp only [source, History.last_map, lastEqual]
            rfl
          have outerPacked := pack_parallel_left
            (parallel first second) third source (Sum.inr query) sourceLast
          have targetPacked := pack_parallel_right
            first (parallel second third) history (Sum.inl query) lastEqual
          let sourceAB := leftHistory source (Sum.inr query) sourceLast
          let sourceB := rightHistory sourceAB query
            (last_leftHistory source (Sum.inr query) sourceLast)
          let targetBC := rightHistory history (Sum.inl query) lastEqual
          let targetB := leftHistory targetBC query
            (last_rightHistory history (Sum.inl query) lastEqual)
          have componentHistoryEqual : sourceB = targetB := by
            apply History.ext
            exact assoc_left_right_queries history.queries
          have answerEqual :
              leftAnswer (parallel first second) source (Sum.inr query)
                  sourceLast ≍
                rightAnswer (parallel second third) history
                  (Sum.inl query) lastEqual := by
            refine (nested_left_right first second source query
              sourceLast).trans ?_
            refine (apply_heq_of_history_eq second
              componentHistoryEqual).trans ?_
            exact (nested_right_left second third history query
              lastEqual).symm
          calc
            mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
                (pack (parallel (parallel first second) third) source) =
                mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
                  ⟨Sum.inl (Sum.inr query),
                    leftAnswer (parallel first second) source
                      (Sum.inr query) sourceLast⟩ :=
              congrArg (mapPackedAnswer
                (Interface.Equiv.parallelAssoc A B C)) outerPacked
            _ = ⟨Sum.inr (Sum.inl query),
                  rightAnswer (parallel second third) history
                    (Sum.inl query) lastEqual⟩ :=
              map_assoc_middle query _ _ answerEqual
            _ = pack (parallel first (parallel second third)) history :=
              targetPacked.symm

      | inr query =>
          have sourceLast : source.last = Sum.inr query := by
            simp only [source, History.last_map, lastEqual]
            rfl
          have outerPacked := pack_parallel_right
            (parallel first second) third source query sourceLast
          have targetPacked := pack_parallel_right
            first (parallel second third) history (Sum.inr query) lastEqual
          let sourceC := rightHistory source query sourceLast
          let targetBC := rightHistory history (Sum.inr query) lastEqual
          let targetC := rightHistory targetBC query
            (last_rightHistory history (Sum.inr query) lastEqual)
          have componentHistoryEqual : sourceC = targetC := by
            apply History.ext
            exact assoc_right_queries history.queries
          have answerEqual :
              rightAnswer third source query sourceLast ≍
                rightAnswer (parallel second third) history
                  (Sum.inr query) lastEqual := by
            unfold rightAnswer
            refine (cast_heq _ _).trans ?_
            refine (apply_heq_of_history_eq third
              componentHistoryEqual).trans ?_
            exact (nested_right_right second third history query
              lastEqual).symm
          calc
            mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
                (pack (parallel (parallel first second) third) source) =
                mapPackedAnswer (Interface.Equiv.parallelAssoc A B C)
                  ⟨Sum.inr query,
                    rightAnswer third source query sourceLast⟩ :=
              congrArg (mapPackedAnswer
                (Interface.Equiv.parallelAssoc A B C)) outerPacked
            _ = ⟨Sum.inr (Sum.inr query),
                  rightAnswer (parallel second third) history
                    (Sum.inr query) lastEqual⟩ :=
              map_assoc_right query _ _ answerEqual
            _ = pack (parallel first (parallel second third)) history :=
              targetPacked.symm

end DDS

end RandomSystems.Ambient
