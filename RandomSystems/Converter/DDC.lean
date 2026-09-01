/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.DDS
import Mathlib.Data.PFun

set_option autoImplicit false

/-!
# Deterministic discrete converters at addressed interfaces

A converter is a partial function on complete received histories.  A received
history records every outer query and every inner reply in the answer fibre
selected by its query, while its outer
projection selects the answer fibre of a final response.  Canonicalization
restricts a raw graph to the exact alternating history tree that the graph
itself generates.

Maurer--Renner 2016 requires converter application and composition but leaves
the converter carrier abstract. Jost's Definition 2.2.2 and Liu--Maurer's
Definition 6 use probabilistic converters; the DDC below is their deterministic
function-graph specialization. Lanzenberger supplies the fixed-interface
DDS/PDS carrier, not this upper converter algebra.
-/

namespace RandomSystems.Ambient

universe u v w z

/-- One received inner reply, carrying the precise query that selected its
answer fibre. -/
abbrev DDC.History.InnerReply (B : Interface.{w, z}) :=
  Σ query : B.query, Option (B.answer query)

/-- Equality of packed replies at the same query is equality in its answer
fibre. -/
theorem DDC.History.reply_eq_of_packed_eq
    {A : Interface.{u, v}} {query : A.query}
    {left right : Option (A.answer query)}
    (equal : (⟨query, left⟩ : DDC.History.InnerReply A) = ⟨query, right⟩) :
    left = right := by
  cases equal
  rfl

namespace Interface.Equiv

/-- Relabel a possibly rejected answer while retaining the query that selects
its answer fibre. -/
def innerReply {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    DDC.History.InnerReply A ≃ DDC.History.InnerReply B :=
  _root_.Equiv.sigmaCongr equivalence.queries fun query =>
    _root_.Equiv.optionCongr (equivalence.answers query)

@[simp]
theorem innerReply_apply {A B : Interface.{u, v}}
    (equivalence : A.Equiv B) (query : A.query)
    (reply : Option (A.answer query)) :
    equivalence.innerReply ⟨query, reply⟩ =
      ⟨equivalence.queries query, reply.map (equivalence.answers query)⟩ := by
  rfl

end Interface.Equiv

/-- Inputs received by a converter are either outer queries or inner replies
in the answer fibre selected by their query. -/
abbrev DDC.History.Input (A : Interface.{u, v}) (B : Interface.{w, z}) :=
  A.query ⊕ DDC.History.InnerReply B

/-- A nonempty received history together with its nonempty outer-query
projection.  The stored equality makes the currently selected outer answer
fibre available without any cast or default value. -/
structure DDC.History (A : Interface.{u, v}) (B : Interface.{w, z}) where
  inputs : _root_.RandomSystems.Ambient.History
    (Interface.single (DDC.History.Input A B) Unit)
  outer : _root_.RandomSystems.Ambient.History A
  projects : inputs.queries.filterMap (fun
      | Sum.inl query => some query
      | Sum.inr _ => none) = outer.queries

namespace DDC.History

/-- The first outer query starts a received history. -/
def singleton {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query) : DDC.History A B where
  inputs := _root_.RandomSystems.Ambient.History.singleton (Sum.inl query)
  outer := _root_.RandomSystems.Ambient.History.singleton query
  projects := rfl

/-- Append a reply to the exact inner query that selects its answer fibre. -/
def snocInner {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : B.query)
    (reply : Option (B.answer query)) : DDC.History A B where
  inputs := _root_.RandomSystems.Ambient.History.snoc history.inputs (Sum.inr ⟨query, reply⟩)
  outer := history.outer
  projects := by simp [_root_.RandomSystems.Ambient.History.snoc, history.projects]

/-- Append the next attempted outer query. -/
def snocOuter {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : A.query) :
    DDC.History A B where
  inputs := _root_.RandomSystems.Ambient.History.snoc history.inputs (Sum.inl query)
  outer := _root_.RandomSystems.Ambient.History.snoc history.outer query
  projects := by simp [_root_.RandomSystems.Ambient.History.snoc, history.projects]

/-- The most recent received input. -/
def lastInput {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) : DDC.History.Input A B :=
  _root_.RandomSystems.Ambient.History.last history.inputs

/-- The most recent attempted outer query. -/
def lastOuter {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) : A.query :=
  _root_.RandomSystems.Ambient.History.last history.outer

@[simp]
theorem lastInput_singleton {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query) :
    lastInput (singleton (B := B) query) = Sum.inl query :=
  _root_.RandomSystems.Ambient.History.last_singleton _

@[simp]
theorem lastOuter_singleton {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query) :
    lastOuter (singleton (B := B) query) = query :=
  _root_.RandomSystems.Ambient.History.last_singleton _

@[simp]
theorem lastInput_snocInner {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : B.query)
    (reply : Option (B.answer query)) :
    lastInput (snocInner history query reply) = Sum.inr ⟨query, reply⟩ :=
  _root_.RandomSystems.Ambient.History.last_snoc _ _

@[simp]
theorem lastOuter_snocInner {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : B.query)
    (reply : Option (B.answer query)) :
    lastOuter (snocInner history query reply) = lastOuter history :=
  rfl

/-- Number of consecutive received inner replies since the most recent outer
query. -/
def innerDepth {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) : Nat :=
  history.inputs.queries.foldl (fun depth input =>
    match input with
    | Sum.inl _ => 0
    | Sum.inr _ => depth + 1) 0

@[simp]
theorem innerDepth_singleton {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query) :
    innerDepth (DDC.History.singleton (B := B) query) = 0 :=
  rfl

@[simp]
theorem innerDepth_snocInner {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : B.query)
    (reply : Option (B.answer query)) :
    innerDepth (history.snocInner query reply) = innerDepth history + 1 := by
  simp [innerDepth, DDC.History.snocInner,
    _root_.RandomSystems.Ambient.History.snoc, List.foldl_append]

@[simp]
theorem innerDepth_snocOuter {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : A.query) :
    innerDepth (history.snocOuter query) = 0 := by
  simp [innerDepth, DDC.History.snocOuter,
    _root_.RandomSystems.Ambient.History.snoc, List.foldl_append]

@[simp]
theorem lastInput_snocOuter {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : A.query) :
    lastInput (snocOuter (B := B) history query) = Sum.inl query :=
  _root_.RandomSystems.Ambient.History.last_snoc _ _

@[simp]
theorem lastOuter_snocOuter {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (query : A.query) :
    lastOuter (snocOuter (B := B) history query) = query :=
  _root_.RandomSystems.Ambient.History.last_snoc _ _

end DDC.History

namespace DDC.History

@[ext]
theorem ext {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : DDC.History A B}
    (inputsEqual : left.inputs = right.inputs) : left = right := by
  cases left with
  | mk leftInputs leftOuter leftProjects =>
      cases right with
      | mk rightInputs rightOuter rightProjects =>
          dsimp at inputsEqual
          subst rightInputs
          have outerLists : leftOuter.queries = rightOuter.queries := by
            rw [← leftProjects, ← rightProjects]
          have outerEqual : leftOuter = rightOuter :=
            _root_.RandomSystems.Ambient.History.ext outerLists
          subst rightOuter
          rfl

def relabelInput {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) :
    DDC.History.Input A B ≃ DDC.History.Input C D :=
  _root_.Equiv.sumCongr outer.queries inner.innerReply

def relabel {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) : DDC.History C D where
  inputs := _root_.RandomSystems.Ambient.History.map (relabelInput outer inner) history.inputs
  outer := _root_.RandomSystems.Ambient.History.map outer.queries history.outer
  projects := by
    change (history.inputs.queries.map (relabelInput outer inner)).filterMap
        (fun input => match input with
          | Sum.inl query => some query
          | Sum.inr _ => none) =
      history.outer.queries.map outer.queries
    have mapFilter :
        (history.inputs.queries.map (relabelInput outer inner)).filterMap
            (fun input => match input with
              | Sum.inl query => some query
              | Sum.inr _ => none) =
          (history.inputs.queries.filterMap (fun input => match input with
              | Sum.inl query => some query
              | Sum.inr _ => none)).map outer.queries := by
      induction history.inputs.queries with
      | nil => rfl
      | cons input tail inductionHypothesis =>
          cases input with
          | inl query =>
              change outer.queries query ::
                  (tail.map (relabelInput outer inner)).filterMap
                    (fun input => match input with
                      | Sum.inl query => some query
                      | Sum.inr _ => none) =
                outer.queries query ::
                  (tail.filterMap (fun input => match input with
                    | Sum.inl query => some query
                    | Sum.inr _ => none)).map outer.queries
              rw [inductionHypothesis]
          | inr reply =>
              change (tail.map (relabelInput outer inner)).filterMap
                    (fun input => match input with
                      | Sum.inl query => some query
                      | Sum.inr _ => none) =
                (tail.filterMap (fun input => match input with
                  | Sum.inl query => some query
                  | Sum.inr _ => none)).map outer.queries
              exact inductionHypothesis
    rw [mapFilter]
    exact congrArg (List.map outer.queries) history.projects

def unrelabel {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History C D) : DDC.History A B where
  inputs := _root_.RandomSystems.Ambient.History.map (relabelInput outer inner).symm history.inputs
  outer := _root_.RandomSystems.Ambient.History.map outer.queries.symm history.outer
  projects := by
    have mapFilter :
        (history.inputs.queries.map (relabelInput outer inner).symm).filterMap
            (fun input => match input with
              | Sum.inl query => some query
              | Sum.inr _ => none) =
          (history.inputs.queries.filterMap (fun input => match input with
              | Sum.inl query => some query
              | Sum.inr _ => none)).map outer.queries.symm := by
      induction history.inputs.queries with
      | nil => rfl
      | cons input tail inductionHypothesis =>
          cases input with
          | inl query =>
              change outer.queries.symm query ::
                  (tail.map (relabelInput outer inner).symm).filterMap
                    (fun input => match input with
                      | Sum.inl query => some query
                      | Sum.inr _ => none) =
                outer.queries.symm query ::
                  (tail.filterMap (fun input => match input with
                    | Sum.inl query => some query
                    | Sum.inr _ => none)).map outer.queries.symm
              rw [inductionHypothesis]
          | inr reply =>
              change (tail.map (relabelInput outer inner).symm).filterMap
                    (fun input => match input with
                      | Sum.inl query => some query
                      | Sum.inr _ => none) =
                (tail.filterMap (fun input => match input with
                  | Sum.inl query => some query
                  | Sum.inr _ => none)).map outer.queries.symm
              exact inductionHypothesis
    change (history.inputs.queries.map (relabelInput outer inner).symm).filterMap
        (fun input => match input with
          | Sum.inl query => some query
          | Sum.inr _ => none) =
      history.outer.queries.map outer.queries.symm
    rw [mapFilter]
    exact congrArg (List.map outer.queries.symm) history.projects

@[simp]
theorem relabel_singleton {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (query : A.query) :
    relabel outer inner (singleton (B := B) query) =
      singleton (B := D) (outer.queries query) := by
  rfl

@[simp]
theorem relabel_snocOuter {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) (query : A.query) :
    relabel outer inner (history.snocOuter query) =
      (relabel outer inner history).snocOuter (outer.queries query) := by
  apply ext
  simp [relabel, relabelInput, DDC.History.snocOuter,
    _root_.RandomSystems.Ambient.History.map_snoc]

@[simp]
theorem relabel_snocInner {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) (query : B.query)
    (reply : Option (B.answer query)) :
    relabel outer inner (history.snocInner query reply) =
      (relabel outer inner history).snocInner (inner.queries query)
        (reply.map (inner.answers query)) := by
  apply ext
  change _root_.RandomSystems.Ambient.History.map
      (B := Interface.single (DDC.History.Input C D) Unit)
      (relabelInput outer inner)
      (_root_.RandomSystems.Ambient.History.snoc
        (A := Interface.single (DDC.History.Input A B) Unit) history.inputs
        (Sum.inr ⟨query, reply⟩)) =
    _root_.RandomSystems.Ambient.History.snoc
      (A := Interface.single (DDC.History.Input C D) Unit)
      (_root_.RandomSystems.Ambient.History.map
        (B := Interface.single (DDC.History.Input C D) Unit)
        (relabelInput outer inner) history.inputs)
      (Sum.inr ⟨inner.queries query,
        reply.map (inner.answers query)⟩ : DDC.History.Input C D)
  rw [_root_.RandomSystems.Ambient.History.map_snoc]
  change _root_.RandomSystems.Ambient.History.snoc
      (A := Interface.single (DDC.History.Input C D) Unit)
      (_root_.RandomSystems.Ambient.History.map
        (B := Interface.single (DDC.History.Input C D) Unit)
        (relabelInput outer inner) history.inputs)
      (Sum.inr (inner.innerReply ⟨query, reply⟩)) =
    _root_.RandomSystems.Ambient.History.snoc
      (A := Interface.single (DDC.History.Input C D) Unit)
      (_root_.RandomSystems.Ambient.History.map
        (B := Interface.single (DDC.History.Input C D) Unit)
        (relabelInput outer inner) history.inputs)
      (Sum.inr ⟨inner.queries query,
        reply.map (inner.answers query)⟩)
  rw [Interface.Equiv.innerReply_apply]

@[simp]
theorem lastOuter_relabel {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) :
    (relabel outer inner history).lastOuter =
      outer.queries history.lastOuter := by
  simp [relabel, DDC.History.lastOuter, _root_.RandomSystems.Ambient.History.last,
    _root_.RandomSystems.Ambient.History.map]

@[simp]
theorem lastInput_relabel {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) :
    (relabel outer inner history).lastInput =
      relabelInput outer inner history.lastInput := by
  simp [relabel, DDC.History.lastInput]

theorem unrelabel_relabel {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) :
    unrelabel outer inner (relabel outer inner history) = history := by
  apply ext
  apply _root_.RandomSystems.Ambient.History.ext
  change List.map (relabelInput outer inner).symm
      (List.map (relabelInput outer inner) history.inputs.queries) =
    history.inputs.queries
  simp

theorem relabel_unrelabel {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History C D) :
    relabel outer inner (unrelabel outer inner history) = history := by
  apply ext
  apply _root_.RandomSystems.Ambient.History.ext
  change List.map (relabelInput outer inner)
      (List.map (relabelInput outer inner).symm history.inputs.queries) =
    history.inputs.queries
  simp

/-- Relabeling is an equivalence of complete dependent received histories. -/
def relabelEquiv {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) :
    DDC.History A B ≃ DDC.History C D where
  toFun := relabel outer inner
  invFun := unrelabel outer inner
  left_inv := unrelabel_relabel outer inner
  right_inv := relabel_unrelabel outer inner

@[simp]
theorem relabel_refl
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) :
    relabel (.refl A) (.refl B) history = history := by
  apply DDC.History.ext
  apply _root_.RandomSystems.Ambient.History.ext
  change history.inputs.1.map
      (DDC.History.relabelInput (.refl A) (.refl B)) =
    history.inputs.1
  calc
    _ = history.inputs.1.map id := by
      apply List.map_congr_left
      intro input membership
      cases input with
      | inl query => rfl
      | inr reply =>
          rcases reply with ⟨query, reply⟩
          cases reply <;> rfl
    _ = history.inputs.1 := by simp

theorem relabel_trans
    {A C E : Interface.{u, v}} {B D F : Interface.{w, z}}
    (firstOuter : A.Equiv C) (firstInner : B.Equiv D)
    (secondOuter : C.Equiv E) (secondInner : D.Equiv F)
    (history : DDC.History A B) :
    relabel secondOuter secondInner
        (relabel firstOuter firstInner history) =
      relabel (firstOuter.trans secondOuter)
        (firstInner.trans secondInner) history := by
  apply DDC.History.ext
  apply _root_.RandomSystems.Ambient.History.ext
  change (history.inputs.1.map
      (DDC.History.relabelInput firstOuter firstInner)).map
        (DDC.History.relabelInput secondOuter secondInner) =
    history.inputs.1.map (DDC.History.relabelInput
      (firstOuter.trans secondOuter) (firstInner.trans secondInner))
  rw [List.map_map]
  apply List.map_congr_left
  intro input membership
  cases input with
  | inl query => rfl
  | inr reply =>
      rcases reply with ⟨query, reply⟩
      cases reply <;> rfl

end DDC.History

/-- A converter response at a received history: either an inner query or an
outer reply in the fibre selected by the latest outer query. -/
abbrev DDC.Response {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) :=
  B.query ⊕ Option (A.answer history.lastOuter)

/-- A raw dependent DDC graph.  Partiality is reserved for histories outside
the graph generated by the converter itself. -/
abbrev DDC.Raw (A : Interface.{u, v}) (B : Interface.{w, z}) :=
  (history : DDC.History A B) → Part (DDC.Response history)

namespace DDC.Raw

/-- The exact alternating dependent history tree generated by a raw graph. -/
inductive Admissible {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) : DDC.History A B → Prop
  | start (query : A.query) : Admissible raw (.singleton query)
  | afterInner {history : DDC.History A B} {query : B.query}
      (prior : Admissible raw history)
      (responds : Sum.inl query ∈ raw history)
      (reply : Option (B.answer query)) :
      Admissible raw (history.snocInner query reply)
  | afterOuter {history : DDC.History A B}
      (prior : Admissible raw history)
      {reply : Option (A.answer history.lastOuter)}
      (responds : Sum.inr reply ∈ raw history)
      (query : A.query) :
      Admissible raw (history.snocOuter query)

theorem Admissible.lastOuter_eq_of_lastInput_outer
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {raw : DDC.Raw A B} {history : DDC.History A B}
    (admissible : Admissible raw history) {query : A.query}
    (lastInput : history.lastInput = Sum.inl query) :
    history.lastOuter = query := by
  induction admissible with
  | start outerQuery => simpa using Sum.inl.inj lastInput
  | afterInner prior responds reply inductionHypothesis =>
      simp at lastInput
  | afterOuter prior responds outerQuery inductionHypothesis =>
      have equal : (Sum.inl outerQuery : DDC.History.Input A B) =
          Sum.inl query := by
        simpa using lastInput
      simpa using Sum.inl.inj equal

/-- One legal continuation after an inner query. -/
def InnerContinuation {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (after before : DDC.History A B) : Prop :=
  ∃ (query : B.query) (reply : Option (B.answer query)),
    Sum.inl query ∈ raw before ∧ after = before.snocInner query reply

/-- Jost, Definition 2.2.2 (printed p. 18): “There is a finite upper
bound on the number of consecutive outputs of the form `(y,I') ∈ X × I_in`.”
This is the deterministic function-graph specialization of that bound. -/
def HasFiniteInnerQueryBound {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) : Prop :=
  ∃ bound : Nat, ∀ history, Admissible raw history →
    DDC.History.innerDepth history ≤ bound

/--
Jost's Definition 2.2.2 (printed pp. 17--18) requires one uniform finite
upper bound on consecutive inner queries.  This well-founded Lean
generalization instead requires every concrete branch to be finite, without
requiring one bound shared by all branches.
-/
def BranchFinite {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) : Prop :=
  WellFounded (InnerContinuation raw)

/-- The graph is defined at every history it generates. -/
def Complete {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) : Prop :=
  ∀ history, Admissible raw history → (raw history).Dom

/-- Erase every value outside the exact dependent alternating tree. -/
def canonicalize {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) : DDC.Raw A B :=
  fun history =>
    { Dom := Admissible raw history ∧ (raw history).Dom
      get := fun defined => (raw history).get defined.2 }

theorem mem_canonicalize_iff {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (history : DDC.History A B)
    (response : DDC.Response history) :
    response ∈ canonicalize raw history ↔
      Admissible raw history ∧ response ∈ raw history := by
  constructor
  · rintro ⟨⟨admissible, defined⟩, equal⟩
    exact ⟨admissible, ⟨defined, equal⟩⟩
  · rintro ⟨admissible, defined, equal⟩
    exact ⟨⟨admissible, defined⟩, equal⟩

theorem admissible_canonicalize_iff
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (history : DDC.History A B) :
    Admissible (canonicalize raw) history ↔ Admissible raw history := by
  constructor
  · intro admissible
    induction admissible with
    | start query => exact .start query
    | afterInner prior responds reply inductionHypothesis =>
        exact .afterInner inductionHypothesis
          ((mem_canonicalize_iff raw _ _).mp responds).2 reply
    | afterOuter prior responds query inductionHypothesis =>
        exact .afterOuter inductionHypothesis
          ((mem_canonicalize_iff raw _ _).mp responds).2 query
  · intro admissible
    induction admissible with
    | start query => exact .start query
    | afterInner prior responds reply inductionHypothesis =>
        exact .afterInner inductionHypothesis
          ((mem_canonicalize_iff raw _ _).mpr ⟨prior, responds⟩) reply
    | afterOuter prior responds query inductionHypothesis =>
        exact .afterOuter inductionHypothesis
          ((mem_canonicalize_iff raw _ _).mpr ⟨prior, responds⟩) query

/-- Canonicalization preserves the existence and value of a finite uniform
bound on consecutive inner queries. -/
theorem hasFiniteInnerQueryBound_canonicalize_iff
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) :
    HasFiniteInnerQueryBound (canonicalize raw) ↔
      HasFiniteInnerQueryBound raw := by
  constructor <;> rintro ⟨bound, bounded⟩ <;> refine ⟨bound, ?_⟩
  · intro history admissible
    exact bounded history
      ((admissible_canonicalize_iff raw history).mpr admissible)
  · intro history admissible
    exact bounded history
      ((admissible_canonicalize_iff raw history).mp admissible)

theorem dom_canonicalize_iff
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (complete : Complete raw)
    (history : DDC.History A B) :
    (canonicalize raw history).Dom ↔ Admissible (canonicalize raw) history := by
  rw [admissible_canonicalize_iff]
  exact and_iff_left_of_imp (complete history)

/-- Jost's finite uniform inner-query bound implies branch-finiteness after
canonicalization. -/
theorem branchFinite_canonicalize_of_hasFiniteInnerQueryBound
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (complete : Complete raw)
    (bounded : HasFiniteInnerQueryBound raw) :
    BranchFinite (canonicalize raw) := by
  obtain ⟨bound, atMost⟩ := bounded
  let remaining := fun history : DDC.History A B =>
    bound - DDC.History.innerDepth history
  refine Subrelation.wf ?_ (measure remaining).wf
  intro after before continuation
  rcases continuation with ⟨query, reply, responds, rfl⟩
  have beforeAdmissible : Admissible (canonicalize raw) before :=
    (dom_canonicalize_iff raw complete before).mp responds.1
  have afterAdmissible :
      Admissible (canonicalize raw) (before.snocInner query reply) :=
    Admissible.afterInner beforeAdmissible responds reply
  have beforeBound := atMost before
    ((admissible_canonicalize_iff raw before).mp beforeAdmissible)
  have afterBound := atMost (before.snocInner query reply)
    ((admissible_canonicalize_iff raw _).mp afterAdmissible)
  change remaining (before.snocInner query reply) < remaining before
  dsimp only [remaining]
  rw [DDC.History.innerDepth_snocInner] at afterBound ⊢
  omega

end DDC.Raw

/-- A canonical exact-domain, branch-finite dependent converter. -/
structure DDC (A : Interface.{u, v}) (B : Interface.{w, z}) where
  toFun : DDC.Raw A B
  exactDomain : ∀ history,
    (toFun history).Dom ↔ DDC.Raw.Admissible toFun history
  branchFinite : DDC.Raw.BranchFinite toFun

namespace DDC

instance {A : Interface.{u, v}} {B : Interface.{w, z}} :
    CoeFun (DDC A B) (fun _ => DDC.Raw A B) := ⟨DDC.toFun⟩

/-- Canonicalize a complete branch-finite dependent raw graph. -/
def ofRaw {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (complete : DDC.Raw.Complete raw)
    (finite : DDC.Raw.BranchFinite raw) : DDC A B where
  toFun := DDC.Raw.canonicalize raw
  exactDomain := DDC.Raw.dom_canonicalize_iff raw complete
  branchFinite := by
    exact Subrelation.wf (fun {_ _} continuation => by
      rcases continuation with ⟨query, reply, responds, equal⟩
      exact ⟨query, reply,
        (DDC.Raw.mem_canonicalize_iff raw _ _).mp responds |>.2, equal⟩) finite

/-- Canonicalize a complete raw converter satisfying Jost's finite uniform
inner-query bound. This is a constructor into the ambient branch-finite DDC
carrier, not a second converter type. -/
def ofRawWithFiniteInnerQueryBound
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (raw : DDC.Raw A B) (complete : DDC.Raw.Complete raw)
    (bounded : DDC.Raw.HasFiniteInnerQueryBound raw) : DDC A B where
  toFun := DDC.Raw.canonicalize raw
  exactDomain := DDC.Raw.dom_canonicalize_iff raw complete
  branchFinite :=
    DDC.Raw.branchFinite_canonicalize_of_hasFiniteInnerQueryBound
      raw complete bounded

/-- Every admissible dependent received history has one response. -/
theorem exists_unique_response {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (history : DDC.History A B)
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    ∃! response : DDC.Response history, response ∈ converter history := by
  have defined := (converter.exactDomain history).mpr admissible
  refine ⟨(converter history).get defined, ⟨defined, rfl⟩, ?_⟩
  intro response membership
  exact Part.mem_unique membership ⟨defined, rfl⟩

/-- The unique response at an admissible received history. -/
def response {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (history : DDC.History A B)
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    DDC.Response history :=
  (converter history).get ((converter.exactDomain history).mpr admissible)

/-- The selected response belongs to the converter's partial function. -/
theorem response_mem {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (history : DDC.History A B)
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    converter.response history admissible ∈ converter history :=
  ⟨(converter.exactDomain history).mpr admissible, rfl⟩

/-- Equality is equality of the complete canonical dependent graph. -/
@[ext]
theorem ext {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : DDC A B}
    (equal : ∀ history response,
      response ∈ left history ↔ response ∈ right history) :
    left = right := by
  have functionEqual : left.toFun = right.toFun := by
    funext history
    apply Part.ext
    exact equal history
  cases left
  cases right
  cases functionEqual
  rfl


/-- The raw forwarding graph.  The equality test is only relevant off the
canonical tree: on a generated history, the reply query is exactly the latest
outer query. -/
noncomputable def Internal.forwardingRaw (A : Interface.{u, v}) : DDC.Raw A A :=
  by
  classical
  exact fun history =>
    match input : history.lastInput with
    | Sum.inl query => Part.some (Sum.inl query)
    | Sum.inr ⟨query, reply⟩ =>
        if equal : query = history.lastOuter then
          Part.some (Sum.inr (equal ▸ reply))
        else
          Part.none

@[simp]
theorem Internal.rawForwarding_singleton (A : Interface.{u, v})
    (query : A.query) :
    Internal.forwardingRaw A (DDC.History.singleton query) =
      Part.some (Sum.inl query) := by
  unfold Internal.forwardingRaw
  rw [DDC.History.lastInput_singleton]

@[simp]
theorem Internal.rawForwarding_snocOuter (A : Interface.{u, v})
    (history : DDC.History A A) (query : A.query) :
    Internal.forwardingRaw A (history.snocOuter query) =
      Part.some (Sum.inl query) := by
  unfold Internal.forwardingRaw
  rw [DDC.History.lastInput_snocOuter]

theorem Internal.rawForwarding_snocInner_of_eq (A : Interface.{u, v})
    (history : DDC.History A A) (query : A.query)
    (reply : Option (A.answer query))
    (equal : query = history.lastOuter) :
    Internal.forwardingRaw A (history.snocInner query reply) =
      Part.some (Sum.inr (equal ▸ reply)) := by
  classical
  subst query
  unfold Internal.forwardingRaw
  rw [DDC.History.lastInput_snocInner]
  simp
  rfl

theorem Internal.rawForwarding_snocInner_of_ne (A : Interface.{u, v})
    (history : DDC.History A A) (query : A.query)
    (reply : Option (A.answer query))
    (different : query ≠ history.lastOuter) :
    Internal.forwardingRaw A (history.snocInner query reply) = Part.none := by
  classical
  unfold Internal.forwardingRaw
  rw [DDC.History.lastInput_snocInner]
  simp [different]

theorem Internal.not_mem_rawForwarding_of_lastInput_inner
    (A : Interface.{u, v}) (history : DDC.History A A)
    (inner : DDC.History.InnerReply A) (equal : history.lastInput = Sum.inr inner)
    (query : A.query) :
    ¬ Sum.inl query ∈ Internal.forwardingRaw A history := by
  classical
  rcases inner with ⟨innerQuery, reply⟩
  change ¬ Sum.inl query ∈
    (match input : history.lastInput with
    | Sum.inl outerQuery => Part.some (Sum.inl outerQuery)
    | Sum.inr ⟨innerQuery, reply⟩ =>
        if same : innerQuery = history.lastOuter then
          Part.some (Sum.inr (same ▸ reply))
        else Part.none)
  rw [equal]
  by_cases same : innerQuery = history.lastOuter
  · simp [same]
  · simp [same]

theorem Internal.rawForwarding_complete (A : Interface.{u, v}) :
    DDC.Raw.Complete (Internal.forwardingRaw A) := by
  classical
  intro history admissible
  induction admissible with
  | start query => simp
  | @afterInner history query prior responds reply inductionHypothesis =>
      cases prior with
      | start outerQuery =>
          have equal : query = outerQuery := by
            simpa using responds
          rw [Internal.rawForwarding_snocInner_of_eq A _ _ _ equal]
          simp
      | @afterInner previous previousQuery previousPrior previousResponds
          previousReply =>
          exact False.elim
            ((Internal.not_mem_rawForwarding_of_lastInput_inner A _
              ⟨previousQuery, previousReply⟩ (by simp) query) responds)
      | @afterOuter previous previousPrior previousReply previousResponds
          outerQuery =>
          have equal : query = outerQuery := by
            simpa using responds
          rw [Internal.rawForwarding_snocInner_of_eq A _ _ _ (by simpa using equal)]
          simp
  | afterOuter prior responds query inductionHypothesis =>
      simp

/-- Rank witnessing that a converter which issues at most one inner query has
no infinite inner continuation. -/
def Internal.oneQueryRank
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) : Nat :=
  match history.lastInput with
  | Sum.inl _ => 1
  | Sum.inr _ => 0

theorem Internal.rawForwarding_branchFinite (A : Interface.{u, v}) :
    DDC.Raw.BranchFinite (Internal.forwardingRaw A) := by
  classical
  refine Subrelation.wf ?_ (measure Internal.oneQueryRank).wf
  intro after before continuation
  rcases continuation with ⟨query, reply, responds, rfl⟩
  change Internal.oneQueryRank (before.snocInner query reply) <
    Internal.oneQueryRank before
  cases input : before.lastInput with
  | inl outerQuery =>
      simp [Internal.oneQueryRank, DDC.History.lastInput_snocInner, input]
  | inr innerReply =>
      exact False.elim
        ((Internal.not_mem_rawForwarding_of_lastInput_inner A before innerReply
          input query) responds)

/-- Forwarding realizes the identity DDC at an interface. -/
noncomputable def forwarding (A : Interface.{u, v}) : DDC A A :=
  ofRaw (Internal.forwardingRaw A) (Internal.rawForwarding_complete A)
    (Internal.rawForwarding_branchFinite A)

/-- The proof-only raw forwarding tree and the canonical forwarding DDC have
the same admissible histories. -/
theorem Internal.admissible_forwardingRaw_iff
    {A : Interface.{u, v}} (history : DDC.History A A) :
    DDC.Raw.Admissible (Internal.forwardingRaw A) history ↔
      DDC.Raw.Admissible (forwarding A).toFun history := by
  change DDC.Raw.Admissible (Internal.forwardingRaw A) history ↔
    DDC.Raw.Admissible
      (DDC.Raw.canonicalize (Internal.forwardingRaw A)) history
  exact (DDC.Raw.admissible_canonicalize_iff
    (Internal.forwardingRaw A) history).symm

theorem Internal.mem_forwardingRaw_iff (A : Interface.{u, v})
    (history : DDC.History A A) (response : DDC.Response history) :
    response ∈ Internal.forwardingRaw A history ↔
      match history.lastInput with
      | Sum.inl query => response = Sum.inl query
      | Sum.inr ⟨query, reply⟩ =>
          ∃ equal : query = history.lastOuter,
            response = Sum.inr (equal ▸ reply) := by
  classical
  cases input : history.lastInput with
  | inl query =>
      unfold Internal.forwardingRaw
      rw [input]
      simp
  | inr innerReply =>
      rcases innerReply with ⟨query, reply⟩
      by_cases equal : query = history.lastOuter
      · unfold Internal.forwardingRaw
        rw [input]
        simp [equal]
      · unfold Internal.forwardingRaw
        rw [input]
        simp [equal]

/-- The complete graph table of forwarding on every canonical history. -/
theorem mem_forwarding_iff (A : Interface.{u, v})
    (history : DDC.History A A) (response : DDC.Response history) :
    response ∈ forwarding A history ↔
      DDC.Raw.Admissible (forwarding A).toFun history ∧
        match history.lastInput with
        | Sum.inl query => response = Sum.inl query
        | Sum.inr ⟨query, reply⟩ =>
            ∃ equal : query = history.lastOuter,
              response = Sum.inr (equal ▸ reply) := by
  change response ∈ DDC.Raw.canonicalize (Internal.forwardingRaw A) history ↔ _
  rw [DDC.Raw.mem_canonicalize_iff, Internal.mem_forwardingRaw_iff]
  change _ ∧ _ ↔
    DDC.Raw.Admissible (DDC.Raw.canonicalize (Internal.forwardingRaw A)) history ∧ _
  rw [DDC.Raw.admissible_canonicalize_iff]

/-- Forwarding has no infinite branch of consecutive inner queries. -/
theorem forwarding_branch_finite (A : Interface.{u, v}) :
    DDC.Raw.BranchFinite (forwarding A).toFun :=
  (forwarding A).branchFinite

end DDC

end RandomSystems.Ambient
