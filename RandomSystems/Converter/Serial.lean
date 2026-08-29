/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.ApplySystem
import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Serial converter composition

Maurer--Renner 2016, Section 3.3 (printed p. 7), requires converter composition to satisfy
`(β ∘ α)ⁱ R = βⁱ (αⁱ R)` and requires the identity converter to induce the
identity function.  Jost, Section 2.2.2 (printed p. 18), defines sequential
composition by the equation `(π′ ∘ π)R = π′(πR)`. The DDC law below supplies
the corresponding one-converter composition; it does not introduce Jost's
tuple of party converters at this layer.

This module constructs serial composition on the query-indexed DDC carrier and
proves those equations.  The construction is a partial function on complete
received histories.  Its proof support factors one received history through
the two converter functions.  All state is represented by the function's
history argument.
-/

namespace RandomSystems.Ambient

universe u v w z

namespace DDC.Internal

/-- A query paired with a possibly rejected answer in its exact fibre. -/
abbrev InnerReply (A : Interface.{u, v}) := DDC.History.InnerReply A

/-- An outer query or a query-indexed inner reply. -/
abbrev ReceivedInput (A : Interface.{u, v}) (B : Interface.{w, z}) :=
  DDC.History.Input A B

/-- The history ending in `query`, used to evaluate a DDS as a function. -/
def innerHistory {A : Interface.{u, v}}
    (prior : List A.query) (query : A.query) : _root_.RandomSystems.Ambient.History A where
  queries := prior ++ [query]
  nonempty := by simp

@[simp]
theorem last_innerHistory {A : Interface.{u, v}}
    (prior : List A.query) (query : A.query) :
    (innerHistory prior query).last = query := by
  simp [innerHistory, _root_.RandomSystems.Ambient.History.last]

def innerReplyAt {A : Interface.{u, v}} (system : DDS A)
    (prior : List A.query) (query : A.query) : Option (A.answer query) :=
  cast (congrArg (fun selected => Option (A.answer selected))
    (last_innerHistory prior query)) (system (innerHistory prior query))

end DDC.Internal

namespace DDC

private theorem lastOuter_eq_of_lastInput_outer
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {raw : DDC.Raw A B} {history : DDC.History A B}
    (admissible : DDC.Raw.Admissible raw history) {query : A.query}
    (lastInput : history.lastInput = Sum.inl query) :
    history.lastOuter = query := by
  induction admissible with
  | start outerQuery => simpa using Sum.inl.inj lastInput
  | afterInner prior responds reply inductionHypothesis => simp at lastInput
  | afterOuter prior responds outerQuery inductionHypothesis =>
      have equal : (Sum.inl outerQuery : DDC.History.Input A B) =
          Sum.inl query := by simpa using lastInput
      simpa using Sum.inl.inj equal

private noncomputable def rawForwarding (A : Interface.{u, v}) : DDC.Raw A A := by
  classical
  exact fun history =>
    match history.lastInput with
    | Sum.inl query => Part.some (Sum.inl query)
    | Sum.inr ⟨query, reply⟩ =>
        if equal : query = history.lastOuter then
          Part.some (Sum.inr (equal ▸ reply))
        else Part.none

private theorem mem_rawForwarding_table_iff
    {A : Interface.{u, v}} (history : DDC.History A A)
    (response : DDC.Response history) :
    response ∈ rawForwarding A history ↔
      match history.lastInput with
      | Sum.inl query => response = Sum.inl query
      | Sum.inr ⟨query, reply⟩ =>
          ∃ equal : query = history.lastOuter,
            response = Sum.inr (equal ▸ reply) := by
  classical
  unfold rawForwarding
  split
  · rename_i query inputEqual
    simp
  · rename_i query reply inputEqual
    by_cases equal : query = history.lastOuter
    · simp [equal]
    · simp [equal]

private theorem admissible_rawForwarding_iff
    {A : Interface.{u, v}} (history : DDC.History A A) :
    DDC.Raw.Admissible (rawForwarding A) history ↔
      DDC.Raw.Admissible (DDC.forwarding A).toFun history := by
  constructor
  · intro admissible
    induction admissible with
    | start query => exact .start query
    | @afterInner prior query earlier responds reply inductionHypothesis =>
        apply DDC.Raw.Admissible.afterInner inductionHypothesis
        · exact (DDC.mem_forwarding_iff A prior _).mpr
            ⟨inductionHypothesis,
              (mem_rawForwarding_table_iff prior _).mp responds⟩
    | @afterOuter prior earlier reply responds query inductionHypothesis =>
        apply DDC.Raw.Admissible.afterOuter inductionHypothesis
        · exact (DDC.mem_forwarding_iff A prior _).mpr
            ⟨inductionHypothesis,
              (mem_rawForwarding_table_iff prior _).mp responds⟩
  · intro admissible
    induction admissible with
    | start query => exact .start query
    | @afterInner prior query earlier responds reply inductionHypothesis =>
        apply DDC.Raw.Admissible.afterInner inductionHypothesis
        · exact (mem_rawForwarding_table_iff prior _).mpr
            ((DDC.mem_forwarding_iff A prior _).mp responds).2
    | @afterOuter prior earlier reply responds query inductionHypothesis =>
        apply DDC.Raw.Admissible.afterOuter inductionHypothesis
        · exact (mem_rawForwarding_table_iff prior _).mpr
            ((DDC.mem_forwarding_iff A prior _).mp responds).2

private theorem mem_forwarding_canonical_iff (A : Interface.{u, v})
    (history : DDC.History A A) (response : DDC.Response history) :
    response ∈ forwarding A history ↔
      DDC.Raw.Admissible (rawForwarding A) history ∧
        match history.lastInput with
        | Sum.inl query => response = Sum.inl query
        | Sum.inr ⟨query, reply⟩ =>
            ∃ equal : query = history.lastOuter,
              response = Sum.inr (equal ▸ reply) := by
  rw [RandomSystems.Ambient.DDC.mem_forwarding_iff]
  constructor
  · rintro ⟨admissible, responseEqual⟩
    exact ⟨(admissible_rawForwarding_iff history).mpr admissible,
      responseEqual⟩
  · rintro ⟨admissible, responseEqual⟩
    exact ⟨(admissible_rawForwarding_iff history).mp admissible,
      responseEqual⟩

end DDC

namespace DDC

open Internal

namespace Internal

/-! ## Serial history factorization -/

/-- A proof-only serial-prefix response.  The dependent sum retains the
outer query selecting an outer answer until the whole attempted history fixes
that query. -/
abbrev PackedResponse (A C : Interface.{u, v}) :=
  C.query ⊕ InnerReply A

/-- A completed inner converter can receive the next middle-interface query. -/
def InnerClosed {B C : Interface.{u, v}} (inner : DDC B C) :
    Option (DDC.History B C) → Prop
  | none => True
  | some history => ∃ reply, Sum.inr reply ∈ inner history

mutual

/-- The outer phase of three-interface serial factorization. -/
inductive OuterPrefixFactorization
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    (outerHistory : DDC.History A B) →
      Option (DDC.History B C) →
      PackedResponse A C →
      DDC.History A B → Option (DDC.History B C) → Prop
  | outerReply {outerHistory innerHistory reply}
      (responds : Sum.inr reply ∈ outer outerHistory) :
      OuterPrefixFactorization outer inner outerHistory innerHistory
        (Sum.inr ⟨outerHistory.lastOuter, reply⟩) outerHistory innerHistory
  | outerQueryFirst {outerHistory query response finalOuter finalInner}
      (responds : Sum.inl query ∈ outer outerHistory)
      (tail : InnerPrefixFactorization outer inner outerHistory
        (DDC.History.singleton query) response
        finalOuter finalInner) :
      OuterPrefixFactorization outer inner outerHistory none response
        finalOuter finalInner
  | outerQueryNext
      {outerHistory innerHistory query response finalOuter finalInner}
      (closed : InnerClosed inner (some innerHistory))
      (responds : Sum.inl query ∈ outer outerHistory)
      (tail : InnerPrefixFactorization outer inner outerHistory
        (innerHistory.snocOuter query) response
        finalOuter finalInner) :
      OuterPrefixFactorization outer inner outerHistory (some innerHistory)
        response finalOuter finalInner

/-- The inner phase of three-interface serial factorization.  `linked`
records that the inner history's current outer query is exactly the query
exposed by the outer converter. -/
inductive InnerPrefixFactorization
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    (outerHistory : DDC.History A B) →
      (innerHistory : DDC.History B C) →
      PackedResponse A C →
      DDC.History A B → Option (DDC.History B C) → Prop
  | innerQuery {outerHistory innerHistory query}
      (linked : Sum.inl innerHistory.lastOuter ∈ outer outerHistory)
      (responds : Sum.inl query ∈ inner innerHistory) :
      InnerPrefixFactorization outer inner outerHistory innerHistory
        (Sum.inl query) outerHistory (some innerHistory)
  | innerReply {outerHistory innerHistory reply response
      finalOuter finalInner}
      (linked : Sum.inl innerHistory.lastOuter ∈ outer outerHistory)
      (responds : Sum.inr reply ∈ inner innerHistory)
      (tail : OuterPrefixFactorization outer inner
        (outerHistory.snocInner innerHistory.lastOuter reply)
        (some innerHistory) response finalOuter finalInner) :
      InnerPrefixFactorization outer inner outerHistory innerHistory
        response finalOuter finalInner

end

theorem OuterPrefixFactorization.unique
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {leftResponse rightResponse : PackedResponse A C}
    {leftOuter rightOuter : DDC.History A B}
    {leftInner rightInner : Option (DDC.History B C)}
    (left : OuterPrefixFactorization outer inner outerHistory innerHistory
      leftResponse leftOuter leftInner)
    (right : OuterPrefixFactorization outer inner outerHistory innerHistory
      rightResponse rightOuter rightInner) :
    leftResponse = rightResponse ∧ leftOuter = rightOuter ∧
      leftInner = rightInner := by
  induction left using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory innerHistory leftResponse leftOuter
        leftInner leftFactorization =>
          ∀ {rightResponse rightOuter rightInner},
            InnerPrefixFactorization outer inner outerHistory innerHistory
              rightResponse rightOuter rightInner →
            leftResponse = rightResponse ∧ leftOuter = rightOuter ∧
              leftInner = rightInner)
      generalizing rightResponse rightOuter rightInner with
  | outerReply leftResponds =>
      cases right with
      | outerReply rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          exact ⟨rfl, rfl, rfl⟩
      | outerQueryFirst rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQueryNext rightClosed rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | outerQueryFirst leftResponds leftTail leftTail_ih =>
      cases right with
      | outerReply rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQueryFirst rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact leftTail_ih rightTail
  | outerQueryNext leftClosed leftResponds leftTail leftTail_ih =>
      cases right with
      | outerReply rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQueryNext rightClosed rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact leftTail_ih rightTail
  | innerQuery leftLinked leftResponds right =>
      cases right with
      | innerQuery rightLinked rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact ⟨rfl, rfl, rfl⟩
      | innerReply rightLinked rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | innerReply leftLinked leftResponds leftTail inductionHypothesis right =>
      cases right with
      | innerQuery rightLinked rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | innerReply rightLinked rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          simpa using inductionHypothesis rightTail

theorem InnerPrefixFactorization.unique
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {leftResponse rightResponse : PackedResponse A C}
    {leftOuter rightOuter : DDC.History A B}
    {leftInner rightInner : Option (DDC.History B C)}
    (left : InnerPrefixFactorization outer inner outerHistory innerHistory
      leftResponse leftOuter leftInner)
    (right : InnerPrefixFactorization outer inner outerHistory innerHistory
      rightResponse rightOuter rightInner) :
    leftResponse = rightResponse ∧ leftOuter = rightOuter ∧
      leftInner = rightInner := by
  induction left using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory innerHistory leftResponse leftOuter
        leftInner leftFactorization =>
          ∀ {rightResponse rightOuter rightInner},
            OuterPrefixFactorization outer inner outerHistory innerHistory
              rightResponse rightOuter rightInner →
            leftResponse = rightResponse ∧ leftOuter = rightOuter ∧
              leftInner = rightInner)
      generalizing rightResponse rightOuter rightInner with
  | outerReply leftResponds right =>
      cases right with
      | outerReply rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          exact ⟨rfl, rfl, rfl⟩
      | outerQueryFirst rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQueryNext rightClosed rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | outerQueryFirst leftResponds leftTail inductionHypothesis right =>
      cases right with
      | outerReply rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQueryFirst rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          simpa using inductionHypothesis rightTail
  | outerQueryNext leftClosed leftResponds leftTail inductionHypothesis right =>
      cases right with
      | outerReply rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQueryNext rightClosed rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          simpa using inductionHypothesis rightTail
  | innerQuery leftLinked leftResponds =>
      cases right with
      | innerQuery rightLinked rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact ⟨rfl, rfl, rfl⟩
      | innerReply rightLinked rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | innerReply leftLinked leftResponds leftTail inductionHypothesis =>
      cases right with
      | innerQuery rightLinked rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | innerReply rightLinked rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          exact inductionHypothesis rightTail

private def OuterResult
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (outerHistory : DDC.History A B)
    (innerHistory : Option (DDC.History B C)) : Prop :=
  ∃ response finalOuter finalInner,
    OuterPrefixFactorization outer inner outerHistory innerHistory
      response finalOuter finalInner

private def InnerResult
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (outerHistory : DDC.History A B)
    (innerHistory : DDC.History B C) : Prop :=
  ∃ response finalOuter finalInner,
    InnerPrefixFactorization outer inner outerHistory innerHistory
      response finalOuter finalInner

theorem exists_innerPrefixFactorization_of_outer
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (outerHistory : DDC.History A B)
    (innerHistory : DDC.History B C)
    (outerAdmissible : DDC.Raw.Admissible outer.toFun outerHistory)
    (innerAdmissible : DDC.Raw.Admissible inner.toFun innerHistory)
    (linked : Sum.inl innerHistory.lastOuter ∈ outer outerHistory)
    (afterOuter : ∀ nextOuter,
      DDC.Raw.InnerContinuation outer.toFun nextOuter outerHistory →
      DDC.Raw.Admissible outer.toFun nextOuter →
      ∀ nextInner,
        (∀ history, nextInner = some history →
          DDC.Raw.Admissible inner.toFun history) →
        InnerClosed inner nextInner →
        OuterResult outer inner nextOuter nextInner) :
    InnerResult outer inner outerHistory innerHistory := by
  cases responseEqual : inner.response innerHistory innerAdmissible with
  | inl query =>
      have responds : Sum.inl query ∈ inner innerHistory :=
        responseEqual ▸ inner.response_mem innerHistory innerAdmissible
      exact ⟨Sum.inl query, outerHistory, some innerHistory,
        InnerPrefixFactorization.innerQuery linked responds⟩
  | inr reply =>
      have responds : Sum.inr reply ∈ inner innerHistory :=
        responseEqual ▸ inner.response_mem innerHistory innerAdmissible
      let nextOuter := outerHistory.snocInner innerHistory.lastOuter reply
      have nextOuterAdmissible :
          DDC.Raw.Admissible outer.toFun nextOuter :=
        .afterInner outerAdmissible linked reply
      have descends : DDC.Raw.InnerContinuation outer.toFun
          nextOuter outerHistory :=
        ⟨innerHistory.lastOuter, reply, linked, rfl⟩
      obtain ⟨response, finalOuter, finalInner, factorization⟩ :=
        afterOuter nextOuter descends nextOuterAdmissible
          (some innerHistory)
          (fun history equal => by
            cases Option.some.inj equal.symm
            exact innerAdmissible)
          ⟨reply, responds⟩
      exact ⟨response, finalOuter, finalInner,
        InnerPrefixFactorization.innerReply linked responds factorization⟩

/-- Three-interface prefix factorization follows solely from the outer
converter's well-founded inner-query relation. -/
theorem exists_outerPrefixFactorization
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (outerHistory : DDC.History A B)
    (innerHistory : Option (DDC.History B C))
    (outerAdmissible : DDC.Raw.Admissible outer.toFun outerHistory)
    (innerAdmissible : ∀ history, innerHistory = some history →
      DDC.Raw.Admissible inner.toFun history)
    (innerClosed : InnerClosed inner innerHistory) :
    OuterResult outer inner outerHistory innerHistory := by
  induction outerHistory using outer.branchFinite.induction
      generalizing innerHistory with
  | h outerHistory outerInduction =>
      cases responseEqual : outer.response outerHistory outerAdmissible with
      | inr reply =>
          have responds : Sum.inr reply ∈ outer outerHistory :=
            responseEqual ▸ outer.response_mem outerHistory outerAdmissible
          exact ⟨Sum.inr ⟨outerHistory.lastOuter, reply⟩,
            outerHistory, innerHistory,
            OuterPrefixFactorization.outerReply responds⟩
      | inl query =>
          have responds : Sum.inl query ∈ outer outerHistory :=
            responseEqual ▸ outer.response_mem outerHistory outerAdmissible
          cases historyEqual : innerHistory with
          | none =>
              let nextInner := DDC.History.singleton (B := C) query
              have nextInnerAdmissible :
                  DDC.Raw.Admissible inner.toFun nextInner := .start query
              obtain ⟨response, finalOuter, finalInner, factorization⟩ :=
                exists_innerPrefixFactorization_of_outer outer inner
                  outerHistory nextInner outerAdmissible nextInnerAdmissible
                  (by simpa [nextInner] using responds)
                  (fun nextOuter descends nextAdmissible nextInner =>
                    outerInduction nextOuter descends nextInner nextAdmissible)
              exact ⟨response, finalOuter, finalInner,
                OuterPrefixFactorization.outerQueryFirst responds
                  factorization⟩
          | some previousInner =>
              rw [historyEqual] at innerClosed
              obtain ⟨previousReply, previousResponds⟩ := innerClosed
              let nextInner := previousInner.snocOuter query
              have nextInnerAdmissible :
                  DDC.Raw.Admissible inner.toFun nextInner :=
                .afterOuter (innerAdmissible previousInner historyEqual)
                  previousResponds query
              obtain ⟨response, finalOuter, finalInner, factorization⟩ :=
                exists_innerPrefixFactorization_of_outer outer inner
                  outerHistory nextInner outerAdmissible nextInnerAdmissible
                  (by simpa [nextInner] using responds)
                  (fun nextOuter descends nextAdmissible nextInner =>
                    outerInduction nextOuter descends nextInner nextAdmissible)
              exact ⟨response, finalOuter, finalInner,
                OuterPrefixFactorization.outerQueryNext
                  ⟨previousReply, previousResponds⟩ responds factorization⟩

structure PrefixEndpointValid
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (response : PackedResponse A C)
    (outerHistory : DDC.History A B)
    (innerHistory : Option (DDC.History B C)) : Prop where
  outerAdmissible : DDC.Raw.Admissible outer.toFun outerHistory
  innerAdmissible : ∀ history, innerHistory = some history →
    DDC.Raw.Admissible inner.toFun history
  exposedInner : ∀ query, response = Sum.inl query →
    ∃ history, innerHistory = some history ∧
      Sum.inl query ∈ inner history ∧
      Sum.inl history.lastOuter ∈ outer outerHistory
  selectedOuter : ∀ reply, response = Sum.inr reply →
    reply.1 = outerHistory.lastOuter
  closedOuter : ∀ reply : Option (A.answer outerHistory.lastOuter),
    response = Sum.inr ⟨outerHistory.lastOuter, reply⟩ →
      Sum.inr reply ∈ outer outerHistory ∧ InnerClosed inner innerHistory

theorem OuterPrefixFactorization.endpointValid
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner)
    (outerAdmissible : DDC.Raw.Admissible outer.toFun outerHistory)
    (innerAdmissible : ∀ history, innerHistory = some history →
      DDC.Raw.Admissible inner.toFun history)
    (innerClosed : InnerClosed inner innerHistory) :
    PrefixEndpointValid outer inner response finalOuter finalInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory innerHistory response finalOuter finalInner
          factorization =>
        DDC.Raw.Admissible outer.toFun outerHistory →
        DDC.Raw.Admissible inner.toFun innerHistory →
        PrefixEndpointValid outer inner response finalOuter finalInner) with
  | outerReply responds =>
      exact
        { outerAdmissible := outerAdmissible
          innerAdmissible := innerAdmissible
          exposedInner := by intro _ impossible; cases impossible
          selectedOuter := by
            intro reply equal
            exact (congrArg Sigma.fst (Sum.inr.inj equal)).symm
          closedOuter := by
            intro reply equal
            cases Sum.inr.inj equal
            exact ⟨responds, innerClosed⟩ }
  | outerQueryFirst responds tail inductionHypothesis =>
      exact inductionHypothesis outerAdmissible (.start _)
  | outerQueryNext closed responds tail inductionHypothesis =>
      obtain ⟨previousReply, previousResponds⟩ := closed
      exact inductionHypothesis outerAdmissible
        (.afterOuter (innerAdmissible _ rfl) previousResponds _)
  | innerQuery linked responds currentOuterAdmissible currentInnerAdmissible =>
      exact
        { outerAdmissible := currentOuterAdmissible
          innerAdmissible := by
            intro history equal
            cases Option.some.inj equal.symm
            exact currentInnerAdmissible
          exposedInner := by
            intro query equal
            cases Sum.inl.inj equal
            exact ⟨_, rfl, responds, linked⟩
          selectedOuter := by intro _ impossible; cases impossible
          closedOuter := by intro _ impossible; cases impossible }
  | innerReply linked responds tail inductionHypothesis
      currentOuterAdmissible currentInnerAdmissible =>
      exact inductionHypothesis
        (.afterInner currentOuterAdmissible linked _)
        (fun history equal => by
          cases Option.some.inj equal.symm
          exact currentInnerAdmissible)
        ⟨_, responds⟩

theorem InnerPrefixFactorization.endpointValid
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner)
    (outerAdmissible : DDC.Raw.Admissible outer.toFun outerHistory)
    (innerAdmissible : DDC.Raw.Admissible inner.toFun innerHistory) :
    PrefixEndpointValid outer inner response finalOuter finalInner := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory innerHistory response finalOuter finalInner
          factorization =>
        DDC.Raw.Admissible outer.toFun outerHistory →
        (∀ history, innerHistory = some history →
          DDC.Raw.Admissible inner.toFun history) →
        InnerClosed inner innerHistory →
        PrefixEndpointValid outer inner response finalOuter finalInner)
      with
  | outerReply responds currentOuterAdmissible currentInnerAdmissible
      currentInnerClosed =>
      exact
        { outerAdmissible := currentOuterAdmissible
          innerAdmissible := currentInnerAdmissible
          exposedInner := by intro _ impossible; cases impossible
          selectedOuter := by
            intro reply equal
            exact (congrArg Sigma.fst (Sum.inr.inj equal)).symm
          closedOuter := by
            intro reply equal
            cases Sum.inr.inj equal
            exact ⟨responds, currentInnerClosed⟩ }
  | outerQueryFirst responds tail inductionHypothesis
      currentOuterAdmissible currentInnerAdmissible currentInnerClosed =>
      exact inductionHypothesis currentOuterAdmissible (.start _)
  | outerQueryNext closed responds tail inductionHypothesis
      currentOuterAdmissible currentInnerAdmissible currentInnerClosed =>
      obtain ⟨previousReply, previousResponds⟩ := closed
      exact inductionHypothesis currentOuterAdmissible
        (.afterOuter (currentInnerAdmissible _ rfl) previousResponds _)
  | innerQuery linked responds =>
      exact
        { outerAdmissible := outerAdmissible
          innerAdmissible := by
            intro history equal
            cases Option.some.inj equal.symm
            exact innerAdmissible
          exposedInner := by
            intro query equal
            cases Sum.inl.inj equal
            exact ⟨_, rfl, responds, linked⟩
          selectedOuter := by intro _ impossible; cases impossible
          closedOuter := by intro _ impossible; cases impossible }
  | innerReply linked responds tail inductionHypothesis =>
      exact inductionHypothesis
        (.afterInner outerAdmissible linked _)
        (fun history equal => by
          cases Option.some.inj equal.symm
          exact innerAdmissible)
        ⟨_, responds⟩

theorem OuterPrefixFactorization.lastOuter_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner) :
    finalOuter.lastOuter = outerHistory.lastOuter := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory _ _ finalOuter _ _ =>
        finalOuter.lastOuter = outerHistory.lastOuter) with
  | outerReply => rfl
  | outerQueryFirst _ _ inductionHypothesis => exact inductionHypothesis
  | outerQueryNext _ _ _ inductionHypothesis => exact inductionHypothesis
  | innerQuery => rfl
  | innerReply _ _ _ inductionHypothesis =>
      exact inductionHypothesis.trans (by simp)

theorem InnerPrefixFactorization.lastOuter_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner) :
    finalOuter.lastOuter = outerHistory.lastOuter := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory _ _ finalOuter _ _ =>
        finalOuter.lastOuter = outerHistory.lastOuter) with
  | outerReply => rfl
  | outerQueryFirst _ _ inductionHypothesis => exact inductionHypothesis
  | outerQueryNext _ _ _ inductionHypothesis => exact inductionHypothesis
  | innerQuery => rfl
  | innerReply _ _ _ inductionHypothesis =>
      exact inductionHypothesis.trans (by simp)

/-- Pack a response while retaining the outer query selecting its answer. -/
def packResponse {A C : Interface.{u, v}}
    (history : DDC.History A C) :
    DDC.Response history → PackedResponse A C
  | Sum.inl query => Sum.inl query
  | Sum.inr reply => Sum.inr ⟨history.lastOuter, reply⟩

private theorem packResponse_injective {A C : Interface.{u, v}}
    (history : DDC.History A C) :
    Function.Injective (packResponse history) := by
  intro left right equal
  cases left with
  | inl leftQuery =>
      cases right with
      | inl rightQuery => exact congrArg Sum.inl (Sum.inl.inj equal)
      | inr rightReply => cases equal
  | inr leftReply =>
      cases right with
      | inl rightQuery => cases equal
      | inr rightReply =>
          have packedEqual := Sum.inr.inj equal
          cases packedEqual
          rfl

/-- Canonical constructor presentation of a dependent received history. -/
inductive AttemptedHistory (A C : Interface.{u, v}) where
  | start (query : A.query)
  | afterInner (prior : AttemptedHistory A C) (query : C.query)
      (reply : Option (C.answer query))
  | afterOuter (prior : AttemptedHistory A C) (query : A.query)

namespace AttemptedHistory

private def inputs {A C : Interface.{u, v}} :
    AttemptedHistory A C → List (ReceivedInput A C)
  | .start query => [Sum.inl query]
  | .afterInner prior query reply =>
      inputs prior ++ [Sum.inr ⟨query, reply⟩]
  | .afterOuter prior query => inputs prior ++ [Sum.inl query]

private theorem inputs_ne_nil {A C : Interface.{u, v}}
    (history : AttemptedHistory A C) : history.inputs ≠ [] := by
  cases history <;> simp [inputs]

private theorem inputs_injective {A C : Interface.{u, v}} :
    Function.Injective (@inputs A C) := by
  intro left
  induction left with
  | start leftQuery =>
      intro right equal
      cases right with
      | start rightQuery =>
          simp [inputs] at equal
          subst rightQuery
          rfl
      | afterInner prior query reply =>
          have empty : [] = prior.inputs := by
            simpa [inputs] using congrArg List.dropLast equal
          exact (prior.inputs_ne_nil empty.symm).elim
      | afterOuter prior query =>
          have empty : [] = prior.inputs := by
            simpa [inputs] using congrArg List.dropLast equal
          exact (prior.inputs_ne_nil empty.symm).elim
  | afterInner leftPrior leftQuery leftReply inductionHypothesis =>
      intro right equal
      cases right with
      | start rightQuery =>
          have empty : leftPrior.inputs = [] := by
            simpa [inputs] using congrArg List.dropLast equal
          exact (leftPrior.inputs_ne_nil empty).elim
      | afterInner rightPrior rightQuery rightReply =>
          have priorEqual : leftPrior.inputs = rightPrior.inputs := by
            simpa [inputs] using congrArg List.dropLast equal
          cases inductionHypothesis priorEqual
          have lastEqual :
              (Sum.inr ⟨leftQuery, leftReply⟩ : ReceivedInput A C) =
                Sum.inr ⟨rightQuery, rightReply⟩ := by
            simpa [inputs] using congrArg List.getLast? equal
          cases Sum.inr.inj lastEqual
          rfl
      | afterOuter rightPrior rightQuery =>
          have lastEqual := congrArg List.getLast? equal
          simp [inputs] at lastEqual
  | afterOuter leftPrior leftQuery inductionHypothesis =>
      intro right equal
      cases right with
      | start rightQuery =>
          have empty : leftPrior.inputs = [] := by
            simpa [inputs] using congrArg List.dropLast equal
          exact (leftPrior.inputs_ne_nil empty).elim
      | afterInner rightPrior rightQuery rightReply =>
          have lastEqual := congrArg List.getLast? equal
          simp [inputs] at lastEqual
      | afterOuter rightPrior rightQuery =>
          have priorEqual : leftPrior.inputs = rightPrior.inputs := by
            simpa [inputs] using congrArg List.dropLast equal
          cases inductionHypothesis priorEqual
          have lastEqual :
              (Sum.inl leftQuery : ReceivedInput A C) = Sum.inl rightQuery := by
            simpa [inputs] using congrArg List.getLast? equal
          cases Sum.inl.inj lastEqual
          rfl

/-- The received history represented by its canonical constructor tree. -/
def toReceived {A C : Interface.{u, v}} :
    AttemptedHistory A C → DDC.History A C
  | .start query => DDC.History.singleton query
  | .afterInner prior query reply => prior.toReceived.snocInner query reply
  | .afterOuter prior query => prior.toReceived.snocOuter query

private theorem inputs_toReceived {A C : Interface.{u, v}}
    (history : AttemptedHistory A C) : history.toReceived.inputs.1 =
      history.inputs := by
  induction history with
  | start query => rfl
  | afterInner prior query reply inductionHypothesis =>
      simp [toReceived, DDC.History.snocInner, inputs,
        _root_.RandomSystems.Ambient.History.snoc, inductionHypothesis]
  | afterOuter prior query inductionHypothesis =>
      simp [toReceived, DDC.History.snocOuter, inputs,
        _root_.RandomSystems.Ambient.History.snoc, inductionHypothesis]

theorem toReceived_injective {A C : Interface.{u, v}} :
    Function.Injective (@toReceived A C) := by
  intro left right equal
  apply inputs_injective
  rw [← inputs_toReceived left, ← inputs_toReceived right, equal]

@[simp]
private theorem lastOuter_start {A C : Interface.{u, v}}
    (query : A.query) :
    (AttemptedHistory.start (C := C) query).toReceived.lastOuter = query := rfl

@[simp]
private theorem lastOuter_afterInner {A C : Interface.{u, v}}
    (prior : AttemptedHistory A C) (query : C.query)
    (reply : Option (C.answer query)) :
    (AttemptedHistory.afterInner prior query reply).toReceived.lastOuter =
      prior.toReceived.lastOuter := rfl

@[simp]
private theorem lastOuter_afterOuter {A C : Interface.{u, v}}
    (prior : AttemptedHistory A C) (query : A.query) :
    (AttemptedHistory.afterOuter prior query).toReceived.lastOuter = query := by
  simp [toReceived]

end AttemptedHistory

/-- Complete factorization indexed by the canonical constructor presentation
of the received history. -/
inductive SerialFactorization
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    AttemptedHistory A C → PackedResponse A C →
      DDC.History A B → Option (DDC.History B C) → Prop
  | start {outerQuery response finalOuter finalInner}
      (middleFactorization : OuterPrefixFactorization outer inner
        (DDC.History.singleton outerQuery) none response
        finalOuter finalInner)
      (valid : PrefixEndpointValid outer inner response finalOuter finalInner) :
      SerialFactorization outer inner (.start outerQuery) response
        finalOuter finalInner
  | afterInner {history query currentOuter currentInner reply response
      finalOuter finalInner}
      (previous : SerialFactorization outer inner history (Sum.inl query)
        currentOuter (some currentInner))
      (middleFactorization : InnerPrefixFactorization outer inner currentOuter
        (currentInner.snocInner query reply) response finalOuter finalInner)
      (valid : PrefixEndpointValid outer inner response finalOuter finalInner) :
      SerialFactorization outer inner (.afterInner history query reply)
        response finalOuter finalInner
  | afterOuter {history previousReply currentOuter currentInner outerQuery
      response finalOuter finalInner}
      (previous : SerialFactorization outer inner history
        (Sum.inr ⟨history.toReceived.lastOuter, previousReply⟩)
        currentOuter currentInner)
      (middleFactorization : OuterPrefixFactorization outer inner
        (currentOuter.snocOuter outerQuery) currentInner response
        finalOuter finalInner)
      (valid : PrefixEndpointValid outer inner response finalOuter finalInner) :
      SerialFactorization outer inner (.afterOuter history outerQuery)
        response finalOuter finalInner

theorem SerialFactorization.unique
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C}
    {leftResponse rightResponse : PackedResponse A C}
    {leftOuter rightOuter : DDC.History A B}
    {leftInner rightInner : Option (DDC.History B C)}
    (left : SerialFactorization outer inner history leftResponse
      leftOuter leftInner)
    (right : SerialFactorization outer inner history rightResponse
      rightOuter rightInner) :
    leftResponse = rightResponse ∧ leftOuter = rightOuter ∧
      leftInner = rightInner := by
  induction left generalizing rightResponse rightOuter rightInner with
  | start leftMiddle leftValid =>
      cases right with
      | start rightMiddle rightValid =>
          exact OuterPrefixFactorization.unique leftMiddle rightMiddle
  | afterInner leftPrevious leftMiddle leftValid inductionHypothesis =>
      cases right with
      | afterInner rightPrevious rightMiddle rightValid =>
          obtain ⟨queryEqual, outerEqual, innerEqual⟩ :=
            inductionHypothesis rightPrevious
          cases Sum.inl.inj queryEqual
          cases outerEqual
          cases Option.some.inj innerEqual
          exact InnerPrefixFactorization.unique leftMiddle rightMiddle
  | afterOuter leftPrevious leftMiddle leftValid inductionHypothesis =>
      cases right with
      | afterOuter rightPrevious rightMiddle rightValid =>
          obtain ⟨replyEqual, outerEqual, innerEqual⟩ :=
            inductionHypothesis rightPrevious
          cases Sum.inr.inj replyEqual
          cases outerEqual
          cases innerEqual
          exact OuterPrefixFactorization.unique leftMiddle rightMiddle

theorem SerialFactorization.endpointValid
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    PrefixEndpointValid outer inner response outerHistory innerHistory := by
  cases factorization with
  | start _ valid => exact valid
  | afterInner _ _ valid => exact valid
  | afterOuter _ _ valid => exact valid

theorem SerialFactorization.outerLast_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    outerHistory.lastOuter = history.toReceived.lastOuter := by
  induction factorization with
  | start middleFactorization valid =>
      simpa using middleFactorization.lastOuter_eq
  | afterInner previous middleFactorization valid inductionHypothesis =>
      exact middleFactorization.lastOuter_eq.trans
        (by simpa using inductionHypothesis)
  | afterOuter previous middleFactorization valid inductionHypothesis =>
      simpa using middleFactorization.lastOuter_eq

theorem SerialFactorization.realizeResponse
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    ∃ actual : DDC.Response history.toReceived,
      packResponse history.toReceived actual = response := by
  have valid := factorization.endpointValid
  cases response with
  | inl query => exact ⟨Sum.inl query, rfl⟩
  | inr packed =>
      rcases packed with ⟨query, reply⟩
      have queryEqual : query = history.toReceived.lastOuter :=
        (valid.selectedOuter ⟨query, reply⟩ rfl).trans
          factorization.outerLast_eq
      subst query
      exact ⟨Sum.inr reply, rfl⟩

private def SerialWitness
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (history : DDC.History A C) (response : DDC.Response history) :
    Prop :=
  ∃ attempted, attempted.toReceived = history ∧
    ∃ outerHistory innerHistory,
      SerialFactorization outer inner attempted (packResponse history response)
        outerHistory innerHistory

/-- The raw DDC graph determined by serial history factorization. -/
noncomputable def serialRaw
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    DDC.Raw A C :=
  fun history =>
    { Dom := ∃ response, SerialWitness outer inner history response
      get := fun defined => Classical.choose defined }

private theorem serialWitness_unique
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : DDC.History A C}
    {left right : DDC.Response history}
    (leftWitness : SerialWitness outer inner history left)
    (rightWitness : SerialWitness outer inner history right) : left = right := by
  obtain ⟨leftAttempted, leftHistory, leftOuter, leftInner,
    leftFactorization⟩ := leftWitness
  obtain ⟨rightAttempted, rightHistory, rightOuter, rightInner,
    rightFactorization⟩ := rightWitness
  have attemptedEqual : leftAttempted = rightAttempted :=
    AttemptedHistory.toReceived_injective (leftHistory.trans rightHistory.symm)
  subst rightAttempted
  have packedEqual :=
    (SerialFactorization.unique leftFactorization rightFactorization).1
  exact packResponse_injective history packedEqual

theorem mem_serialRaw_iff
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (history : DDC.History A C) (response : DDC.Response history) :
    response ∈ serialRaw outer inner history ↔
      SerialWitness outer inner history response := by
  constructor
  · rintro ⟨defined, valueEqual⟩
    have chosenWitness : SerialWitness outer inner history
        (Classical.choose defined) := Classical.choose_spec defined
    exact valueEqual ▸ chosenWitness
  · intro witness
    let defined : ∃ response, SerialWitness outer inner history response :=
      ⟨response, witness⟩
    refine ⟨defined, ?_⟩
    exact serialWitness_unique (Classical.choose_spec defined) witness

private theorem SerialFactorization.serialRaw_admissible
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    DDC.Raw.Admissible (serialRaw outer inner) history.toReceived := by
  induction factorization with
  | start middleFactorization valid => exact .start _
  | afterInner previous middleFactorization valid inductionHypothesis =>
      rename_i prior query currentOuter currentInner reply response
        finalOuter finalInner
      have responds : Sum.inl query ∈
          serialRaw outer inner prior.toReceived := by
        rw [mem_serialRaw_iff]
        exact ⟨prior, rfl, currentOuter, some currentInner, previous⟩
      exact .afterInner inductionHypothesis responds reply
  | afterOuter previous middleFactorization valid inductionHypothesis =>
      rename_i prior previousReply currentOuter currentInner outerQuery
        response finalOuter finalInner
      have responds : Sum.inr previousReply ∈
          serialRaw outer inner prior.toReceived := by
        rw [mem_serialRaw_iff]
        exact ⟨prior, rfl, currentOuter, currentInner, previous⟩
      exact .afterOuter inductionHypothesis responds outerQuery

private theorem serialWitness_admissible
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : DDC.History A C} {response : DDC.Response history}
    (witness : SerialWitness outer inner history response) :
    DDC.Raw.Admissible (serialRaw outer inner) history := by
  obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
    factorization⟩ := witness
  subst history
  exact factorization.serialRaw_admissible

private theorem serialRaw_complete
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    DDC.Raw.Complete (serialRaw outer inner) := by
  intro history admissible
  induction admissible with
  | start outerQuery =>
      let initialOuter := DDC.History.singleton (B := B) outerQuery
      obtain ⟨packed, finalOuter, finalInner, middleFactorization⟩ :=
        exists_outerPrefixFactorization outer inner initialOuter none
          (.start outerQuery) (by intro _ impossible; cases impossible) trivial
      have valid := middleFactorization.endpointValid (.start outerQuery)
        (by intro _ impossible; cases impossible) trivial
      let whole : SerialFactorization outer inner (.start outerQuery) packed
          finalOuter finalInner := .start middleFactorization valid
      obtain ⟨response, responseEqual⟩ := whole.realizeResponse
      refine ⟨response, ?_⟩
      refine ⟨AttemptedHistory.start outerQuery, rfl, finalOuter,
        finalInner, ?_⟩
      change SerialFactorization outer inner (.start outerQuery)
        (packResponse (AttemptedHistory.start outerQuery).toReceived response)
        finalOuter finalInner
      rw [responseEqual]
      exact whole

  | @afterInner history query prior responds reply inductionHypothesis =>
      have previousWitness :=
        (mem_serialRaw_iff outer inner history (Sum.inl query)).mp responds
      obtain ⟨attempted, historyEqual, currentOuter, currentInnerState,
        previousFactorization⟩ := previousWitness
      subst history
      have previousValid := previousFactorization.endpointValid
      obtain ⟨currentInner, innerEqual, innerResponds, linked⟩ :=
        previousValid.exposedInner query rfl
      cases innerEqual
      let nextInner := currentInner.snocInner query reply
      have nextInnerAdmissible : DDC.Raw.Admissible inner.toFun nextInner :=
        .afterInner (previousValid.innerAdmissible currentInner rfl)
          innerResponds reply
      obtain ⟨packed, finalOuter, finalInner, middleFactorization⟩ :=
        exists_innerPrefixFactorization_of_outer outer inner currentOuter
          nextInner previousValid.outerAdmissible nextInnerAdmissible
          (by simpa [nextInner] using linked)
          (fun nextOuter _ nextOuterAdmissible nextInnerState
              nextInnerAdmissible nextInnerClosed =>
            exists_outerPrefixFactorization outer inner nextOuter
              nextInnerState nextOuterAdmissible nextInnerAdmissible
              nextInnerClosed)
      have valid := middleFactorization.endpointValid
        previousValid.outerAdmissible nextInnerAdmissible
      let whole : SerialFactorization outer inner
          (.afterInner attempted query reply) packed finalOuter finalInner :=
        .afterInner previousFactorization middleFactorization valid
      obtain ⟨response, responseEqual⟩ := whole.realizeResponse
      refine ⟨response, ?_⟩
      refine ⟨AttemptedHistory.afterInner attempted query reply, rfl,
        finalOuter, finalInner, ?_⟩
      change SerialFactorization outer inner
        (.afterInner attempted query reply)
        (packResponse
          (AttemptedHistory.afterInner attempted query reply).toReceived
          response)
        finalOuter finalInner
      rw [responseEqual]
      exact whole
  | @afterOuter history prior previousReply responds outerQuery
      inductionHypothesis =>
      have previousWitness :=
        (mem_serialRaw_iff outer inner history
          (Sum.inr previousReply)).mp responds
      obtain ⟨attempted, historyEqual, currentOuter, currentInner,
        previousFactorization⟩ := previousWitness
      subst history
      have previousValid := previousFactorization.endpointValid
      have lastEqual := previousFactorization.outerLast_eq
      let adjustedReply : Option (A.answer currentOuter.lastOuter) :=
        cast (congrArg (fun query => Option (A.answer query)) lastEqual.symm)
          previousReply
      have packedEqual :
          (⟨attempted.toReceived.lastOuter, previousReply⟩ : InnerReply A) =
            ⟨currentOuter.lastOuter, adjustedReply⟩ := by
        apply Sigma.ext lastEqual.symm
        exact (cast_heq
          (congrArg (fun query => Option (A.answer query)) lastEqual.symm)
          previousReply).symm
      obtain ⟨outerResponds, innerClosed⟩ :=
        previousValid.closedOuter adjustedReply (congrArg Sum.inr packedEqual)
      let nextOuter := currentOuter.snocOuter outerQuery
      have nextOuterAdmissible : DDC.Raw.Admissible outer.toFun nextOuter :=
        .afterOuter previousValid.outerAdmissible outerResponds outerQuery
      obtain ⟨packed, finalOuter, finalInner, middleFactorization⟩ :=
        exists_outerPrefixFactorization outer inner nextOuter currentInner
          nextOuterAdmissible previousValid.innerAdmissible innerClosed
      have valid := middleFactorization.endpointValid nextOuterAdmissible
        previousValid.innerAdmissible innerClosed
      let whole : SerialFactorization outer inner
          (.afterOuter attempted outerQuery) packed finalOuter finalInner :=
        .afterOuter previousFactorization middleFactorization valid
      obtain ⟨response, responseEqual⟩ := whole.realizeResponse
      refine ⟨response, ?_⟩
      refine ⟨AttemptedHistory.afterOuter attempted outerQuery, rfl,
        finalOuter, finalInner, ?_⟩
      change SerialFactorization outer inner (.afterOuter attempted outerQuery)
        (packResponse
          (AttemptedHistory.afterOuter attempted outerQuery).toReceived
          response)
        finalOuter finalInner
      rw [responseEqual]
      exact whole

mutual

private theorem OuterPrefixFactorization.outer_reflTransGen
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C} {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner) :
    Relation.ReflTransGen (DDC.Raw.InnerContinuation outer.toFun)
      finalOuter outerHistory := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory _ _ finalOuter _ _ =>
        Relation.ReflTransGen (DDC.Raw.InnerContinuation outer.toFun)
          finalOuter outerHistory) with
  | outerReply => exact .refl
  | outerQueryFirst _ _ inductionHypothesis => exact inductionHypothesis
  | outerQueryNext _ _ _ inductionHypothesis => exact inductionHypothesis
  | innerQuery => exact .refl
  | innerReply linked _ _ inductionHypothesis =>
      exact .tail inductionHypothesis ⟨_, _, linked, rfl⟩

private theorem InnerPrefixFactorization.outer_reflTransGen
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C} {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner) :
    Relation.ReflTransGen (DDC.Raw.InnerContinuation outer.toFun)
      finalOuter outerHistory := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory _ _ finalOuter _ _ =>
        Relation.ReflTransGen (DDC.Raw.InnerContinuation outer.toFun)
          finalOuter outerHistory) with
  | outerReply => exact .refl
  | outerQueryFirst _ _ inductionHypothesis => exact inductionHypothesis
  | outerQueryNext _ _ _ inductionHypothesis => exact inductionHypothesis
  | innerQuery => exact .refl
  | innerReply linked _ _ inductionHypothesis =>
      exact .tail inductionHypothesis ⟨_, _, linked, rfl⟩

end

private theorem InnerPrefixFactorization.same_outer
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory finalOuter : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner)
    (same : finalOuter = outerHistory) :
    ∃ query, response = Sum.inl query ∧ finalInner = some innerHistory ∧
      Sum.inl query ∈ inner innerHistory := by
  cases factorization with
  | innerQuery linked responds => exact ⟨_, rfl, rfl, responds⟩
  | innerReply linked responds tail =>
      rename_i reply
      have tailPath := tail.outer_reflTransGen
      have cycle : Relation.TransGen
          (DDC.Raw.InnerContinuation outer.toFun) finalOuter outerHistory :=
        Relation.TransGen.tail' tailPath ⟨_, reply, linked, rfl⟩
      rw [same] at cycle
      have transitiveWellFounded : WellFounded
          (Relation.TransGen (DDC.Raw.InnerContinuation outer.toFun)) :=
        WellFounded.intro (fun history => acc_transGen_iff.mpr
          (outer.branchFinite.apply history))
      exact (transitiveWellFounded.irrefl.irrefl outerHistory cycle).elim

private theorem branchFinite_transGen
    {A B : Interface.{u, v}} (converter : DDC A B) :
    WellFounded (Relation.TransGen
      (DDC.Raw.InnerContinuation converter.toFun)) :=
  WellFounded.intro fun history =>
    acc_transGen_iff.mpr (converter.branchFinite.apply history)

private theorem serialRaw_accessible_of_factorization
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    Acc (DDC.Raw.InnerContinuation (serialRaw outer inner))
      history.toReceived := by
  let outerProperty := fun currentOuter : DDC.History A B =>
    ∀ (currentHistory : AttemptedHistory A C)
      (currentResponse : PackedResponse A C)
      (currentInner : Option (DDC.History B C)),
      SerialFactorization outer inner currentHistory currentResponse
          currentOuter currentInner →
        Acc (DDC.Raw.InnerContinuation (serialRaw outer inner))
          currentHistory.toReceived
  have outerAll : ∀ currentOuter, outerProperty currentOuter := by
    intro currentOuter
    induction currentOuter using (branchFinite_transGen outer).induction with
    | h currentOuter outerInduction =>
        intro currentHistory currentResponse currentInner currentFactorization
        cases currentResponse with
        | inr packedReply =>
            obtain ⟨actualResponse, packedEqual⟩ :=
              currentFactorization.realizeResponse
            cases actualResponse with
            | inl query => cases packedEqual
            | inr outerReply =>
                apply Acc.intro
                intro after continues
                rcases continues with ⟨query, reply, responds, afterEqual⟩
                have currentResponds : Sum.inr outerReply ∈
                    serialRaw outer inner currentHistory.toReceived := by
                  rw [mem_serialRaw_iff]
                  refine ⟨currentHistory, rfl, currentOuter, currentInner, ?_⟩
                  rw [packedEqual]
                  exact currentFactorization
                cases Part.mem_unique responds currentResponds
        | inl exposedQuery =>
            have currentValid := currentFactorization.endpointValid
            obtain ⟨exposedInner, innerEqual, endpointResponds,
              outerLinked⟩ := currentValid.exposedInner exposedQuery rfl
            cases innerEqual
            let innerProperty := fun currentInnerHistory :
                DDC.History B C =>
              ∀ (currentHistory : AttemptedHistory A C) (query : C.query),
                SerialFactorization outer inner currentHistory (Sum.inl query)
                    currentOuter (some currentInnerHistory) →
                  Acc (DDC.Raw.InnerContinuation (serialRaw outer inner))
                    currentHistory.toReceived
            have innerAll : ∀ currentInnerHistory,
                innerProperty currentInnerHistory := by
              intro currentInnerHistory
              induction currentInnerHistory using inner.branchFinite.induction with
              | h currentInnerHistory innerInduction =>
                  intro before query beforeFactorization
                  apply Acc.intro
                  intro after continues
                  rcases continues with
                    ⟨actualQuery, reply, actualResponds, afterEqual⟩
                  have beforeResponds : Sum.inl query ∈
                      serialRaw outer inner before.toReceived := by
                    rw [mem_serialRaw_iff]
                    exact ⟨before, rfl, currentOuter,
                      some currentInnerHistory, beforeFactorization⟩
                  have queryEqual :=
                    Part.mem_unique actualResponds beforeResponds
                  cases Sum.inl.inj queryEqual
                  subst after
                  have beforeValid := beforeFactorization.endpointValid
                  obtain ⟨innerAtQuery, endpointInnerEqual,
                    endpointResponds, endpointLinked⟩ :=
                    beforeValid.exposedInner query rfl
                  cases Option.some.inj endpointInnerEqual
                  let nextInner := currentInnerHistory.snocInner query reply
                  have nextInnerAdmissible : DDC.Raw.Admissible
                      inner.toFun nextInner :=
                    .afterInner
                      (beforeValid.innerAdmissible currentInnerHistory rfl)
                      endpointResponds reply
                  obtain ⟨nextResponse, finalOuter, finalInner,
                    nextMiddle⟩ :=
                    exists_innerPrefixFactorization_of_outer outer inner
                      currentOuter nextInner beforeValid.outerAdmissible
                      nextInnerAdmissible
                      (by simpa [nextInner] using endpointLinked)
                      (fun nextOuter _ nextOuterAdmissible nextInnerState
                          nextInnerStateAdmissible nextInnerClosed =>
                        exists_outerPrefixFactorization outer inner nextOuter
                          nextInnerState nextOuterAdmissible
                          nextInnerStateAdmissible nextInnerClosed)
                  have nextValid := nextMiddle.endpointValid
                    beforeValid.outerAdmissible nextInnerAdmissible
                  have afterFactorization :
                      SerialFactorization outer inner
                        (.afterInner before query reply) nextResponse
                        finalOuter finalInner :=
                    .afterInner beforeFactorization nextMiddle nextValid
                  have outerPath := nextMiddle.outer_reflTransGen
                  by_cases sameOuter : finalOuter = currentOuter
                  · obtain ⟨nextQuery, responseEqual, innerStateEqual,
                      nextResponds⟩ := nextMiddle.same_outer sameOuter
                    subst nextResponse
                    subst finalInner
                    exact innerInduction nextInner
                      ⟨query, reply, endpointResponds, rfl⟩
                      (.afterInner before query reply) nextQuery
                      (sameOuter ▸ afterFactorization)
                  · have strictOuter : Relation.TransGen
                        (DDC.Raw.InnerContinuation outer.toFun)
                        finalOuter currentOuter := by
                      rcases Relation.reflTransGen_iff_eq_or_transGen.mp
                        outerPath with equal | strict
                      · exact (sameOuter equal.symm).elim
                      · exact strict
                    exact outerInduction finalOuter strictOuter
                      (.afterInner before query reply) nextResponse
                      finalInner afterFactorization
            exact innerAll exposedInner currentHistory exposedQuery
              currentFactorization
  exact outerAll outerHistory history response innerHistory factorization

private theorem serialRaw_branchFinite
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    DDC.Raw.BranchFinite (serialRaw outer inner) := by
  apply WellFounded.intro
  intro history
  by_cases admissible : DDC.Raw.Admissible (serialRaw outer inner) history
  · have defined := serialRaw_complete outer inner history admissible
    let response := (serialRaw outer inner history).get defined
    have responds : response ∈ serialRaw outer inner history := ⟨defined, rfl⟩
    obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
      factorization⟩ :=
      (mem_serialRaw_iff outer inner history response).mp responds
    subst history
    exact serialRaw_accessible_of_factorization outer inner factorization
  · apply Acc.intro
    intro after continues
    rcases continues with ⟨query, reply, responds, afterEqual⟩
    exact (admissible (serialWitness_admissible
      ((mem_serialRaw_iff outer inner history (Sum.inl query)).mp
        responds))).elim

end Internal

/--
Serial composition of branch-finite DDCs.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “Σ is equipped with a composition
operation ◦ satisfying `(β ◦ α)ⁱ R = βⁱ (αⁱ R)`.”
-/
noncomputable def serial
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C) :
    DDC A C :=
  { toFun := DDC.Raw.canonicalize (serialRaw outer inner)
    exactDomain := DDC.Raw.dom_canonicalize_iff
      (serialRaw outer inner) (serialRaw_complete outer inner)
    branchFinite := by
      apply WellFounded.mono (serialRaw_branchFinite outer inner)
      intro after before continues
      rcases continues with ⟨query, reply, responds, afterEqual⟩
      have rawResponds :=
        (DDC.Raw.mem_canonicalize_iff (serialRaw outer inner)
          before (Sum.inl query)).mp responds |>.2
      exact ⟨query, reply, rawResponds, afterEqual⟩ }

theorem mem_serial_iff
    {A B C : Interface.{u, v}} (outer : DDC A B) (inner : DDC B C)
    (history : DDC.History A C) (response : DDC.Response history) :
    response ∈ serial outer inner history ↔
      response ∈ serialRaw outer inner history := by
  rw [serial, DDC.Raw.mem_canonicalize_iff]
  constructor
  · exact And.right
  · intro membership
    exact ⟨serialWitness_admissible
      ((mem_serialRaw_iff outer inner history response).mp membership),
      membership⟩

namespace Internal

private theorem InnerPrefixFactorization.identity_outer
    {B C : Interface.{u, v}} {inner : DDC B C}
    {outerHistory : DDC.History B B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse B C}
    {finalOuter : DDC.History B B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization (forwarding B) inner outerHistory
      innerHistory response finalOuter finalInner) :
    finalInner = some innerHistory ∧
      ∃ actual : DDC.Response innerHistory,
        response = packResponse innerHistory actual ∧
          actual ∈ inner innerHistory := by
  classical
  cases factorization with
  | innerQuery linked responds =>
      exact ⟨rfl, Sum.inl _, rfl, responds⟩
  | innerReply linked responds middleFactorization =>
      rename_i reply
      have linkedInfo := (mem_forwarding_canonical_iff B outerHistory _).mp linked
      have linkedRaw := linkedInfo.2
      have linkedInput : outerHistory.lastInput =
          Sum.inl innerHistory.lastOuter := by
        cases inputEqual : outerHistory.lastInput with
        | inl outerQuery =>
            rw [inputEqual] at linkedRaw
            have queryEqual : innerHistory.lastOuter = outerQuery :=
              Sum.inl.inj linkedRaw
            exact congrArg Sum.inl queryEqual.symm
        | inr previousReply =>
            rw [inputEqual] at linkedRaw
            rcases previousReply with ⟨previousQuery, previousValue⟩
            rcases linkedRaw with ⟨same, impossible⟩
            cases impossible
      have linkedEqual : innerHistory.lastOuter = outerHistory.lastOuter := by
        exact (lastOuter_eq_of_lastInput_outer linkedInfo.1 linkedInput).symm
      cases middleFactorization with
      | outerReply outerResponds =>
          have outerRaw := (mem_forwarding_canonical_iff B _ _).mp outerResponds |>.2
          simp [linkedEqual] at outerRaw
          have replyEqual := outerRaw
          cases Sum.inr.inj replyEqual
          refine ⟨rfl, Sum.inr reply, ?_, responds⟩
          apply congrArg Sum.inr
          apply Sigma.ext linkedEqual.symm
          simpa only [DDC.History.lastOuter_snocInner] using
            (eqRec_heq (φ := fun query => Option (B.answer query))
              linkedEqual reply)
      | outerQueryNext closed outerResponds tail =>
          have outerRaw := (mem_forwarding_canonical_iff B _ _).mp outerResponds |>.2
          simp [linkedEqual] at outerRaw

private theorem OuterPrefixFactorization.identity_outer_none
    {B C : Interface.{u, v}} {inner : DDC B C}
    {outerHistory : DDC.History B B} {input : B.query}
    {response : PackedResponse B C}
    {finalOuter : DDC.History B B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization (forwarding B) inner outerHistory
      none response finalOuter finalInner)
    (lastInput : outerHistory.lastInput = Sum.inl input) :
    finalInner = some (DDC.History.singleton (B := C) input) ∧
      ∃ actual : DDC.Response
          (DDC.History.singleton (B := C) input),
        response = packResponse (DDC.History.singleton (B := C) input)
          actual ∧
        actual ∈ inner (DDC.History.singleton (B := C) input) := by
  cases factorization with
  | outerReply responds =>
      have raw := (mem_forwarding_canonical_iff B outerHistory _).mp responds |>.2
      rw [lastInput] at raw
      simp at raw
  | outerQueryFirst responds tail =>
      rename_i query
      have raw := (mem_forwarding_canonical_iff B outerHistory _).mp responds |>.2
      rw [lastInput] at raw
      have queryEqual : query = input := by simpa using raw
      subst query
      exact tail.identity_outer

private theorem OuterPrefixFactorization.identity_outer_some
    {B C : Interface.{u, v}} {inner : DDC B C}
    {outerHistory : DDC.History B B} {input : B.query}
    {previousInner : DDC.History B C}
    {response : PackedResponse B C}
    {finalOuter : DDC.History B B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization (forwarding B) inner outerHistory
      (some previousInner) response finalOuter finalInner)
    (lastInput : outerHistory.lastInput = Sum.inl input) :
    finalInner = some (previousInner.snocOuter input) ∧
      ∃ actual : DDC.Response (previousInner.snocOuter input),
        response = packResponse (previousInner.snocOuter input) actual ∧
          actual ∈ inner (previousInner.snocOuter input) := by
  cases factorization with
  | outerReply responds =>
      have raw := (mem_forwarding_canonical_iff B outerHistory _).mp responds |>.2
      rw [lastInput] at raw
      simp at raw
  | outerQueryNext closed responds tail =>
      rename_i query
      have raw := (mem_forwarding_canonical_iff B outerHistory _).mp responds |>.2
      rw [lastInput] at raw
      have queryEqual : query = input := by simpa using raw
      subst query
      exact tail.identity_outer

private theorem SerialFactorization.identity_outer
    {B C : Interface.{u, v}} {inner : DDC B C}
    {history : AttemptedHistory B C} {response : PackedResponse B C}
    {outerHistory : DDC.History B B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization (forwarding B) inner history response
      outerHistory innerHistory) :
    innerHistory = some history.toReceived ∧
      ∃ actual : DDC.Response history.toReceived,
        response = packResponse history.toReceived actual ∧
          actual ∈ inner history.toReceived := by
  induction factorization with
  | start middleFactorization valid =>
      simpa only [AttemptedHistory.toReceived] using
        middleFactorization.identity_outer_none rfl
  | afterInner previous middleFactorization valid inductionHypothesis =>
      rename_i prior query currentOuter currentInner reply response
        finalOuter finalInner
      obtain ⟨innerEqual, previousActual, previousEqual,
        previousResponds⟩ := inductionHypothesis
      cases Option.some.inj innerEqual
      cases previousActual with
      | inl actualQuery =>
          have queryEqual : query = actualQuery :=
            Sum.inl.inj previousEqual
          subst actualQuery
          simpa only [AttemptedHistory.toReceived] using
            middleFactorization.identity_outer
      | inr previousReply => cases previousEqual
  | afterOuter previous middleFactorization valid inductionHypothesis =>
      rename_i prior previousReply currentOuter currentInner outerQuery
        response finalOuter finalInner
      obtain ⟨innerEqual, previousActual, previousEqual,
        previousResponds⟩ := inductionHypothesis
      cases previousActual with
      | inl query => cases previousEqual
      | inr actualReply =>
          rw [innerEqual] at middleFactorization
          simpa only [AttemptedHistory.toReceived] using
            middleFactorization.identity_outer_some
              (by simp)

private theorem identity_outer_serialRaw_mem_of_admissible
    {B C : Interface.{u, v}} (inner : DDC B C)
    (history : DDC.History B C)
    (serialAdmissible : DDC.Raw.Admissible
      (serialRaw (forwarding B) inner) history)
    {response : DDC.Response history} (responds : response ∈ inner history) :
    response ∈ serialRaw (forwarding B) inner history := by
  have defined := serialRaw_complete (forwarding B) inner history
    serialAdmissible
  let actual := (serialRaw (forwarding B) inner history).get defined
  have actualResponds : actual ∈
      serialRaw (forwarding B) inner history := ⟨defined, rfl⟩
  obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
    factorization⟩ :=
    (mem_serialRaw_iff (forwarding B) inner history actual).mp actualResponds
  subst history
  obtain ⟨innerEqual, innerActual, packedEqual, innerResponds⟩ :=
    factorization.identity_outer
  have actualEqual : actual = innerActual :=
    packResponse_injective _ packedEqual
  have targetEqual : innerActual = response :=
    Part.mem_unique innerResponds responds
  exact (actualEqual.trans targetEqual) ▸ actualResponds

private theorem identity_outer_serialRaw_admissible
    {B C : Interface.{u, v}} (inner : DDC B C)
    {history : DDC.History B C}
    (admissible : DDC.Raw.Admissible inner.toFun history) :
    DDC.Raw.Admissible (serialRaw (forwarding B) inner) history := by
  induction admissible with
  | start outerQuery => exact .start outerQuery
  | afterInner prior responds reply inductionHypothesis =>
      exact .afterInner inductionHypothesis
        (identity_outer_serialRaw_mem_of_admissible inner _
          inductionHypothesis responds) reply
  | afterOuter prior responds outerQuery inductionHypothesis =>
      exact .afterOuter inductionHypothesis
        (identity_outer_serialRaw_mem_of_admissible inner _
          inductionHypothesis responds) outerQuery

end Internal

/--
Forwarding in the outer position is the serial identity.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “It satisfies
`id ◦ α = α ◦ id = α`.”
-/
@[simp]
theorem forwarding_serial_eq
    {B C : Interface.{u, v}} (inner : DDC B C) :
    serial (forwarding B) inner = inner := by
  -- Compare the two canonical DDC graphs at an arbitrary history and response.
  apply DDC.ext
  intro history response
  rw [mem_serial_iff]
  constructor
  -- A serial witness through forwarding projects to the original inner response.
  · intro membership
    obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
      factorization⟩ :=
      (mem_serialRaw_iff (forwarding B) inner history response).mp membership
    subst history
    obtain ⟨innerEqual, actual, packedEqual, responds⟩ :=
      factorization.identity_outer
    have responseEqual : response = actual :=
      packResponse_injective _ packedEqual
    exact responseEqual ▸ responds
  -- Conversely, an inner response supplies the unique forwarding factorization.
  · intro responds
    have innerAdmissible : DDC.Raw.Admissible inner.toFun history :=
      (inner.exactDomain history).mp responds.1
    exact identity_outer_serialRaw_mem_of_admissible inner history
      (identity_outer_serialRaw_admissible inner innerAdmissible) responds

namespace Internal

private theorem InnerPrefixFactorization.identity_inner_query
    {A B : Interface.{u, v}} {outer : DDC A B}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B B}
    {response : PackedResponse A B}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B B)}
    (factorization : InnerPrefixFactorization outer (forwarding B) outerHistory
      innerHistory response finalOuter finalInner)
    (lastInput : innerHistory.lastInput = Sum.inl innerHistory.lastOuter) :
    finalOuter = outerHistory ∧
      ∃ actual : DDC.Response outerHistory,
        response = packResponse outerHistory actual ∧
          actual ∈ outer outerHistory := by
  cases factorization with
  | innerQuery linked responds =>
      rename_i query
      have raw := (mem_forwarding_canonical_iff B innerHistory _).mp responds |>.2
      rw [lastInput] at raw
      have queryEqual : query = innerHistory.lastOuter := by simpa using raw
      subst query
      exact ⟨rfl, Sum.inl _, rfl, linked⟩
  | innerReply linked responds middleFactorization =>
      have raw := (mem_forwarding_canonical_iff B innerHistory _).mp responds |>.2
      rw [lastInput] at raw
      simp at raw

private theorem OuterPrefixFactorization.identity_inner
    {A B : Interface.{u, v}} {outer : DDC A B}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B B)}
    {response : PackedResponse A B}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B B)}
    (factorization : OuterPrefixFactorization outer (forwarding B) outerHistory
      innerHistory response finalOuter finalInner) :
    finalOuter = outerHistory ∧
      ∃ actual : DDC.Response outerHistory,
        response = packResponse outerHistory actual ∧
          actual ∈ outer outerHistory := by
  cases factorization with
  | outerReply responds => exact ⟨rfl, Sum.inr _, rfl, responds⟩
  | outerQueryFirst responds tail =>
      exact tail.identity_inner_query (by simp)
  | outerQueryNext closed responds tail =>
      exact tail.identity_inner_query (by simp)

private theorem InnerPrefixFactorization.identity_inner_reply
    {A B : Interface.{u, v}} {outer : DDC A B}
    {outerHistory : DDC.History A B}
    {previousInner : DDC.History B B} {query : B.query}
    {reply : Option (B.answer query)}
    {response : PackedResponse A B}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B B)}
    (factorization : InnerPrefixFactorization outer (forwarding B) outerHistory
      (previousInner.snocInner query reply) response finalOuter finalInner) :
    finalOuter = outerHistory.snocInner query reply ∧
      ∃ actual : DDC.Response (outerHistory.snocInner query reply),
        response = packResponse (outerHistory.snocInner query reply) actual ∧
          actual ∈ outer (outerHistory.snocInner query reply) := by
  cases factorization with
  | innerQuery linked responds =>
      have raw := (mem_forwarding_canonical_iff B _ _).mp responds |>.2
      have queryEqual : query = previousInner.lastOuter := by
        by_contra different
        simp [different] at raw
      subst query
      simp at raw
  | innerReply linked responds middleFactorization =>
      rename_i actualReply
      have raw := (mem_forwarding_canonical_iff B _ _).mp responds |>.2
      have queryEqual : query = previousInner.lastOuter := by
        by_contra different
        simp [different] at raw
      subst query
      simp at raw
      have replyEqual := Sum.inr.inj raw
      cases replyEqual
      exact middleFactorization.identity_inner

private theorem SerialFactorization.identity_inner
    {A B : Interface.{u, v}} {outer : DDC A B}
    {history : AttemptedHistory A B} {response : PackedResponse A B}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B B)}
    (factorization : SerialFactorization outer (forwarding B) history response
      outerHistory innerHistory) :
    outerHistory = history.toReceived ∧
      ∃ actual : DDC.Response history.toReceived,
        response = packResponse history.toReceived actual ∧
          actual ∈ outer history.toReceived := by
  induction factorization with
  | start middleFactorization valid =>
      simpa only [AttemptedHistory.toReceived] using
        middleFactorization.identity_inner
  | afterInner previous middleFactorization valid inductionHypothesis =>
      rename_i prior query currentOuter currentInner reply response
        finalOuter finalInner
      obtain ⟨outerEqual, previousActual, previousEqual,
        previousResponds⟩ := inductionHypothesis
      cases previousActual with
      | inl actualQuery =>
          have queryEqual : query = actualQuery := Sum.inl.inj previousEqual
          subst actualQuery
          subst currentOuter
          simpa only [AttemptedHistory.toReceived] using
            middleFactorization.identity_inner_reply
      | inr previousReply => cases previousEqual
  | afterOuter previous middleFactorization valid inductionHypothesis =>
      rename_i prior previousReply currentOuter currentInner outerQuery
        response finalOuter finalInner
      obtain ⟨outerEqual, previousActual, previousEqual,
        previousResponds⟩ := inductionHypothesis
      cases previousActual with
      | inl query => cases previousEqual
      | inr actualReply =>
          subst currentOuter
          simpa only [AttemptedHistory.toReceived] using
            middleFactorization.identity_inner

private theorem identity_inner_serialRaw_mem_of_admissible
    {A B : Interface.{u, v}} (outer : DDC A B)
    (history : DDC.History A B)
    (serialAdmissible : DDC.Raw.Admissible
      (serialRaw outer (forwarding B)) history)
    {response : DDC.Response history} (responds : response ∈ outer history) :
    response ∈ serialRaw outer (forwarding B) history := by
  have defined := serialRaw_complete outer (forwarding B) history
    serialAdmissible
  let actual := (serialRaw outer (forwarding B) history).get defined
  have actualResponds : actual ∈
      serialRaw outer (forwarding B) history := ⟨defined, rfl⟩
  obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
    factorization⟩ :=
    (mem_serialRaw_iff outer (forwarding B) history actual).mp actualResponds
  subst history
  obtain ⟨outerEqual, outerActual, packedEqual, outerResponds⟩ :=
    factorization.identity_inner
  have actualEqual : actual = outerActual :=
    packResponse_injective _ packedEqual
  have targetEqual : outerActual = response :=
    Part.mem_unique outerResponds responds
  exact (actualEqual.trans targetEqual) ▸ actualResponds

private theorem identity_inner_serialRaw_admissible
    {A B : Interface.{u, v}} (outer : DDC A B)
    {history : DDC.History A B}
    (admissible : DDC.Raw.Admissible outer.toFun history) :
    DDC.Raw.Admissible (serialRaw outer (forwarding B)) history := by
  induction admissible with
  | start outerQuery => exact .start outerQuery
  | afterInner prior responds reply inductionHypothesis =>
      exact .afterInner inductionHypothesis
        (identity_inner_serialRaw_mem_of_admissible outer _
          inductionHypothesis responds) reply
  | afterOuter prior responds outerQuery inductionHypothesis =>
      exact .afterOuter inductionHypothesis
        (identity_inner_serialRaw_mem_of_admissible outer _
          inductionHypothesis responds) outerQuery

end Internal

/--
Forwarding in the inner position is the serial identity.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “It satisfies
`id ◦ α = α ◦ id = α`.”
-/
@[simp]
theorem serial_forwarding_eq
    {A B : Interface.{u, v}} (outer : DDC A B) :
    serial outer (forwarding B) = outer := by
  -- Compare the two canonical DDC graphs at an arbitrary history and response.
  apply DDC.ext
  intro history response
  rw [mem_serial_iff]
  constructor
  -- A serial witness through inner forwarding projects to the outer response.
  · intro membership
    obtain ⟨attempted, historyEqual, outerHistory, innerHistory,
      factorization⟩ :=
      (mem_serialRaw_iff outer (forwarding B) history response).mp membership
    subst history
    obtain ⟨outerEqual, actual, packedEqual, responds⟩ :=
      factorization.identity_inner
    have responseEqual : response = actual :=
      packResponse_injective _ packedEqual
    exact responseEqual ▸ responds
  -- Conversely, an outer response supplies the unique forwarding factorization.
  · intro responds
    have outerAdmissible : DDC.Raw.Admissible outer.toFun history :=
      (outer.exactDomain history).mp responds.1
    exact identity_inner_serialRaw_mem_of_admissible outer history
      (identity_inner_serialRaw_admissible outer outerAdmissible) responds

namespace Internal

private def closedHistory {A : Interface.{u, v}} (history : _root_.RandomSystems.Ambient.History A) :
    DDC.History A Interface.empty.{u, v} where
  inputs :=
    ⟨history.1.map (fun query =>
      (Sum.inl query : ReceivedInput A Interface.empty.{u, v})), by
        intro empty
        exact history.2 (List.map_eq_nil_iff.mp empty)⟩
  outer := history
  projects := by simp

@[simp]
private theorem closedHistory_outer {A : Interface} (history : _root_.RandomSystems.Ambient.History A) :
    (closedHistory history).outer = history := rfl

private theorem closedHistory_injective {A : Interface.{u, v}} :
    Function.Injective (@closedHistory A) := by
  intro left right equal
  exact congrArg DDC.History.outer equal

private theorem receivedHistory_ext
    {A B : Interface.{u, v}} {left right : DDC.History A B}
    (inputsEqual : left.inputs = right.inputs)
    (outerEqual : left.outer = right.outer) : left = right := by
  cases left
  cases right
  simp_all

@[simp]
private theorem closedHistory_snoc {A : Interface} (history : _root_.RandomSystems.Ambient.History A)
    (query : A.query) :
    closedHistory (_root_.RandomSystems.Ambient.History.snoc history query) =
      (closedHistory history).snocOuter query := by
  apply receivedHistory_ext
  · apply _root_.RandomSystems.Ambient.History.ext
    simp [closedHistory, _root_.RandomSystems.Ambient.History.snoc,
      DDC.History.snocOuter]
  · rfl

private def rawClosedSystem {A : Interface.{u, v}} (system : DDS A) :
    DDC.Raw A Interface.empty.{u, v} :=
  fun history => Part.some (Sum.inr (system history.outer))

private theorem rawClosedSystem_complete {A : Interface} (system : DDS A) :
    DDC.Raw.Complete (rawClosedSystem system) := by
  intro history admissible
  simp [rawClosedSystem]

private theorem rawClosedSystem_branchFinite {A : Interface}
    (system : DDS A) :
    DDC.Raw.BranchFinite (rawClosedSystem system) := by
  apply WellFounded.intro
  intro history
  apply Acc.intro
  intro after continuation
  rcases continuation with ⟨query, reply, responds, equal⟩
  exact PEmpty.elim query

/-- Regard a DDS as the DDC that answers each outer query directly and has no
inner interface. This is an embedding into the same functional DDC carrier. -/
def ofDDS {A : Interface.{u, v}} (system : DDS A) :
    DDC A Interface.empty.{u, v} :=
  DDC.ofRaw (rawClosedSystem system) (rawClosedSystem_complete system)
    (rawClosedSystem_branchFinite system)

private theorem mem_ofDDS_iff {A : Interface} (system : DDS A)
    (history : DDC.History A Interface.empty.{u, v})
    (response : DDC.Response history) :
    response ∈ ofDDS system history ↔
      DDC.Raw.Admissible (rawClosedSystem system) history ∧
        response = Sum.inr (system history.outer) := by
  change response ∈ DDC.Raw.canonicalize (rawClosedSystem system) history ↔ _
  rw [DDC.Raw.mem_canonicalize_iff]
  constructor
  · rintro ⟨admissible, membership⟩
    refine ⟨admissible, ?_⟩
    have canonical : Sum.inr (system history.outer) ∈
        rawClosedSystem system history := ⟨trivial, rfl⟩
    exact Part.mem_unique membership canonical
  · rintro ⟨admissible, rfl⟩
    exact ⟨admissible, ⟨trivial, rfl⟩⟩

private theorem admissible_closedHistory_cons {A : Interface}
    (system : DDS A) (first : A.query) : ∀ rest : List A.query,
      DDC.Raw.Admissible (rawClosedSystem system)
        (closedHistory ⟨first :: rest, List.cons_ne_nil first rest⟩) := by
  intro rest
  induction rest using List.reverseRecOn with
  | nil => exact .start first
  | append_singleton prior query inductionHypothesis =>
      let priorHistory : _root_.RandomSystems.Ambient.History A :=
        ⟨first :: prior, List.cons_ne_nil first prior⟩
      have responds : Sum.inr (system priorHistory) ∈
          rawClosedSystem system (closedHistory priorHistory) :=
        ⟨trivial, rfl⟩
      have next := DDC.Raw.Admissible.afterOuter inductionHypothesis
        responds query
      have historyEqual :
          _root_.RandomSystems.Ambient.History.snoc priorHistory query =
            ⟨first :: prior ++ [query], by simp⟩ := by
        apply _root_.RandomSystems.Ambient.History.ext
        simp [priorHistory, _root_.RandomSystems.Ambient.History.snoc,
          List.cons_append]
      have encodedEqual := congrArg closedHistory historyEqual
      rw [closedHistory_snoc] at encodedEqual
      exact encodedEqual ▸ next

private theorem admissible_closedHistory {A : Interface} (system : DDS A) :
    ∀ history : _root_.RandomSystems.Ambient.History A,
      DDC.Raw.Admissible (rawClosedSystem system) (closedHistory history) := by
  rintro ⟨inputs, nonempty⟩
  cases inputs with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest => exact admissible_closedHistory_cons system first rest

private theorem ofDDS_responds {A : Interface} (system : DDS A)
    (history : _root_.RandomSystems.Ambient.History A) :
    Sum.inr (system history) ∈ ofDDS system (closedHistory history) := by
  change Sum.inr (system (closedHistory history).outer) ∈
    ofDDS system (closedHistory history)
  change Sum.inr (system (closedHistory history).outer) ∈
    DDC.Raw.canonicalize (rawClosedSystem system) (closedHistory history)
  apply (DDC.Raw.mem_canonicalize_iff (rawClosedSystem system)
    (closedHistory history) _).mpr
  exact ⟨admissible_closedHistory system history, ⟨trivial, rfl⟩⟩

private def closedState {A : Interface.{u, v}} :
    List A.query → Option (DDC.History A Interface.empty.{u, v})
  | [] => none
  | first :: rest => some (closedHistory
      ⟨first :: rest, List.cons_ne_nil first rest⟩)

@[simp]
private theorem closedState_nil {A : Interface} :
    closedState ([] : List A.query) = none := rfl

private theorem closedState_append {A : Interface} (prior : List A.query)
    (query : A.query) :
    closedState (prior ++ [query]) =
      some (closedHistory (innerHistory prior query)) := by
  cases prior with
  | nil => rfl
  | cons first rest =>
      change some (closedHistory
        ⟨first :: rest ++ [query], by simp⟩) =
        some (closedHistory (innerHistory (first :: rest) query))
      rfl

private theorem closedState_admissible {A : Interface} (system : DDS A)
    (prior : List A.query)
    (history : DDC.History A Interface.empty.{u, v})
    (equal : closedState prior = some history) :
    DDC.Raw.Admissible (ofDDS system).toFun history := by
  apply (DDC.Raw.admissible_canonicalize_iff
    (rawClosedSystem system) history).mpr
  cases prior with
  | nil => cases equal
  | cons first rest =>
      cases Option.some.inj equal
      exact admissible_closedHistory system _

private theorem closedState_closed {A : Interface} (system : DDS A)
    (prior : List A.query) : InnerClosed (ofDDS system)
      (closedState prior) := by
  cases prior with
  | nil => trivial
  | cons first rest =>
      refine ⟨system ⟨first :: rest, by simp⟩, ?_⟩
      exact ofDDS_responds system _

private theorem closedInner_last {A : Interface.{u, v}} (prior : List A.query)
    (query : A.query) :
    (closedHistory (innerHistory prior query) :
      DDC.History A Interface.empty.{u, v}).lastOuter = query := by
  change (innerHistory prior query).last = query
  exact last_innerHistory prior query

private theorem snocInner_closedInner_eq {A B : Interface.{u, v}} (system : DDS B)
    (history : DDC.History A B) (prior : List B.query)
    (query : B.query) :
    history.snocInner
        (closedHistory (innerHistory prior query) :
          DDC.History B Interface.empty.{u, v}).lastOuter
        (system (innerHistory prior query)) =
      history.snocInner query (innerReplyAt system prior query) := by
  have lastEqual :
      (closedHistory (innerHistory prior query) :
        DDC.History B Interface.empty.{u, v}).lastOuter = query :=
    closedInner_last prior query
  apply receivedHistory_ext
  · apply _root_.RandomSystems.Ambient.History.ext
    simp only [DDC.History.snocInner,
      _root_.RandomSystems.Ambient.History.coe_snoc]
    apply congrArg (fun input : DDC.History.InnerReply B =>
      (show List (DDC.History.Input A B) from history.inputs.queries) ++
        [(Sum.inr input : DDC.History.Input A B)])
    apply Sigma.ext lastEqual
    unfold innerReplyAt
    exact (cast_heq _ _).symm
  · rfl

private def appendOuterAttempts {A : Interface.{u, v}} :
    AttemptedHistory A Interface.empty.{u, v} → List A.query →
      AttemptedHistory A Interface.empty.{u, v} :=
  List.foldl AttemptedHistory.afterOuter

private def closedAttempted {A : Interface.{u, v}} (history : _root_.RandomSystems.Ambient.History A) :
    AttemptedHistory A Interface.empty.{u, v} :=
  appendOuterAttempts (.start (_root_.RandomSystems.Ambient.History.head history))
    (_root_.RandomSystems.Ambient.History.tail history)

private theorem appendOuterAttempts_toReceived {A : Interface}
    (attempted : AttemptedHistory A Interface.empty.{u, v})
    (queries : List A.query) :
    (appendOuterAttempts attempted queries).toReceived =
      List.foldl DDC.History.snocOuter attempted.toReceived queries := by
  induction queries generalizing attempted with
  | nil => rfl
  | cons query rest inductionHypothesis =>
      simpa [appendOuterAttempts, List.foldl_cons] using
        inductionHypothesis (.afterOuter attempted query)

private theorem closedAttempted_toReceived {A : Interface} (history : _root_.RandomSystems.Ambient.History A) :
    (closedAttempted history).toReceived = closedHistory history := by
  rcases history with ⟨inputs, nonempty⟩
  cases inputs with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      change (appendOuterAttempts (.start first) rest).toReceived =
        closedHistory ⟨first :: rest, nonempty⟩
      rw [appendOuterAttempts_toReceived]
      induction rest using List.reverseRecOn with
      | nil => rfl
      | append_singleton prior query inductionHypothesis =>
          rw [List.foldl_append,
            inductionHypothesis (List.cons_ne_nil first prior)]
          simp only [List.foldl_cons, List.foldl_nil]
          rw [← closedHistory_snoc]
          apply congrArg closedHistory
          apply _root_.RandomSystems.Ambient.History.ext
          simp [_root_.RandomSystems.Ambient.History.snoc]

private theorem selectReply_eq_of_packed_eq
    {A : Interface.{u, v}} {query : A.query}
    (reply : Option (A.answer query)) (packed : InnerReply A)
    (equal : (⟨query, reply⟩ : InnerReply A) = packed) :
    Attachment.selectReply query packed = reply := by
  cases equal
  simp [Attachment.selectReply]

private theorem pack_selectReply_eq
    {A : Interface.{u, v}} (query : A.query) (packed : InnerReply A)
    (equal : packed.1 = query) :
    (⟨query, Attachment.selectReply query packed⟩ : InnerReply A) = packed := by
  rcases packed with ⟨selected, reply⟩
  cases equal
  simp [Attachment.selectReply]

private theorem InnerPrefixFactorization.of_inner_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {left right : DDC.History B C} {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (equal : left = right)
    (factorization : InnerPrefixFactorization outer inner outerHistory right
      response finalOuter finalInner) :
    InnerPrefixFactorization outer inner outerHistory left response
      finalOuter finalInner := by
  cases equal
  exact factorization

private theorem OuterPrefixFactorization.of_inner_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {left right : Option (DDC.History B C)}
    {response : PackedResponse A C} {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (equal : left = right)
    (factorization : OuterPrefixFactorization outer inner outerHistory right
      response finalOuter finalInner) :
    OuterPrefixFactorization outer inner outerHistory left response
      finalOuter finalInner := by
  cases equal
  exact factorization

private theorem OuterPrefixFactorization.of_outer_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {left right : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C} {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (equal : left = right)
    (factorization : OuterPrefixFactorization outer inner right innerHistory
      response finalOuter finalInner) :
    OuterPrefixFactorization outer inner left innerHistory response
      finalOuter finalInner := by
  cases equal
  exact factorization

private theorem SerialFactorization.of_response_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {left right : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (equal : left = right)
    (factorization : SerialFactorization outer inner history right
      finalOuter finalInner) :
    SerialFactorization outer inner history left finalOuter finalInner := by
  cases equal
  exact factorization

private theorem prependCompatibleInnerQuery
    {A B : Interface.{u, v}} (converter : DDC A B) (system : DDS B)
    (history : DDC.History A B) (prior : List B.query)
    (query : B.query) {response : PackedResponse A Interface.empty}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B Interface.empty)}
    (responds : Sum.inl query ∈ converter history)
    (tail : OuterPrefixFactorization converter (ofDDS system)
      (history.snocInner query (innerReplyAt system prior query))
      (closedState (prior ++ [query])) response finalOuter finalInner) :
    OuterPrefixFactorization converter (ofDDS system) history
      (closedState prior) response finalOuter finalInner := by
  cases prior with
  | nil =>
      let inner : DDC.History B Interface.empty :=
        closedHistory (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory [] query)
      have stateEqual : closedState ([] ++ [query]) = some inner := by
        simpa [inner] using closedState_append ([] : List B.query) query
      have stateTail : OuterPrefixFactorization converter
          (ofDDS system)
          (history.snocInner query (innerReplyAt system [] query))
          (some inner) response finalOuter finalInner :=
        OuterPrefixFactorization.of_inner_eq stateEqual tail
      have outerEqual :
          history.snocInner inner.lastOuter
              (system (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory [] query)) =
            history.snocInner query (innerReplyAt system [] query) :=
        snocInner_closedInner_eq system history [] query
      have adjustedTail : OuterPrefixFactorization converter
          (ofDDS system)
          (history.snocInner inner.lastOuter
            (system (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory [] query)))
          (some inner) response finalOuter finalInner :=
        OuterPrefixFactorization.of_outer_eq outerEqual stateTail
      have linked : Sum.inl inner.lastOuter ∈ converter history := by
        simpa [inner, closedInner_last] using responds
      have systemResponds :
          Sum.inr (system (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory [] query)) ∈
            ofDDS system inner := ofDDS_responds system _
      have innerPrefix : InnerPrefixFactorization converter
          (ofDDS system) history inner response finalOuter finalInner :=
        .innerReply linked systemResponds adjustedTail
      have singletonEqual : DDC.History.singleton query = inner := by
        apply receivedHistory_ext
        · apply _root_.RandomSystems.Ambient.History.ext
          rfl
        · rfl
      have singletonPrefix : InnerPrefixFactorization converter
          (ofDDS system) history (DDC.History.singleton query)
          response finalOuter finalInner :=
        InnerPrefixFactorization.of_inner_eq singletonEqual innerPrefix
      have factorization : OuterPrefixFactorization converter
          (ofDDS system) history none response finalOuter finalInner :=
        .outerQueryFirst responds singletonPrefix
      change OuterPrefixFactorization converter (ofDDS system) history
        none response finalOuter finalInner
      exact factorization
  | cons first rest =>
      let priorHistory : _root_.RandomSystems.Ambient.History B :=
        ⟨first :: rest, List.cons_ne_nil first rest⟩
      let inner : DDC.History B Interface.empty :=
        closedHistory
          (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory (first :: rest) query)
      have stateEqual : closedState ((first :: rest) ++ [query]) =
          some inner := by
        simpa [inner] using closedState_append (first :: rest) query
      have stateTail : OuterPrefixFactorization converter
          (ofDDS system)
          (history.snocInner query
            (innerReplyAt system (first :: rest) query))
          (some inner) response finalOuter finalInner :=
        OuterPrefixFactorization.of_inner_eq stateEqual tail
      have outerEqual :
          history.snocInner inner.lastOuter
              (system (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory
                (first :: rest) query)) =
            history.snocInner query
              (innerReplyAt system (first :: rest) query) :=
        snocInner_closedInner_eq system history (first :: rest) query
      have adjustedTail : OuterPrefixFactorization converter
          (ofDDS system)
          (history.snocInner inner.lastOuter
            (system (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory
              (first :: rest) query)))
          (some inner) response finalOuter finalInner :=
        OuterPrefixFactorization.of_outer_eq outerEqual stateTail
      have linked : Sum.inl inner.lastOuter ∈ converter history := by
        simpa [inner, closedInner_last] using responds
      have systemResponds :
          Sum.inr (system (_root_.RandomSystems.Ambient.DDC.Internal.innerHistory
            (first :: rest) query)) ∈ ofDDS system inner :=
        ofDDS_responds system _
      have innerPrefix : InnerPrefixFactorization converter
          (ofDDS system) history inner response finalOuter finalInner :=
        .innerReply linked systemResponds adjustedTail
      have nextInnerEqual :
          (closedHistory priorHistory).snocOuter query = inner := by
        rw [← closedHistory_snoc]
        apply congrArg closedHistory
        apply _root_.RandomSystems.Ambient.History.ext
        simp [priorHistory, _root_.RandomSystems.Ambient.DDC.Internal.innerHistory,
          _root_.RandomSystems.Ambient.History.snoc]
      have priorPrefix : InnerPrefixFactorization converter
          (ofDDS system) history
          ((closedHistory priorHistory).snocOuter query) response
          finalOuter finalInner :=
        InnerPrefixFactorization.of_inner_eq nextInnerEqual innerPrefix
      have currentClosed : InnerClosed (ofDDS system)
          (some (closedHistory priorHistory)) := by
        simpa [closedState, priorHistory] using
          closedState_closed system (first :: rest)
      have factorization : OuterPrefixFactorization converter
          (ofDDS system) history (some (closedHistory priorHistory))
          response finalOuter finalInner :=
        .outerQueryNext currentClosed responds priorPrefix
      change OuterPrefixFactorization converter (ofDDS system) history
        (some (closedHistory priorHistory)) response finalOuter finalInner
      exact factorization

private theorem compatibleFrom_serialFactorization
    {A B : Interface.{u, v}} (converter : DDC A B) (system : DDS B)
    {history : DDC.History A B} {innerPrior : List B.query}
    {remainingOuter : List A.query}
    {inputs : List (ReceivedInput A B)}
    {responses : List (PackedResponse A B)} {final : InnerReply A}
    (compatible : Attachment.CompatibleFrom converter system history innerPrior
      remainingOuter inputs responses final)
    (outerAdmissible : DDC.Raw.Admissible converter.toFun history)
    (attempted : AttemptedHistory A Interface.empty.{u, v})
    (lastEqual : history.lastOuter = attempted.toReceived.lastOuter)
    (integrate : ∀ {response finalOuter finalInner},
      OuterPrefixFactorization converter (ofDDS system) history
          (closedState innerPrior) response finalOuter finalInner →
      PrefixEndpointValid converter (ofDDS system) response
          finalOuter finalInner →
      SerialFactorization converter (ofDDS system) attempted response
          finalOuter finalInner) :
    ∃ finalOuter finalInner,
      SerialFactorization converter (ofDDS system)
        (appendOuterAttempts attempted remainingOuter) (Sum.inr final)
        finalOuter finalInner := by
  induction compatible generalizing attempted with
  | @innerQuery history innerPrior remainingOuter query tailInputs
      tailResponses final responds tail inductionHypothesis =>
      have nextAdmissible : DDC.Raw.Admissible converter.toFun
          (history.snocInner query
            (innerReplyAt system innerPrior query)) :=
        .afterInner outerAdmissible responds _
      apply inductionHypothesis nextAdmissible attempted lastEqual
      intro response finalOuter finalInner tailPrefix tailValid
      exact integrate
        (prependCompatibleInnerQuery converter system history innerPrior query
          responds tailPrefix)
        tailValid
  | @outerLast history innerPrior reply responds =>
      let factorization : OuterPrefixFactorization converter (ofDDS system)
          history (closedState innerPrior)
          (Sum.inr ⟨history.lastOuter, reply⟩) history
          (closedState innerPrior) := .outerReply responds
      have valid : PrefixEndpointValid converter (ofDDS system)
          (Sum.inr ⟨history.lastOuter, reply⟩) history
          (closedState innerPrior) := factorization.endpointValid outerAdmissible
        (closedState_admissible system innerPrior)
        (closedState_closed system innerPrior)
      refine ⟨history, closedState innerPrior, ?_⟩
      simpa [appendOuterAttempts] using integrate factorization valid
  | @outerNext history innerPrior reply nextOuter rest tailInputs
      tailResponses final responds tail inductionHypothesis =>
      let factorization : OuterPrefixFactorization converter (ofDDS system)
          history (closedState innerPrior)
          (Sum.inr ⟨history.lastOuter, reply⟩) history
          (closedState innerPrior) := .outerReply responds
      have valid : PrefixEndpointValid converter (ofDDS system)
          (Sum.inr ⟨history.lastOuter, reply⟩) history
          (closedState innerPrior) := factorization.endpointValid outerAdmissible
        (closedState_admissible system innerPrior)
        (closedState_closed system innerPrior)
      have previous := integrate factorization valid
      let adjustedReply : Option
          (A.answer attempted.toReceived.lastOuter) :=
        cast (congrArg (fun query => Option (A.answer query)) lastEqual) reply
      have packedEqual :
          (⟨history.lastOuter, reply⟩ : InnerReply A) =
            ⟨attempted.toReceived.lastOuter, adjustedReply⟩ := by
        apply Sigma.ext lastEqual
        exact (cast_heq
          (congrArg (fun query => Option (A.answer query)) lastEqual)
          reply).symm
      have adjustedPrevious : SerialFactorization converter
          (ofDDS system) attempted
          (Sum.inr ⟨attempted.toReceived.lastOuter, adjustedReply⟩)
          history (closedState innerPrior) :=
        SerialFactorization.of_response_eq
          (congrArg Sum.inr packedEqual).symm previous
      have nextAdmissible : DDC.Raw.Admissible converter.toFun
          (history.snocOuter nextOuter) :=
        .afterOuter outerAdmissible responds nextOuter
      apply inductionHypothesis nextAdmissible
        (.afterOuter attempted nextOuter) (by simp)
      intro response finalOuter finalInner nextPrefix nextValid
      exact .afterOuter adjustedPrevious nextPrefix nextValid

private theorem compatible_serialFactorization
    {A B : Interface.{u, v}} (converter : DDC A B) (system : DDS B)
    (outerHistory : _root_.RandomSystems.Ambient.History A)
    (transcript : Attachment.Transcript A B)
    (compatible : Attachment.Compatible converter system outerHistory transcript) :
    ∃ finalOuter finalInner,
      SerialFactorization converter (ofDDS system)
        (closedAttempted outerHistory)
        (Sum.inr transcript.final)
        finalOuter finalInner := by
  have startAdmissible : DDC.Raw.Admissible converter.toFun
      (DDC.History.singleton
        (_root_.RandomSystems.Ambient.History.head outerHistory)) :=
    .start (_root_.RandomSystems.Ambient.History.head outerHistory)
  have factorized := compatibleFrom_serialFactorization converter system
    compatible startAdmissible
    (.start (_root_.RandomSystems.Ambient.History.head outerHistory)) rfl
    (fun middle valid => SerialFactorization.start middle valid)
  simpa [closedAttempted] using factorized

private theorem serial_ofDDS_responds
    {A B : Interface.{u, v}} (converter : DDC A B) (system : DDS B)
    (outerHistory : _root_.RandomSystems.Ambient.History A) :
    Sum.inr (applySystem converter system outerHistory) ∈
      serial converter (ofDDS system) (closedHistory outerHistory) := by
  obtain ⟨transcript, compatible⟩ :=
    Attachment.exists_compatible converter system outerHistory
  obtain ⟨finalOuter, finalInner, factorization⟩ :=
    compatible_serialFactorization converter system outerHistory transcript compatible
  have attemptedEqual := closedAttempted_toReceived outerHistory
  have attemptedLastEqual :
      (closedAttempted outerHistory).toReceived.lastOuter =
        outerHistory.last := by
    rw [attemptedEqual]
    rfl
  have finalQueryEqual :
      transcript.final.1 = outerHistory.last :=
    (factorization.endpointValid.selectedOuter _ rfl).trans
      (factorization.outerLast_eq.trans attemptedLastEqual)
  have appliedEqual :
      applySystem converter system outerHistory =
        Attachment.selectReply outerHistory.last transcript.final := by
    apply (applySystem_eq_iff converter system outerHistory _).mpr
    exact ⟨transcript, compatible,
      (Attachment.selectReply_heq_second outerHistory.last transcript.final
        finalQueryEqual).symm⟩
  have packedEqual :
      packResponse (closedHistory outerHistory)
          (Sum.inr (applySystem converter system outerHistory)) =
        Sum.inr transcript.final := by
    apply congrArg Sum.inr
    rw [appliedEqual]
    change (⟨outerHistory.last,
      Attachment.selectReply outerHistory.last transcript.final⟩ : InnerReply A) =
      transcript.final
    exact pack_selectReply_eq outerHistory.last _ finalQueryEqual
  apply (mem_serial_iff converter (ofDDS system)
    (closedHistory outerHistory)
    (Sum.inr (applySystem converter system outerHistory))).mpr
  apply (mem_serialRaw_iff converter (ofDDS system)
    (closedHistory outerHistory)
    (Sum.inr (applySystem converter system outerHistory))).mpr
  refine ⟨closedAttempted outerHistory, attemptedEqual, finalOuter,
    finalInner, ?_⟩
  exact SerialFactorization.of_response_eq packedEqual factorization

private theorem exists_closedHistory_of_admissible
    {A : Interface.{u, v}}
    (converter : DDC A Interface.empty.{u, v})
    {history : DDC.History A Interface.empty.{u, v}}
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    ∃ outerHistory : _root_.RandomSystems.Ambient.History A, closedHistory outerHistory = history := by
  induction admissible with
  | start query =>
      exact ⟨⟨[query], by simp⟩, rfl⟩
  | @afterInner history query prior responds reply inductionHypothesis =>
      exact PEmpty.elim query
  | @afterOuter history prior reply responds query inductionHypothesis =>
      obtain ⟨outerHistory, historyEqual⟩ := inductionHypothesis
      subst history
      exact ⟨_root_.RandomSystems.Ambient.History.snoc outerHistory query,
        closedHistory_snoc outerHistory query⟩

private theorem serial_ofDDS_eq
    {A B : Interface.{u, v}} (converter : DDC A B) (system : DDS B) :
    serial converter (ofDDS system) =
      ofDDS (applySystem converter system) := by
  apply DDC.ext
  intro history response
  constructor
  · intro membership
    have admissible : DDC.Raw.Admissible
        (serial converter (ofDDS system)).toFun history :=
      ((serial converter (ofDDS system)).exactDomain history).mp
        membership.1
    obtain ⟨outerHistory, historyEqual⟩ :=
      exists_closedHistory_of_admissible
        (serial converter (ofDDS system)) admissible
    subst history
    have canonical :=
      serial_ofDDS_responds converter system outerHistory
    have responseEqual := Part.mem_unique membership canonical
    exact responseEqual ▸
      ofDDS_responds (applySystem converter system) outerHistory
  · intro membership
    have admissible : DDC.Raw.Admissible
        (ofDDS (applySystem converter system)).toFun history :=
      ((ofDDS (applySystem converter system)).exactDomain history).mp
        membership.1
    obtain ⟨outerHistory, historyEqual⟩ :=
      exists_closedHistory_of_admissible
        (ofDDS (applySystem converter system)) admissible
    subst history
    have canonical :=
      ofDDS_responds (applySystem converter system) outerHistory
    have responseEqual := Part.mem_unique membership canonical
    exact responseEqual ▸
      serial_ofDDS_responds converter system outerHistory

private theorem ofDDS_injective {A : Interface.{u, v}} :
    Function.Injective (@ofDDS A) := by
  intro left right equal
  funext history
  have leftResponds := ofDDS_responds left history
  rw [equal] at leftResponds
  have rightResponds := ofDDS_responds right history
  exact Sum.inr.inj (Part.mem_unique leftResponds rightResponds)

private structure ThreeHistories
    (A B C D : Interface.{u, v}) where
  outer : Option (DDC.History A B)
  middle : Option (DDC.History B C)
  inner : Option (DDC.History C D)

private def ThreeHistories.empty
    {A B C D : Interface.{u, v}} : ThreeHistories A B C D :=
  ⟨none, none, none⟩

private def receiveOuter
    {A B : Interface.{u, v}} :
    Option (DDC.History A B) → A.query → DDC.History A B
  | none, query => .singleton query
  | some history, query => history.snocOuter query

private def receiveInner
    {A B : Interface.{u, v}}
    (history : DDC.History A B) (reply : InnerReply B) :
    DDC.History A B :=
  history.snocInner reply.1 reply.2

private def ThreeHistories.receiveOuterAtOuter
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (query : A.query) : ThreeHistories A B C D :=
  { histories with outer := some (receiveOuter histories.outer query) }

private def ThreeHistories.receiveInnerAtOuter
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (reply : InnerReply B) (history : DDC.History A B) :
    ThreeHistories A B C D :=
  { histories with outer := some (receiveInner history reply) }

private def ThreeHistories.receiveOuterAtMiddle
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (query : B.query) : ThreeHistories A B C D :=
  { histories with middle := some (receiveOuter histories.middle query) }

private def ThreeHistories.receiveInnerAtMiddle
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (reply : InnerReply C) (history : DDC.History B C) :
    ThreeHistories A B C D :=
  { histories with middle := some (receiveInner history reply) }

private def ThreeHistories.receiveOuterAtInner
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (query : C.query) : ThreeHistories A B C D :=
  { histories with inner := some (receiveOuter histories.inner query) }

private def ThreeHistories.receiveInnerAtInner
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (reply : InnerReply D) (history : DDC.History C D) :
    ThreeHistories A B C D :=
  { histories with inner := some (receiveInner history reply) }

private def ThreeHistories.withFront
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (outer : DDC.History A B)
    (middle : Option (DDC.History B C)) : ThreeHistories A B C D :=
  { histories with outer := some outer, middle := middle }

private def ThreeHistories.withBack
    {A B C D : Interface.{u, v}} (histories : ThreeHistories A B C D)
    (middle : DDC.History B C)
    (inner : Option (DDC.History C D)) : ThreeHistories A B C D :=
  { histories with middle := some middle, inner := inner }

mutual

private inductive ThreeOuterFactorization
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    ThreeHistories A B C D → DDC.History A B →
      ThreeHistories A B C D → PackedResponse A D → Prop
  | outerReply {before current reply}
      (stored : before.outer = some current)
      (responds : Sum.inr reply ∈ outer current) :
      ThreeOuterFactorization outer middle inner before current before
        (Sum.inr ⟨current.lastOuter, reply⟩)
  | outerQuery {before current query after response}
      (stored : before.outer = some current)
      (responds : Sum.inl query ∈ outer current)
      (tail : ThreeMiddleFactorization outer middle inner
        (before.receiveOuterAtMiddle query)
        (receiveOuter before.middle query) after response) :
      ThreeOuterFactorization outer middle inner before current after response

private inductive ThreeMiddleFactorization
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    ThreeHistories A B C D → DDC.History B C →
      ThreeHistories A B C D → PackedResponse A D → Prop
  | middleReply {before current reply outerHistory after response}
      (stored : before.middle = some current)
      (outerStored : before.outer = some outerHistory)
      (responds : Sum.inr reply ∈ middle current)
      (tail : ThreeOuterFactorization outer middle inner
        (before.receiveInnerAtOuter ⟨current.lastOuter, reply⟩ outerHistory)
        (receiveInner outerHistory ⟨current.lastOuter, reply⟩)
        after response) :
      ThreeMiddleFactorization outer middle inner before current after response
  | middleQuery {before current query after response}
      (stored : before.middle = some current)
      (responds : Sum.inl query ∈ middle current)
      (tail : ThreeInnerFactorization outer middle inner
        (before.receiveOuterAtInner query)
        (receiveOuter before.inner query) after response) :
      ThreeMiddleFactorization outer middle inner before current after response

private inductive ThreeInnerFactorization
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    ThreeHistories A B C D → DDC.History C D →
      ThreeHistories A B C D → PackedResponse A D → Prop
  | innerReply {before current reply middleHistory after response}
      (stored : before.inner = some current)
      (middleStored : before.middle = some middleHistory)
      (responds : Sum.inr reply ∈ inner current)
      (tail : ThreeMiddleFactorization outer middle inner
        (before.receiveInnerAtMiddle ⟨current.lastOuter, reply⟩ middleHistory)
        (receiveInner middleHistory ⟨current.lastOuter, reply⟩)
        after response) :
      ThreeInnerFactorization outer middle inner before current after response
  | innerQuery {before current query}
      (stored : before.inner = some current)
      (responds : Sum.inl query ∈ inner current) :
      ThreeInnerFactorization outer middle inner before current before
        (Sum.inl query)

end

private theorem OuterPrefixFactorization.toThreeReply
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {outerHistory : DDC.History A B}
    {middleHistory : Option (DDC.History B C)}
    {response : PackedResponse A C} {reply : InnerReply A}
    {finalOuter : DDC.History A B}
    {finalMiddle : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer middle outerHistory
      middleHistory response finalOuter finalMiddle)
    (responseEqual : response = Sum.inr reply)
    {before : ThreeHistories A B C D}
    (outerStored : before.outer = some outerHistory)
    (middleStored : before.middle = middleHistory) :
    ThreeOuterFactorization outer middle inner before outerHistory
      (before.withFront finalOuter finalMiddle) (Sum.inr reply) := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory middleHistory response finalOuter
          finalMiddle _ =>
        ∀ {reply : InnerReply A}, response = Sum.inr reply →
          ∀ {before : ThreeHistories A B C D},
            before.outer = some outerHistory →
            before.middle = some middleHistory →
            ThreeMiddleFactorization outer middle inner before middleHistory
              (before.withFront finalOuter finalMiddle) (Sum.inr reply))
      generalizing reply before with
  | outerReply responds =>
      rename_i currentOuter currentMiddle currentReply
      cases Sum.inr.inj responseEqual
      have beforeEqual : before.withFront currentOuter currentMiddle = before := by
        cases before
        simp_all [ThreeHistories.withFront]
      simpa only [beforeEqual] using
        (ThreeOuterFactorization.outerReply (middle := middle) (inner := inner)
          outerStored responds)
  | outerQueryFirst responds tail inductionHypothesis =>
      rename_i currentOuter query currentResponse currentFinalOuter
        currentFinalMiddle
      apply ThreeOuterFactorization.outerQuery outerStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtMiddle query)
        (by simp [ThreeHistories.receiveOuterAtMiddle, outerStored])
        (by simp [ThreeHistories.receiveOuterAtMiddle, receiveOuter,
          middleStored])
      have currentEqual : receiveOuter before.middle query =
          DDC.History.singleton query := by
        rw [middleStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtMiddle,
        ThreeHistories.withFront] using tail'
  | outerQueryNext closed responds tail inductionHypothesis =>
      rename_i currentOuter currentMiddle query currentResponse
        currentFinalOuter currentFinalMiddle
      apply ThreeOuterFactorization.outerQuery outerStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtMiddle query)
        (by simp [ThreeHistories.receiveOuterAtMiddle, outerStored])
        (by simp [ThreeHistories.receiveOuterAtMiddle, receiveOuter,
          middleStored])
      have currentEqual : receiveOuter before.middle query =
          currentMiddle.snocOuter query := by
        rw [middleStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtMiddle,
        ThreeHistories.withFront] using tail'
  | innerQuery linked responds => simp_all
  | innerReply linked responds tail inductionHypothesis =>
      apply ThreeMiddleFactorization.middleReply
      · assumption
      · assumption
      · exact responds
      · apply inductionHypothesis (by assumption)
        · rfl
        · assumption

private theorem InnerPrefixFactorization.toThreeReply
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {outerHistory : DDC.History A B}
    {middleHistory : DDC.History B C}
    {response : PackedResponse A C} {reply : InnerReply A}
    {finalOuter : DDC.History A B}
    {finalMiddle : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer middle outerHistory
      middleHistory response finalOuter finalMiddle)
    (responseEqual : response = Sum.inr reply)
    {before : ThreeHistories A B C D}
    (outerStored : before.outer = some outerHistory)
    (middleStored : before.middle = some middleHistory) :
    ThreeMiddleFactorization outer middle inner before middleHistory
      (before.withFront finalOuter finalMiddle) (Sum.inr reply) := by
  cases factorization with
  | innerQuery linked responds => simp_all
  | innerReply linked responds tail =>
      apply ThreeMiddleFactorization.middleReply middleStored outerStored
        responds
      apply tail.toThreeReply responseEqual
      · rfl
      · exact middleStored

private theorem OuterPrefixFactorization.toThreeQuery
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {outerHistory : DDC.History A B}
    {middleHistory : Option (DDC.History B C)}
    {response : PackedResponse A C} {query : C.query}
    {finalOuter : DDC.History A B}
    {finalMiddle : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer middle outerHistory
      middleHistory response finalOuter finalMiddle)
    (responseEqual : response = Sum.inl query)
    {before : ThreeHistories A B C D}
    (outerStored : before.outer = some outerHistory)
    (middleStored : before.middle = middleHistory)
    {after : ThreeHistories A B C D} {final : PackedResponse A D}
    (tail : ThreeInnerFactorization outer middle inner
      ((before.withFront finalOuter finalMiddle).receiveOuterAtInner query)
      (receiveOuter before.inner query) after final) :
    ThreeOuterFactorization outer middle inner before outerHistory after final := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory middleHistory response finalOuter
          finalMiddle _ =>
        ∀ {query : C.query}, response = Sum.inl query →
          ∀ {before : ThreeHistories A B C D},
            before.outer = some outerHistory →
            before.middle = some middleHistory →
            ∀ {after : ThreeHistories A B C D}
              {final : PackedResponse A D},
              ThreeInnerFactorization outer middle inner
                ((before.withFront finalOuter finalMiddle).receiveOuterAtInner
                  query)
                (receiveOuter before.inner query) after final →
              ThreeMiddleFactorization outer middle inner before middleHistory
                after final)
      generalizing query before after final with
  | outerReply responds => simp_all
  | outerQueryFirst responds sourceTail inductionHypothesis =>
      rename_i currentOuter nextQuery currentResponse currentFinalOuter
        currentFinalMiddle
      apply ThreeOuterFactorization.outerQuery outerStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtMiddle nextQuery)
        (by simp [ThreeHistories.receiveOuterAtMiddle, outerStored])
        (by simp [ThreeHistories.receiveOuterAtMiddle, receiveOuter,
          middleStored])
        (by simpa [ThreeHistories.receiveOuterAtMiddle,
          ThreeHistories.withFront, ThreeHistories.receiveOuterAtInner]
          using tail)
      have currentEqual : receiveOuter before.middle nextQuery =
          DDC.History.singleton nextQuery := by
        rw [middleStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtMiddle] using tail'
  | outerQueryNext closed responds sourceTail inductionHypothesis =>
      rename_i currentOuter currentMiddle nextQuery currentResponse
        currentFinalOuter currentFinalMiddle
      apply ThreeOuterFactorization.outerQuery outerStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtMiddle nextQuery)
        (by simp [ThreeHistories.receiveOuterAtMiddle, outerStored])
        (by simp [ThreeHistories.receiveOuterAtMiddle, receiveOuter,
          middleStored])
        (by simpa [ThreeHistories.receiveOuterAtMiddle,
          ThreeHistories.withFront, ThreeHistories.receiveOuterAtInner]
          using tail)
      have currentEqual : receiveOuter before.middle nextQuery =
          currentMiddle.snocOuter nextQuery := by
        rw [middleStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtMiddle] using tail'
  | innerQuery linked responds =>
      apply ThreeMiddleFactorization.middleQuery (by assumption) responds
      simp_all [ThreeHistories.withFront,
        ThreeHistories.receiveOuterAtInner]
  | innerReply linked responds sourceTail inductionHypothesis =>
      apply ThreeMiddleFactorization.middleReply
      · assumption
      · assumption
      · exact responds
      · apply inductionHypothesis (by assumption)
        · rfl
        · assumption
        · simpa [ThreeHistories.receiveInnerAtOuter,
            ThreeHistories.withFront,
            ThreeHistories.receiveOuterAtInner]

private theorem InnerPrefixFactorization.toThreeQuery
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {outerHistory : DDC.History A B}
    {middleHistory : DDC.History B C}
    {response : PackedResponse A C} {query : C.query}
    {finalOuter : DDC.History A B}
    {finalMiddle : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer middle outerHistory
      middleHistory response finalOuter finalMiddle)
    (responseEqual : response = Sum.inl query)
    {before : ThreeHistories A B C D}
    (outerStored : before.outer = some outerHistory)
    (middleStored : before.middle = some middleHistory)
    {after : ThreeHistories A B C D} {final : PackedResponse A D}
    (tail : ThreeInnerFactorization outer middle inner
      ((before.withFront finalOuter finalMiddle).receiveOuterAtInner query)
      (receiveOuter before.inner query) after final) :
    ThreeMiddleFactorization outer middle inner before middleHistory after final := by
  cases factorization with
  | innerQuery linked responds =>
      cases Sum.inl.inj responseEqual
      apply ThreeMiddleFactorization.middleQuery middleStored responds
      simpa [ThreeHistories.withFront,
        ThreeHistories.receiveOuterAtInner, outerStored, middleStored] using tail
  | innerReply linked responds sourceTail =>
      apply ThreeMiddleFactorization.middleReply middleStored outerStored
        responds
      apply sourceTail.toThreeQuery responseEqual
      · rfl
      · exact middleStored
      · simpa [ThreeHistories.receiveInnerAtOuter,
          ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, outerStored, middleStored] using tail

private theorem OuterPrefixFactorization.toThreeInside
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {middleHistory : DDC.History B C}
    {innerHistory : Option (DDC.History C D)}
    {response : PackedResponse B D} {query : D.query}
    {finalMiddle : DDC.History B C}
    {finalInner : Option (DDC.History C D)}
    (factorization : OuterPrefixFactorization middle inner middleHistory
      innerHistory response finalMiddle finalInner)
    (responseEqual : response = Sum.inl query)
    {before : ThreeHistories A B C D}
    (middleStored : before.middle = some middleHistory)
    (innerStored : before.inner = innerHistory) :
    ThreeMiddleFactorization outer middle inner before middleHistory
      (before.withBack finalMiddle finalInner) (Sum.inl query) := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun middleHistory innerHistory response finalMiddle
          finalInner _ =>
        ∀ {query : D.query}, response = Sum.inl query →
          ∀ {before : ThreeHistories A B C D},
            before.middle = some middleHistory →
            before.inner = some innerHistory →
            ThreeInnerFactorization outer middle inner before innerHistory
              (before.withBack finalMiddle finalInner) (Sum.inl query))
      generalizing query before with
  | outerReply responds => simp_all
  | outerQueryFirst responds sourceTail inductionHypothesis =>
      rename_i currentMiddle nextQuery currentResponse currentFinalMiddle
        currentFinalInner
      apply ThreeMiddleFactorization.middleQuery middleStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtInner nextQuery)
        (by simp [ThreeHistories.receiveOuterAtInner, middleStored])
        (by simp [ThreeHistories.receiveOuterAtInner, receiveOuter,
          innerStored])
      have currentEqual : receiveOuter before.inner nextQuery =
          DDC.History.singleton nextQuery := by
        rw [innerStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtInner,
        ThreeHistories.withBack] using tail'
  | outerQueryNext closed responds sourceTail inductionHypothesis =>
      rename_i currentMiddle currentInner nextQuery currentResponse
        currentFinalMiddle currentFinalInner
      apply ThreeMiddleFactorization.middleQuery middleStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtInner nextQuery)
        (by simp [ThreeHistories.receiveOuterAtInner, middleStored])
        (by simp [ThreeHistories.receiveOuterAtInner, receiveOuter,
          innerStored])
      have currentEqual : receiveOuter before.inner nextQuery =
          currentInner.snocOuter nextQuery := by
        rw [innerStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtInner,
        ThreeHistories.withBack] using tail'
  | innerQuery linked responds =>
      rename_i currentMiddle currentInner sourceQuery targetQuery equal before
        currentMiddleStored currentInnerStored
      cases Sum.inl.inj equal
      have current := ThreeInnerFactorization.innerQuery (outer := outer)
        (middle := middle) (inner := inner) currentInnerStored responds
      have beforeEqual : before.withBack currentMiddle (some currentInner) =
          before := by
        cases before
        simp_all [ThreeHistories.withBack]
      simpa only [beforeEqual] using current
  | innerReply linked responds sourceTail inductionHypothesis =>
      apply ThreeInnerFactorization.innerReply
      · assumption
      · assumption
      · exact responds
      · apply inductionHypothesis (by assumption)
        · rfl
        · assumption

private theorem InnerPrefixFactorization.toThreeInside
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {middleHistory : DDC.History B C}
    {innerHistory : DDC.History C D}
    {response : PackedResponse B D} {query : D.query}
    {finalMiddle : DDC.History B C}
    {finalInner : Option (DDC.History C D)}
    (factorization : InnerPrefixFactorization middle inner middleHistory
      innerHistory response finalMiddle finalInner)
    (responseEqual : response = Sum.inl query)
    {before : ThreeHistories A B C D}
    (middleStored : before.middle = some middleHistory)
    (innerStored : before.inner = some innerHistory) :
    ThreeInnerFactorization outer middle inner before innerHistory
      (before.withBack finalMiddle finalInner) (Sum.inl query) := by
  cases factorization with
  | innerQuery linked responds =>
      cases Sum.inl.inj responseEqual
      have current := ThreeInnerFactorization.innerQuery (outer := outer)
        (middle := middle) (inner := inner) innerStored responds
      have beforeEqual : before.withBack middleHistory (some innerHistory) =
          before := by
        cases before
        simp_all [ThreeHistories.withBack]
      simpa only [beforeEqual] using current
  | innerReply linked responds sourceTail =>
      apply ThreeInnerFactorization.innerReply innerStored middleStored responds
      apply sourceTail.toThreeInside responseEqual
      · rfl
      · exact innerStored

private theorem OuterPrefixFactorization.toThreeOutside
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {middleHistory : DDC.History B C}
    {innerHistory : Option (DDC.History C D)}
    {response : PackedResponse B D} {reply : InnerReply B}
    {finalMiddle : DDC.History B C}
    {finalInner : Option (DDC.History C D)}
    (factorization : OuterPrefixFactorization middle inner middleHistory
      innerHistory response finalMiddle finalInner)
    (responseEqual : response = Sum.inr reply)
    {before : ThreeHistories A B C D}
    (middleStored : before.middle = some middleHistory)
    (innerStored : before.inner = innerHistory)
    {outerHistory : DDC.History A B}
    (outerStored : before.outer = some outerHistory)
    {after : ThreeHistories A B C D} {final : PackedResponse A D}
    (tail : ThreeOuterFactorization outer middle inner
      ((before.withBack finalMiddle finalInner).receiveInnerAtOuter
        reply outerHistory)
      (receiveInner outerHistory reply) after final) :
    ThreeMiddleFactorization outer middle inner before middleHistory after final := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun middleHistory innerHistory response finalMiddle
          finalInner _ =>
        ∀ {reply : InnerReply B}, response = Sum.inr reply →
          ∀ {before : ThreeHistories A B C D},
            before.middle = some middleHistory →
            before.inner = some innerHistory →
            ∀ {outerHistory : DDC.History A B},
              before.outer = some outerHistory →
              ∀ {after : ThreeHistories A B C D}
                {final : PackedResponse A D},
                ThreeOuterFactorization outer middle inner
                  ((before.withBack finalMiddle finalInner).receiveInnerAtOuter
                    reply outerHistory)
                  (receiveInner outerHistory reply) after final →
                ThreeInnerFactorization outer middle inner before innerHistory
                  after final)
      generalizing reply before outerHistory after final with
  | outerReply responds =>
      rename_i currentMiddle currentInner currentReply
      cases Sum.inr.inj responseEqual
      apply ThreeMiddleFactorization.middleReply middleStored outerStored responds
      simpa [ThreeHistories.withBack,
        ThreeHistories.receiveInnerAtOuter, middleStored, innerStored] using tail
  | outerQueryFirst responds sourceTail inductionHypothesis =>
      rename_i currentMiddle nextQuery currentResponse currentFinalMiddle
        currentFinalInner
      apply ThreeMiddleFactorization.middleQuery middleStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtInner nextQuery)
        (by simp [ThreeHistories.receiveOuterAtInner, middleStored])
        (by simp [ThreeHistories.receiveOuterAtInner, receiveOuter,
          innerStored])
        (outerHistory := outerHistory)
        (by simp [ThreeHistories.receiveOuterAtInner, outerStored])
        (by simpa [ThreeHistories.receiveOuterAtInner,
          ThreeHistories.withBack, ThreeHistories.receiveInnerAtOuter]
          using tail)
      have currentEqual : receiveOuter before.inner nextQuery =
          DDC.History.singleton nextQuery := by
        rw [innerStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtInner] using tail'
  | outerQueryNext closed responds sourceTail inductionHypothesis =>
      rename_i currentMiddle currentInner nextQuery currentResponse
        currentFinalMiddle currentFinalInner
      apply ThreeMiddleFactorization.middleQuery middleStored responds
      have tail' := inductionHypothesis responseEqual
        (before := before.receiveOuterAtInner nextQuery)
        (by simp [ThreeHistories.receiveOuterAtInner, middleStored])
        (by simp [ThreeHistories.receiveOuterAtInner, receiveOuter,
          innerStored])
        (outerHistory := outerHistory)
        (by simp [ThreeHistories.receiveOuterAtInner, outerStored])
        (by simpa [ThreeHistories.receiveOuterAtInner,
          ThreeHistories.withBack, ThreeHistories.receiveInnerAtOuter]
          using tail)
      have currentEqual : receiveOuter before.inner nextQuery =
          currentInner.snocOuter nextQuery := by
        rw [innerStored]
        rfl
      simpa only [currentEqual, ThreeHistories.receiveOuterAtInner] using tail'
  | innerQuery linked responds => simp_all
  | innerReply linked responds sourceTail inductionHypothesis =>
      apply ThreeInnerFactorization.innerReply
      · assumption
      · assumption
      · exact responds
      · apply inductionHypothesis (by assumption)
        · rfl
        · assumption
        · assumption
        · simpa [ThreeHistories.receiveInnerAtMiddle,
            ThreeHistories.withBack,
            ThreeHistories.receiveInnerAtOuter]

private theorem InnerPrefixFactorization.toThreeOutside
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {middleHistory : DDC.History B C}
    {innerHistory : DDC.History C D}
    {response : PackedResponse B D} {reply : InnerReply B}
    {finalMiddle : DDC.History B C}
    {finalInner : Option (DDC.History C D)}
    (factorization : InnerPrefixFactorization middle inner middleHistory
      innerHistory response finalMiddle finalInner)
    (responseEqual : response = Sum.inr reply)
    {before : ThreeHistories A B C D}
    (middleStored : before.middle = some middleHistory)
    (innerStored : before.inner = some innerHistory)
    {outerHistory : DDC.History A B}
    (outerStored : before.outer = some outerHistory)
    {after : ThreeHistories A B C D} {final : PackedResponse A D}
    (tail : ThreeOuterFactorization outer middle inner
      ((before.withBack finalMiddle finalInner).receiveInnerAtOuter
        reply outerHistory)
      (receiveInner outerHistory reply) after final) :
    ThreeInnerFactorization outer middle inner before innerHistory after final := by
  cases factorization with
  | innerQuery linked responds => simp_all
  | innerReply linked responds sourceTail =>
      apply ThreeInnerFactorization.innerReply innerStored middleStored responds
      apply sourceTail.toThreeOutside responseEqual
      · rfl
      · exact innerStored
      · simpa [ThreeHistories.receiveInnerAtMiddle] using outerStored
      · simpa [ThreeHistories.receiveInnerAtMiddle,
          ThreeHistories.withBack,
          ThreeHistories.receiveInnerAtOuter] using tail

mutual

private theorem ThreeOuterFactorization.unique
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {current : DDC.History A B}
    {leftAfter rightAfter : ThreeHistories A B C D}
    {leftResponse rightResponse : PackedResponse A D}
    (left : ThreeOuterFactorization outer middle inner before current
      leftAfter leftResponse)
    (right : ThreeOuterFactorization outer middle inner before current
      rightAfter rightResponse) :
    leftAfter = rightAfter ∧ leftResponse = rightResponse := by
  induction left using ThreeOuterFactorization.rec
      (motive_2 := fun before current leftAfter leftResponse _ =>
        ∀ {rightAfter rightResponse},
          ThreeMiddleFactorization outer middle inner before current
            rightAfter rightResponse →
          leftAfter = rightAfter ∧ leftResponse = rightResponse)
      (motive_3 := fun before current leftAfter leftResponse _ =>
        ∀ {rightAfter rightResponse},
          ThreeInnerFactorization outer middle inner before current
            rightAfter rightResponse →
          leftAfter = rightAfter ∧ leftResponse = rightResponse)
      generalizing rightAfter rightResponse with
  | outerReply leftStored leftResponds =>
      cases right with
      | outerReply rightStored rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          exact ⟨rfl, rfl⟩
      | outerQuery rightStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | outerQuery leftStored leftResponds leftTail inductionHypothesis =>
      cases right with
      | outerReply rightStored rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQuery rightStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact inductionHypothesis rightTail
  | middleReply leftStored leftOuterStored leftResponds leftTail
      inductionHypothesis right =>
      cases right with
      | middleReply rightStored rightOuterStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          have historyEqual := Option.some.inj
            (leftOuterStored.symm.trans rightOuterStored)
          cases historyEqual
          exact inductionHypothesis rightTail
      | middleQuery rightStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | middleQuery leftStored leftResponds leftTail inductionHypothesis right =>
      cases right with
      | middleReply rightStored rightOuterStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | middleQuery rightStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact inductionHypothesis rightTail
  | innerReply leftStored leftMiddleStored leftResponds leftTail
      inductionHypothesis right =>
      cases right with
      | innerReply rightStored rightMiddleStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          have historyEqual := Option.some.inj
            (leftMiddleStored.symm.trans rightMiddleStored)
          cases historyEqual
          exact inductionHypothesis rightTail
      | innerQuery rightStored rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
  | innerQuery leftStored leftResponds right =>
      cases right with
      | innerReply rightStored rightMiddleStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | innerQuery rightStored rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact ⟨rfl, rfl⟩

private theorem ThreeMiddleFactorization.unique
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {current : DDC.History B C}
    {leftAfter rightAfter : ThreeHistories A B C D}
    {leftResponse rightResponse : PackedResponse A D}
    (left : ThreeMiddleFactorization outer middle inner before current
      leftAfter leftResponse)
    (right : ThreeMiddleFactorization outer middle inner before current
      rightAfter rightResponse) :
    leftAfter = rightAfter ∧ leftResponse = rightResponse := by
  induction left using ThreeMiddleFactorization.rec
      (motive_1 := fun before current leftAfter leftResponse _ =>
        ∀ {rightAfter rightResponse},
          ThreeOuterFactorization outer middle inner before current
            rightAfter rightResponse →
          leftAfter = rightAfter ∧ leftResponse = rightResponse)
      (motive_3 := fun before current leftAfter leftResponse _ =>
        ∀ {rightAfter rightResponse},
          ThreeInnerFactorization outer middle inner before current
            rightAfter rightResponse →
          leftAfter = rightAfter ∧ leftResponse = rightResponse)
      generalizing rightAfter rightResponse with
  | outerReply leftStored leftResponds right =>
      cases right with
      | outerReply rightStored rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          exact ⟨rfl, rfl⟩
      | outerQuery rightStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | outerQuery leftStored leftResponds leftTail inductionHypothesis right =>
      cases right with
      | outerReply rightStored rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQuery rightStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact inductionHypothesis rightTail
  | middleReply leftStored leftOuterStored leftResponds leftTail
      inductionHypothesis =>
      cases right with
      | middleReply rightStored rightOuterStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          have historyEqual := Option.some.inj
            (leftOuterStored.symm.trans rightOuterStored)
          cases historyEqual
          exact inductionHypothesis rightTail
      | middleQuery rightStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | middleQuery leftStored leftResponds leftTail inductionHypothesis =>
      cases right with
      | middleReply rightStored rightOuterStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | middleQuery rightStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact inductionHypothesis rightTail
  | innerReply leftStored leftMiddleStored leftResponds leftTail
      inductionHypothesis right =>
      cases right with
      | innerReply rightStored rightMiddleStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          have historyEqual := Option.some.inj
            (leftMiddleStored.symm.trans rightMiddleStored)
          cases historyEqual
          exact inductionHypothesis rightTail
      | innerQuery rightStored rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
  | innerQuery leftStored leftResponds right =>
      cases right with
      | innerReply rightStored rightMiddleStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | innerQuery rightStored rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact ⟨rfl, rfl⟩

private theorem ThreeInnerFactorization.unique
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {current : DDC.History C D}
    {leftAfter rightAfter : ThreeHistories A B C D}
    {leftResponse rightResponse : PackedResponse A D}
    (left : ThreeInnerFactorization outer middle inner before current
      leftAfter leftResponse)
    (right : ThreeInnerFactorization outer middle inner before current
      rightAfter rightResponse) :
    leftAfter = rightAfter ∧ leftResponse = rightResponse := by
  induction left using ThreeInnerFactorization.rec
      (motive_1 := fun before current leftAfter leftResponse _ =>
        ∀ {rightAfter rightResponse},
          ThreeOuterFactorization outer middle inner before current
            rightAfter rightResponse →
          leftAfter = rightAfter ∧ leftResponse = rightResponse)
      (motive_2 := fun before current leftAfter leftResponse _ =>
        ∀ {rightAfter rightResponse},
          ThreeMiddleFactorization outer middle inner before current
            rightAfter rightResponse →
          leftAfter = rightAfter ∧ leftResponse = rightResponse)
      generalizing rightAfter rightResponse with
  | outerReply leftStored leftResponds right =>
      cases right with
      | outerReply rightStored rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          exact ⟨rfl, rfl⟩
      | outerQuery rightStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | outerQuery leftStored leftResponds leftTail inductionHypothesis right =>
      cases right with
      | outerReply rightStored rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
      | outerQuery rightStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact inductionHypothesis rightTail
  | middleReply leftStored leftOuterStored leftResponds leftTail
      inductionHypothesis right =>
      cases right with
      | middleReply rightStored rightOuterStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          have historyEqual := Option.some.inj
            (leftOuterStored.symm.trans rightOuterStored)
          cases historyEqual
          exact inductionHypothesis rightTail
      | middleQuery rightStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
  | middleQuery leftStored leftResponds leftTail inductionHypothesis right =>
      cases right with
      | middleReply rightStored rightOuterStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | middleQuery rightStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact inductionHypothesis rightTail
  | innerReply leftStored leftMiddleStored leftResponds leftTail
      inductionHypothesis =>
      cases right with
      | innerReply rightStored rightMiddleStored rightResponds rightTail =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj equal
          have historyEqual := Option.some.inj
            (leftMiddleStored.symm.trans rightMiddleStored)
          cases historyEqual
          exact inductionHypothesis rightTail
      | innerQuery rightStored rightResponds =>
          cases Part.mem_unique leftResponds rightResponds
  | innerQuery leftStored leftResponds =>
      cases right with
      | innerReply rightStored rightMiddleStored rightResponds rightTail =>
          cases Part.mem_unique leftResponds rightResponds
      | innerQuery rightStored rightResponds =>
          have equal := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj equal
          exact ⟨rfl, rfl⟩

end

private inductive ThreeHistoryFactorization
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    AttemptedHistory A D → ThreeHistories A B C D →
      PackedResponse A D → Prop
  | start {query after response}
      (segment : ThreeOuterFactorization outer middle inner
        (ThreeHistories.empty.receiveOuterAtOuter query)
        (DDC.History.singleton query) after response) :
      ThreeHistoryFactorization outer middle inner (.start query) after response
  | afterInner {history before query reply current after response}
      (previous : ThreeHistoryFactorization outer middle inner history before
        (Sum.inl query))
      (stored : before.inner = some current)
      (segment : ThreeInnerFactorization outer middle inner
        (before.receiveInnerAtInner ⟨query, reply⟩ current)
        (receiveInner current ⟨query, reply⟩) after response) :
      ThreeHistoryFactorization outer middle inner
        (.afterInner history query reply) after response
  | afterOuter {history before previousReply query current after response}
      (previous : ThreeHistoryFactorization outer middle inner history before
        (Sum.inr ⟨history.toReceived.lastOuter, previousReply⟩))
      (stored : before.outer = some current)
      (segment : ThreeOuterFactorization outer middle inner
        (before.receiveOuterAtOuter query)
        (current.snocOuter query) after response) :
      ThreeHistoryFactorization outer middle inner
        (.afterOuter history query) after response

private theorem ThreeHistoryFactorization.unique
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {history : AttemptedHistory A D}
    {leftAfter rightAfter : ThreeHistories A B C D}
    {leftResponse rightResponse : PackedResponse A D}
    (left : ThreeHistoryFactorization outer middle inner history leftAfter
      leftResponse)
    (right : ThreeHistoryFactorization outer middle inner history rightAfter
      rightResponse) :
    leftAfter = rightAfter ∧ leftResponse = rightResponse := by
  induction left generalizing rightAfter rightResponse with
  | start leftSegment =>
      cases right with
      | start rightSegment => exact leftSegment.unique rightSegment
  | afterInner leftPrevious leftStored leftSegment inductionHypothesis =>
      cases right with
      | afterInner rightPrevious rightStored rightSegment =>
          obtain ⟨beforeEqual, responseEqual⟩ :=
            inductionHypothesis rightPrevious
          cases beforeEqual
          cases Sum.inl.inj responseEqual
          have currentEqual := Option.some.inj
            (leftStored.symm.trans rightStored)
          cases currentEqual
          exact leftSegment.unique rightSegment
  | afterOuter leftPrevious leftStored leftSegment inductionHypothesis =>
      cases right with
      | afterOuter rightPrevious rightStored rightSegment =>
          obtain ⟨beforeEqual, responseEqual⟩ :=
            inductionHypothesis rightPrevious
          cases beforeEqual
          cases Sum.inr.inj responseEqual
          have currentEqual := Option.some.inj
            (leftStored.symm.trans rightStored)
          cases currentEqual
          exact leftSegment.unique rightSegment

private theorem SerialFactorization.start_prefix
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {query : A.query} {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner (.start query) response
      finalOuter finalInner) :
    OuterPrefixFactorization outer inner (DDC.History.singleton query)
      none response finalOuter finalInner := by
  cases factorization
  assumption

private theorem SerialFactorization.afterInner_prefix
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C}
    {beforeOuter : DDC.History A B}
    {beforeInner : DDC.History B C} {query : C.query}
    (before : SerialFactorization outer inner history (Sum.inl query)
      beforeOuter (some beforeInner))
    (reply : Option (C.answer query))
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner
      (.afterInner history query reply) response finalOuter finalInner) :
    InnerPrefixFactorization outer inner beforeOuter
      (beforeInner.snocInner query reply) response finalOuter finalInner := by
  cases factorization
  obtain ⟨responseEqual, outerEqual, innerEqual⟩ :=
    before.unique (by assumption)
  cases Sum.inl.inj responseEqual
  cases outerEqual
  cases Option.some.inj innerEqual
  assumption

private theorem SerialFactorization.afterOuter_prefix
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C}
    {beforeOuter : DDC.History A B}
    {beforeInner : Option (DDC.History B C)}
    {reply : Option (A.answer history.toReceived.lastOuter)}
    (before : SerialFactorization outer inner history
      (Sum.inr ⟨history.toReceived.lastOuter, reply⟩)
      beforeOuter beforeInner)
    (query : A.query)
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner
      (.afterOuter history query) response finalOuter finalInner) :
    OuterPrefixFactorization outer inner
      (beforeOuter.snocOuter query) beforeInner response finalOuter
        finalInner := by
  cases factorization
  obtain ⟨responseEqual, outerEqual, innerEqual⟩ :=
    before.unique (by assumption)
  cases Sum.inr.inj responseEqual
  cases outerEqual
  cases innerEqual
  assumption

private def ThreeGlobalGraph
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (history : DDC.History A D) (response : DDC.Response history) :
    Prop :=
  ∃ attempted, attempted.toReceived = history ∧
    ∃ after, ThreeHistoryFactorization outer middle inner attempted after
      (packResponse history response)

private theorem ThreeGlobalGraph.unique
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {history : DDC.History A D}
    {left right : DDC.Response history}
    (leftGraph : ThreeGlobalGraph outer middle inner history left)
    (rightGraph : ThreeGlobalGraph outer middle inner history right) :
    left = right := by
  obtain ⟨leftAttempted, leftHistory, leftAfter, leftFactorization⟩ :=
    leftGraph
  obtain ⟨rightAttempted, rightHistory, rightAfter, rightFactorization⟩ :=
    rightGraph
  have attemptedEqual : leftAttempted = rightAttempted :=
    AttemptedHistory.toReceived_injective
      (leftHistory.trans rightHistory.symm)
  subst rightAttempted
  have packedEqual :=
    (ThreeHistoryFactorization.unique leftFactorization rightFactorization).2
  exact packResponse_injective history packedEqual

private theorem ThreeHistoryFactorization.mem_of_graph
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    (candidate : DDC A D)
    (toGraph : ∀ history response, response ∈ candidate history →
      ThreeGlobalGraph outer middle inner history response)
    {history : AttemptedHistory A D}
    {after : ThreeHistories A B C D} {response : PackedResponse A D}
    (factorization : ThreeHistoryFactorization outer middle inner history after
      response) :
    ∀ {actual : DDC.Response history.toReceived},
      packResponse history.toReceived actual = response →
      actual ∈ candidate history.toReceived := by
  induction factorization with
  | start segment =>
      rename_i query after response
      intro actual packedEqual
      have admissible : DDC.Raw.Admissible candidate.toFun
          (DDC.History.singleton query) := .start query
      have chosen := candidate.response_mem _ admissible
      have chosenGraph := toGraph _ _ chosen
      have currentGraph : ThreeGlobalGraph outer middle inner
          (DDC.History.singleton query) actual := by
        refine ⟨.start query, rfl, after, ?_⟩
        change ThreeHistoryFactorization outer middle inner
          (AttemptedHistory.start query) after
            (packResponse (AttemptedHistory.start query).toReceived actual)
        rw [packedEqual]
        exact .start segment
      have actualEqual := ThreeGlobalGraph.unique chosenGraph currentGraph
      exact actualEqual ▸ chosen
  | afterInner previous stored segment inductionHypothesis =>
      intro actual packedEqual
      rename_i prior before query reply current after response
      have previousMembership := inductionHypothesis
        (actual := Sum.inl query) rfl
      have previousAdmissible :=
        (candidate.exactDomain prior.toReceived).mp previousMembership.1
      have admissible : DDC.Raw.Admissible candidate.toFun
          (prior.toReceived.snocInner query reply) :=
        .afterInner previousAdmissible previousMembership reply
      have chosen := candidate.response_mem _ admissible
      have chosenGraph := toGraph _ _ chosen
      have currentGraph : ThreeGlobalGraph outer middle inner
          (prior.toReceived.snocInner query reply) actual := by
        refine ⟨.afterInner prior query reply, rfl, after, ?_⟩
        have packedEqual' :
            packResponse (prior.toReceived.snocInner query reply) actual =
              response := by
          simpa using packedEqual
        rw [packedEqual']
        exact .afterInner previous stored segment
      have actualEqual := ThreeGlobalGraph.unique chosenGraph currentGraph
      exact actualEqual ▸ chosen
  | afterOuter previous stored segment inductionHypothesis =>
      intro actual packedEqual
      rename_i prior before previousReply query current after response
      have previousMembership := inductionHypothesis
        (actual := Sum.inr previousReply) rfl
      have previousAdmissible :=
        (candidate.exactDomain prior.toReceived).mp previousMembership.1
      have admissible : DDC.Raw.Admissible candidate.toFun
          (prior.toReceived.snocOuter query) :=
        .afterOuter previousAdmissible previousMembership query
      have chosen := candidate.response_mem _ admissible
      have chosenGraph := toGraph _ _ chosen
      have currentGraph : ThreeGlobalGraph outer middle inner
          (prior.toReceived.snocOuter query) actual := by
        refine ⟨.afterOuter prior query, rfl, after, ?_⟩
        have packedEqual' :
            packResponse (prior.toReceived.snocOuter query) actual =
              response := by
          simpa using packedEqual
        rw [packedEqual']
        exact .afterOuter previous stored segment
      have actualEqual := ThreeGlobalGraph.unique chosenGraph currentGraph
      exact actualEqual ▸ chosen

/-! The next declarations retain exactly the endpoint information needed to
translate a parenthesized serial factorization into the parenthesis-free
three-history graph.  They are proof relations, not additional semantics. -/

private inductive ThreeFrontFactorization
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (before : ThreeHistories A B C D) :
    Bool → ThreeHistories A B C D → PackedResponse A D → Prop
  | outer {current after response}
      (factorization : ThreeOuterFactorization outer middle inner before
        current after response) :
      ThreeFrontFactorization outer middle inner before false after response
  | middle {current after response}
      (factorization : ThreeMiddleFactorization outer middle inner before
        current after response) :
      ThreeFrontFactorization outer middle inner before true after response

private inductive ThreeBackFactorization
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (before : ThreeHistories A B C D) :
    Bool → ThreeHistories A B C D → PackedResponse A D → Prop
  | middle {current after response}
      (factorization : ThreeMiddleFactorization outer middle inner before
        current after response) :
      ThreeBackFactorization outer middle inner before false after response
  | inner {current after response}
      (factorization : ThreeInnerFactorization outer middle inner before
        current after response) :
      ThreeBackFactorization outer middle inner before true after response

private theorem ThreeMiddleFactorization.current_eq
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before after : ThreeHistories A B C D}
    {current expected : DDC.History B C}
    {response : PackedResponse A D}
    (factorization : ThreeMiddleFactorization outer middle inner before current
      after response)
    (expectedStored : before.middle = some expected) : current = expected := by
  cases factorization with
  | middleReply stored outerStored responds tail =>
      exact Option.some.inj (stored.symm.trans expectedStored)
  | middleQuery stored responds tail =>
      exact Option.some.inj (stored.symm.trans expectedStored)

private theorem ThreeOuterFactorization.current_eq
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before after : ThreeHistories A B C D}
    {current expected : DDC.History A B}
    {response : PackedResponse A D}
    (factorization : ThreeOuterFactorization outer middle inner before current
      after response)
    (expectedStored : before.outer = some expected) : current = expected := by
  cases factorization with
  | outerReply stored responds =>
      exact Option.some.inj (stored.symm.trans expectedStored)
  | outerQuery stored responds tail =>
      exact Option.some.inj (stored.symm.trans expectedStored)

private theorem ThreeInnerFactorization.current_eq
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before after : ThreeHistories A B C D}
    {current expected : DDC.History C D}
    {response : PackedResponse A D}
    (factorization : ThreeInnerFactorization outer middle inner before current
      after response)
    (expectedStored : before.inner = some expected) : current = expected := by
  cases factorization with
  | innerReply stored middleStored responds tail =>
      exact Option.some.inj (stored.symm.trans expectedStored)
  | innerQuery stored responds =>
      exact Option.some.inj (stored.symm.trans expectedStored)
private inductive LeftSourceCase
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (before : ThreeHistories A B C D) :
    (history : DDC.History A C) → DDC.Response history →
      Bool → Prop
  | outer {history response attempted sourceOuter sourceMiddle
      finalOuter finalMiddle}
      (source : SerialFactorization outer middle attempted
        (packResponse history response) finalOuter finalMiddle)
      (historyEqual : attempted.toReceived = history)
      (sourceFactorization : OuterPrefixFactorization outer middle sourceOuter
        sourceMiddle (packResponse history response) finalOuter finalMiddle)
      (outerStored : before.outer = some sourceOuter)
      (middleStored : before.middle = sourceMiddle) :
      LeftSourceCase outer middle inner before history response false
  | middle {history response attempted sourceOuter sourceMiddle
      finalOuter finalMiddle}
      (source : SerialFactorization outer middle attempted
        (packResponse history response) finalOuter finalMiddle)
      (historyEqual : attempted.toReceived = history)
      (sourceFactorization : InnerPrefixFactorization outer middle sourceOuter
        sourceMiddle (packResponse history response) finalOuter finalMiddle)
      (outerStored : before.outer = some sourceOuter)
      (middleStored : before.middle = some sourceMiddle) :
      LeftSourceCase outer middle inner before history response true

private inductive LeftEndpoint
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    (history : DDC.History A C) → PackedResponse A D →
      Option (DDC.History C D) → ThreeHistories A B C D → Prop
  | inside {history attempted sourceOuter sourceMiddle sourceQuery
      thirdHistory query}
      (source : SerialFactorization outer middle attempted
        (packResponse history (Sum.inl sourceQuery)) sourceOuter
          (some sourceMiddle))
      (historyEqual : attempted.toReceived = history)
      (responds : Sum.inl query ∈ inner thirdHistory) :
      LeftEndpoint outer middle inner history (Sum.inl query)
        (some thirdHistory)
        ⟨some sourceOuter, some sourceMiddle, some thirdHistory⟩
  | outside {history attempted sourceOuter sourceMiddle thirdHistory reply}
      (source : SerialFactorization outer middle attempted
        (packResponse history (Sum.inr reply)) sourceOuter sourceMiddle)
      (historyEqual : attempted.toReceived = history) :
      LeftEndpoint outer middle inner history
        (Sum.inr ⟨history.lastOuter, reply⟩) thirdHistory
          ⟨some sourceOuter, sourceMiddle, thirdHistory⟩

private theorem LeftEndpoint.outside_data
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {history : DDC.History A C} {response : PackedResponse A D}
    {thirdHistory : Option (DDC.History C D)}
    {before : ThreeHistories A B C D}
    (endpoint : LeftEndpoint outer middle inner history response thirdHistory
      before)
    {packed : InnerReply A} (responseEqual : response = Sum.inr packed) :
    ∃ attempted sourceOuter sourceMiddle reply,
      SerialFactorization outer middle attempted
          (packResponse history (Sum.inr reply)) sourceOuter sourceMiddle ∧
        attempted.toReceived = history ∧
          before = ⟨some sourceOuter, sourceMiddle, thirdHistory⟩ := by
  cases endpoint with
  | inside source historyEqual responds => cases responseEqual
  | outside source historyEqual =>
      exact ⟨_, _, _, _, source, historyEqual, rfl⟩

private theorem LeftSourceCase.toReply
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {history : DDC.History A C} {response : DDC.Response history}
    {reply : Option (A.answer history.lastOuter)}
    {phase : Bool}
    (sourceCase : LeftSourceCase outer middle inner before history response phase)
    (responseEqual : response = Sum.inr reply) :
    ∃ after,
      ThreeFrontFactorization outer middle inner before phase after
          (Sum.inr ⟨history.lastOuter, reply⟩) ∧
        LeftEndpoint outer middle inner history
          (Sum.inr ⟨history.lastOuter, reply⟩) before.inner after := by
  cases sourceCase with
  | outer source historyEqual sourceFactorization outerStored middleStored =>
      rename_i attempted sourceOuter sourceMiddle finalOuter finalMiddle
      cases responseEqual
      refine ⟨before.withFront finalOuter finalMiddle,
        ThreeFrontFactorization.outer (current := sourceOuter) ?_, ?_⟩
      · exact sourceFactorization.toThreeReply rfl outerStored middleStored
      · simpa [ThreeHistories.withFront] using
          LeftEndpoint.outside (inner := inner) source historyEqual
  | middle source historyEqual sourceFactorization outerStored middleStored =>
      rename_i attempted sourceOuter sourceMiddle finalOuter finalMiddle
      cases responseEqual
      refine ⟨before.withFront finalOuter finalMiddle,
        ThreeFrontFactorization.middle (current := sourceMiddle) ?_, ?_⟩
      · exact sourceFactorization.toThreeReply rfl outerStored middleStored
      · simpa [ThreeHistories.withFront] using
          LeftEndpoint.outside (inner := inner) source historyEqual

private theorem LeftSourceCase.toQuery
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {history : DDC.History A C} {response : DDC.Response history}
    {query : C.query}
    {phase : Bool}
    (sourceCase : LeftSourceCase outer middle inner before history response phase)
    (responseEqual : response = Sum.inl query)
    {final : PackedResponse A D}
    {finalHistory : DDC.History A C}
    {finalThird : Option (DDC.History C D)}
    (tail : ∀ {attempted sourceOuter sourceMiddle sourceQuery},
      SerialFactorization outer middle attempted
          (packResponse history (Sum.inl sourceQuery)) sourceOuter
            (some sourceMiddle) →
        attempted.toReceived = history → sourceQuery = query →
          ∃ after,
            ThreeInnerFactorization outer middle inner
                ((before.withFront sourceOuter (some sourceMiddle)).receiveOuterAtInner
                  query)
                (receiveOuter before.inner query) after final ∧
              LeftEndpoint outer middle inner finalHistory final finalThird
                after) :
    ∃ after,
      ThreeFrontFactorization outer middle inner before phase after final ∧
        LeftEndpoint outer middle inner finalHistory final finalThird after := by
  cases sourceCase with
  | outer source historyEqual sourceFactorization outerStored middleStored =>
      rename_i attempted sourceOuter sourceMiddle finalOuter finalMiddle
      cases responseEqual
      obtain ⟨openMiddle, middleOpen, sourceResponds⟩ :=
        source.endpointValid.exposedInner query rfl
      cases middleOpen
      obtain ⟨after, innerFactorization, endpoint⟩ :=
        tail source historyEqual rfl
      refine ⟨after,
        ThreeFrontFactorization.outer (current := sourceOuter) ?_, endpoint⟩
      exact sourceFactorization.toThreeQuery rfl outerStored middleStored
        innerFactorization
  | middle source historyEqual sourceFactorization outerStored middleStored =>
      rename_i attempted sourceOuter sourceMiddle finalOuter finalMiddle
      cases responseEqual
      obtain ⟨openMiddle, middleOpen, sourceResponds⟩ :=
        source.endpointValid.exposedInner query rfl
      cases middleOpen
      obtain ⟨after, innerFactorization, endpoint⟩ :=
        tail source historyEqual rfl
      refine ⟨after,
        ThreeFrontFactorization.middle (current := sourceMiddle) ?_, endpoint⟩
      exact sourceFactorization.toThreeQuery rfl outerStored middleStored
        innerFactorization

private theorem OuterPrefixFactorization.leftFactorization
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {aggregateHistory : DDC.History A C}
    {thirdHistory : Option (DDC.History C D)}
    {response : PackedResponse A D}
    {finalAggregate : DDC.History A C}
    {finalThird : Option (DDC.History C D)}
    (factorization : OuterPrefixFactorization (serial outer middle) inner
      aggregateHistory thirdHistory response finalAggregate finalThird)
    {before : ThreeHistories A B C D}
    {phase : Bool}
    (thirdStored : before.inner = thirdHistory)
    (expand : ∀ {current : DDC.Response aggregateHistory},
      current ∈ serial outer middle aggregateHistory →
        LeftSourceCase outer middle inner before aggregateHistory current
          phase) :
    ∃ after,
      ThreeFrontFactorization outer middle inner before phase after response ∧
        LeftEndpoint outer middle inner finalAggregate response finalThird
          after := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun aggregateHistory thirdHistory response finalAggregate
          finalThird _ =>
        ∀ {attempted sourceOuter sourceMiddle sourceQuery},
          SerialFactorization outer middle attempted
              (packResponse aggregateHistory (Sum.inl sourceQuery))
              sourceOuter (some sourceMiddle) →
            attempted.toReceived = aggregateHistory →
              ∀ {before : ThreeHistories A B C D},
                before.outer = some sourceOuter →
                before.middle = some sourceMiddle →
                before.inner = some thirdHistory →
                  ∃ after,
                    ThreeInnerFactorization outer middle inner before
                        thirdHistory after response ∧
                      LeftEndpoint outer middle inner finalAggregate response
                        finalThird after)
      generalizing before phase with
  | outerReply responds =>
      obtain ⟨after, front, endpoint⟩ := (expand responds).toReply rfl
      cases thirdStored
      exact ⟨after, front, endpoint⟩
  | outerQueryFirst responds sourceTail inductionHypothesis =>
      let sourceExpansion := expand responds
      apply sourceExpansion.toQuery rfl
      intro attempted sourceOuter sourceMiddle sourceQuery source historyEqual
        queryEqual
      let nextBefore :=
        (before.withFront sourceOuter
          (some sourceMiddle)).receiveOuterAtInner sourceQuery
      cases queryEqual
      have result := inductionHypothesis source historyEqual
        (before := nextBefore)
        (by simp [ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, nextBefore])
        (by simp [ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, nextBefore])
        (by simp [ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, receiveOuter, thirdStored,
          nextBefore])
      simpa [nextBefore, receiveOuter, thirdStored] using result
  | outerQueryNext closed responds sourceTail inductionHypothesis =>
      let sourceExpansion := expand responds
      apply sourceExpansion.toQuery rfl
      intro attempted sourceOuter sourceMiddle sourceQuery source historyEqual
        queryEqual
      let nextBefore :=
        (before.withFront sourceOuter
          (some sourceMiddle)).receiveOuterAtInner sourceQuery
      cases queryEqual
      have result := inductionHypothesis source historyEqual
        (before := nextBefore)
        (by simp [ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, nextBefore])
        (by simp [ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, nextBefore])
        (by simp [ThreeHistories.withFront,
          ThreeHistories.receiveOuterAtInner, receiveOuter, thirdStored,
          nextBefore])
      simpa [nextBefore, receiveOuter, thirdStored] using result
  | innerQuery linked responds =>
      rename_i currentAggregate currentThird query attempted sourceOuter
        sourceMiddle sourceQuery source historyEqual before outerStored
        middleStored innerStored
      refine ⟨before,
        ThreeInnerFactorization.innerQuery innerStored responds, ?_⟩
      have beforeEqual :
          (⟨some sourceOuter, some sourceMiddle, some currentThird⟩ :
            ThreeHistories A B C D) = before := by
        cases before
        simp_all
      simpa only [beforeEqual] using
        LeftEndpoint.inside (inner := inner) source historyEqual responds
  | innerReply linked responds sourceTail inductionHypothesis =>
      rename_i currentAggregate currentThird reply currentResponse
        currentFinalAggregate currentFinalThird sourceAttempted sourceOuter
        sourceMiddle sourceQuery source historyEqual before outerStored
        middleStored innerStored
      have sourceResponds : Sum.inl sourceQuery ∈
          serial outer middle currentAggregate := by
        rw [mem_serial_iff, mem_serialRaw_iff]
        exact ⟨_, historyEqual, sourceOuter, some sourceMiddle, source⟩
      have queryEqual : sourceQuery = currentThird.lastOuter := by
        exact Sum.inl.inj (Part.mem_unique sourceResponds linked)
      cases queryEqual
      let nextBefore := before.receiveInnerAtMiddle
        ⟨currentThird.lastOuter, reply⟩ sourceMiddle
      obtain ⟨after, front, endpoint⟩ := inductionHypothesis
        (before := nextBefore) (phase := true)
        (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle,
          innerStored]) (by
        intro current currentResponds
        rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
        obtain ⟨attempted, currentHistory, currentOuter, currentMiddle,
          currentSource⟩ := currentResponds
        have expectedHistory :
            (AttemptedHistory.afterInner sourceAttempted
                currentThird.lastOuter reply).toReceived =
              currentAggregate.snocInner currentThird.lastOuter reply := by
          change sourceAttempted.toReceived.snocInner currentThird.lastOuter
            reply = _
          rw [historyEqual]
        have attemptedEqual : attempted =
            AttemptedHistory.afterInner sourceAttempted
              currentThird.lastOuter reply :=
          AttemptedHistory.toReceived_injective
            (currentHistory.trans expectedHistory.symm)
        subst attempted
        have sourcePrefix := source.afterInner_prefix reply currentSource
        exact LeftSourceCase.middle currentSource expectedHistory sourcePrefix
          (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle,
            outerStored])
          (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle,
            receiveInner]))
      cases front with
      | middle middleFactorization =>
          have currentEqual := middleFactorization.current_eq
            (expected := receiveInner sourceMiddle
              ⟨currentThird.lastOuter, reply⟩)
            (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle])
          cases currentEqual
          exact ⟨after,
            ThreeInnerFactorization.innerReply innerStored middleStored
              responds middleFactorization,
            endpoint⟩

private theorem InnerPrefixFactorization.leftFactorization
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {aggregateHistory : DDC.History A C}
    {thirdHistory : DDC.History C D}
    {response : PackedResponse A D}
    {finalAggregate : DDC.History A C}
    {finalThird : Option (DDC.History C D)}
    (factorization : InnerPrefixFactorization (serial outer middle) inner
      aggregateHistory thirdHistory response finalAggregate finalThird)
    {sourceAttempted : AttemptedHistory A C}
    {sourceOuter : DDC.History A B}
    {sourceMiddle : DDC.History B C} {sourceQuery : C.query}
    (source : SerialFactorization outer middle sourceAttempted
      (packResponse aggregateHistory (Sum.inl sourceQuery)) sourceOuter
        (some sourceMiddle))
    (historyEqual : sourceAttempted.toReceived = aggregateHistory)
    {before : ThreeHistories A B C D}
    (outerStored : before.outer = some sourceOuter)
    (middleStored : before.middle = some sourceMiddle)
    (innerStored : before.inner = some thirdHistory) :
    ∃ after,
      ThreeInnerFactorization outer middle inner before thirdHistory after
          response ∧
        LeftEndpoint outer middle inner finalAggregate response finalThird
          after := by
  cases factorization with
  | innerQuery linked responds =>
      have queryEqual : sourceQuery = thirdHistory.lastOuter := by
        have sourceResponds : Sum.inl sourceQuery ∈
            serial outer middle aggregateHistory := by
          rw [mem_serial_iff, mem_serialRaw_iff]
          exact ⟨sourceAttempted, historyEqual, sourceOuter,
            some sourceMiddle, source⟩
        exact Sum.inl.inj (Part.mem_unique sourceResponds linked)
      cases queryEqual
      refine ⟨before,
        ThreeInnerFactorization.innerQuery innerStored responds, ?_⟩
      have beforeEqual :
          (⟨some sourceOuter, some sourceMiddle, some thirdHistory⟩ :
            ThreeHistories A B C D) = before := by
        cases before
        simp_all
      simpa only [beforeEqual] using
        LeftEndpoint.inside (inner := inner) source historyEqual responds
  | innerReply linked responds tail =>
      rename_i reply
      have queryEqual : sourceQuery = thirdHistory.lastOuter := by
        have sourceResponds : Sum.inl sourceQuery ∈
            serial outer middle aggregateHistory := by
          rw [mem_serial_iff, mem_serialRaw_iff]
          exact ⟨sourceAttempted, historyEqual, sourceOuter,
            some sourceMiddle, source⟩
        exact Sum.inl.inj (Part.mem_unique sourceResponds linked)
      cases queryEqual
      let nextBefore := before.receiveInnerAtMiddle
        ⟨thirdHistory.lastOuter, reply⟩ sourceMiddle
      obtain ⟨after, front, endpoint⟩ := tail.leftFactorization
        (before := nextBefore) (phase := true)
        (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle,
          innerStored]) (by
        intro current currentResponds
        rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
        obtain ⟨attempted, currentHistory, currentOuter, currentMiddle,
          currentSource⟩ := currentResponds
        have expectedHistory :
            (AttemptedHistory.afterInner sourceAttempted
                thirdHistory.lastOuter reply).toReceived =
              aggregateHistory.snocInner thirdHistory.lastOuter reply := by
          change sourceAttempted.toReceived.snocInner thirdHistory.lastOuter
            reply = _
          rw [historyEqual]
        have attemptedEqual : attempted =
            AttemptedHistory.afterInner sourceAttempted
              thirdHistory.lastOuter reply :=
          AttemptedHistory.toReceived_injective
            (currentHistory.trans expectedHistory.symm)
        subst attempted
        have sourcePrefix := source.afterInner_prefix reply currentSource
        exact LeftSourceCase.middle currentSource expectedHistory sourcePrefix
          (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle,
            outerStored])
          (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle,
            receiveInner]))
      cases front with
      | middle middleFactorization =>
          have currentEqual := middleFactorization.current_eq
            (expected := receiveInner sourceMiddle
              ⟨thirdHistory.lastOuter, reply⟩)
            (by simp [nextBefore, ThreeHistories.receiveInnerAtMiddle])
          cases currentEqual
          exact ⟨after,
            ThreeInnerFactorization.innerReply innerStored middleStored
              responds middleFactorization,
            endpoint⟩

private theorem SerialFactorization.leftFactorization
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {history : AttemptedHistory A D}
    {response : PackedResponse A D}
    {finalAggregate : DDC.History A C}
    {finalThird : Option (DDC.History C D)}
    (factorization : SerialFactorization (serial outer middle) inner history
      response finalAggregate finalThird) :
    ∃ after,
      ThreeHistoryFactorization outer middle inner history after response ∧
        LeftEndpoint outer middle inner finalAggregate response finalThird
          after := by
  induction factorization with
  | start localFactorization endpointValid =>
      rename_i query currentResponse currentFinalAggregate currentFinalThird
      let before : ThreeHistories A B C D :=
        ThreeHistories.empty.receiveOuterAtOuter query
      obtain ⟨after, localExtension, endpoint⟩ :=
        localFactorization.leftFactorization
          (before := before) (phase := false) rfl (by
          intro current currentResponds
          rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
          obtain ⟨attempted, currentHistory, currentOuter, currentMiddle,
            currentSource⟩ := currentResponds
          have expectedHistory :
              (AttemptedHistory.start (C := C) query).toReceived =
                DDC.History.singleton (B := C) query := rfl
          have attemptedEqual : attempted =
              AttemptedHistory.start (C := C) query :=
            AttemptedHistory.toReceived_injective
              (currentHistory.trans expectedHistory.symm)
          subst attempted
          have sourcePrefix := currentSource.start_prefix
          exact LeftSourceCase.outer currentSource rfl sourcePrefix
            (by simp [before, ThreeHistories.empty,
              ThreeHistories.receiveOuterAtOuter, receiveOuter])
            (by simp [before, ThreeHistories.empty,
              ThreeHistories.receiveOuterAtOuter]))
      cases localExtension with
      | outer outerFactorization =>
          have currentEqual := outerFactorization.current_eq
            (expected := DDC.History.singleton (B := B) query)
            (by simp [before, ThreeHistories.empty,
              ThreeHistories.receiveOuterAtOuter, receiveOuter])
          cases currentEqual
          exact ⟨after,
            .start (by simpa [before] using outerFactorization), endpoint⟩
  | afterInner previous localFactorization endpointValid
      inductionHypothesis =>
      rename_i prior query currentAggregate currentThird reply currentResponse
        currentFinalAggregate currentFinalThird
      obtain ⟨before, front, endpoint⟩ := inductionHypothesis
      cases endpoint with
      | inside source historyEqual responds =>
          rename_i sourceAttempted sourceOuter sourceMiddle sourceQuery
          let nextBefore : ThreeHistories A B C D :=
            (⟨some sourceOuter, some sourceMiddle, some currentThird⟩ :
              ThreeHistories A B C D).receiveInnerAtInner
                ⟨query, reply⟩ currentThird
          obtain ⟨after, localExtension, nextEndpoint⟩ :=
            localFactorization.leftFactorization source historyEqual
              (before := nextBefore)
              (by simp [nextBefore, ThreeHistories.receiveInnerAtInner])
              (by simp [nextBefore, ThreeHistories.receiveInnerAtInner])
              (by simp [nextBefore, ThreeHistories.receiveInnerAtInner,
                receiveInner])
          exact ⟨after,
            .afterInner front rfl
              (by simpa [nextBefore] using localExtension),
            nextEndpoint⟩
  | afterOuter previous localFactorization endpointValid
      inductionHypothesis =>
      rename_i prior previousReply currentAggregate currentThird query
        currentResponse currentFinalAggregate currentFinalThird
      obtain ⟨before, front, endpoint⟩ := inductionHypothesis
      obtain ⟨sourceAttempted, sourceOuter, sourceMiddle, sourceReply,
        source, historyEqual, beforeEqual⟩ :=
        endpoint.outside_data rfl
      cases beforeEqual
      cases historyEqual
      let nextBefore : ThreeHistories A B C D :=
        (⟨some sourceOuter, sourceMiddle, currentThird⟩ :
          ThreeHistories A B C D).receiveOuterAtOuter query
      obtain ⟨after, localExtension, nextEndpoint⟩ :=
        localFactorization.leftFactorization
          (before := nextBefore) (phase := false)
          (by simp [nextBefore, ThreeHistories.receiveOuterAtOuter]) (by
          intro current currentResponds
          rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
          obtain ⟨attempted, currentHistory, currentOuter,
            currentMiddle, currentSource⟩ := currentResponds
          have expectedHistory :
              (AttemptedHistory.afterOuter sourceAttempted query).toReceived =
                sourceAttempted.toReceived.snocOuter query := rfl
          have attemptedEqual : attempted =
              AttemptedHistory.afterOuter sourceAttempted query :=
            AttemptedHistory.toReceived_injective
              (currentHistory.trans expectedHistory.symm)
          subst attempted
          have sourcePrefix := source.afterOuter_prefix query currentSource
          exact LeftSourceCase.outer currentSource expectedHistory
            sourcePrefix
            (by simp [nextBefore, ThreeHistories.receiveOuterAtOuter,
              receiveOuter])
            (by simp [nextBefore, ThreeHistories.receiveOuterAtOuter]))
      cases localExtension with
      | outer outerFactorization =>
          have currentEqual := outerFactorization.current_eq
            (expected := sourceOuter.snocOuter query)
            (by simp [nextBefore, ThreeHistories.receiveOuterAtOuter,
              receiveOuter])
          cases currentEqual
          exact ⟨after,
            .afterOuter front rfl
              (by simpa [nextBefore] using outerFactorization),
            nextEndpoint⟩

private inductive RightState
    {A B C D : Interface.{u, v}}
    (middle : DDC B C) (inner : DDC C D) :
    ThreeHistories A B C D → Option (DDC.History B D) → Prop
  | none {before}
      (middleEmpty : before.middle = none)
      (innerEmpty : before.inner = none) :
      RightState middle inner before none
  | some {before aggregateHistory reply attempted finalMiddle finalInner}
      (source : SerialFactorization middle inner attempted
        (packResponse aggregateHistory (Sum.inr reply)) finalMiddle finalInner)
      (historyEqual : attempted.toReceived = aggregateHistory)
      (middleStored : before.middle = some finalMiddle)
      (innerStored : before.inner = finalInner) :
      RightState middle inner before (some aggregateHistory)

private theorem RightState.receiveOuterAtOuter
    {A B C D : Interface.{u, v}}
    {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {aggregateHistory : Option (DDC.History B D)}
    (state : RightState middle inner before aggregateHistory)
    (query : A.query) :
    RightState middle inner (before.receiveOuterAtOuter query)
      aggregateHistory := by
  cases state with
  | none middleEmpty innerEmpty =>
      exact .none
        (by simpa [ThreeHistories.receiveOuterAtOuter] using middleEmpty)
        (by simpa [ThreeHistories.receiveOuterAtOuter] using innerEmpty)
  | some source historyEqual middleStored innerStored =>
      exact .some source historyEqual
        (by simpa [ThreeHistories.receiveOuterAtOuter] using middleStored)
        (by simpa [ThreeHistories.receiveOuterAtOuter] using innerStored)

private inductive RightSourceCase
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (before : ThreeHistories A B C D) :
    (history : DDC.History B D) → DDC.Response history →
      Bool → Prop
  | middle {history response attempted sourceMiddle sourceInner
      finalMiddle finalInner}
      (source : SerialFactorization middle inner attempted
        (packResponse history response) finalMiddle finalInner)
      (historyEqual : attempted.toReceived = history)
      (sourceFactorization : OuterPrefixFactorization middle inner
        sourceMiddle sourceInner (packResponse history response) finalMiddle
          finalInner)
      (middleStored : before.middle = some sourceMiddle)
      (innerStored : before.inner = sourceInner) :
      RightSourceCase outer middle inner before history response false
  | inner {history response attempted sourceMiddle sourceInner
      finalMiddle finalInner}
      (source : SerialFactorization middle inner attempted
        (packResponse history response) finalMiddle finalInner)
      (historyEqual : attempted.toReceived = history)
      (sourceFactorization : InnerPrefixFactorization middle inner
        sourceMiddle sourceInner (packResponse history response) finalMiddle
          finalInner)
      (middleStored : before.middle = some sourceMiddle)
      (innerStored : before.inner = some sourceInner) :
      RightSourceCase outer middle inner before history response true

private inductive RightEndpoint
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    PackedResponse A D → DDC.History A B →
      Option (DDC.History B D) → ThreeHistories A B C D → Prop
  | inside {aggregateHistory attempted sourceMiddle sourceInner query
      outerHistory}
      (source : SerialFactorization middle inner attempted
        (packResponse aggregateHistory (Sum.inl query)) sourceMiddle
          (some sourceInner))
      (historyEqual : attempted.toReceived = aggregateHistory) :
      RightEndpoint outer middle inner (Sum.inl query) outerHistory
        (some aggregateHistory)
        ⟨some outerHistory, some sourceMiddle, some sourceInner⟩
  | outside {outerHistory aggregateHistory before}
      {reply : Option (A.answer outerHistory.lastOuter)}
      (outerStored : before.outer = some outerHistory)
      (state : RightState middle inner before aggregateHistory) :
      RightEndpoint outer middle inner
        (Sum.inr ⟨outerHistory.lastOuter, reply⟩) outerHistory
          aggregateHistory before

private theorem RightEndpoint.outside_data
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {response : PackedResponse A D} {outerHistory : DDC.History A B}
    {aggregateHistory : Option (DDC.History B D)}
    {before : ThreeHistories A B C D}
    (endpoint : RightEndpoint outer middle inner response outerHistory
      aggregateHistory before)
    {packed : InnerReply A} (responseEqual : response = Sum.inr packed) :
    before.outer = some outerHistory ∧
      RightState middle inner before aggregateHistory := by
  cases endpoint with
  | inside source historyEqual => cases responseEqual
  | outside outerStored state => exact ⟨outerStored, state⟩

private theorem RightSourceCase.toInside
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {history : DDC.History B D} {response : DDC.Response history}
    {query : D.query} {phase : Bool}
    (sourceCase : RightSourceCase outer middle inner before history response phase)
    (responseEqual : response = Sum.inl query)
    {outerHistory : DDC.History A B}
    (outerStored : before.outer = some outerHistory) :
    ∃ after,
      ThreeBackFactorization outer middle inner before phase after
          (Sum.inl query) ∧
        RightEndpoint outer middle inner (Sum.inl query) outerHistory
          (some history) after := by
  cases sourceCase with
  | middle source historyEqual sourceFactorization middleStored innerStored =>
      rename_i attempted sourceMiddle sourceInner finalMiddle finalInner
      cases responseEqual
      obtain ⟨openInner, innerOpen, sourceResponds⟩ :=
        source.endpointValid.exposedInner query rfl
      cases innerOpen
      refine ⟨before.withBack finalMiddle (some openInner),
        ThreeBackFactorization.middle (current := sourceMiddle) ?_, ?_⟩
      · exact sourceFactorization.toThreeInside rfl middleStored innerStored
      · simpa [ThreeHistories.withBack, outerStored] using
          RightEndpoint.inside (outer := outer) source historyEqual
  | inner source historyEqual sourceFactorization middleStored innerStored =>
      rename_i attempted sourceMiddle sourceInner finalMiddle finalInner
      cases responseEqual
      obtain ⟨openInner, innerOpen, sourceResponds⟩ :=
        source.endpointValid.exposedInner query rfl
      cases innerOpen
      refine ⟨before.withBack finalMiddle (some openInner),
        ThreeBackFactorization.inner (current := sourceInner) ?_, ?_⟩
      · exact sourceFactorization.toThreeInside rfl middleStored innerStored
      · simpa [ThreeHistories.withBack, outerStored] using
          RightEndpoint.inside (outer := outer) source historyEqual

private theorem RightSourceCase.toOutside
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {before : ThreeHistories A B C D}
    {history : DDC.History B D} {response : DDC.Response history}
    {reply : Option (B.answer history.lastOuter)} {phase : Bool}
    (sourceCase : RightSourceCase outer middle inner before history response phase)
    (responseEqual : response = Sum.inr reply)
    {outerHistory : DDC.History A B}
    (outerStored : before.outer = some outerHistory)
    {final : PackedResponse A D}
    {finalOuter : DDC.History A B}
    {finalSuffix : Option (DDC.History B D)}
    (tail : ∀ {attempted finalMiddle finalInner},
      SerialFactorization middle inner attempted
          (packResponse history (Sum.inr reply)) finalMiddle finalInner →
        attempted.toReceived = history →
          ∃ after,
            ThreeOuterFactorization outer middle inner
                ((before.withBack finalMiddle finalInner).receiveInnerAtOuter
                  ⟨history.lastOuter, reply⟩ outerHistory)
                (receiveInner outerHistory ⟨history.lastOuter, reply⟩)
                after final ∧
              RightEndpoint outer middle inner final finalOuter finalSuffix
                after) :
    ∃ after,
      ThreeBackFactorization outer middle inner before phase after final ∧
        RightEndpoint outer middle inner final finalOuter finalSuffix after := by
  cases sourceCase with
  | middle source historyEqual sourceFactorization middleStored innerStored =>
      rename_i attempted sourceMiddle sourceInner finalMiddle finalInner
      cases responseEqual
      obtain ⟨after, outerFactorization, endpoint⟩ :=
        tail source historyEqual
      refine ⟨after,
        ThreeBackFactorization.middle (current := sourceMiddle) ?_, endpoint⟩
      exact sourceFactorization.toThreeOutside rfl middleStored innerStored
        outerStored outerFactorization
  | inner source historyEqual sourceFactorization middleStored innerStored =>
      rename_i attempted sourceMiddle sourceInner finalMiddle finalInner
      cases responseEqual
      obtain ⟨after, outerFactorization, endpoint⟩ :=
        tail source historyEqual
      refine ⟨after,
        ThreeBackFactorization.inner (current := sourceInner) ?_, endpoint⟩
      exact sourceFactorization.toThreeOutside rfl middleStored innerStored
        outerStored outerFactorization

private theorem OuterPrefixFactorization.rightFactorization
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {outerHistory : DDC.History A B}
    {suffixHistory : Option (DDC.History B D)}
    {response : PackedResponse A D}
    {finalOuter : DDC.History A B}
    {finalSuffix : Option (DDC.History B D)}
    (factorization : OuterPrefixFactorization outer (serial middle inner)
      outerHistory suffixHistory response finalOuter finalSuffix)
    {before : ThreeHistories A B C D}
    (outerStored : before.outer = some outerHistory)
    (state : RightState middle inner before suffixHistory) :
    ∃ after,
      ThreeOuterFactorization outer middle inner before outerHistory after
          response ∧
        RightEndpoint outer middle inner response finalOuter finalSuffix
          after := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory suffixHistory response finalOuter
          finalSuffix _ =>
        ∀ {before : ThreeHistories A B C D} {phase : Bool},
          before.outer = some outerHistory →
            (∀ {current : DDC.Response suffixHistory},
              current ∈ serial middle inner suffixHistory →
                RightSourceCase outer middle inner before suffixHistory current
                  phase) →
              ∃ after,
                ThreeBackFactorization outer middle inner before phase after
                    response ∧
                  RightEndpoint outer middle inner response finalOuter
                    finalSuffix after)
      generalizing before with
  | outerReply responds =>
      refine ⟨before,
        ThreeOuterFactorization.outerReply outerStored responds, ?_⟩
      exact RightEndpoint.outside outerStored state
  | outerQueryFirst responds sourceTail inductionHypothesis =>
      rename_i currentOuter query currentResponse currentFinalOuter
        currentFinalSuffix
      cases state with
      | none middleEmpty innerEmpty =>
          let nextBefore := before.receiveOuterAtMiddle query
          obtain ⟨after, back, endpoint⟩ := inductionHypothesis
            (before := nextBefore) (phase := false)
            (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
              outerStored]) (by
            intro current currentResponds
            rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
            obtain ⟨attempted, currentHistory, currentMiddle, currentInner,
              currentSource⟩ := currentResponds
            have expectedHistory :
                (AttemptedHistory.start (C := D) query).toReceived =
                  DDC.History.singleton (B := D) query := rfl
            have attemptedEqual : attempted =
                AttemptedHistory.start (C := D) query :=
              AttemptedHistory.toReceived_injective
                (currentHistory.trans expectedHistory.symm)
            subst attempted
            have sourcePrefix := currentSource.start_prefix
            exact RightSourceCase.middle currentSource rfl sourcePrefix
              (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
                receiveOuter, middleEmpty])
              (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
                innerEmpty]))
          cases back with
          | middle middleFactorization =>
              have currentEqual := middleFactorization.current_eq
                (expected := DDC.History.singleton (B := C) query)
                (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
                  receiveOuter, middleEmpty])
              cases currentEqual
              exact ⟨after,
                ThreeOuterFactorization.outerQuery outerStored responds
                  (by simpa [nextBefore, receiveOuter, middleEmpty] using
                    middleFactorization),
                endpoint⟩
  | outerQueryNext closed responds sourceTail inductionHypothesis =>
      rename_i currentOuter currentSuffix query currentResponse
        currentFinalOuter currentFinalSuffix
      cases state with
      | some previousSource previousHistory middleStored innerStored =>
          rename_i sourceAttempted finalMiddle finalInner previousReply
          cases previousHistory
          let nextBefore := before.receiveOuterAtMiddle query
          obtain ⟨after, back, endpoint⟩ := inductionHypothesis
            (before := nextBefore) (phase := false)
            (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
              outerStored]) (by
            intro current currentResponds
            rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
            obtain ⟨attempted, currentHistory, currentMiddle, currentInner,
              currentSource⟩ := currentResponds
            have expectedHistory :
                (AttemptedHistory.afterOuter sourceAttempted query).toReceived =
                  sourceAttempted.toReceived.snocOuter query := rfl
            have attemptedEqual : attempted =
                AttemptedHistory.afterOuter sourceAttempted query :=
              AttemptedHistory.toReceived_injective
                (currentHistory.trans expectedHistory.symm)
            subst attempted
            have sourcePrefix :=
              previousSource.afterOuter_prefix query currentSource
            exact RightSourceCase.middle currentSource expectedHistory
              sourcePrefix
              (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
                receiveOuter, middleStored])
              (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
                innerStored]))
          cases back with
          | middle middleFactorization =>
              have currentEqual := middleFactorization.current_eq
                (expected := finalMiddle.snocOuter query)
                (by simp [nextBefore, ThreeHistories.receiveOuterAtMiddle,
                  receiveOuter, middleStored])
              cases currentEqual
              exact ⟨after,
                ThreeOuterFactorization.outerQuery outerStored responds
                  (by simpa [nextBefore, receiveOuter, middleStored] using
                    middleFactorization),
                endpoint⟩
  | innerQuery linked responds =>
      rename_i currentOuter currentSuffix query before phase outerStored expand
      let sourceExpansion := expand responds
      simpa using sourceExpansion.toInside rfl outerStored
  | innerReply linked responds sourceTail inductionHypothesis =>
      rename_i currentOuter currentSuffix reply currentResponse
        currentFinalOuter currentFinalSuffix before phase outerStored expand
      let sourceExpansion := expand responds
      refine sourceExpansion.toOutside rfl outerStored ?_
      intro attempted finalMiddle finalInner source historyEqual
      let nextBefore :=
        (before.withBack finalMiddle finalInner).receiveInnerAtOuter
          ⟨currentSuffix.lastOuter, reply⟩ currentOuter
      obtain ⟨after, outerFactorization, endpoint⟩ := inductionHypothesis
        (before := nextBefore)
        (by simp [nextBefore, ThreeHistories.receiveInnerAtOuter,
          receiveInner])
        (RightState.some source historyEqual
          (by simp [nextBefore, ThreeHistories.receiveInnerAtOuter,
            ThreeHistories.withBack])
          (by simp [nextBefore, ThreeHistories.receiveInnerAtOuter,
            ThreeHistories.withBack]))
      exact ⟨after, by simpa [nextBefore, outerStored] using
        outerFactorization, endpoint⟩

private theorem InnerPrefixFactorization.rightFactorization
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {outerHistory : DDC.History A B}
    {suffixHistory : DDC.History B D}
    {response : PackedResponse A D}
    {finalOuter : DDC.History A B}
    {finalSuffix : Option (DDC.History B D)}
    (factorization : InnerPrefixFactorization outer (serial middle inner)
      outerHistory suffixHistory response finalOuter finalSuffix)
    {before : ThreeHistories A B C D} {phase : Bool}
    (outerStored : before.outer = some outerHistory)
    (expand : ∀ {current : DDC.Response suffixHistory},
      current ∈ serial middle inner suffixHistory →
        RightSourceCase outer middle inner before suffixHistory current phase) :
    ∃ after,
      ThreeBackFactorization outer middle inner before phase after response ∧
        RightEndpoint outer middle inner response finalOuter finalSuffix
          after := by
  cases factorization with
  | innerQuery linked responds =>
      exact (expand responds).toInside rfl outerStored
  | innerReply linked responds tail =>
      rename_i reply
      let sourceExpansion := expand responds
      refine sourceExpansion.toOutside rfl outerStored ?_
      intro attempted finalMiddle finalInner source historyEqual
      let nextBefore :=
        (before.withBack finalMiddle finalInner).receiveInnerAtOuter
          ⟨suffixHistory.lastOuter, reply⟩ outerHistory
      obtain ⟨after, outerFactorization, endpoint⟩ :=
        tail.rightFactorization (before := nextBefore)
          (by simp [nextBefore, ThreeHistories.receiveInnerAtOuter,
            receiveInner])
          (RightState.some source historyEqual
            (by simp [nextBefore, ThreeHistories.receiveInnerAtOuter,
              ThreeHistories.withBack])
            (by simp [nextBefore, ThreeHistories.receiveInnerAtOuter,
              ThreeHistories.withBack]))
      exact ⟨after, by simpa [nextBefore, outerStored] using
        outerFactorization, endpoint⟩

private theorem SerialFactorization.rightFactorization
    {A B C D : Interface.{u, v}}
    {outer : DDC A B} {middle : DDC B C} {inner : DDC C D}
    {history : AttemptedHistory A D}
    {response : PackedResponse A D}
    {finalOuter : DDC.History A B}
    {finalSuffix : Option (DDC.History B D)}
    (factorization : SerialFactorization outer (serial middle inner) history
      response finalOuter finalSuffix) :
    ∃ after,
      ThreeHistoryFactorization outer middle inner history after response ∧
        RightEndpoint outer middle inner response finalOuter finalSuffix
          after := by
  induction factorization with
  | start localFactorization endpointValid =>
      rename_i query currentResponse currentFinalOuter currentFinalSuffix
      let before : ThreeHistories A B C D :=
        ThreeHistories.empty.receiveOuterAtOuter query
      obtain ⟨after, outerFactorization, endpoint⟩ :=
        localFactorization.rightFactorization
          (before := before)
          (by simp [before, ThreeHistories.empty,
            ThreeHistories.receiveOuterAtOuter, receiveOuter])
          (RightState.none
            (by simp [before, ThreeHistories.empty,
              ThreeHistories.receiveOuterAtOuter])
            (by simp [before, ThreeHistories.empty,
              ThreeHistories.receiveOuterAtOuter]))
      have currentEqual := outerFactorization.current_eq
        (expected := DDC.History.singleton (B := B) query)
        (by simp [before, ThreeHistories.empty,
          ThreeHistories.receiveOuterAtOuter, receiveOuter])
      cases currentEqual
      exact ⟨after,
        .start (by simpa [before] using outerFactorization), endpoint⟩
  | afterInner previous localFactorization endpointValid
      inductionHypothesis =>
      rename_i prior query currentOuter currentSuffix reply currentResponse
        currentFinalOuter currentFinalSuffix
      obtain ⟨before, front, endpoint⟩ := inductionHypothesis
      cases endpoint with
      | inside source historyEqual =>
          rename_i sourceAttempted sourceMiddle sourceInner
          let nextBefore : ThreeHistories A B C D :=
            (⟨some currentOuter, some sourceMiddle, some sourceInner⟩ :
              ThreeHistories A B C D).receiveInnerAtInner
                ⟨query, reply⟩ sourceInner
          obtain ⟨after, back, nextEndpoint⟩ :=
            localFactorization.rightFactorization
              (before := nextBefore) (phase := true)
              (by simp [nextBefore, ThreeHistories.receiveInnerAtInner]) (by
              intro current currentResponds
              rw [mem_serial_iff, mem_serialRaw_iff] at currentResponds
              obtain ⟨attempted, currentHistory, currentMiddle,
                currentInner, currentSource⟩ := currentResponds
              have expectedHistory :
                  (AttemptedHistory.afterInner sourceAttempted query reply).toReceived =
                    currentSuffix.snocInner query reply := by
                change sourceAttempted.toReceived.snocInner query reply = _
                rw [historyEqual]
              have attemptedEqual : attempted =
                  AttemptedHistory.afterInner sourceAttempted query reply :=
                AttemptedHistory.toReceived_injective
                  (currentHistory.trans expectedHistory.symm)
              subst attempted
              have sourcePrefix :=
                source.afterInner_prefix reply currentSource
              exact RightSourceCase.inner currentSource expectedHistory
                sourcePrefix
                (by simp [nextBefore, ThreeHistories.receiveInnerAtInner])
                (by simp [nextBefore, ThreeHistories.receiveInnerAtInner,
                  receiveInner]))
          cases back with
          | inner innerFactorization =>
              have currentEqual := innerFactorization.current_eq
                (expected := sourceInner.snocInner query reply)
                (by simp [nextBefore, ThreeHistories.receiveInnerAtInner,
                  receiveInner])
              cases currentEqual
              exact ⟨after,
                .afterInner front rfl
                  (by simpa [nextBefore] using innerFactorization),
                nextEndpoint⟩
  | afterOuter previous localFactorization endpointValid
      inductionHypothesis =>
      rename_i prior previousReply currentOuter currentSuffix query
        currentResponse currentFinalOuter currentFinalSuffix
      obtain ⟨before, front, endpoint⟩ := inductionHypothesis
      obtain ⟨outerStored, state⟩ := endpoint.outside_data rfl
      let nextBefore := before.receiveOuterAtOuter query
      obtain ⟨after, outerFactorization, nextEndpoint⟩ :=
        localFactorization.rightFactorization
          (before := nextBefore)
          (by simp [nextBefore, ThreeHistories.receiveOuterAtOuter,
            receiveOuter, outerStored])
          (state.receiveOuterAtOuter query)
      have currentEqual := outerFactorization.current_eq
        (expected := currentOuter.snocOuter query)
        (by simp [nextBefore, ThreeHistories.receiveOuterAtOuter,
          receiveOuter, outerStored])
      cases currentEqual
      exact ⟨after,
        .afterOuter front outerStored
          (by simpa [nextBefore] using outerFactorization),
        nextEndpoint⟩

private theorem mem_left_serial_imp_threeGlobalGraph
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (history : DDC.History A D) (response : DDC.Response history)
    (responds : response ∈ serial (serial outer middle) inner history) :
    ThreeGlobalGraph outer middle inner history response := by
  rw [mem_serial_iff, mem_serialRaw_iff] at responds
  obtain ⟨attempted, historyEqual, finalAggregate, finalThird,
    factorization⟩ := responds
  obtain ⟨after, threeFactorization, endpoint⟩ :=
    factorization.leftFactorization
  exact ⟨attempted, historyEqual, after, threeFactorization⟩

private theorem mem_right_serial_imp_threeGlobalGraph
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D)
    (history : DDC.History A D) (response : DDC.Response history)
    (responds : response ∈ serial outer (serial middle inner) history) :
    ThreeGlobalGraph outer middle inner history response := by
  rw [mem_serial_iff, mem_serialRaw_iff] at responds
  obtain ⟨attempted, historyEqual, finalOuter, finalSuffix,
    factorization⟩ := responds
  obtain ⟨after, threeFactorization, endpoint⟩ :=
    factorization.rightFactorization
  exact ⟨attempted, historyEqual, after, threeFactorization⟩

end Internal

/-- Regard a DDS as the DDC that answers each outer query directly and has no
inner interface. -/
abbrev ofDDS {A : Interface.{u, v}} (system : DDS A) :
    DDC A Interface.empty.{u, v} :=
  Internal.ofDDS system

/-- Serial composition of DDC functions is associative. -/
theorem serial_assoc
    {A B C D : Interface.{u, v}}
    (outer : DDC A B) (middle : DDC B C) (inner : DDC C D) :
    serial (serial outer middle) inner =
      serial outer (serial middle inner) := by
  -- Both bracketings are compared through the same three-converter graph.
  apply DDC.ext
  intro history response
  constructor
  -- Factor the left bracketing, then reconstruct the right bracketing.
  · intro responds
    obtain ⟨attempted, historyEqual, after, factorization⟩ :=
      mem_left_serial_imp_threeGlobalGraph outer middle inner history response
        responds
    cases historyEqual
    exact factorization.mem_of_graph
      (serial outer (serial middle inner))
      (mem_right_serial_imp_threeGlobalGraph outer middle inner) rfl
  -- Factor the right bracketing, then reconstruct the left bracketing.
  · intro responds
    obtain ⟨attempted, historyEqual, after, factorization⟩ :=
      mem_right_serial_imp_threeGlobalGraph outer middle inner history response
        responds
    cases historyEqual
    exact factorization.mem_of_graph
      (serial (serial outer middle) inner)
      (mem_left_serial_imp_threeGlobalGraph outer middle inner) rfl

/--
Attachment is an action of serial converter composition.

Maurer--Renner 2016, Section 3.3 (printed p. 7):
“`(β ◦ α)ⁱ R = βⁱ (αⁱ R)`.”
The proof is equality of functions on DDS histories.
-/
theorem applySystem_serial_eq
    {A B C : Interface.{u, v}}
    (outer : DDC A B) (inner : DDC B C) (system : DDS C) :
    applySystem (serial outer inner) system =
      applySystem outer (applySystem inner system) := by
  apply ofDDS_injective
  rw [← serial_ofDDS_eq (serial outer inner) system,
    ← serial_ofDDS_eq outer (applySystem inner system),
    ← serial_ofDDS_eq inner system,
    serial_assoc]

private theorem ofDDS_empty_eq_forwarding :
    Internal.ofDDS (DDS.empty : DDS Interface.empty.{u, v}) =
      forwarding Interface.empty.{u, v} := by
  apply DDC.ext
  intro history _
  exact PEmpty.elim history.outer.head

/-- Attaching the DDC induced by a DDS to the empty DDS recovers that DDS. -/
@[simp]
theorem applySystem_ofDDS_eq
    {A : Interface.{u, v}} (system : DDS A) :
    applySystem (ofDDS system) (DDS.empty : DDS Interface.empty.{u, v}) =
      system := by
  change applySystem (Internal.ofDDS system)
      (DDS.empty : DDS Interface.empty.{u, v}) = system
  apply ofDDS_injective
  rw [← serial_ofDDS_eq, ofDDS_empty_eq_forwarding,
    serial_forwarding_eq]

end DDC

end RandomSystems.Ambient
