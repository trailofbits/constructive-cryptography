/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.DDC
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Converter attachment

Maurer--Renner 2016, Section 3.3 (printed p. 7), states: “A converter α, when
applied as an interface i of a resource, induces a function Φ → Φ.”
Jost, Definition 2.2.2 (printed pp. 17–18), specifies the corresponding
interaction and requires: “There is a finite upper bound on the number of
consecutive outputs” to inside interfaces.

The definitions below give that attachment as a mathematical function from a
DDC and a DDS to a DDS.  Its value is selected by the unique finite received
history compatible with the two functions.  Rejection is the ordinary answer
`none`; it is not termination or hidden state.  The recursive argument appears
only in the proof that this compatible history exists.

The concrete DDC carrier assumes well-founded inner continuation rather than
Jost's stronger single numerical upper bound.  Attachment uses exactly that
weaker hypothesis.  No categorical law is postulated in this module; identity
and serial laws are proved in the converter modules that own those operations.
-/

namespace RandomSystems.Ambient

universe u v w z

namespace Attachment

/-- An inner query or a query-indexed outer answer in an attachment transcript. -/
abbrev Response
    (A : Interface.{u, v}) (B : Interface.{w, z}) :=
  B.query ⊕ DDC.History.InnerReply A

/-- Inner queries among a list of attachment responses. -/
def innerQueries
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (responses : List (Response A B)) : List B.query :=
  responses.filterMap fun
    | Sum.inl query => some query
    | Sum.inr _ => none

@[simp]
theorem innerQueries_nil
    {A : Interface.{u, v}} {B : Interface.{w, z}} :
    innerQueries ([] : List (Response A B)) = [] :=
  rfl

@[simp]
theorem innerQueries_cons_inner
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : B.query) (responses : List (Response A B)) :
    innerQueries (Sum.inl query :: responses) =
      query :: innerQueries responses :=
  rfl

@[simp]
theorem innerQueries_cons_outer
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (reply : DDC.History.InnerReply A)
    (responses : List (Response A B)) :
    innerQueries (Sum.inr reply :: responses) = innerQueries responses :=
  rfl

/-- One complete attachment transcript. -/
structure Transcript
    (A : Interface.{u, v}) (B : Interface.{w, z}) where
  inputs : List (DDC.History.Input A B)
  responses : List (Response A B)
  final : DDC.History.InnerReply A

namespace Transcript

@[ext]
theorem ext
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : Transcript A B}
    (inputsEqual : left.inputs = right.inputs)
    (responsesEqual : left.responses = right.responses)
    (finalEqual : left.final = right.final) : left = right := by
  cases left
  cases right
  simp_all

end Transcript

private def innerHistory {B : Interface.{w, z}}
    (prior : List B.query) (query : B.query) : History B where
  queries := prior ++ [query]
  nonempty := by simp

@[simp]
private theorem last_innerHistory {B : Interface.{w, z}}
    (prior : List B.query) (query : B.query) :
    (innerHistory prior query).last = query := by
  simp [innerHistory, History.last]

/-- The query-indexed answer supplied by a DDS after the preceding inner queries. -/
def innerReplyAt {B : Interface.{w, z}} (system : DDS B)
    (prior : List B.query) (query : B.query) : Option (B.answer query) :=
  cast (congrArg (fun selected => Option (B.answer selected))
    (last_innerHistory prior query)) (system (innerHistory prior query))

/--
The finite functional interaction witnessing attachment from a fixed converter
history.  Each inner query is answered in its exact query-indexed fibre; each
outer answer either ends the current outer query or continues with the next
outer query.
-/
inductive CompatibleFrom
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) :
    DDC.History A B → List B.query → List A.query →
      List (DDC.History.Input A B) → List (Response A B) →
      DDC.History.InnerReply A → Prop
  | innerQuery {history : DDC.History A B}
      {innerPrior : List B.query} {remainingOuter : List A.query}
      {query : B.query} {tailInputs : List (DDC.History.Input A B)}
      {tailResponses : List (Response A B)} {final : DDC.History.InnerReply A}
      (responds : Sum.inl query ∈ converter history)
      (tail : CompatibleFrom converter system
        (history.snocInner query (innerReplyAt system innerPrior query))
        (innerPrior ++ [query]) remainingOuter tailInputs tailResponses final) :
      CompatibleFrom converter system history innerPrior remainingOuter
        (history.lastInput :: tailInputs)
        (Sum.inl query :: tailResponses) final
  | outerLast {history : DDC.History A B}
      {innerPrior : List B.query}
      {reply : Option (A.answer history.lastOuter)}
      (responds : Sum.inr reply ∈ converter history) :
      CompatibleFrom converter system history innerPrior []
        [history.lastInput] [Sum.inr ⟨history.lastOuter, reply⟩]
        ⟨history.lastOuter, reply⟩
  | outerNext {history : DDC.History A B}
      {innerPrior : List B.query}
      {reply : Option (A.answer history.lastOuter)}
      {nextOuter : A.query} {remainingOuter : List A.query}
      {tailInputs : List (DDC.History.Input A B)}
      {tailResponses : List (Response A B)} {final : DDC.History.InnerReply A}
      (responds : Sum.inr reply ∈ converter history)
      (tail : CompatibleFrom converter system
        (history.snocOuter nextOuter) innerPrior remainingOuter
        tailInputs tailResponses final) :
      CompatibleFrom converter system history innerPrior
        (nextOuter :: remainingOuter)
        (history.lastInput :: tailInputs)
        (Sum.inr ⟨history.lastOuter, reply⟩ :: tailResponses) final

/-- A compatible factorization remains compatible after replacing the inner
DDS when the two DDSs agree on every inner history used by the factorization. -/
theorem CompatibleFrom.congr_dds_of_length_le
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (left right : DDS B)
    {history : DDC.History A B} {innerPrior : List B.query}
    {remainingOuter : List A.query}
    {inputs : List (DDC.History.Input A B)}
    {responses : List (Response A B)}
    {final : DDC.History.InnerReply A}
    (compatible : CompatibleFrom converter left history innerPrior
      remainingOuter inputs responses final)
    (limit : Nat)
    (equal : ∀ queryHistory : History B,
      queryHistory.queries.length ≤ limit →
        right queryHistory = left queryHistory)
    (within : innerPrior.length + (innerQueries responses).length ≤ limit) :
    CompatibleFrom converter right history innerPrior remainingOuter
      inputs responses final := by
  induction compatible with
  | innerQuery responds tail inductionHypothesis =>
      rename_i history innerPrior remainingOuter query tailInputs
        tailResponses final
      let queryHistory : History B :=
        { queries := innerPrior ++ [query]
          nonempty := by simp }
      -- The current inner history lies within the displayed bound.
      have currentWithin : queryHistory.queries.length ≤ limit := by
        change (innerPrior ++ [query]).length ≤ limit
        change innerPrior.length +
          ((innerQueries tailResponses).length + 1) ≤ limit at within
        simp only [List.length_append, List.length_singleton]
        omega
      have currentEqual := equal queryHistory currentWithin
      have replyEqual :
          innerReplyAt right innerPrior query =
            innerReplyAt left innerPrior query := by
        unfold innerReplyAt
        change cast _ (right queryHistory) = cast _ (left queryHistory)
        rw [currentEqual]
      apply CompatibleFrom.innerQuery responds
      rw [replyEqual]
      apply inductionHypothesis
      -- Removing the current response preserves the remaining length bound.
      change (innerPrior ++ [query]).length +
        (innerQueries tailResponses).length ≤ limit
      change innerPrior.length +
        ((innerQueries tailResponses).length + 1) ≤ limit at within
      simp only [List.length_append, List.length_singleton]
      omega
  | outerLast responds =>
      exact CompatibleFrom.outerLast responds
  | outerNext responds tail inductionHypothesis =>
      apply CompatibleFrom.outerNext responds
      apply inductionHypothesis
      simpa using within

/-- Compatible continuations from the same history have the same transcript. -/
theorem CompatibleFrom.unique
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {system : DDS B}
    {history : DDC.History A B} {innerPrior : List B.query}
    {remainingOuter : List A.query}
    {leftInputs rightInputs : List (DDC.History.Input A B)}
    {leftResponses rightResponses : List (Response A B)}
    {leftFinal rightFinal : DDC.History.InnerReply A}
    (left : CompatibleFrom converter system history innerPrior remainingOuter
      leftInputs leftResponses leftFinal)
    (right : CompatibleFrom converter system history innerPrior remainingOuter
      rightInputs rightResponses rightFinal) :
    leftInputs = rightInputs ∧ leftResponses = rightResponses ∧
      leftFinal = rightFinal := by
  induction left generalizing rightInputs rightResponses rightFinal with
  | innerQuery leftResponds leftTail inductionHypothesis =>
      cases right with
      | innerQuery rightResponds rightTail =>
          have queryEqual := Part.mem_unique leftResponds rightResponds
          cases Sum.inl.inj queryEqual
          obtain ⟨inputsEqual, responsesEqual, finalEqual⟩ :=
            inductionHypothesis rightTail
          simp_all
      | outerLast rightResponds =>
          have impossible := Part.mem_unique leftResponds rightResponds
          cases impossible
      | outerNext rightResponds rightTail =>
          have impossible := Part.mem_unique leftResponds rightResponds
          cases impossible
  | outerLast leftResponds =>
      cases right with
      | innerQuery rightResponds rightTail =>
          have impossible := Part.mem_unique leftResponds rightResponds
          cases impossible
      | outerLast rightResponds =>
          have replyEqual := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj replyEqual
          exact ⟨rfl, rfl, rfl⟩
  | outerNext leftResponds leftTail inductionHypothesis =>
      cases right with
      | innerQuery rightResponds rightTail =>
          have impossible := Part.mem_unique leftResponds rightResponds
          cases impossible
      | outerNext rightResponds rightTail =>
          have replyEqual := Part.mem_unique leftResponds rightResponds
          cases Sum.inr.inj replyEqual
          obtain ⟨inputsEqual, responsesEqual, finalEqual⟩ :=
            inductionHypothesis rightTail
          simp_all

private def firstQuery {A : Interface.{u, v}} (history : History A) : A.query :=
  history.queries.head history.nonempty

private def remainingQueries {A : Interface.{u, v}}
    (history : History A) : List A.query :=
  history.queries.tail

/--
A complete transcript is compatible when each converter response is selected
by its received history and each inner reply is the attached DDS value on the
complete attempted inner history.
-/
def Compatible
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A)
    (transcript : Transcript A B) : Prop :=
  CompatibleFrom converter system
    (DDC.History.singleton (B := B) (firstQuery outerHistory)) []
    (remainingQueries outerHistory) transcript.inputs transcript.responses
    transcript.final

private noncomputable def response
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (history : DDC.History A B)
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    DDC.Response history :=
  (converter.exists_unique_response history admissible).choose

private theorem response_mem
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (history : DDC.History A B)
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    response converter history admissible ∈ converter history :=
  (converter.exists_unique_response history admissible).choose_spec.1

private theorem exists_compatibleFrom
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) :
    ∀ (remainingOuter : List A.query) (history : DDC.History A B)
      (innerPrior : List B.query),
      DDC.Raw.Admissible converter.toFun history →
      ∃ inputs responses final,
        CompatibleFrom converter system history innerPrior remainingOuter
          inputs responses final := by
  intro remainingOuter
  induction remainingOuter with
  | nil =>
      intro history
      refine converter.branchFinite.induction (C := fun history =>
        ∀ innerPrior,
          DDC.Raw.Admissible converter.toFun history →
          ∃ inputs responses final,
            CompatibleFrom converter system history innerPrior []
              inputs responses final) history ?_
      intro history innerInduction innerPrior admissible
      cases responseEqual : response converter history admissible with
      | inl query =>
          let reply := innerReplyAt system innerPrior query
          let nextHistory := history.snocInner query reply
          have responds : Sum.inl query ∈ converter history :=
            responseEqual ▸ response_mem converter history admissible
          have nextAdmissible :
              DDC.Raw.Admissible converter.toFun nextHistory :=
            .afterInner admissible responds reply
          have decreases : DDC.Raw.InnerContinuation converter.toFun
              nextHistory history := ⟨query, reply, responds, rfl⟩
          obtain ⟨inputs, responses, final, tail⟩ :=
            innerInduction nextHistory decreases
              (innerPrior ++ [query]) nextAdmissible
          exact ⟨history.lastInput :: inputs, Sum.inl query :: responses,
            final, CompatibleFrom.innerQuery responds tail⟩
      | inr reply =>
          have responds : Sum.inr reply ∈ converter history :=
            responseEqual ▸ response_mem converter history admissible
          exact ⟨[history.lastInput],
            [Sum.inr ⟨history.lastOuter, reply⟩],
            ⟨history.lastOuter, reply⟩,
            CompatibleFrom.outerLast responds⟩
  | cons nextOuter remainingOuter outerInduction =>
      intro history
      refine converter.branchFinite.induction (C := fun history =>
        ∀ innerPrior,
          DDC.Raw.Admissible converter.toFun history →
          ∃ inputs responses final,
            CompatibleFrom converter system history innerPrior
              (nextOuter :: remainingOuter) inputs responses final)
        history ?_
      intro history innerInduction innerPrior admissible
      cases responseEqual : response converter history admissible with
      | inl query =>
          let reply := innerReplyAt system innerPrior query
          let nextHistory := history.snocInner query reply
          have responds : Sum.inl query ∈ converter history :=
            responseEqual ▸ response_mem converter history admissible
          have nextAdmissible :
              DDC.Raw.Admissible converter.toFun nextHistory :=
            .afterInner admissible responds reply
          have decreases : DDC.Raw.InnerContinuation converter.toFun
              nextHistory history := ⟨query, reply, responds, rfl⟩
          obtain ⟨inputs, responses, final, tail⟩ :=
            innerInduction nextHistory decreases
              (innerPrior ++ [query]) nextAdmissible
          exact ⟨history.lastInput :: inputs, Sum.inl query :: responses,
            final, CompatibleFrom.innerQuery responds tail⟩
      | inr reply =>
          have responds : Sum.inr reply ∈ converter history :=
            responseEqual ▸ response_mem converter history admissible
          let nextHistory := history.snocOuter nextOuter
          have nextAdmissible :
              DDC.Raw.Admissible converter.toFun nextHistory :=
            .afterOuter admissible responds nextOuter
          obtain ⟨inputs, responses, final, tail⟩ :=
            outerInduction nextHistory innerPrior nextAdmissible
          exact ⟨history.lastInput :: inputs,
            Sum.inr ⟨history.lastOuter, reply⟩ :: responses, final,
            CompatibleFrom.outerNext responds tail⟩

/-- Every branch-finite attachment has a compatible finite transcript. -/
theorem exists_compatible
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A) :
    ∃ transcript, Compatible converter system outerHistory transcript := by
  let start := DDC.History.singleton (B := B) (firstQuery outerHistory)
  have startAdmissible : DDC.Raw.Admissible converter.toFun start :=
    .start (firstQuery outerHistory)
  obtain ⟨inputs, responses, final, compatible⟩ :=
    exists_compatibleFrom converter system (remainingQueries outerHistory)
      start [] startAdmissible
  exact ⟨⟨inputs, responses, final⟩, compatible⟩

/-- A compatible attachment transcript is unique. -/
theorem compatible_unique
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A)
    {left right : Transcript A B}
    (leftCompatible : Compatible converter system outerHistory left)
    (rightCompatible : Compatible converter system outerHistory right) :
    left = right := by
  obtain ⟨inputsEqual, responsesEqual, finalEqual⟩ :=
    CompatibleFrom.unique leftCompatible rightCompatible
  exact Transcript.ext inputsEqual responsesEqual finalEqual

/-- Exactly one compatible attachment transcript exists. -/
theorem exists_unique_compatible
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A) :
    ∃! transcript, Compatible converter system outerHistory transcript := by
  obtain ⟨transcript, compatible⟩ :=
    exists_compatible converter system outerHistory
  exact ⟨transcript, compatible, fun other otherCompatible =>
    compatible_unique converter system outerHistory otherCompatible compatible⟩

private noncomputable def compatibleTranscript
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A) :
    Transcript A B :=
  (exists_unique_compatible converter system outerHistory).choose

private theorem compatibleTranscript_compatible
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A) :
    Compatible converter system outerHistory
      (compatibleTranscript converter system outerHistory) :=
  (exists_unique_compatible converter system outerHistory).choose_spec.1

private def outerContinuation
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (history : DDC.History A B) (remaining : List A.query) : History A where
  queries := history.outer.queries ++ remaining
  nonempty := List.append_ne_nil_of_left_ne_nil history.outer.nonempty remaining

private theorem CompatibleFrom.final_query_eq
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {system : DDS B}
    {history : DDC.History A B} {innerPrior : List B.query}
    {remainingOuter : List A.query}
    {inputs : List (DDC.History.Input A B)}
    {responses : List (Response A B)} {final : DDC.History.InnerReply A}
    (compatible : CompatibleFrom converter system history innerPrior
      remainingOuter inputs responses final) :
    final.1 = (outerContinuation history remainingOuter).last := by
  induction compatible with
  | innerQuery responds tail inductionHypothesis =>
      simpa [outerContinuation, DDC.History.snocInner] using
        inductionHypothesis
  | @outerLast history innerPrior reply responds =>
      have equal : outerContinuation history [] = history.outer := by
        apply History.ext
        simp [outerContinuation]
      exact congrArg History.last equal.symm
  | @outerNext history innerPrior reply nextOuter remainingOuter tailInputs
      tailResponses final responds tail inductionHypothesis =>
      have equal : outerContinuation (history.snocOuter nextOuter)
          remainingOuter =
          outerContinuation history (nextOuter :: remainingOuter) := by
        apply History.ext
        change (history.outer.queries ++ [nextOuter]) ++ remainingOuter =
          history.outer.queries ++ nextOuter :: remainingOuter
        rw [List.append_assoc, List.singleton_append]
      exact (congrArg History.last equal).symm ▸ inductionHypothesis

/-- The final answer belongs to the fibre selected by the final outer query. -/
theorem Compatible.final_query_eq_last
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {system : DDS B}
    {outerHistory : History A} {transcript : Transcript A B}
    (compatible : Compatible converter system outerHistory transcript) :
    transcript.final.1 = outerHistory.last := by
  have equal := CompatibleFrom.final_query_eq compatible
  have historyEqual : outerContinuation
      (DDC.History.singleton (B := B) (firstQuery outerHistory))
      (remainingQueries outerHistory) = outerHistory := by
    apply History.ext
    change firstQuery outerHistory :: remainingQueries outerHistory =
      outerHistory.queries
    exact List.cons_head_tail outerHistory.nonempty
  exact equal.trans (congrArg History.last historyEqual)

/-- Select a query's answer from a packed query-indexed reply. -/
noncomputable def selectReply
    {A : Interface.{u, v}} (query : A.query) (reply : DDC.History.InnerReply A) :
    Option (A.answer query) := by
  classical
  exact if equal : reply.1 = query then equal ▸ reply.2 else none

/-- Selecting at the packed query recovers its dependent answer. -/
theorem selectReply_heq_second
    {A : Interface.{u, v}} (query : A.query) (reply : DDC.History.InnerReply A)
    (equal : reply.1 = query) : selectReply query reply ≍ reply.2 := by
  unfold selectReply
  split
  next selected =>
    exact eqRec_heq (φ := fun query => Option (A.answer query)) selected reply.2
  next rejected => exact (rejected equal).elim

private def forwardingFinal
    {A : Interface.{u, v}} (system : DDS A)
    (innerPrior : List A.query) (current : A.query) :
    List A.query → DDC.History.InnerReply A
  | [] => ⟨current, innerReplyAt system innerPrior current⟩
  | next :: remaining =>
      forwardingFinal system (innerPrior ++ [current]) next remaining

private theorem compatibleFrom_forwarding
    {A : Interface.{u, v}} (system : DDS A)
    (history : DDC.History A A) (innerPrior : List A.query)
    (current : A.query)
    (lastInput : history.lastInput = Sum.inl current)
    (lastOuter : history.lastOuter = current)
    (admissible : DDC.Raw.Admissible (DDC.forwarding A).toFun history) :
    ∀ remaining,
      ∃ inputs responses,
        CompatibleFrom (DDC.forwarding A) system history innerPrior remaining
          inputs responses
          (forwardingFinal system innerPrior current remaining) := by
  intro remaining
  induction remaining generalizing history innerPrior current with
  | nil =>
      subst current
      have queryResponds : Sum.inl history.lastOuter ∈
          DDC.forwarding A history := by
        apply (DDC.mem_forwarding_iff A history _).mpr
        refine ⟨admissible, ?_⟩
        rw [lastInput]
      let answer := innerReplyAt system innerPrior history.lastOuter
      let after := history.snocInner history.lastOuter answer
      have afterAdmissible :
          DDC.Raw.Admissible (DDC.forwarding A).toFun after :=
        .afterInner admissible queryResponds answer
      have replyResponds : Sum.inr answer ∈ DDC.forwarding A after := by
        apply (DDC.mem_forwarding_iff A after _).mpr
        refine ⟨afterAdmissible, ?_⟩
        simp [after]
      refine ⟨[history.lastInput, after.lastInput],
        [Sum.inl history.lastOuter,
          Sum.inr ⟨after.lastOuter, answer⟩], ?_⟩
      apply CompatibleFrom.innerQuery queryResponds
      simpa [forwardingFinal, answer, after] using
        (CompatibleFrom.outerLast replyResponds)
  | cons next remaining inductionHypothesis =>
      subst current
      have queryResponds : Sum.inl history.lastOuter ∈
          DDC.forwarding A history := by
        apply (DDC.mem_forwarding_iff A history _).mpr
        refine ⟨admissible, ?_⟩
        rw [lastInput]
      let answer := innerReplyAt system innerPrior history.lastOuter
      let after := history.snocInner history.lastOuter answer
      have afterAdmissible :
          DDC.Raw.Admissible (DDC.forwarding A).toFun after :=
        .afterInner admissible queryResponds answer
      have replyResponds : Sum.inr answer ∈ DDC.forwarding A after := by
        apply (DDC.mem_forwarding_iff A after _).mpr
        refine ⟨afterAdmissible, ?_⟩
        simp [after]
      let nextHistory := after.snocOuter next
      have nextAdmissible :
          DDC.Raw.Admissible (DDC.forwarding A).toFun nextHistory :=
        .afterOuter afterAdmissible replyResponds next
      obtain ⟨tailInputs, tailResponses, tail⟩ :=
        inductionHypothesis nextHistory
          (innerPrior ++ [history.lastOuter]) next
          (by simp [nextHistory]) (by simp [nextHistory]) nextAdmissible
      refine ⟨history.lastInput :: after.lastInput :: tailInputs,
        Sum.inl history.lastOuter ::
          Sum.inr ⟨after.lastOuter, answer⟩ :: tailResponses, ?_⟩
      apply CompatibleFrom.innerQuery queryResponds
      apply CompatibleFrom.outerNext replyResponds
      simpa [forwardingFinal, answer, nextHistory] using tail

private def appendHistory
    {A : Interface.{u, v}} (prior : List A.query) (current : A.query)
    (remaining : List A.query) : History A where
  queries := prior ++ current :: remaining
  nonempty := by simp

private theorem forwardingFinal_eq
    {A : Interface.{u, v}} (system : DDS A)
    (prior : List A.query) (current : A.query)
    (remaining : List A.query) :
    forwardingFinal system prior current remaining =
      ⟨(appendHistory prior current remaining).last,
        system (appendHistory prior current remaining)⟩ := by
  induction remaining generalizing prior current with
  | nil =>
      have historyEqual : appendHistory prior current [] =
          innerHistory prior current := by
        apply History.ext
        rfl
      rw [historyEqual]
      simp only [forwardingFinal]
      apply Sigma.ext (last_innerHistory prior current).symm
      unfold innerReplyAt
      exact cast_heq _ _
  | cons next remaining inductionHypothesis =>
      rw [forwardingFinal, inductionHypothesis]
      have historyEqual :
          appendHistory (prior ++ [current]) next remaining =
            appendHistory prior current (next :: remaining) := by
        apply History.ext
        simp [appendHistory, List.append_assoc]
      rw [historyEqual]

end Attachment

/-- Attachment of a DDC to a DDS. -/
noncomputable def applySystem
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) : DDS A :=
  fun outerHistory => Attachment.selectReply outerHistory.last
    (Attachment.compatibleTranscript converter system outerHistory).final

/-- Attachment has one canonical compatible transcript at every outer
history. -/
theorem applySystem_has_unique_transcript
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A) :
    ∃! transcript,
      Attachment.Compatible converter system outerHistory transcript ∧
      HEq transcript.final.2 (applySystem converter system outerHistory) := by
  let transcript := Attachment.compatibleTranscript converter system outerHistory
  have compatible :=
    Attachment.compatibleTranscript_compatible converter system outerHistory
  have finalQuery :=
    Attachment.Compatible.final_query_eq_last (compatible := compatible)
  have selected := Attachment.selectReply_heq_second outerHistory.last
    transcript.final finalQuery
  refine ⟨transcript, ⟨compatible, selected.symm⟩, ?_⟩
  intro other otherProperty
  exact Attachment.compatible_unique converter system outerHistory
    otherProperty.1 compatible

/-- Exact compatible-transcript characterization of attachment. -/
theorem applySystem_eq_iff
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A)
    (reply : Option (A.answer outerHistory.last)) :
    applySystem converter system outerHistory = reply ↔
      ∃ transcript,
        Attachment.Compatible converter system outerHistory transcript ∧
        HEq transcript.final.2 reply := by
  constructor
  · intro equal
    let transcript := Attachment.compatibleTranscript converter system outerHistory
    have compatible :=
      Attachment.compatibleTranscript_compatible converter system outerHistory
    have finalQuery :=
      Attachment.Compatible.final_query_eq_last (compatible := compatible)
    have selected := Attachment.selectReply_heq_second outerHistory.last
      transcript.final finalQuery
    exact ⟨transcript, compatible, selected.symm.trans (heq_of_eq equal)⟩
  · rintro ⟨transcript, compatible, finalEqual⟩
    have transcriptEqual := Attachment.compatible_unique converter system
      outerHistory compatible
      (Attachment.compatibleTranscript_compatible converter system outerHistory)
    subst transcript
    have finalQuery :=
      Attachment.Compatible.final_query_eq_last (compatible := compatible)
    have selected := Attachment.selectReply_heq_second outerHistory.last
      (Attachment.compatibleTranscript converter system outerHistory).final
      finalQuery
    exact eq_of_heq (selected.trans finalEqual)

/-- Rejection is the ordinary final answer `none` of the same compatible
transcript. -/
theorem applySystem_eq_none_iff
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (outerHistory : History A) :
    applySystem converter system outerHistory = none ↔
      ∃ transcript,
        Attachment.Compatible converter system outerHistory transcript ∧
        HEq transcript.final.2
          (none : Option (A.answer outerHistory.last)) :=
  applySystem_eq_iff converter system outerHistory none

/-- Forwarding attachment is the identity on deterministic discrete systems. -/
@[simp]
theorem applySystem_forwarding_eq
    (A : Interface.{u, v}) (system : DDS A) :
    applySystem (DDC.forwarding A) system = system := by
  apply DDS.ext
  intro outerHistory
  rw [applySystem_eq_iff]
  let start := DDC.History.singleton (B := A)
    (Attachment.firstQuery outerHistory)
  have admissible :
      DDC.Raw.Admissible (DDC.forwarding A).toFun start :=
    .start (Attachment.firstQuery outerHistory)
  obtain ⟨inputs, responses, compatible⟩ :=
    Attachment.compatibleFrom_forwarding system start []
      (Attachment.firstQuery outerHistory) (by simp [start])
      (by simp [start]) admissible (Attachment.remainingQueries outerHistory)
  let transcript : Attachment.Transcript A A :=
    { inputs := inputs
      responses := responses
      final := Attachment.forwardingFinal system []
        (Attachment.firstQuery outerHistory)
        (Attachment.remainingQueries outerHistory) }
  refine ⟨transcript, compatible, ?_⟩
  have historyEqual : Attachment.appendHistory []
      (Attachment.firstQuery outerHistory)
      (Attachment.remainingQueries outerHistory) = outerHistory := by
    apply History.ext
    change Attachment.firstQuery outerHistory ::
      Attachment.remainingQueries outerHistory = outerHistory.queries
    exact List.cons_head_tail outerHistory.nonempty
  change HEq
    (Attachment.forwardingFinal system []
      (Attachment.firstQuery outerHistory)
      (Attachment.remainingQueries outerHistory)).2
    (system outerHistory)
  rw [Attachment.forwardingFinal_eq, historyEqual]

/-- Forwarding preserves rejection exactly as the ordinary answer `none`. -/
theorem applySystem_forwarding_none_iff
    (A : Interface.{u, v}) (system : DDS A) (history : History A) :
    applySystem (DDC.forwarding A) system history = none ↔
      system history = none := by
  rw [applySystem_forwarding_eq]

end RandomSystems.Ambient
