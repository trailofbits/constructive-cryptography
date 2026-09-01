/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.BoundedInnerQueries

set_option autoImplicit false

/-!
# Filters

A filter is the one-query DDC that either forwards the current outer query or
answers `none`.  Its acceptance function receives the complete attempted outer
history.  Rejected attempts therefore remain arguments of the filter on later
queries, while only forwarded queries occur in the attached DDS history.

This is a repository one-inner-query DDC constructor derived from Jost's
bounded-query converter condition. It is not a specification-level choice
setting.
-/

namespace RandomSystems.Ambient

universe u v w z

namespace DDC

variable {U : Type u} {V : Type v} {X : Type w} {Y : Type z}

/-- Outer queries in a complete received DDC history. -/
def outerQueries
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) : List U :=
  history.outer.queries

@[simp]
theorem outerQueries_singleton (query : U) :
    outerQueries (V := V) (X := X) (Y := Y)
      (DDC.History.singleton query) = [query] :=
  rfl

@[simp]
theorem outerQueries_snocOuter
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) (query : U) :
    outerQueries (history.snocOuter query) = outerQueries history ++ [query] :=
  rfl

@[simp]
theorem outerQueries_snocInner
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (query : X) (reply : Option Y) :
    outerQueries (history.snocInner query reply) = outerQueries history :=
  rfl

/-- The complete-history response function of a filter. -/
def filterResponse (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) :
    DDC.Response history :=
  responseWithInnerQueryBound 1
    (fun history _ =>
      if accept (outerQueries history) then
        Sum.inl (query history.lastOuter)
      else
        Sum.inr none)
    (fun history reached =>
      reply history.lastOuter
        ((latestReplies history).getLast
          (List.ne_nil_of_length_pos (Nat.zero_lt_one.trans_le reached))))
    history

/-- A history-sensitive filter. An accepted outer query is forwarded once;
a rejected outer query returns `none` without issuing an inner query. -/
noncomputable def filter (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V) :
    DDC (Interface.single U V) (Interface.single X Y) :=
  ofInnerQueryBound 1
    (fun history _ =>
      if accept (outerQueries history) then
        Sum.inl (query history.lastOuter)
      else
        Sum.inr none)
    (fun history reached =>
      reply history.lastOuter
        ((latestReplies history).getLast
          (List.ne_nil_of_length_pos (Nat.zero_lt_one.trans_le reached))))

/-- The canonical filter graph is its complete-history response function on
every admissible history. -/
theorem mem_filter_iff (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (response : DDC.Response history) :
    response ∈ filter accept query reply history ↔
      DDC.Raw.Admissible (filter accept query reply).toFun history ∧
        response = filterResponse accept query reply history := by
  rw [filter, mem_ofInnerQueryBound_iff]
  rfl

theorem filter_mem_query (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (admissible : DDC.Raw.Admissible
      (filter accept query reply).toFun history)
    (noReplies : latestReplies history = [])
    (accepted : accept (outerQueries history)) :
    Sum.inl (query history.lastOuter) ∈
      filter accept query reply history := by
  apply (mem_filter_iff accept query reply history
    (show DDC.Response history from
      Sum.inl (query history.lastOuter))).mpr
  refine ⟨admissible, ?_⟩
  simp [filterResponse, responseWithInnerQueryBound, noReplies, accepted]

theorem filter_mem_reject (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (admissible : DDC.Raw.Admissible
      (filter accept query reply).toFun history)
    (noReplies : latestReplies history = [])
    (rejected : ¬ accept (outerQueries history)) :
    Sum.inr (none : Option V) ∈ filter accept query reply history := by
  apply (mem_filter_iff accept query reply history
    (show DDC.Response history from Sum.inr (none : Option V))).mpr
  refine ⟨admissible, ?_⟩
  simp [filterResponse, responseWithInnerQueryBound, noReplies, rejected]

theorem filter_mem_reply (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (admissible : DDC.Raw.Admissible
      (filter accept query reply).toFun history)
    (noReplies : latestReplies history = [])
    (queryResponse : Sum.inl (query history.lastOuter) ∈
      filter accept query reply history)
    (innerReply : Option Y) :
    Sum.inr (reply history.lastOuter innerReply) ∈
      filter accept query reply
        (history.snocInner (query history.lastOuter) innerReply) := by
  apply (mem_filter_iff accept query reply
    (history.snocInner (query history.lastOuter) innerReply)
    (show DDC.Response
        (history.snocInner (query history.lastOuter) innerReply) from
      Sum.inr (reply history.lastOuter innerReply))).mpr
  constructor
  · exact .afterInner admissible queryResponse innerReply
  · simp [filterResponse, responseWithInnerQueryBound, noReplies]

/-- Queries forwarded by a filter while extending one outer prefix. -/
def acceptedQueriesFrom (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (prior : List U) : List U → List X
  | [] => []
  | input :: remaining =>
      if accept (prior ++ [input]) then
        query input :: acceptedQueriesFrom accept query
          (prior ++ [input]) remaining
      else
        acceptedQueriesFrom accept query (prior ++ [input]) remaining

theorem acceptedQueriesFrom_append (accept : List U → Prop)
    [DecidablePred accept]
    (query : U → X) (prior left right : List U) :
    acceptedQueriesFrom accept query prior (left ++ right) =
      acceptedQueriesFrom accept query prior left ++
        acceptedQueriesFrom accept query (prior ++ left) right := by
  induction left generalizing prior with
  | nil => simp [acceptedQueriesFrom]
  | cons input remaining inductionHypothesis =>
      simp only [List.cons_append, acceptedQueriesFrom]
      split_ifs <;>
        simp only [List.cons_append, List.append_assoc,
          List.nil_append, inductionHypothesis]

/-- All inner queries forwarded from one complete outer history. -/
def acceptedQueries (accept : List U → Prop) [DecidablePred accept]
    (query : U → X)
    (history : _root_.RandomSystems.Ambient.History
      (Interface.single U V)) : List X :=
  acceptedQueriesFrom accept query [] history.queries

theorem acceptedQueriesFrom_nonempty_of_last_accept
    (accept : List U → Prop) [DecidablePred accept] (query : U → X)
    (prior inputs : List U) (nonempty : inputs ≠ [])
    (accepted : accept (prior ++ inputs)) :
    acceptedQueriesFrom accept query prior inputs ≠ [] := by
  induction inputs generalizing prior with
  | nil => exact (nonempty rfl).elim
  | cons input remaining inductionHypothesis =>
      by_cases remainingEmpty : remaining = []
      · subst remaining
        simp [acceptedQueriesFrom] at accepted ⊢
        exact accepted
      · unfold acceptedQueriesFrom
        by_cases current : accept (prior ++ [input])
        · simp [current]
        · simp [current]
          apply inductionHypothesis (prior ++ [input]) remainingEmpty
          simpa [List.append_assoc] using accepted

/-- The nonempty inner-query history forwarded from an accepted outer
history. -/
def acceptedQueryHistory (accept : List U → Prop) [DecidablePred accept]
    (query : U → X)
    (history : _root_.RandomSystems.Ambient.History
      (Interface.single U V))
    (accepted : accept history.queries) :
    _root_.RandomSystems.Ambient.History (Interface.single X Y) :=
  ⟨acceptedQueries accept query history,
    acceptedQueriesFrom_nonempty_of_last_accept accept query []
      history.queries history.nonempty (by simpa using accepted)⟩

theorem last_append_singleton (prior : List U) (query : U)
    (nonempty : prior ++ [query] ≠ []) :
    (_root_.RandomSystems.Ambient.History.mk
      (A := Interface.single U V) (prior ++ [query]) nonempty).last = query := by
  unfold _root_.RandomSystems.Ambient.History.last
  have proofEqual : nonempty =
      List.append_ne_nil_of_right_ne_nil prior (List.cons_ne_nil query []) :=
    Subsingleton.elim _ _
  subst nonempty
  exact List.getLast_append_singleton prior

theorem innerReplyAt_eq
    (system : DDS (Interface.single X Y)) (prior : List X) (query : X) :
    Attachment.innerReplyAt system prior query =
      system (Attachment.innerHistory prior query) := by
  unfold Attachment.innerReplyAt
  change cast _ (system (Attachment.innerHistory prior query)) = _
  generalize_proofs equal
  rw [show equal = Eq.refl (Option Y) from Subsingleton.elim _ _]
  rfl

theorem acceptedQueryHistory_append_current
    (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (prior : List U) (input : U)
    (accepted : accept (prior ++ [input])) :
    acceptedQueryHistory (V := V) (Y := Y) accept query
        ⟨prior ++ [input],
          List.append_ne_nil_of_right_ne_nil prior
            (List.cons_ne_nil input [])⟩ accepted =
      Attachment.innerHistory
        (acceptedQueriesFrom accept query [] prior) (query input) := by
  apply _root_.RandomSystems.Ambient.History.ext
  change acceptedQueriesFrom accept query [] (prior ++ [input]) = _
  rw [acceptedQueriesFrom_append]
  simp [acceptedQueriesFrom, accepted, Attachment.innerHistory]

def filterValue (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (system : DDS (Interface.single X Y))
    (history : _root_.RandomSystems.Ambient.History
      (Interface.single U V)) : Option V :=
  if accepted : accept history.queries then
    reply history.last
      (system (acceptedQueryHistory (Y := Y) accept query history accepted))
  else
    none

theorem filter_compatibleFrom
    (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (system : DDS (Interface.single X Y))
    (whole : _root_.RandomSystems.Ambient.History
      (Interface.single U V))
    (prior : List U) (input : U) (remaining : List U)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (innerPrior : List X)
    (wholeEqual : whole.queries = prior ++ input :: remaining)
    (outerEqual : outerQueries history = prior ++ [input])
    (lastOuter : history.lastOuter = input)
    (noReplies : latestReplies history = [])
    (innerEqual : innerPrior = acceptedQueriesFrom accept query [] prior)
    (admissible : DDC.Raw.Admissible
      (filter accept query reply).toFun history) :
    ∃ inputs responses,
      Attachment.CompatibleFrom (filter accept query reply) system history
        innerPrior remaining inputs responses
        ⟨whole.last, filterValue accept query reply system whole⟩ := by
  induction remaining generalizing prior input history innerPrior with
  | nil =>
      have wholeCurrent : whole =
          ({ queries := prior ++ [input]
             nonempty := List.append_ne_nil_of_right_ne_nil prior
               (List.cons_ne_nil input []) } :
            _root_.RandomSystems.Ambient.History
              (Interface.single U V)) := by
        apply _root_.RandomSystems.Ambient.History.ext
        simpa using wholeEqual
      by_cases accepted : accept (prior ++ [input])
      · have queryResponds' : Sum.inl (query history.lastOuter) ∈
            filter accept query reply history :=
          filter_mem_query accept query reply history admissible noReplies
            (outerEqual.symm ▸ accepted)
        let innerReply := Attachment.innerReplyAt system innerPrior
          (query history.lastOuter)
        let after := history.snocInner (query history.lastOuter) innerReply
        have outerResponds :
            Sum.inr (reply history.lastOuter innerReply) ∈
              filter accept query reply after := by
          simpa [after] using
            filter_mem_reply accept query reply history admissible noReplies
              queryResponds' innerReply
        have wholeLast : whole.last = input := by
          subst whole
          exact last_append_singleton prior input _
        have afterLast : after.lastOuter = input := by
          simp [after, lastOuter]
        have wholeAccepted : accept whole.queries := by
          simpa [wholeCurrent] using accepted
        have innerReplyEqual : innerReply =
            system (acceptedQueryHistory (Y := Y) accept query whole
              wholeAccepted) := by
          subst whole
          dsimp only [innerReply]
          rw [innerReplyAt_eq, innerEqual, lastOuter]
          rw [show wholeAccepted = accepted from Subsingleton.elim _ _]
          exact congrArg
            (show (_root_.RandomSystems.Ambient.History
                (Interface.single X Y) → Option Y) from system)
            (acceptedQueryHistory_append_current
              (V := V) (Y := Y) accept query prior input accepted).symm
        have finalEqual :
            (⟨after.lastOuter, reply history.lastOuter innerReply⟩ :
                DDC.History.InnerReply (Interface.single U V)) =
              ⟨whole.last, filterValue accept query reply system whole⟩ := by
          rw [afterLast, wholeLast, lastOuter]
          apply congrArg (Sigma.mk input)
          rw [filterValue, dif_pos wholeAccepted, innerReplyEqual]
          exact congrArg
            (fun current => reply current
              (system (acceptedQueryHistory (Y := Y) accept query whole
                wholeAccepted))) wholeLast.symm
        refine ⟨[history.lastInput, after.lastInput],
          [Sum.inl (query history.lastOuter),
            Sum.inr ⟨after.lastOuter,
              reply history.lastOuter innerReply⟩],
          Attachment.CompatibleFrom.innerQuery queryResponds' ?_⟩
        have closes := Attachment.CompatibleFrom.outerLast
          (system := system)
          (innerPrior := innerPrior ++ [query history.lastOuter])
          outerResponds
        exact finalEqual ▸ closes
      · have rejectResponds : Sum.inr (none : Option V) ∈
            filter accept query reply history :=
          filter_mem_reject accept query reply history admissible noReplies
            (by simpa [outerEqual] using accepted)
        refine ⟨[history.lastInput],
          [Sum.inr ⟨history.lastOuter, (none : Option V)⟩], ?_⟩
        have wholeLast : whole.last = input := by
          subst whole
          exact last_append_singleton prior input _
        have wholeRejected : ¬ accept whole.queries := by
          simpa [wholeCurrent] using accepted
        have finalEqual :
            (⟨history.lastOuter, (none : Option V)⟩ :
                DDC.History.InnerReply (Interface.single U V)) =
              ⟨whole.last, filterValue accept query reply system whole⟩ := by
          rw [lastOuter, wholeLast]
          apply congrArg (Sigma.mk input)
          rw [filterValue, dif_neg wholeRejected]
        have closes := Attachment.CompatibleFrom.outerLast
          (system := system) (innerPrior := innerPrior) rejectResponds
        exact finalEqual ▸ closes
  | cons next rest inductionHypothesis =>
      by_cases accepted : accept (prior ++ [input])
      · have queryResponds' : Sum.inl (query history.lastOuter) ∈
            filter accept query reply history :=
          filter_mem_query accept query reply history admissible noReplies
            (outerEqual.symm ▸ accepted)
        let innerReply := Attachment.innerReplyAt system innerPrior
          (query history.lastOuter)
        let after := history.snocInner (query history.lastOuter) innerReply
        have afterAdmissible : DDC.Raw.Admissible
            (filter accept query reply).toFun after :=
          .afterInner admissible queryResponds' innerReply
        have outerResponds :
            Sum.inr (reply history.lastOuter innerReply) ∈
              filter accept query reply after := by
          simpa [after] using
            filter_mem_reply accept query reply history admissible noReplies
              queryResponds' innerReply
        let nextHistory := after.snocOuter next
        have nextAdmissible : DDC.Raw.Admissible
            (filter accept query reply).toFun nextHistory :=
          .afterOuter afterAdmissible outerResponds next
        have nextInnerEqual : innerPrior ++ [query history.lastOuter] =
            acceptedQueriesFrom accept query [] (prior ++ [input]) := by
          rw [acceptedQueriesFrom_append]
          simp [acceptedQueriesFrom, accepted, innerEqual, lastOuter]
        obtain ⟨tailInputs, tailResponses, tail⟩ :=
          inductionHypothesis (prior ++ [input]) next nextHistory
            (innerPrior ++ [query history.lastOuter])
            (by simpa [List.append_assoc] using wholeEqual)
            (by simp [nextHistory, after, outerEqual])
            (by simp [nextHistory])
            (by simp [nextHistory])
            nextInnerEqual nextAdmissible
        refine ⟨history.lastInput :: after.lastInput :: tailInputs,
          Sum.inl (query history.lastOuter) ::
            Sum.inr ⟨after.lastOuter,
              reply history.lastOuter innerReply⟩ :: tailResponses,
          Attachment.CompatibleFrom.innerQuery queryResponds' ?_⟩
        simpa [after, nextHistory] using
          (Attachment.CompatibleFrom.outerNext outerResponds tail)
      · have rejectResponds : Sum.inr (none : Option V) ∈
            filter accept query reply history :=
          filter_mem_reject accept query reply history admissible noReplies
            (by simpa [outerEqual] using accepted)
        let nextHistory := history.snocOuter next
        have nextAdmissible : DDC.Raw.Admissible
            (filter accept query reply).toFun nextHistory :=
          .afterOuter admissible rejectResponds next
        have nextInnerEqual : innerPrior =
            acceptedQueriesFrom accept query [] (prior ++ [input]) := by
          rw [acceptedQueriesFrom_append]
          simp [acceptedQueriesFrom, accepted, innerEqual]
        obtain ⟨tailInputs, tailResponses, tail⟩ :=
          inductionHypothesis (prior ++ [input]) next nextHistory innerPrior
            (by simpa [List.append_assoc] using wholeEqual)
            (by simp [nextHistory, outerEqual])
            (by simp [nextHistory])
            (by simp [nextHistory])
            nextInnerEqual nextAdmissible
        exact ⟨history.lastInput :: tailInputs,
          Sum.inr ⟨history.lastOuter, (none : Option V)⟩ :: tailResponses, by
          simpa [nextHistory] using
            (Attachment.CompatibleFrom.outerNext rejectResponds tail)⟩

theorem applySystem_filter_eq
    (accept : List U → Prop) [DecidablePred accept]
    (query : U → X) (reply : U → Option Y → Option V)
    (system : DDS (Interface.single X Y)) :
    applySystem (filter accept query reply) system =
      fun history => filterValue accept query reply system history := by
  apply DDS.ext
  intro whole
  rw [applySystem_eq_iff]
  let first := whole.queries.head whole.nonempty
  let remaining := whole.queries.tail
  let start := DDC.History.singleton
    (B := Interface.single X Y) first
  have admissible : DDC.Raw.Admissible
      (filter accept query reply).toFun start :=
    .start first
  obtain ⟨inputs, responses, compatible⟩ :=
    filter_compatibleFrom accept query reply system whole [] first remaining
      start []
      (by
        change whole.queries = first :: remaining
        exact (List.cons_head_tail whole.nonempty).symm)
      (by simp [start, first])
      (by simp [start])
      (by simp [start])
      (by simp [acceptedQueriesFrom]) admissible
  let transcript : Attachment.Transcript
      (Interface.single U V) (Interface.single X Y) :=
    ⟨inputs, responses,
      ⟨whole.last, filterValue accept query reply system whole⟩⟩
  exact ⟨transcript, compatible, HEq.rfl⟩

theorem acceptedQueriesFrom_eq_map
    (accept : List U → Prop) [DecidablePred accept]
    (prefixClosed : ∀ {priorPrefix wholeHistory : List U},
      priorPrefix <+: wholeHistory → accept wholeHistory → accept priorPrefix)
    (query : U → X) (prior inputs : List U)
    (accepted : accept (prior ++ inputs)) :
    acceptedQueriesFrom accept query prior inputs = inputs.map query := by
  induction inputs generalizing prior with
  | nil => rfl
  | cons input remaining inductionHypothesis =>
      have currentPrefix : prior ++ [input] <+:
          prior ++ input :: remaining :=
        ⟨remaining, by simp [List.append_assoc]⟩
      have currentAccepted : accept (prior ++ [input]) :=
        prefixClosed currentPrefix (by simpa using accepted)
      rw [acceptedQueriesFrom]
      simp only [currentAccepted, if_pos, List.map_cons, List.cons.injEq,
        true_and]
      apply inductionHypothesis (prior ++ [input])
      simpa [List.append_assoc] using accepted

theorem acceptedQueryHistory_eq_map
    (accept : List U → Prop) [DecidablePred accept]
    (prefixClosed : ∀ {priorPrefix wholeHistory : List U},
      priorPrefix <+: wholeHistory → accept wholeHistory → accept priorPrefix)
    (query : U → X)
    (history : _root_.RandomSystems.Ambient.History
      (Interface.single U V))
    (accepted : accept history.queries) :
    acceptedQueryHistory (Y := Y) accept query history accepted =
      _root_.RandomSystems.Ambient.History.map query history := by
  apply _root_.RandomSystems.Ambient.History.ext
  change acceptedQueriesFrom accept query [] history.queries =
    history.queries.map query
  exact acceptedQueriesFrom_eq_map accept prefixClosed query []
    history.queries (by simpa using accepted)

/-- Attachment of a prefix-closed filter forwards the complete mapped query
history when the final query is admitted, and returns `none` otherwise. -/
theorem applySystem_filter_of_prefix_closed
    (accept : List U → Prop) [DecidablePred accept]
    (prefixClosed : ∀ {priorPrefix wholeHistory : List U},
      priorPrefix <+: wholeHistory → accept wholeHistory → accept priorPrefix)
    (query : U → X) (reply : U → Option Y → Option V)
    (system : DDS (Interface.single X Y)) :
    applySystem (filter accept query reply) system =
      fun history =>
        if accept history.queries then
          reply history.last
            (system
              (_root_.RandomSystems.Ambient.History.map query history))
        else
          none := by
  -- Start from the exact attachment equation.
  rw [applySystem_filter_eq]
  apply DDS.ext
  intro history
  -- Prefix closure means every query in an admitted history was forwarded.
  by_cases accepted : accept history.queries
  · rw [filterValue, dif_pos accepted, if_pos accepted,
      acceptedQueryHistory_eq_map accept prefixClosed query history accepted]
  · rw [filterValue, dif_neg accepted, if_neg accepted]

end DDC

end RandomSystems.Ambient
