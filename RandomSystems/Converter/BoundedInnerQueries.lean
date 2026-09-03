/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Relabel
import Mathlib.Tactic

set_option autoImplicit false

/-!
# DDCs with bounded inner queries

Jost, immediately before Definition 2.2.2 (printed p. 17), states that a
converter is “allowed to make a bounded number of queries to the inside
interfaces.”  The constructors here turn ordinary Lean functions into
query-indexed DDCs and prove their attachment equations.  They do not define a
second converter semantics: every constructor returns the same canonical DDC
carrier used by serial composition and relabeling.
-/

namespace RandomSystems.Ambient

universe u v w z

open DDC.Internal

namespace DDC

open Internal

namespace Internal

/-- The raw table for a noninteractive one-query converter. -/
noncomputable def rawOneQuery
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) : DDC.Raw A B := by
  classical
  exact fun history =>
    match history.lastInput with
    | Sum.inl outer => Part.some (Sum.inl (query outer))
    | Sum.inr ⟨inner, answer⟩ =>
        if equal : inner = query history.lastOuter then
          Part.some (Sum.inr (reply history.lastOuter (equal ▸ answer)))
        else Part.none

@[simp]
theorem rawOneQuery_singleton
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (outer : A.query) :
    rawOneQuery query reply (DDC.History.singleton outer) =
      Part.some (Sum.inl (query outer)) := by
  unfold rawOneQuery
  rw [DDC.History.lastInput_singleton]

@[simp]
theorem rawOneQuery_snocOuter
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (history : DDC.History A B)
    (outer : A.query) :
    rawOneQuery query reply (history.snocOuter outer) =
      Part.some (Sum.inl (query outer)) := by
  unfold rawOneQuery
  rw [DDC.History.lastInput_snocOuter]

theorem rawOneQuery_snocInner_of_eq
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (history : DDC.History A B)
    (inner : B.query) (answer : Option (B.answer inner))
    (equal : inner = query history.lastOuter) :
    rawOneQuery query reply (history.snocInner inner answer) =
      Part.some (Sum.inr
        (reply history.lastOuter (equal ▸ answer))) := by
  classical
  unfold rawOneQuery
  rw [DDC.History.lastInput_snocInner]
  simp [equal]
  rfl

theorem not_mem_rawOneQuery_of_lastInput_inner
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (history : DDC.History A B)
    (inner : DDC.History.InnerReply B) (equal : history.lastInput = Sum.inr inner)
    (next : B.query) :
    ¬ Sum.inl next ∈ rawOneQuery query reply history := by
  classical
  rcases inner with ⟨innerQuery, answer⟩
  change ¬ Sum.inl next ∈
    (match history.lastInput with
    | Sum.inl outer => Part.some (Sum.inl (query outer))
    | Sum.inr ⟨inner, answer⟩ =>
        if same : inner = query history.lastOuter then
          Part.some (Sum.inr (reply history.lastOuter (same ▸ answer)))
        else Part.none)
  rw [equal]
  by_cases same : innerQuery = query history.lastOuter
  · simp [same]
  · simp [same]

theorem rawOneQuery_complete
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) :
    DDC.Raw.Complete (rawOneQuery query reply) := by
  classical
  intro history admissible
  induction admissible with
  | start outer => simp
  | @afterInner history inner prior responds answer inductionHypothesis =>
      cases prior with
      | start outer =>
          have equal : inner = query outer := by simpa using responds
          rw [rawOneQuery_snocInner_of_eq query reply _ _ _ equal]
          simp
      | @afterInner previous previousQuery previousPrior previousResponds
          previousReply =>
          exact False.elim
            ((not_mem_rawOneQuery_of_lastInput_inner query reply _
              ⟨previousQuery, previousReply⟩ (by simp) inner) responds)
      | @afterOuter previous previousPrior previousReply previousResponds
          outer =>
          have equal : inner = query outer := by simpa using responds
          rw [rawOneQuery_snocInner_of_eq query reply _ _ _
            (by simpa using equal)]
          simp
  | afterOuter prior responds outer inductionHypothesis => simp

theorem rawOneQuery_branchFinite
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) :
    DDC.Raw.BranchFinite (rawOneQuery query reply) := by
  classical
  refine Subrelation.wf ?_ (measure oneQueryRank).wf
  intro after before continuation
  rcases continuation with ⟨inner, answer, responds, rfl⟩
  change oneQueryRank (before.snocInner inner answer) < oneQueryRank before
  cases input : before.lastInput with
  | inl outer => simp [oneQueryRank, input]
  | inr previous =>
      exact False.elim
        ((not_mem_rawOneQuery_of_lastInput_inner query reply _ previous input
          inner) responds)

end Internal

/-- A pure one-query DDC.  `none` is passed to `reply` exactly like every
other inner answer in the fibre selected by its query. -/
noncomputable def oneQuery
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) : DDC A B :=
  RandomSystems.Ambient.DDC.ofRaw
    (rawOneQuery query reply) (rawOneQuery_complete query reply)
    (rawOneQuery_branchFinite query reply)

namespace Internal

theorem mem_oneQuery_iff
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (history : DDC.History A B)
    (response : DDC.Response history) :
    response ∈ oneQuery query reply history ↔
      DDC.Raw.Admissible (rawOneQuery query reply) history ∧
        response ∈ rawOneQuery query reply history :=
  by
    change response ∈ DDC.Raw.canonicalize
        (rawOneQuery query reply) history ↔ _
    exact DDC.Raw.mem_canonicalize_iff _ _ _

theorem rawOneQuery_of_lastInput_outer
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (history : DDC.History A B)
    (outer : A.query) (equal : history.lastInput = Sum.inl outer) :
    rawOneQuery query reply history = Part.some (Sum.inl (query outer)) := by
  unfold rawOneQuery
  rw [equal]

/-- The closed answer obtained by composing the remaining one-query rounds.
This is a pure recursion on the supplied finite outer history. -/
def oneQueryFinal
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (system : DDS B)
    (innerPrior : List B.query) (current : A.query) :
    List A.query → DDC.History.InnerReply A
  | [] => ⟨current, reply current (Attachment.innerReplyAt system innerPrior (query current))⟩
  | next :: remaining =>
      oneQueryFinal query reply system (innerPrior ++ [query current])
        next remaining

theorem compatibleFrom_oneQuery
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (system : DDS B)
    (history : DDC.History A B) (innerPrior : List B.query)
    (current : A.query)
    (lastInput : history.lastInput = Sum.inl current)
    (lastOuter : history.lastOuter = current)
    (admissible : DDC.Raw.Admissible (rawOneQuery query reply) history) :
    ∀ remaining,
      ∃ inputs responses,
        Attachment.CompatibleFrom (oneQuery query reply) system history innerPrior
          remaining inputs responses
          (oneQueryFinal query reply system innerPrior current remaining) := by
  intro remaining
  induction remaining generalizing history innerPrior current with
  | nil =>
      subst current
      have queryResponds : Sum.inl (query history.lastOuter) ∈
          oneQuery query reply history := by
        rw [mem_oneQuery_iff]
        refine ⟨admissible, ?_⟩
        rw [rawOneQuery_of_lastInput_outer query reply history
          history.lastOuter lastInput]
        simp
      let answer := Attachment.innerReplyAt system innerPrior (query history.lastOuter)
      let after := history.snocInner (query history.lastOuter) answer
      have afterAdmissible :
          DDC.Raw.Admissible (rawOneQuery query reply) after :=
        .afterInner admissible
          (by
            rw [rawOneQuery_of_lastInput_outer query reply history
              history.lastOuter
              lastInput]
            simp)
          answer
      have equalQuery : query history.lastOuter = query history.lastOuter := rfl
      have rawReplyResponds :
          Sum.inr (reply history.lastOuter answer) ∈
            rawOneQuery query reply after := by
        rw [rawOneQuery_snocInner_of_eq query reply history _ _ equalQuery]
        exact Part.mem_some_iff.mpr rfl
      have replyResponds :
          Sum.inr (reply history.lastOuter answer) ∈
            oneQuery query reply after := by
        exact (mem_oneQuery_iff query reply after _).mpr
          ⟨afterAdmissible, rawReplyResponds⟩
      refine ⟨[history.lastInput, after.lastInput],
        [Sum.inl (query history.lastOuter),
          Sum.inr ⟨after.lastOuter, reply history.lastOuter answer⟩], ?_⟩
      apply Attachment.CompatibleFrom.innerQuery queryResponds
      simpa [oneQueryFinal, answer, after] using
        (Attachment.CompatibleFrom.outerLast replyResponds)
  | cons next remaining inductionHypothesis =>
      subst current
      have queryResponds : Sum.inl (query history.lastOuter) ∈
          oneQuery query reply history := by
        rw [mem_oneQuery_iff]
        refine ⟨admissible, ?_⟩
        rw [rawOneQuery_of_lastInput_outer query reply history
          history.lastOuter lastInput]
        simp
      let answer := Attachment.innerReplyAt system innerPrior (query history.lastOuter)
      let after := history.snocInner (query history.lastOuter) answer
      have afterAdmissible :
          DDC.Raw.Admissible (rawOneQuery query reply) after :=
        .afterInner admissible
          (by
            rw [rawOneQuery_of_lastInput_outer query reply history
              history.lastOuter
              lastInput]
            simp)
          answer
      have equalQuery : query history.lastOuter = query history.lastOuter := rfl
      have rawReplyResponds :
          Sum.inr (reply history.lastOuter answer) ∈
            rawOneQuery query reply after := by
        rw [rawOneQuery_snocInner_of_eq query reply history _ _ equalQuery]
        exact Part.mem_some_iff.mpr rfl
      have replyResponds :
          Sum.inr (reply history.lastOuter answer) ∈
            oneQuery query reply after := by
        exact (mem_oneQuery_iff query reply after _).mpr
          ⟨afterAdmissible, rawReplyResponds⟩
      let nextHistory := after.snocOuter next
      have nextAdmissible :
          DDC.Raw.Admissible (rawOneQuery query reply) nextHistory :=
        .afterOuter afterAdmissible rawReplyResponds next
      obtain ⟨tailInputs, tailResponses, tail⟩ :=
        inductionHypothesis nextHistory
          (innerPrior ++ [query history.lastOuter]) next
          (by simp [nextHistory]) (by simp [nextHistory]) nextAdmissible
      refine ⟨history.lastInput :: after.lastInput :: tailInputs,
        Sum.inl (query history.lastOuter) ::
          Sum.inr ⟨after.lastOuter,
            reply history.lastOuter answer⟩ :: tailResponses,
        ?_⟩
      apply Attachment.CompatibleFrom.innerQuery queryResponds
      apply Attachment.CompatibleFrom.outerNext replyResponds
      simpa [oneQueryFinal, answer, nextHistory] using tail

end Internal

/-- The DDS obtained by attaching a one-query DDC. -/
noncomputable def oneQueryDDS
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (system : DDS B) : DDS A :=
  fun history => Attachment.selectReply history.last
    (oneQueryFinal query reply system [] (_root_.RandomSystems.Ambient.History.head history)
      (_root_.RandomSystems.Ambient.History.tail history))

/-- The noninteractive special case falls out of the general attachment
definition; it is not a separate attachment semantics. -/
theorem applySystem_oneQuery_eq
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (query : A.query → B.query)
    (reply : ∀ outer, Option (B.answer (query outer)) →
      Option (A.answer outer)) (system : DDS B) :
    applySystem (oneQuery query reply) system =
      oneQueryDDS query reply system := by
  apply DDS.ext
  intro outerHistory
  rw [applySystem_eq_iff]
  let start := DDC.History.singleton (B := B)
    (_root_.RandomSystems.Ambient.History.head outerHistory)
  have admissible : DDC.Raw.Admissible (rawOneQuery query reply) start :=
    .start (_root_.RandomSystems.Ambient.History.head outerHistory)
  obtain ⟨inputs, responses, compatible⟩ :=
    compatibleFrom_oneQuery query reply system start []
      (_root_.RandomSystems.Ambient.History.head outerHistory)
      (by simp [start]) (by simp [start]) admissible
      (_root_.RandomSystems.Ambient.History.tail outerHistory)
  let transcript : Attachment.Transcript A B :=
    ⟨inputs, responses,
      oneQueryFinal query reply system []
        (_root_.RandomSystems.Ambient.History.head outerHistory)
        (_root_.RandomSystems.Ambient.History.tail outerHistory)⟩
  have compatibleFull : Attachment.Compatible
      (oneQuery query reply) system outerHistory transcript := by
    simpa only [Attachment.Compatible, transcript, start] using compatible
  exact ⟨transcript, compatibleFull,
    (Attachment.selectReply_heq_second outerHistory.last _
      (Attachment.Compatible.final_query_eq_last compatibleFull)).symm⟩

/-! ## Pure finite DDC function tables

Jost, immediately before Definition 2.2.2 (printed p. 17), states that a
converter is “allowed to make a bounded number of queries to the inside
interfaces.”  The constructors below encode that bound once, while applications
supply ordinary total Lean functions.
-/

variable {U : Type u} {V : Type v} {X : Type w} {Y : Type z}

/-- Inner replies received since the latest outer query. -/
def latestReplies
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) : List (Option Y) :=
  history.inputs.queries.foldl
    (fun replies input => match input with
      | Sum.inl _ => []
      | Sum.inr ⟨_, reply⟩ => replies ++ [show Option Y from reply]) []

@[simp]
theorem latestReplies_singleton (query : U) :
    latestReplies (V := V)
      (DDC.History.singleton
        (B := Interface.single X Y) query) = [] :=
  rfl

@[simp]
theorem latestReplies_snoc_outer
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) (query : U) :
    latestReplies (history.snocOuter query) = [] := by
  simp [latestReplies,
    DDC.History.snocOuter,
    _root_.RandomSystems.Ambient.History.snoc, List.foldl_append]

@[simp]
theorem latestReplies_snoc_inner
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) (query : X) (reply : Option Y) :
    latestReplies (history.snocInner query reply) =
      latestReplies history ++ [reply] := by
  simp [latestReplies,
    DDC.History.snocInner,
    _root_.RandomSystems.Ambient.History.snoc, List.foldl_append]

/-- The pure response table obtained by using the open row below `bound` and
the closing row at or above `bound`. -/
def responseWithInnerQueryBound (bound : Nat)
    (openResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      (latestReplies history).length < bound →
        DDC.Response history)
    (closeResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      bound ≤ (latestReplies history).length → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) :
      DDC.Response history :=
  if below : (latestReplies history).length < bound then
    openResponse history below
  else
    Sum.inr (closeResponse history (Nat.le_of_not_gt below))

namespace Internal

def rawWithInnerQueryBound (bound : Nat)
    (openResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      (latestReplies history).length < bound →
        DDC.Response history)
    (closeResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      bound ≤ (latestReplies history).length → Option V) :
    DDC.Raw (Interface.single U V) (Interface.single X Y) :=
  fun history => Part.some
    (responseWithInnerQueryBound bound openResponse closeResponse history)

theorem rawWithInnerQueryBound_complete (bound : Nat)
    (openResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      (latestReplies history).length < bound →
        DDC.Response history)
    (closeResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      bound ≤ (latestReplies history).length → Option V) :
    DDC.Raw.Complete
      (rawWithInnerQueryBound bound openResponse closeResponse) := by
  intro history admissible
  simp [rawWithInnerQueryBound]

def remainingInnerQueries (bound : Nat)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) : Nat :=
  bound - (latestReplies history).length

theorem rawWithInnerQueryBound_branchFinite (bound : Nat)
    (openResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      (latestReplies history).length < bound →
        DDC.Response history)
    (closeResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      bound ≤ (latestReplies history).length → Option V) :
    DDC.Raw.BranchFinite
      (rawWithInnerQueryBound bound openResponse closeResponse) := by
  refine Subrelation.wf ?_ (measure (remainingInnerQueries bound)).wf
  intro after before continuation
  rcases continuation with ⟨query, reply, responds, rfl⟩
  -- An emitted inner query can occur only below the displayed bound.
  have responseEqual :
      responseWithInnerQueryBound bound openResponse closeResponse before =
        Sum.inl query := by
    simpa [rawWithInnerQueryBound] using (Part.mem_some_iff.mp responds).symm
  have below : (latestReplies before).length < bound := by
    by_contra notBelow
    simp only [responseWithInnerQueryBound, dif_neg notBelow] at responseEqual
    cases responseEqual
  -- Receiving its reply increases the current-round reply count by one.
  change remainingInnerQueries bound (before.snocInner query reply) <
    remainingInnerQueries bound before
  rw [remainingInnerQueries, remainingInnerQueries, latestReplies_snoc_inner]
  simp only [List.length_append, List.length_singleton]
  omega

end Internal

/-- Build a canonical branch-finite DDC from one pure complete-history
function with a forced closing row. -/
noncomputable def ofInnerQueryBound (bound : Nat)
    (openResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      (latestReplies history).length < bound →
        DDC.Response history)
    (closeResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      bound ≤ (latestReplies history).length → Option V) :
    RandomSystems.Ambient.DDC (Interface.single U V) (Interface.single X Y) :=
  RandomSystems.Ambient.DDC.ofRaw
    (rawWithInnerQueryBound bound openResponse closeResponse)
    (rawWithInnerQueryBound_complete bound openResponse closeResponse)
    (rawWithInnerQueryBound_branchFinite bound openResponse closeResponse)

theorem mem_ofInnerQueryBound_iff (bound : Nat)
    (openResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      (latestReplies history).length < bound →
        DDC.Response history)
    (closeResponse : (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) →
      bound ≤ (latestReplies history).length → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (response : DDC.Response history) :
    response ∈ ofInnerQueryBound bound openResponse closeResponse history ↔
      DDC.Raw.Admissible
          (ofInnerQueryBound bound openResponse closeResponse).toFun history ∧
        response = responseWithInnerQueryBound bound openResponse closeResponse history := by
  change response ∈ DDC.Raw.canonicalize
      (rawWithInnerQueryBound bound openResponse closeResponse) history ↔
    DDC.Raw.Admissible
        (DDC.Raw.canonicalize
          (rawWithInnerQueryBound bound openResponse closeResponse)) history ∧ _
  rw [DDC.Raw.admissible_canonicalize_iff]
  rw [DDC.Raw.mem_canonicalize_iff]
  constructor
  · rintro ⟨admissible, membership⟩
    exact ⟨admissible, Part.mem_some_iff.mp membership⟩
  · rintro ⟨admissible, rfl⟩
    exact ⟨admissible, Part.mem_some _⟩

/-- The response selected from the current outer query and the inner replies
received since that query, under one fixed inner-query bound. -/
def boundedInnerQueryResponse (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y)) :
    DDC.Response history :=
  responseWithInnerQueryBound bound
    (fun history below =>
      openResponse history.lastOuter (latestReplies history)
        ⟨(latestReplies history).length, below⟩)
    (fun history _ => closeResponse history.lastOuter (latestReplies history))
    history

/-- Construct a DDC whose response depends only on the current outer query and
the inner replies received since that query, with at most `bound` inner
queries. -/
noncomputable def ofBoundedInnerQueries (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V) :
    RandomSystems.Ambient.DDC (Interface.single U V) (Interface.single X Y) :=
  ofInnerQueryBound bound
    (fun history below =>
      openResponse history.lastOuter (latestReplies history)
        ⟨(latestReplies history).length, below⟩)
    (fun history _ => closeResponse history.lastOuter (latestReplies history))

theorem mem_ofBoundedInnerQueries_iff (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (response : DDC.Response history) :
    response ∈ ofBoundedInnerQueries bound openResponse closeResponse history ↔
      DDC.Raw.Admissible
          (ofBoundedInnerQueries bound openResponse closeResponse).toFun history ∧
        response = boundedInnerQueryResponse bound openResponse closeResponse
          history := by
  rw [ofBoundedInnerQueries, mem_ofInnerQueryBound_iff]
  rfl

/-- The ordinary recursive result of a bounded-inner-query DDC against one
stateless answer function. -/
def boundedInnerQueryResult (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (answer : X → Option Y) (outer : U)
    (replies : List (Option Y)) : Option V :=
  if below : replies.length < bound then
    match openResponse outer replies ⟨replies.length, below⟩ with
    | Sum.inl query =>
        boundedInnerQueryResult bound openResponse closeResponse answer outer
          (replies ++ [answer query])
    | Sum.inr result => result
  else
    closeResponse outer replies
termination_by bound - replies.length
decreasing_by
  simp only [List.length_append, List.length_singleton]
  omega

/-- Inner queries made while completing one outer query against an ordinary
answer function. -/
def innerQueriesWithinBound (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (answer : X → Option Y) (outer : U)
    (replies : List (Option Y)) : List X :=
  if below : replies.length < bound then
    match openResponse outer replies ⟨replies.length, below⟩ with
    | Sum.inl query =>
        query :: innerQueriesWithinBound bound openResponse answer outer
          (replies ++ [answer query])
    | Sum.inr _ => []
  else
    []
termination_by bound - replies.length
decreasing_by
  simp only [List.length_append, List.length_singleton]
  omega

/-- Inner queries made while completing the current and displayed remaining
outer queries. -/
def innerQueriesWithinBoundContinuation (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (answer : X → Option Y) : U → List (Option Y) → List U → List X
  | outer, replies, [] =>
      innerQueriesWithinBound bound openResponse answer outer replies
  | outer, replies, next :: remaining =>
      innerQueriesWithinBound bound openResponse answer outer replies ++
        innerQueriesWithinBoundContinuation bound openResponse answer
          next [] remaining

def boundedInnerQueryContinuation (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (answer : X → Option Y) :
    U → List (Option Y) → List U → Option V
  | outer, replies, [] =>
      boundedInnerQueryResult bound openResponse closeResponse answer outer replies
  | _, _, next :: remaining =>
      boundedInnerQueryContinuation bound openResponse closeResponse answer
        next [] remaining

theorem innerReplyAt_function
    (function : X → Y) (prior : List X) (query : X) :
    Attachment.innerReplyAt
        (show DDS (Interface.single X Y) from
          fun history => some (function history.last)) prior query =
      some (function query) := by
  unfold Attachment.innerReplyAt
  change cast _
      (some (function ((prior ++ [query]).getLast (by simp)))) =
    some (function query)
  rw [List.getLast_append_singleton]
  generalize_proofs proof
  rw [show proof = Eq.refl (Option Y) from Subsingleton.elim _ _]
  rfl

theorem innerQueriesWithinBound_eq_nil_of_outer
    (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (answer : X → Option Y)
    (history : DDC.History
      (Interface.single U V) (Interface.single X Y))
    (current : U) (reply : Option V)
    (current_eq : history.lastOuter = current)
    (responds : Sum.inr reply ∈
      ofBoundedInnerQueries bound openResponse closeResponse history) :
    innerQueriesWithinBound bound openResponse answer current
        (latestReplies history) = [] := by
  have responseEqual :=
    (mem_ofBoundedInnerQueries_iff bound openResponse closeResponse history
      (Sum.inr reply)).mp responds |>.2
  by_cases below : (latestReplies history).length < bound
  · have openEqual :
        openResponse current (latestReplies history)
            ⟨(latestReplies history).length, below⟩ = Sum.inr reply := by
      simpa only [boundedInnerQueryResponse, responseWithInnerQueryBound, dif_pos below,
        current_eq] using responseEqual.symm
    rw [innerQueriesWithinBound, dif_pos below, openEqual]
  · rw [innerQueriesWithinBound, dif_neg below]

theorem CompatibleFrom.boundedInnerQueries_innerQueries
    (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (function : X → Y)
    {history : DDC.History
      (Interface.single U V) (Interface.single X Y)}
    {innerPrior : List X} {remainingOuter : List U}
    {inputs : List
      (DDC.History.Input
        (Interface.single U V) (Interface.single X Y))}
    {responses : List
      (Attachment.Response
        (Interface.single U V) (Interface.single X Y))}
    {final : DDC.History.InnerReply (Interface.single U V)}
    (compatible : Attachment.CompatibleFrom
      (ofBoundedInnerQueries bound openResponse closeResponse)
      (fun systemHistory => some (function systemHistory.last))
      history innerPrior remainingOuter inputs responses final)
    (current : U) (current_eq : history.lastOuter = current) :
    Attachment.innerQueries responses =
      innerQueriesWithinBoundContinuation bound openResponse
        (fun query => some (function query)) current
        (latestReplies history) remainingOuter := by
  induction compatible generalizing current with
  | innerQuery responds tail inductionHypothesis =>
      rename_i history innerPrior remainingOuter query tailInputs
        tailResponses final
      have tailQueries := inductionHypothesis current
        (by simpa using current_eq)
      have responseEqual :=
        (mem_ofBoundedInnerQueries_iff bound openResponse closeResponse
          history (Sum.inl query)).mp responds |>.2
      have below : (latestReplies history).length < bound := by
        by_contra notBelow
        simp only [boundedInnerQueryResponse, responseWithInnerQueryBound,
          dif_neg notBelow] at responseEqual
        cases responseEqual
      have openEqual :
          openResponse current (latestReplies history)
              ⟨(latestReplies history).length, below⟩ = Sum.inl query := by
        simpa only [boundedInnerQueryResponse, responseWithInnerQueryBound,
          dif_pos below, current_eq] using responseEqual.symm
      rw [latestReplies_snoc_inner,
        innerReplyAt_function function innerPrior query] at tailQueries
      cases remainingOuter with
      | nil =>
          rw [innerQueriesWithinBoundContinuation,
            innerQueriesWithinBound, dif_pos below, openEqual]
          exact congrArg (List.cons query) tailQueries
      | cons next remaining =>
          rw [innerQueriesWithinBoundContinuation,
            innerQueriesWithinBound, dif_pos below, openEqual]
          simp only [List.cons_append]
          exact congrArg (List.cons query) tailQueries
  | outerLast responds =>
      have noQueries := innerQueriesWithinBound_eq_nil_of_outer
        bound openResponse closeResponse (fun query => some (function query))
        _ current _ current_eq responds
      rw [innerQueriesWithinBoundContinuation, noQueries]
      rfl
  | outerNext responds tail inductionHypothesis =>
      rename_i history innerPrior reply next remaining tailInputs
        tailResponses final
      have noQueries := innerQueriesWithinBound_eq_nil_of_outer
        bound openResponse closeResponse (fun query => some (function query))
        _ current _ current_eq responds
      have tailQueries := inductionHypothesis next (by simp)
      simp only [latestReplies_snoc_outer] at tailQueries
      rw [innerQueriesWithinBoundContinuation, noQueries, List.nil_append]
      change Attachment.innerQueries tailResponses = _
      exact tailQueries

/-- The inner queries in a compatible bounded-inner-query attachment are
exactly the queries of its ordinary recursive function. -/
theorem innerQueries_ofBoundedInnerQueries_eq (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (function : X → Y)
    (outerHistory : _root_.RandomSystems.Ambient.History
      (Interface.single U V))
    (transcript : Attachment.Transcript
      (Interface.single U V) (Interface.single X Y))
    (compatible : Attachment.Compatible
      (ofBoundedInnerQueries bound openResponse closeResponse)
      (fun systemHistory => some (function systemHistory.last))
      outerHistory transcript) :
    Attachment.innerQueries transcript.responses =
      innerQueriesWithinBoundContinuation bound openResponse
        (fun query => some (function query)) outerHistory.head []
        outerHistory.tail := by
  exact CompatibleFrom.boundedInnerQueries_innerQueries bound openResponse
    closeResponse function compatible outerHistory.head rfl

theorem CompatibleFrom.boundedInnerQueries_final
    (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (function : X → Y)
    {history : DDC.History
      (Interface.single U V) (Interface.single X Y)}
    {innerPrior : List X} {remainingOuter : List U}
    {inputs : List
      (DDC.History.Input
        (Interface.single U V) (Interface.single X Y))}
    {responses : List
      (Attachment.Response
        (Interface.single U V) (Interface.single X Y))}
    {final : DDC.History.InnerReply
      (Interface.single U V)}
    (compatible : Attachment.CompatibleFrom
      (ofBoundedInnerQueries bound openResponse closeResponse)
      (fun systemHistory => some (function systemHistory.last))
      history innerPrior remainingOuter inputs responses final)
    (current : U) (current_eq : history.lastOuter = current) :
    final.2 = boundedInnerQueryContinuation bound openResponse closeResponse
      (fun query => some (function query)) current (latestReplies history)
        remainingOuter := by
  induction compatible generalizing current with
  | innerQuery responds tail inductionHypothesis =>
      rename_i history innerPrior remainingOuter query tailInputs
        tailResponses final
      have responseEqual :=
        (mem_ofBoundedInnerQueries_iff bound openResponse closeResponse history
          (Sum.inl query)).mp responds |>.2
      -- The table issued an inner query, so the current round is below bound.
      have below : (latestReplies history).length < bound := by
        by_contra notBelow
        simp only [boundedInnerQueryResponse, responseWithInnerQueryBound,
          dif_neg notBelow] at responseEqual
        cases responseEqual
      have openEqual :
          openResponse current (latestReplies history)
              ⟨(latestReplies history).length, below⟩ =
            Sum.inl query := by
        simpa only [boundedInnerQueryResponse, responseWithInnerQueryBound,
          dif_pos below, current_eq] using
          responseEqual.symm
      -- The attached function supplies exactly the next displayed reply.
      have tailFinal := inductionHypothesis current (by simpa using current_eq)
      rw [latestReplies_snoc_inner,
        innerReplyAt_function function innerPrior query] at tailFinal
      cases remainingOuter with
      | nil =>
          -- With no later outer query, this is the recursive result now.
          change final.2 = boundedInnerQueryResult bound openResponse
            closeResponse (fun query => some (function query)) current
              (latestReplies history)
          rw [boundedInnerQueryResult.eq_def, dif_pos below, openEqual]
          exact tailFinal
      | cons next remaining =>
          -- Replies following a later outer query form a new list.
          simpa [boundedInnerQueryContinuation] using tailFinal
  | outerLast responds =>
      rename_i history innerPrior reply
      have responseEqual :=
        (mem_ofBoundedInnerQueries_iff bound openResponse closeResponse history
          (Sum.inr reply)).mp responds |>.2
      change reply = boundedInnerQueryResult bound openResponse closeResponse
        (fun query => some (function query)) current (latestReplies history)
      by_cases below : (latestReplies history).length < bound
      · have openEqual :
            openResponse current (latestReplies history)
                ⟨(latestReplies history).length, below⟩ =
              Sum.inr reply := by
          simpa only [boundedInnerQueryResponse, responseWithInnerQueryBound,
            dif_pos below, current_eq] using
            responseEqual.symm
        rw [boundedInnerQueryResult.eq_def, dif_pos below, openEqual]
      · have closeEqual :
            closeResponse current (latestReplies history) = reply := by
          exact Sum.inr.inj (by
            simpa only [boundedInnerQueryResponse, responseWithInnerQueryBound,
              dif_neg below, current_eq] using
              responseEqual.symm)
        rw [boundedInnerQueryResult.eq_def, dif_neg below, closeEqual]
  | outerNext responds tail inductionHypothesis =>
      rename_i history innerPrior reply next remaining tailInputs
        tailResponses final
      have tailFinal := inductionHypothesis next (by simp)
      -- Compatibility starts the following outer round with no inner replies.
      simpa [boundedInnerQueryContinuation] using tailFinal

theorem boundedInnerQueryContinuation_eq_last (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (answer : X → Option Y) (current : U) (remaining : List U) :
    boundedInnerQueryContinuation bound openResponse closeResponse answer
        current [] remaining =
      boundedInnerQueryResult bound openResponse closeResponse answer
        ((current :: remaining).getLast (by simp)) [] := by
  induction remaining generalizing current with
  | nil => rfl
  | cons next remaining inductionHypothesis =>
      calc
        boundedInnerQueryContinuation bound openResponse closeResponse answer
            current [] (next :: remaining) =
          boundedInnerQueryContinuation bound openResponse closeResponse answer
            next [] remaining := rfl
        _ = boundedInnerQueryResult bound openResponse closeResponse answer
            ((next :: remaining).getLast (by simp)) [] :=
          inductionHypothesis next
        _ = boundedInnerQueryResult bound openResponse closeResponse answer
            ((current :: next :: remaining).getLast (by simp)) [] := by
          apply congrArg (fun outer => boundedInnerQueryResult bound openResponse
            closeResponse answer outer [])
          exact (List.getLast_cons
            (by simp : next :: remaining ≠ [])).symm

/-- Attachment of a bounded-inner-query DDC to a stateless DDS is its ordinary
recursive function. -/
theorem applySystem_ofBoundedInnerQueries_eq (bound : Nat)
    (openResponse : U → List (Option Y) → Fin bound → X ⊕ Option V)
    (closeResponse : U → List (Option Y) → Option V)
    (function : X → Y) :
    applySystem
        (ofBoundedInnerQueries bound openResponse closeResponse)
        (fun history => some (function history.last)) =
      fun outerHistory =>
        boundedInnerQueryResult bound openResponse closeResponse
          (fun query => some (function query)) outerHistory.last [] := by
  apply DDS.ext
  intro outerHistory
  -- Use the unique compatible transcript defining attachment.
  rw [applySystem_eq_iff]
  obtain ⟨transcript, compatible⟩ :=
    Attachment.exists_compatible
      (ofBoundedInnerQueries bound openResponse closeResponse)
      (fun history => some (function history.last)) outerHistory
  refine ⟨transcript, compatible, ?_⟩
  have finalEqual := CompatibleFrom.boundedInnerQueries_final bound openResponse
    closeResponse function compatible
      (_root_.RandomSystems.Ambient.History.head outerHistory) rfl
  change transcript.final.2 =
    boundedInnerQueryContinuation bound openResponse closeResponse
      (fun query => some (function query))
      (_root_.RandomSystems.Ambient.History.head outerHistory) []
      (_root_.RandomSystems.Ambient.History.tail outerHistory) at finalEqual
  have continuationEqual := boundedInnerQueryContinuation_eq_last bound
    openResponse closeResponse (fun query => some (function query))
      (_root_.RandomSystems.Ambient.History.head outerHistory)
      (_root_.RandomSystems.Ambient.History.tail outerHistory)
  -- The last outer round is the last query of the supplied DDS history.
  have lastEqual :
      (_root_.RandomSystems.Ambient.History.head outerHistory ::
        _root_.RandomSystems.Ambient.History.tail outerHistory).getLast
          (by simp) = outerHistory.last := by
    unfold _root_.RandomSystems.Ambient.History.last
    apply List.getLast_congr
    exact List.cons_head_tail outerHistory.nonempty
  have continuationEqual' :
      boundedInnerQueryContinuation bound openResponse closeResponse
          (fun query => some (function query))
          (_root_.RandomSystems.Ambient.History.head outerHistory) []
          (_root_.RandomSystems.Ambient.History.tail outerHistory) =
        boundedInnerQueryResult bound openResponse closeResponse
          (fun query => some (function query)) outerHistory.last [] := by
    exact continuationEqual.trans
      (congrArg (fun outer => boundedInnerQueryResult bound openResponse
        closeResponse (fun query => some (function query)) outer []) lastEqual)
  exact heq_of_eq (finalEqual.trans continuationEqual')

end DDC

end RandomSystems.Ambient
