import RandomSystems.Converter.Filter
import RandomSystems.Converter.SerialCongruence

set_option autoImplicit false

/-!
# Query limits

A query limit forwards at most a prescribed number of queries.  This file
also records the query histories needed to move such a limit through serial
converter composition.
-/

namespace RandomSystems.Ambient.DDC

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- Forward at most `q` queries. -/
def queryLimit (q : Nat) :
    DDC (Interface.single X Y) (Interface.single X Y) :=
  DDC.filter (fun queries : List X => queries.length ≤ q)
    id (fun _ answer => answer)

namespace History

/-- Inner queries for which a reply has been received. -/
def receivedInnerQueries {A B : Interface.{u, v}}
    (history : DDC.History A B) : List B.query :=
  history.inputs.queries.filterMap fun
    | Sum.inl _ => none
    | Sum.inr reply => some reply.1

@[simp]
lemma receivedInnerQueries_singleton {A B : Interface.{u, v}}
    (query : A.query) :
    receivedInnerQueries (DDC.History.singleton (B := B) query) = [] :=
  rfl

@[simp]
lemma receivedInnerQueries_snocInner {A B : Interface.{u, v}}
    (history : DDC.History A B) (query : B.query)
    (reply : Option (B.answer query)) :
    (history.snocInner query reply).receivedInnerQueries =
      history.receivedInnerQueries ++ [query] := by
  simp [receivedInnerQueries, DDC.History.snocInner,
    RandomSystems.Ambient.History.snoc, List.filterMap_append]

@[simp]
lemma receivedInnerQueries_snocOuter {A B : Interface.{u, v}}
    (history : DDC.History A B) (query : A.query) :
    (history.snocOuter query).receivedInnerQueries =
      history.receivedInnerQueries := by
  simp [receivedInnerQueries, DDC.History.snocOuter,
    RandomSystems.Ambient.History.snoc, List.filterMap_append]

end History

namespace Internal

def innerOuterQueries {B C : Interface.{u, v}} :
    Option (DDC.History B C) → List B.query
  | none => []
  | some history => history.outer.queries

def SerialQueriesAtEndpoint
    {A B C : Interface.{u, v}}
    (response : PackedResponse A C)
    (outerHistory : DDC.History A B)
    (innerHistory : Option (DDC.History B C)) : Prop :=
  match response with
  | Sum.inl _ => ∃ history, innerHistory = some history ∧
      history.outer.queries =
        outerHistory.receivedInnerQueries ++ [history.lastOuter]
  | Sum.inr _ => innerOuterQueries innerHistory =
      outerHistory.receivedInnerQueries

mutual

lemma OuterPrefixFactorization.queriesAtEndpoint
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner)
    (closed : innerOuterQueries innerHistory =
      outerHistory.receivedInnerQueries) :
    SerialQueriesAtEndpoint response finalOuter finalInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory innerHistory response finalOuter finalInner
          _ =>
        innerHistory.outer.queries =
            outerHistory.receivedInnerQueries ++ [innerHistory.lastOuter] →
          SerialQueriesAtEndpoint response finalOuter finalInner) with
  | outerReply responds =>
      simpa only [SerialQueriesAtEndpoint] using closed
  | outerQueryFirst responds tail inductionHypothesis =>
      apply inductionHypothesis
      simp only [innerOuterQueries] at closed
      rw [← closed]
      rfl
  | @outerQueryNext outerHistory innerHistory query response finalOuter
      finalInner innerClosed responds tail inductionHypothesis =>
      apply inductionHypothesis
      simp only [innerOuterQueries] at closed
      rw [DDC.History.lastOuter_snocOuter]
      change innerHistory.outer.queries ++ [query] =
        outerHistory.receivedInnerQueries ++ [query]
      rw [closed]
  | @innerQuery outerHistory innerHistory query linked responds pending =>
      exact ⟨innerHistory, rfl, pending⟩
  | @innerReply outerHistory innerHistory reply response finalOuter finalInner
      linked responds tail inductionHypothesis pending =>
      apply inductionHypothesis
      simpa only [innerOuterQueries,
        History.receivedInnerQueries_snocInner] using pending

lemma InnerPrefixFactorization.queriesAtEndpoint
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner)
    (pending : innerHistory.outer.queries =
      outerHistory.receivedInnerQueries ++ [innerHistory.lastOuter]) :
    SerialQueriesAtEndpoint response finalOuter finalInner := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory innerHistory response finalOuter finalInner
          _ =>
        innerOuterQueries innerHistory =
            outerHistory.receivedInnerQueries →
          SerialQueriesAtEndpoint response finalOuter finalInner) with
  | @outerReply outerHistory innerHistory reply responds closed =>
      simpa only [SerialQueriesAtEndpoint] using closed
  | @outerQueryFirst outerHistory query response finalOuter finalInner
      responds tail inductionHypothesis closed =>
      apply inductionHypothesis
      simp only [innerOuterQueries] at closed
      rw [← closed]
      rfl
  | @outerQueryNext outerHistory innerHistory query response finalOuter
      finalInner innerClosed responds tail inductionHypothesis closed =>
      apply inductionHypothesis
      simp only [innerOuterQueries] at closed
      rw [DDC.History.lastOuter_snocOuter]
      change innerHistory.outer.queries ++ [query] =
        outerHistory.receivedInnerQueries ++ [query]
      rw [closed]
  | @innerQuery outerHistory innerHistory query linked responds =>
      exact ⟨innerHistory, rfl, pending⟩
  | @innerReply outerHistory innerHistory reply response finalOuter finalInner
      linked responds tail inductionHypothesis =>
      apply inductionHypothesis
      simpa only [innerOuterQueries,
        History.receivedInnerQueries_snocInner] using pending

end

lemma SerialFactorization.queriesAtEndpoint
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    SerialQueriesAtEndpoint response outerHistory innerHistory := by
  induction factorization with
  | start middle valid =>
      apply middle.queriesAtEndpoint
      rfl
  | afterInner previous middle valid inductionHypothesis =>
      obtain ⟨currentInner, innerEqual, pending⟩ := inductionHypothesis
      cases Option.some.inj innerEqual
      apply middle.queriesAtEndpoint
      rw [DDC.History.lastOuter_snocInner]
      exact pending
  | afterOuter previous middle valid inductionHypothesis =>
      apply middle.queriesAtEndpoint
      simpa only [SerialQueriesAtEndpoint,
        History.receivedInnerQueries_snocOuter] using inductionHypothesis

/-- At a serially exposed inner query, the inner history consists of the
completed queries recorded by the outer history and the pending query. -/
theorem SerialFactorization.exists_innerHistory_outerQueries_eq_of_query
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C} {query : C.query}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history (Sum.inl query)
      outerHistory innerHistory) :
    ∃ currentInner, innerHistory = some currentInner ∧
      currentInner.outer.queries =
        outerHistory.receivedInnerQueries ++ [currentInner.lastOuter] :=
  factorization.queriesAtEndpoint

/-- At a serially exposed outer reply, the inner history contains exactly the
completed queries recorded by the outer history. -/
theorem SerialFactorization.innerOuterQueries_eq_of_reply
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C}
    {reply : DDC.History.InnerReply A}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history (Sum.inr reply)
      outerHistory innerHistory) :
    innerOuterQueries innerHistory = outerHistory.receivedInnerQueries :=
  factorization.queriesAtEndpoint

def optionReceivedInnerQueries {B C : Interface.{u, v}} :
    Option (DDC.History B C) → List C.query
  | none => []
  | some history => history.receivedInnerQueries

mutual

lemma OuterPrefixFactorization.receivedInnerQueries_length_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner) :
    (optionReceivedInnerQueries finalInner).length =
      (optionReceivedInnerQueries innerHistory).length := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory innerHistory response finalOuter finalInner
          _ =>
        (optionReceivedInnerQueries finalInner).length =
          innerHistory.receivedInnerQueries.length) with
  | outerReply => rfl
  | outerQueryFirst responds tail inductionHypothesis =>
      simpa [optionReceivedInnerQueries] using inductionHypothesis
  | outerQueryNext closed responds tail inductionHypothesis =>
      simpa [optionReceivedInnerQueries] using inductionHypothesis
  | innerQuery => rfl
  | innerReply linked responds tail inductionHypothesis =>
      simpa [optionReceivedInnerQueries] using inductionHypothesis

lemma InnerPrefixFactorization.receivedInnerQueries_length_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer inner outerHistory
      innerHistory response finalOuter finalInner) :
    (optionReceivedInnerQueries finalInner).length =
      innerHistory.receivedInnerQueries.length := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory innerHistory response finalOuter finalInner
          _ =>
        (optionReceivedInnerQueries finalInner).length =
          (optionReceivedInnerQueries innerHistory).length) with
  | outerReply => rfl
  | outerQueryFirst responds tail inductionHypothesis =>
      simpa [optionReceivedInnerQueries] using inductionHypothesis
  | outerQueryNext closed responds tail inductionHypothesis =>
      simpa [optionReceivedInnerQueries] using inductionHypothesis
  | innerQuery => rfl
  | innerReply linked responds tail inductionHypothesis =>
      simpa [optionReceivedInnerQueries] using inductionHypothesis

end


/-- Serial factorization preserves the number of replies received from the
innermost interface. -/
theorem SerialFactorization.receivedInnerQueries_length_eq
    {A B C : Interface.{u, v}} {outer : DDC A B} {inner : DDC B C}
    {history : AttemptedHistory A C}
    {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer inner history response
      outerHistory innerHistory) :
    (match innerHistory with
      | none => []
      | some currentInner => currentInner.receivedInnerQueries).length =
        history.toReceived.receivedInnerQueries.length := by
  change (optionReceivedInnerQueries innerHistory).length = _
  induction factorization with
  | start middle valid =>
      simpa [optionReceivedInnerQueries,
        AttemptedHistory.toReceived] using
          middle.receivedInnerQueries_length_eq
  | afterInner previous middle valid inductionHypothesis =>
      rw [middle.receivedInnerQueries_length_eq]
      simpa [optionReceivedInnerQueries,
        AttemptedHistory.toReceived] using inductionHypothesis
  | afterOuter previous middle valid inductionHypothesis =>
      rw [middle.receivedInnerQueries_length_eq]
      simpa [optionReceivedInnerQueries,
        AttemptedHistory.toReceived] using inductionHypothesis

end Internal

namespace Internal

lemma filter_query_implies_latestReplies_eq_nil
    {U : Type u} {V : Type v}
    (accept : List U → Prop) [DecidablePred accept]
    (history : DDC.History
      (Interface.single U V) (Interface.single U V))
    {query : U}
    (responds : Sum.inl query ∈
      DDC.filter accept id (fun _ answer => answer) history) :
    DDC.latestReplies history = [] := by
  have responseEqual :=
    (DDC.mem_filter_iff accept id (fun _ answer => answer)
      history (Sum.inl query)).mp responds |>.2
  unfold DDC.filterResponse DDC.responseWithInnerQueryBound at responseEqual
  split at responseEqual
  next below =>
    exact List.eq_nil_of_length_eq_zero (Nat.lt_one_iff.mp below)
  next notBelow => cases responseEqual

lemma filter_query_eq_lastOuter
    {U : Type u} {V : Type v}
    (accept : List U → Prop) [DecidablePred accept]
    (history : DDC.History
      (Interface.single U V) (Interface.single U V))
    {query : U}
    (responds : Sum.inl query ∈
      DDC.filter accept id (fun _ answer => answer) history) :
    query = history.lastOuter := by
  have responseEqual :=
    (DDC.mem_filter_iff accept id (fun _ answer => answer)
      history (Sum.inl query)).mp responds |>.2
  unfold DDC.filterResponse DDC.responseWithInnerQueryBound at responseEqual
  split at responseEqual
  next below =>
    by_cases accepted : accept (DDC.outerQueries history)
    · simp only [accepted, if_true, id_eq] at responseEqual
      exact Sum.inl.inj responseEqual
    · simp only [accepted, if_false] at responseEqual
      cases responseEqual
  next notBelow => cases responseEqual

lemma filter_query_implies_accept
    {U : Type u} {V : Type v}
    (accept : List U → Prop) [DecidablePred accept]
    (history : DDC.History
      (Interface.single U V) (Interface.single U V))
    {query : U}
    (responds : Sum.inl query ∈
      DDC.filter accept id (fun _ answer => answer) history) :
    accept (DDC.outerQueries history) := by
  have responseEqual :=
    (DDC.mem_filter_iff accept id (fun _ answer => answer)
      history (Sum.inl query)).mp responds |>.2
  unfold DDC.filterResponse DDC.responseWithInnerQueryBound at responseEqual
  split at responseEqual
  next below =>
    by_cases accepted : accept (DDC.outerQueries history)
    · exact accepted
    · simp only [accepted, if_false] at responseEqual
      cases responseEqual
  next notBelow => cases responseEqual

lemma filter_reply_of_accept_implies_latestReplies_ne_nil
    {U : Type u} {V : Type v}
    (accept : List U → Prop) [DecidablePred accept]
    (history : DDC.History
      (Interface.single U V) (Interface.single U V))
    {reply : Option V}
    (responds : Sum.inr reply ∈
      DDC.filter accept id (fun _ answer => answer) history)
    (accepted : accept (DDC.outerQueries history)) :
    DDC.latestReplies history ≠ [] := by
  have responseEqual :=
    (DDC.mem_filter_iff accept id (fun _ answer => answer)
      history (Sum.inr reply)).mp responds |>.2
  intro empty
  unfold DDC.filterResponse DDC.responseWithInnerQueryBound at responseEqual
  simp [empty, accepted] at responseEqual

lemma filter_history_queries
    {U : Type u} {V : Type v}
    (accept : List U → Prop) [DecidablePred accept]
    (prefixClosed : ∀ {prior whole : List U},
      List.IsPrefix prior whole → accept whole → accept prior)
    (history : DDC.History
      (Interface.single U V) (Interface.single U V))
    (admissible : DDC.Raw.Admissible
      (DDC.filter accept id (fun _ answer => answer)).toFun history)
    (accepted : accept (DDC.outerQueries history)) :
    (DDC.latestReplies history = [] →
      history.receivedInnerQueries ++ [history.lastOuter] =
        history.outer.queries) ∧
    (DDC.latestReplies history ≠ [] →
      history.receivedInnerQueries = history.outer.queries) := by
  induction admissible with
  | start query =>
      constructor
      · intro
        rfl
      · simp
  | @afterInner history query prior responds reply inductionHypothesis =>
      have priorAccepted : accept (DDC.outerQueries history) := by
        simpa using accepted
      have priorNoReplies :=
        filter_query_implies_latestReplies_eq_nil accept history responds
      have priorOpen := (inductionHypothesis priorAccepted).1 priorNoReplies
      have queryEqual := filter_query_eq_lastOuter accept history responds
      constructor
      · simp
      · intro
        simp only [History.receivedInnerQueries_snocInner]
        rw [queryEqual, priorOpen]
        rfl
  | @afterOuter history prior reply responds query inductionHypothesis =>
      have priorPrefix : List.IsPrefix (DDC.outerQueries history)
          (DDC.outerQueries (history.snocOuter query)) := by
        simp only [DDC.outerQueries_snocOuter]
        exact List.prefix_append _ _
      have priorAccepted : accept (DDC.outerQueries history) :=
        prefixClosed priorPrefix accepted
      have priorHasReplies :=
        filter_reply_of_accept_implies_latestReplies_ne_nil accept history
          responds priorAccepted
      have priorClosed := (inductionHypothesis priorAccepted).2 priorHasReplies
      constructor
      · intro
        simp only [History.receivedInnerQueries_snocOuter]
        rw [priorClosed]
        simpa only [DDC.History.lastOuter_snocOuter, DDC.outerQueries] using
          (DDC.outerQueries_snocOuter history query).symm
      · simp

end Internal

/-- At a query emitted by a prefix-closed identity filter, the complete outer
history is exactly the history of forwarded queries including the pending one. -/
theorem filter_query_history
    {U : Type u} {V : Type v}
    (accept : List U → Prop) [DecidablePred accept]
    (prefixClosed : ∀ {prior whole : List U},
      List.IsPrefix prior whole → accept whole → accept prior)
    (history : DDC.History
      (Interface.single U V) (Interface.single U V))
    {query : U}
    (responds : Sum.inl query ∈
      DDC.filter accept id (fun _ answer => answer) history) :
    accept (DDC.outerQueries history) ∧
      query = history.lastOuter ∧
      history.receivedInnerQueries ++ [history.lastOuter] =
        history.outer.queries := by
  have admissible :=
    (DDC.mem_filter_iff accept id (fun _ answer => answer)
      history (Sum.inl query)).mp responds |>.1
  have accepted := Internal.filter_query_implies_accept accept history responds
  have noReplies :=
    Internal.filter_query_implies_latestReplies_eq_nil accept history responds
  exact ⟨accepted, Internal.filter_query_eq_lastOuter accept history responds,
    (Internal.filter_history_queries accept prefixClosed history admissible
      accepted).1 noReplies⟩

namespace Internal

lemma forwarding_query_eq_lastOuter
    (history : DDC.History
      (Interface.single X Y) (Interface.single X Y))
    {query : X}
    (responds : Sum.inl query ∈
      DDC.forwarding (Interface.single X Y) history) :
    query = history.lastOuter := by
  rw [DDC.mem_forwarding_iff] at responds
  rcases responds with ⟨admissible, shape⟩
  cases input : history.lastInput with
  | inl outerQuery =>
      simp only [input] at shape
      have last := admissible.lastOuter_eq_of_lastInput_outer input
      exact (Sum.inl.inj shape).trans last.symm
  | inr innerReply =>
      simp only [input] at shape
      obtain ⟨_, impossible⟩ := shape
      cases impossible

lemma forwarding_mem_reply
    (history : DDC.History
      (Interface.single X Y) (Interface.single X Y))
    {query : X}
    (responds : Sum.inl query ∈
      DDC.forwarding (Interface.single X Y) history)
    (reply : Option Y) :
    Sum.inr reply ∈ DDC.forwarding (Interface.single X Y)
      (history.snocInner query reply) := by
  rw [DDC.mem_forwarding_iff]
  refine ⟨DDC.Raw.Admissible.afterInner
      ((DDC.mem_forwarding_iff _ _ _).mp responds |>.1) responds reply, ?_⟩
  simp [forwarding_query_eq_lastOuter history responds]

def QueryLimitOuterPhase {A : Interface.{u, v}} (q : Nat)
    (outerHistory : DDC.History A (Interface.single X Y))
    (innerHistory : Option
      (DDC.History (Interface.single X Y) (Interface.single X Y))) : Prop :=
  match innerHistory with
  | none => outerHistory.receivedInnerQueries.length = 0
  | some history =>
      DDC.Raw.Admissible
          (DDC.forwarding (Interface.single X Y)).toFun history ∧
        DDC.Raw.Admissible (DDC.queryLimit q).toFun history ∧
        (DDC.outerQueries history).length =
          outerHistory.receivedInnerQueries.length ∧
        DDC.forwarding (Interface.single X Y) history =
          DDC.queryLimit q history ∧
        DDC.Internal.InnerClosed (DDC.forwarding (Interface.single X Y))
          (some history)

def QueryLimitInnerPhase {A : Interface.{u, v}} (q : Nat)
    (outerHistory : DDC.History A (Interface.single X Y))
    (innerHistory :
      DDC.History (Interface.single X Y) (Interface.single X Y)) : Prop :=
  DDC.Raw.Admissible
      (DDC.forwarding (Interface.single X Y)).toFun innerHistory ∧
    DDC.Raw.Admissible (DDC.queryLimit q).toFun innerHistory ∧
    (DDC.outerQueries innerHistory).length =
      outerHistory.receivedInnerQueries.length + 1 ∧
    DDC.forwarding (Interface.single X Y) innerHistory =
      DDC.queryLimit q innerHistory ∧
    (DDC.outerQueries innerHistory).length ≤ q

end Internal

/-- A converter whose next inner query always has room below `q` cannot
distinguish forwarding from a `q`-query limit below it. -/
theorem serial_forwarding_eq_serial_queryLimit
    {A : Interface.{u, v}}
    (outer : DDC A (Interface.single X Y)) (q : Nat)
    (queryBound : ∀ {history query},
      Sum.inl query ∈ outer history →
      history.receivedInnerQueries.length < q) :
    DDC.serial outer (DDC.forwarding (Interface.single X Y)) =
      DDC.serial outer (DDC.queryLimit q) := by
  apply DDC.serial_congr_right_of_gate
    (outerPhase := Internal.QueryLimitOuterPhase q)
    (innerPhase := Internal.QueryLimitInnerPhase q)
  refine
    { inner_eq := ?_
      outer_query_first := ?_
      outer_query_next := ?_
      inner_query := ?_
      inner_reply := ?_
      outer_next := ?_
      initial := ?_ }
  · intro outerHistory innerHistory phase
    exact phase.2.2.2.1
  · intro outerHistory query phase responds
    change outerHistory.receivedInnerQueries.length = 0 at phase
    have room := queryBound responds
    have positive : 0 < q := by omega
    let history : DDC.History
        (Interface.single X Y) (Interface.single X Y) :=
      DDC.History.singleton query
    have forwardingAdmissible : DDC.Raw.Admissible
        (DDC.forwarding (Interface.single X Y)).toFun history :=
      .start query
    have queryLimitAdmissible : DDC.Raw.Admissible
        (DDC.queryLimit q).toFun history := .start query
    have forwardingResponds : Sum.inl query ∈
        DDC.forwarding (Interface.single X Y) history := by
      rw [DDC.mem_forwarding_iff]
      exact ⟨forwardingAdmissible, by simp [history]⟩
    have queryLimitResponds : Sum.inl query ∈
        DDC.queryLimit q history := by
      simpa only [DDC.queryLimit, id_eq, history,
        DDC.History.lastOuter_singleton] using
        DDC.filter_mem_query
          (fun queries : List X => queries.length ≤ q) id
          (fun _ answer => answer) history queryLimitAdmissible
          (by simp [history]) (by simp [history]; omega)
    refine ⟨forwardingAdmissible, queryLimitAdmissible, ?_, ?_, ?_⟩
    · simpa only [history, DDC.outerQueries_singleton,
        List.length_singleton, History.receivedInnerQueries_singleton,
        List.length_nil, Nat.zero_add] using
          congrArg (fun count => count + 1) phase.symm
    · apply Part.eq_of_mem forwardingResponds.1
      rwa [Part.get_eq_of_mem forwardingResponds]
    · simp only [DDC.outerQueries_singleton, List.length_singleton]
      omega
  · intro outerHistory innerHistory query phase responds
    rcases phase with
      ⟨forwardingAdmissible, queryLimitAdmissible, countEqual,
        equal, closed⟩
    obtain ⟨priorReply, forwardingClosed⟩ := closed
    have queryLimitClosed : Sum.inr priorReply ∈
        DDC.queryLimit q innerHistory := by
      rw [← equal]
      exact forwardingClosed
    have room := queryBound responds
    let next := innerHistory.snocOuter query
    have forwardingNextAdmissible : DDC.Raw.Admissible
        (DDC.forwarding (Interface.single X Y)).toFun next :=
      .afterOuter forwardingAdmissible forwardingClosed query
    have queryLimitNextAdmissible : DDC.Raw.Admissible
        (DDC.queryLimit q).toFun next :=
      .afterOuter queryLimitAdmissible queryLimitClosed query
    have forwardingResponds : Sum.inl query ∈
        DDC.forwarding (Interface.single X Y) next := by
      rw [DDC.mem_forwarding_iff]
      exact ⟨forwardingNextAdmissible, by simp [next]⟩
    have within : (DDC.outerQueries next).length ≤ q := by
      simp only [next, DDC.outerQueries_snocOuter, List.length_append,
        List.length_singleton, countEqual]
      omega
    have queryLimitResponds : Sum.inl query ∈
        DDC.queryLimit q next := by
      have filtered := DDC.filter_mem_query
        (fun queries : List X => queries.length ≤ q) id
        (fun _ answer => answer) next queryLimitNextAdmissible
        (by simp [next]) within
      simpa only [DDC.queryLimit, id_eq, next,
        DDC.History.lastOuter_snocOuter] using filtered
    refine ⟨forwardingNextAdmissible, queryLimitNextAdmissible, ?_, ?_, within⟩
    · simp [countEqual]
    · apply Part.eq_of_mem forwardingResponds.1
      rwa [Part.get_eq_of_mem forwardingResponds]
  · intro outerHistory innerHistory query phase responds reply
    rcases phase with
      ⟨forwardingAdmissible, queryLimitAdmissible, countEqual,
        equal, within⟩
    have queryEqual :=
      Internal.forwarding_query_eq_lastOuter innerHistory responds
    subst query
    have queryLimitResponds : Sum.inl innerHistory.lastOuter ∈
        DDC.queryLimit q innerHistory := by
      rw [← equal]
      exact responds
    let next := innerHistory.snocInner innerHistory.lastOuter reply
    have forwardingNextAdmissible : DDC.Raw.Admissible
        (DDC.forwarding (Interface.single X Y)).toFun next :=
      .afterInner forwardingAdmissible responds reply
    have queryLimitNextAdmissible : DDC.Raw.Admissible
        (DDC.queryLimit q).toFun next :=
      .afterInner queryLimitAdmissible queryLimitResponds reply
    have forwardingResponds : Sum.inr reply ∈
        DDC.forwarding (Interface.single X Y) next := by
      simpa only [next] using
        Internal.forwarding_mem_reply innerHistory responds reply
    have queryLimitReply : Sum.inr reply ∈ DDC.queryLimit q next := by
      have noReplies := Internal.filter_query_implies_latestReplies_eq_nil
        (fun queries : List X => queries.length ≤ q) innerHistory
        (by simpa only [DDC.queryLimit] using queryLimitResponds)
      simpa only [DDC.queryLimit, next, id_eq] using
        DDC.filter_mem_reply
          (fun queries : List X => queries.length ≤ q) id
          (fun _ answer => answer) innerHistory queryLimitAdmissible
          noReplies
          (by simpa only [DDC.queryLimit, id_eq] using queryLimitResponds) reply
    refine ⟨forwardingNextAdmissible, queryLimitNextAdmissible, ?_, ?_, ?_⟩
    · simpa only [next, DDC.outerQueries_snocInner] using countEqual
    · apply Part.eq_of_mem forwardingResponds.1
      rwa [Part.get_eq_of_mem forwardingResponds]
    · simpa only [next, DDC.outerQueries_snocInner] using within
  · intro outerHistory innerHistory reply phase responds
    rcases phase with
      ⟨forwardingAdmissible, queryLimitAdmissible, countEqual,
        equal, within⟩
    refine ⟨forwardingAdmissible, queryLimitAdmissible, ?_, equal,
      ⟨reply, responds⟩⟩
    simpa only [History.receivedInnerQueries_snocInner,
      List.length_append, List.length_singleton] using countEqual
  · intro outerHistory innerHistory reply phase responds query
    cases innerHistory with
    | none =>
        simpa only [Internal.QueryLimitOuterPhase,
          History.receivedInnerQueries_snocOuter] using phase
    | some history =>
        simpa only [Internal.QueryLimitOuterPhase,
          History.receivedInnerQueries_snocOuter] using phase
  · intro query
    rfl

end


end RandomSystems.Ambient.DDC
