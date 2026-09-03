/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.RandomSystem
import RandomSystems.Converter.Relabel
import RandomSystems.Converter.Filter
import RandomSystems.Tactics.ProofAutomationAttributes

set_option autoImplicit false

/-!
# Deterministic converter action on cumulative random systems

Maurer--Renner 2016, Section 3.3 (printed p. 7), says: “A converter α,
when applied as an interface i of a resource, induces a function Φ → Φ.”
Every current DDC has branch-finite attempted histories, which is enough to
compile each finite outer observation to a finite inner observation. Jost's
uniform inside-query bound is therefore a sufficient specialization, not an
extra hypothesis on this deterministic lower action.

The selected probabilistic-converter action is `RandomSystem.applyPDC`. This
module exposes its canonical deterministic specialization as `applyDDC`.
-/

namespace RandomSystems.Ambient

noncomputable section

open Probability
open scoped ENNReal

universe u v w z p

namespace RandomSystem.Internal

namespace DDC

variable {A : Interface.{u, v}} {B : Interface.{w, z}} {R : Type p}

/-- The functional information retained after a DDC has returned one outer
reply.  It is exactly the proof needed to append the next outer query to the
same complete history. -/
structure Answered (converter : RandomSystems.Ambient.DDC A B) where
  history : RandomSystems.Ambient.DDC.History A B
  admissible : RandomSystems.Ambient.DDC.Raw.Admissible converter.toFun history
  reply : Option (A.answer history.lastOuter)
  responds : Sum.inr reply ∈ converter history

/-- The canonical DDC history at the beginning of one outer query. -/
structure Started (converter : RandomSystems.Ambient.DDC A B)
    (outerQuery : A.query) where
  history : RandomSystems.Ambient.DDC.History A B
  admissible : RandomSystems.Ambient.DDC.Raw.Admissible converter.toFun history
  aligned : history.lastOuter = outerQuery

/-- Begin the first outer query, or append a later query after the preceding
outer reply. -/
def beginQuery (converter : RandomSystems.Ambient.DDC A B)
    (previous : Option (Answered converter)) (outerQuery : A.query) :
    Started converter outerQuery :=
  match previous with
  | none =>
      { history := RandomSystems.Ambient.DDC.History.singleton outerQuery
        admissible := .start outerQuery
        aligned := by simp }
  | some answered =>
      { history := answered.history.snocOuter outerQuery
        admissible := .afterOuter answered.admissible answered.responds outerQuery
        aligned := by simp }

/-- The branch-finiteness field is the well-founded inner-continuation
relation used by the functional resolver. -/
theorem branchFinite_wellFounded
    (converter : RandomSystems.Ambient.DDC A B) :
    WellFounded converter.toFun.InnerContinuation := by
  exact converter.branchFinite

/-- Resolve from one admissible DDC history. -/
def resolveFrom (converter : RandomSystems.Ambient.DDC A B)
    (outerQuery : A.query)
    (continuation : Option (A.answer outerQuery) → Answered converter →
      Observation B R)
    (history : RandomSystems.Ambient.DDC.History A B)
    (admissible : RandomSystems.Ambient.DDC.Raw.Admissible converter.toFun history)
    (aligned : history.lastOuter = outerQuery) : Observation B R :=
  (branchFinite_wellFounded converter).fix
    (C := fun history =>
      RandomSystems.Ambient.DDC.Raw.Admissible converter.toFun history →
      history.lastOuter = outerQuery → Observation B R)
    (fun history resolve admissible aligned => by
      let selected : { response : RandomSystems.Ambient.DDC.Response history //
          response ∈ converter history } :=
        ⟨converter.response history admissible,
          converter.response_mem history admissible⟩
      exact match selected with
      | ⟨Sum.inl innerQuery, responds⟩ =>
          .query innerQuery fun reply =>
            resolve (history.snocInner innerQuery reply)
              ⟨innerQuery, reply, responds, rfl⟩
              (.afterInner admissible responds reply)
              (by simpa using aligned)
      | ⟨Sum.inr outerReply, responds⟩ =>
          let answered : Answered converter :=
            { history := history
              admissible := admissible
              reply := outerReply
              responds := responds }
          continuation (aligned ▸ outerReply) answered)
    history admissible aligned

/-- Resolve the finitely many consecutive inner queries selected on one
concrete reply branch.  Termination is exactly `converter.branchFinite`; no
number bounds all branches. -/
def resolveQuery (converter : RandomSystems.Ambient.DDC A B)
    (outerQuery : A.query)
    (continuation : Option (A.answer outerQuery) → Answered converter →
      Observation B R)
    (started : Started converter outerQuery) : Observation B R :=
  resolveFrom converter outerQuery continuation started.history
    started.admissible started.aligned

/-- Functional precomposition of an observation by a DDC. -/
def compileFrom (converter : RandomSystems.Ambient.DDC A B)
    (observation : Observation A R)
    (previous : Option (Answered converter)) : Observation B R :=
  Observation.rec
    (motive := fun _ => Option (Answered converter) → Observation B R)
    (fun result _ => .value result)
    (fun outerQuery _ compiled previous =>
      let started := beginQuery converter previous outerQuery
      resolveQuery converter outerQuery
        (fun reply answered => compiled reply (some answered)) started)
    observation previous

/-- Functional precomposition starting with the empty DDC history. -/
def compile (converter : RandomSystems.Ambient.DDC A B)
    (observation : Observation A R) : Observation B R :=
  compileFrom converter observation none

/-- Relabeling the result of one inner dialogue can be done before or after
the dialogue. -/
theorem resolveFrom_map {S : Type*}
    (converter : RandomSystems.Ambient.DDC A B) (outerQuery : A.query)
    (function : R → S)
    (continuation : Option (A.answer outerQuery) → Answered converter →
      Observation B R)
    (history : RandomSystems.Ambient.DDC.History A B)
    (admissible : RandomSystems.Ambient.DDC.Raw.Admissible converter.toFun history)
    (aligned : history.lastOuter = outerQuery) :
    resolveFrom converter outerQuery
        (fun reply endpoint => Observation.map function
          (continuation reply endpoint)) history admissible aligned =
      Observation.map function
        (resolveFrom converter outerQuery continuation history admissible aligned) := by
  induction history using converter.branchFinite.induction with
  | h history innerInduction =>
      rw [resolveFrom, WellFounded.fix_eq,
        resolveFrom, WellFounded.fix_eq]
      let selected : { response : RandomSystems.Ambient.DDC.Response history //
          response ∈ converter history } :=
        ⟨converter.response history admissible,
          converter.response_mem history admissible⟩
      change
        (match selected with
        | ⟨Sum.inl innerQuery, responds⟩ =>
            Observation.query innerQuery fun reply =>
              resolveFrom converter outerQuery
                (fun outerReply endpoint => Observation.map function
                  (continuation outerReply endpoint))
                (history.snocInner innerQuery reply)
                (.afterInner admissible responds reply) (by simpa using aligned)
        | ⟨Sum.inr outerReply, responds⟩ =>
            Observation.map function
              (continuation (aligned ▸ outerReply)
                { history := history
                  admissible := admissible
                  reply := outerReply
                  responds := responds })) =
        Observation.map function
          (match selected with
          | ⟨Sum.inl innerQuery, responds⟩ =>
              Observation.query innerQuery fun reply =>
                resolveFrom converter outerQuery continuation
                  (history.snocInner innerQuery reply)
                  (.afterInner admissible responds reply)
                  (by simpa using aligned)
          | ⟨Sum.inr outerReply, responds⟩ =>
              continuation (aligned ▸ outerReply)
                { history := history
                  admissible := admissible
                  reply := outerReply
                  responds := responds })
      cases selected with
      | mk response responds =>
          cases response with
          | inl innerQuery =>
              simp only [Observation.map]
              apply congrArg (Observation.query innerQuery)
              funext reply
              exact innerInduction (history.snocInner innerQuery reply)
                ⟨innerQuery, reply, responds, rfl⟩ _ _
          | inr outerReply => rfl

/-- Relabeling observation results commutes with DDC precomposition. -/
theorem compileFrom_map {S : Type*}
    (converter : RandomSystems.Ambient.DDC A B) (function : R → S)
    (observation : Observation A R) (previous : Option (Answered converter)) :
    compileFrom converter (Observation.map function observation) previous =
      Observation.map function (compileFrom converter observation previous) := by
  induction observation generalizing previous with
  | value result => rfl
  | query outerQuery continuation inductionHypothesis =>
      change resolveQuery converter outerQuery
          (fun reply endpoint => compileFrom converter
            (Observation.map function (continuation reply)) (some endpoint))
          (beginQuery converter previous outerQuery) = _
      rw [show (fun reply endpoint => compileFrom converter
          (Observation.map function (continuation reply)) (some endpoint)) =
          (fun reply endpoint => Observation.map function
            (compileFrom converter (continuation reply) (some endpoint))) by
        funext reply endpoint
        exact inductionHypothesis reply (some endpoint)]
      exact resolveFrom_map converter outerQuery function
        (fun reply endpoint =>
          compileFrom converter (continuation reply) (some endpoint))
        (beginQuery converter previous outerQuery).history
        (beginQuery converter previous outerQuery).admissible
        (beginQuery converter previous outerQuery).aligned

theorem compile_map {S : Type*}
    (converter : RandomSystems.Ambient.DDC A B) (function : R → S)
    (observation : Observation A R) :
    compile converter (Observation.map function observation) =
      Observation.map function (compile converter observation) :=
  compileFrom_map converter function observation none

/-- Pointwise equality of continuation laws is preserved by one well-founded
inner dialogue. -/
theorem distributionFrom_resolveFrom_apply_congr
    (behavior : RandomSystem B)
    (converter : RandomSystems.Ambient.DDC A B) (outerQuery : A.query)
    (left right : Option (A.answer outerQuery) → Answered converter →
      Observation B R)
    (history : RandomSystems.Ambient.DDC.History A B)
    (admissible : RandomSystems.Ambient.DDC.Raw.Admissible converter.toFun history)
    (aligned : history.lastOuter = outerQuery)
    (prior : RandomSystem.Internal.Core.Transcript B)
    (result : R)
    (continuationsEqual : ∀ reply endpoint transcript,
      Observation.distributionFrom behavior (left reply endpoint) transcript
          result =
        Observation.distributionFrom behavior (right reply endpoint) transcript
          result) :
    Observation.distributionFrom behavior
        (resolveFrom converter outerQuery left history admissible aligned) prior
        result =
      Observation.distributionFrom behavior
        (resolveFrom converter outerQuery right history admissible aligned) prior
        result := by
  induction history using converter.branchFinite.induction generalizing prior with
  | h history innerInduction =>
      rw [resolveFrom, WellFounded.fix_eq,
        resolveFrom, WellFounded.fix_eq]
      let selected : { response : RandomSystems.Ambient.DDC.Response history //
          response ∈ converter history } :=
        ⟨converter.response history admissible,
          converter.response_mem history admissible⟩
      change
        (Observation.distributionFrom behavior
          (match selected with
          | ⟨Sum.inl innerQuery, responds⟩ =>
              Observation.query innerQuery fun reply =>
                resolveFrom converter outerQuery left
                  (history.snocInner innerQuery reply)
                  (.afterInner admissible responds reply)
                  (by simpa using aligned)
          | ⟨Sum.inr outerReply, responds⟩ =>
              left (aligned ▸ outerReply)
                { history := history
                  admissible := admissible
                  reply := outerReply
                  responds := responds }) prior) result =
        (Observation.distributionFrom behavior
          (match selected with
          | ⟨Sum.inl innerQuery, responds⟩ =>
              Observation.query innerQuery fun reply =>
                resolveFrom converter outerQuery right
                  (history.snocInner innerQuery reply)
                  (.afterInner admissible responds reply)
                  (by simpa using aligned)
          | ⟨Sum.inr outerReply, responds⟩ =>
              right (aligned ▸ outerReply)
                { history := history
                  admissible := admissible
                  reply := outerReply
                  responds := responds }) prior) result
      cases selected with
      | mk response responds =>
          cases response with
          | inl innerQuery =>
              rw [Observation.distributionFrom,
                Observation.distributionFrom,
                Finsupp.sum_apply, Finsupp.sum_apply]
              apply Finsupp.sum_congr
              intro reply membership
              exact innerInduction (history.snocInner innerQuery reply)
                ⟨innerQuery, reply, responds, rfl⟩ _ _
                (prior ++ [⟨innerQuery, reply⟩])
          | inr outerReply =>
              exact continuationsEqual _ _ prior

theorem distributionFrom_resolveQuery_apply_congr
    (behavior : RandomSystem B)
    (converter : RandomSystems.Ambient.DDC A B) (outerQuery : A.query)
    (left right : Option (A.answer outerQuery) → Answered converter →
      Observation B R)
    (started : Started converter outerQuery)
    (prior : RandomSystem.Internal.Core.Transcript B)
    (result : R)
    (continuationsEqual : ∀ reply endpoint transcript,
      Observation.distributionFrom behavior (left reply endpoint) transcript
          result =
        Observation.distributionFrom behavior (right reply endpoint) transcript
          result) :
    Observation.distributionFrom behavior
        (resolveQuery converter outerQuery left started) prior result =
      Observation.distributionFrom behavior
        (resolveQuery converter outerQuery right started) prior result :=
  distributionFrom_resolveFrom_apply_congr behavior converter outerQuery left right
    started.history started.admissible started.aligned prior result
    continuationsEqual

/-- A compiled observation whose every leaf is relabeled to `true` has all of
the current cylinder mass at `true`. -/
theorem distributionFrom_compileFrom_map_const_true
    {S : Type*} (behavior : RandomSystem B)
    (converter : RandomSystems.Ambient.DDC A B)
    (observation : Observation A S)
    (previous : Option (Answered converter))
    (prior : RandomSystem.Internal.Core.Transcript B) :
    Observation.distributionFrom behavior
        (compileFrom converter
          (Observation.map (fun _ => true) observation) previous)
        prior true = behavior.mass prior := by
  rw [compileFrom_map, Observation.distributionFrom_map,
    Distribution.fTransform_const_eq_single_weight,
    Finsupp.single_apply, if_pos rfl,
    Observation.weight_distributionFrom]

/-- A compiled observation whose every leaf is relabeled to `false` has no
mass at `true`. -/
theorem distributionFrom_compileFrom_map_const_false
    {S : Type*} (behavior : RandomSystem B)
    (converter : RandomSystems.Ambient.DDC A B)
    (observation : Observation A S)
    (previous : Option (Answered converter))
    (prior : RandomSystem.Internal.Core.Transcript B) :
    Observation.distributionFrom behavior
        (compileFrom converter
          (Observation.map (fun _ => false) observation) previous)
        prior true = 0 := by
  rw [compileFrom_map, Observation.distributionFrom_map,
    Distribution.fTransform_const_eq_single_weight,
    Finsupp.single_apply, if_neg]
  decide

/-- Selecting one enumerated outer leaf and then compiling has the same
success mass as compiling the exact transcript matcher for that leaf. -/
theorem distributionFrom_compileFrom_select_leaf
    (behavior : RandomSystem B)
    (converter : RandomSystems.Ambient.DDC A B)
    {observation : Observation A R} (leaf : Observation.Leaf observation)
    (previous : Option (Answered converter))
    (prior : RandomSystem.Internal.Core.Transcript B) :
    Observation.distributionFrom behavior
        (compileFrom converter
          (Observation.map (Observation.selectsValue leaf)
            (Observation.enumerate observation)) previous) prior true =
      Observation.distributionFrom behavior
        (compileFrom converter
          (Observation.accepts leaf.transcript) previous) prior true := by
  classical
  induction leaf generalizing previous prior with
  | value result =>
      simp [Observation.enumerate, Observation.Leaf.transcript,
        Observation.accepts, Observation.afterTranscript,
        Observation.selectsValue]
  | @query input continuation selectedReply leaf inductionHypothesis =>
      change Observation.distributionFrom behavior
          (resolveQuery converter input
            (fun actual endpoint => compileFrom converter
              (Observation.map
                (Observation.selectsValue
                  (Observation.Leaf.query selectedReply leaf))
                (Observation.map (Observation.Leaf.query actual)
              (Observation.enumerate (continuation actual))))
              (some endpoint))
            (beginQuery converter previous input)) prior true = _
      change _ = Observation.distributionFrom behavior
          (compileFrom converter
            (Observation.accepts
              (⟨input, selectedReply⟩ :: leaf.transcript)) previous)
          prior true
      rw [Observation.accepts, Observation.afterTranscript_cons]
      change _ = Observation.distributionFrom behavior
          (resolveQuery converter input
            (fun actual endpoint => compileFrom converter
              (if actual = selectedReply then
                Observation.accepts leaf.transcript
              else .value false) (some endpoint))
            (beginQuery converter previous input)) prior true
      exact distributionFrom_resolveQuery_apply_congr
        behavior converter input
        (fun actual endpoint => compileFrom converter
          (Observation.map
            (Observation.selectsValue
              (Observation.Leaf.query selectedReply leaf))
            (Observation.map (Observation.Leaf.query actual)
              (Observation.enumerate (continuation actual))))
          (some endpoint))
        (fun actual endpoint => compileFrom converter
          (if actual = selectedReply then
            Observation.accepts leaf.transcript
          else .value false) (some endpoint))
        (beginQuery converter previous input) prior true (by
          intro actual endpoint transcript
          change Observation.distributionFrom behavior
              (compileFrom converter
                (Observation.map
                  (Observation.selectsValue
                    (Observation.Leaf.query selectedReply leaf))
                  (Observation.map (Observation.Leaf.query actual)
                    (Observation.enumerate (continuation actual))))
                (some endpoint)) transcript true =
            Observation.distributionFrom behavior
              (compileFrom converter
                (if actual = selectedReply then
                  Observation.accepts leaf.transcript
                else .value false) (some endpoint)) transcript true
          by_cases replyEqual : actual = selectedReply
          · subst actual
            rw [if_pos rfl, Observation.map_map]
            have selectorEqual :
                (Observation.selectsValue
                    (Observation.Leaf.query selectedReply leaf) ∘
                  Observation.Leaf.query selectedReply) =
                Observation.selectsValue leaf := by
              funext candidate
              simp only [Function.comp_apply, Observation.selectsValue]
              by_cases equal : candidate = leaf
              · subst candidate
                simp
              · have unequal :
                    Observation.Leaf.query selectedReply candidate ≠
                      Observation.Leaf.query selectedReply leaf := by
                  intro contradiction
                  injection contradiction
                  contradiction
                simp [equal, unequal]
            rw [selectorEqual]
            exact inductionHypothesis (some endpoint) transcript
          · rw [if_neg replyEqual, Observation.map_map]
            have selectorFalse :
                (Observation.selectsValue
                    (Observation.Leaf.query selectedReply leaf) ∘
                  Observation.Leaf.query actual) =
                (fun _ => false) := by
              funext candidate
              simp only [Function.comp_apply, Observation.selectsValue]
              have unequal : Observation.Leaf.query actual candidate ≠
                  Observation.Leaf.query selectedReply leaf := by
                intro contradiction
                have : actual = selectedReply := by
                  injection contradiction
                exact replyEqual this
              simp [unequal]
            rw [selectorFalse]
            calc
              Observation.distributionFrom behavior
                  (compileFrom converter
                    (Observation.map (fun _ => false)
                      (Observation.enumerate (continuation actual)))
                    (some endpoint)) transcript true = 0 :=
                distributionFrom_compileFrom_map_const_false
                  behavior converter
                  (Observation.enumerate (continuation actual))
                  (some endpoint) transcript
              _ = Observation.distributionFrom behavior
                  (compileFrom converter (.value false) (some endpoint))
                  transcript true := by
                simp [compileFrom])

/-- Replacing the successful leaf below a displayed outer transcript by any
finite all-`true` observation preserves its compiled success mass. -/
theorem distributionFrom_compileFrom_afterTranscript_const_true
    {S : Type*} (behavior : RandomSystem B)
    (converter : RandomSystems.Ambient.DDC A B)
    (target : RandomSystem.Internal.Core.Transcript A) (tail : Observation A S)
    (previous : Option (Answered converter))
    (prior : RandomSystem.Internal.Core.Transcript B) :
    Observation.distributionFrom behavior
        (compileFrom converter
          (Observation.afterTranscript target
            (Observation.map (fun _ => true) tail)) previous) prior true =
      Observation.distributionFrom behavior
        (compileFrom converter (Observation.accepts target) previous)
        prior true := by
  classical
  induction target generalizing previous prior with
  | nil =>
      rw [Observation.afterTranscript_nil]
      rw [distributionFrom_compileFrom_map_const_true]
      change behavior.mass prior =
        Observation.distributionFrom behavior (.value true) prior true
      simp [Observation.distributionFrom]
  | cons expected remaining inductionHypothesis =>
      rcases expected with ⟨outerQuery, expectedReply⟩
      rw [Observation.afterTranscript_cons]
      change Observation.distributionFrom behavior
          (resolveQuery converter outerQuery
            (fun reply endpoint => compileFrom converter
              (if reply = expectedReply then
                Observation.afterTranscript remaining
                  (Observation.map (fun _ => true) tail)
              else .value false) (some endpoint))
            (beginQuery converter previous outerQuery)) prior true = _
      rw [Observation.accepts, Observation.afterTranscript_cons]
      change _ = Observation.distributionFrom behavior
          (resolveQuery converter outerQuery
            (fun reply endpoint => compileFrom converter
              (if reply = expectedReply then
                Observation.afterTranscript remaining (.value true)
              else .value false) (some endpoint))
            (beginQuery converter previous outerQuery)) prior true
      exact distributionFrom_resolveQuery_apply_congr
        behavior converter outerQuery
        (fun reply endpoint => compileFrom converter
          (if reply = expectedReply then
            Observation.afterTranscript remaining
              (Observation.map (fun _ => true) tail)
          else .value false) (some endpoint))
        (fun reply endpoint => compileFrom converter
          (if reply = expectedReply then
            Observation.afterTranscript remaining (.value true)
          else .value false) (some endpoint))
        (beginQuery converter previous outerQuery) prior true
        (by
          intro reply endpoint transcript
          by_cases replyEqual : reply = expectedReply
          · simp only [replyEqual, if_pos]
            change Observation.distributionFrom behavior
                (compileFrom converter
                  (Observation.afterTranscript remaining
                    (Observation.map (fun _ => true) tail))
                  (some endpoint)) transcript true =
              Observation.distributionFrom behavior
                (compileFrom converter
                  (Observation.afterTranscript remaining (.value true))
                  (some endpoint)) transcript true
            have inductionEqual := inductionHypothesis (some endpoint) transcript
            simpa only [Observation.accepts] using inductionEqual
          · simp only [replyEqual, if_false])

@[simp]
theorem compile_value (converter : RandomSystems.Ambient.DDC A B)
    (result : R) : compile converter (.value result) = .value result :=
  rfl

namespace Correctness

/-- The semantic invariant carried by the reply branch selected during Observation
evaluation.  It is a proposition about complete functions and histories, not
stored converter state. -/
inductive EvaluationContext
    (converter : RandomSystems.Ambient.DDC A B) (system : DDS B) :
    Option (Answered converter) → List B.query → List A.query → Prop
  | initial : EvaluationContext converter system none [] []
  | answered (endpoint : Answered converter) (innerPrior : List B.query)
      (outerHistory : History A)
      (context : RandomSystems.Ambient.Internal.PrefixContext converter system
        outerHistory endpoint.history innerPrior) :
      EvaluationContext converter system (some endpoint) innerPrior
        outerHistory.queries

/-- Beginning the next outer query preserves the complete-history invariant. -/
theorem beginQuery_context
    {converter : RandomSystems.Ambient.DDC A B} {system : DDS B}
    {previous : Option (Answered converter)} {innerPrior : List B.query}
    {outerPrior : List A.query}
    (context : EvaluationContext converter system previous innerPrior outerPrior)
    (outerQuery : A.query) :
    RandomSystems.Ambient.Internal.PrefixContext converter system
      (Attachment.innerHistory outerPrior outerQuery)
      (beginQuery converter previous outerQuery).history innerPrior := by
  cases context with
  | initial =>
      change RandomSystems.Ambient.Internal.PrefixContext converter system
        (History.singleton outerQuery)
        (RandomSystems.Ambient.DDC.History.singleton outerQuery) []
      exact RandomSystems.Ambient.Internal.PrefixContext.start converter system
        outerQuery
  | answered endpoint innerPrior outerHistory prefixContext =>
      have extended :=
        RandomSystems.Ambient.Internal.PrefixContext.afterOuter prefixContext
          endpoint.responds outerQuery
      have historyEqual : History.snoc outerHistory outerQuery =
          Attachment.innerHistory outerHistory.queries outerQuery := by
        apply History.ext
        rfl
      simpa only [beginQuery, historyEqual] using extended

/-- The direct cast selected by `Started.aligned` is the ordinary query-indexed
reply of the attached deterministic system. -/
theorem selected_outer_reply_eq
    {converter : RandomSystems.Ambient.DDC A B} {system : DDS B}
    {innerPrior : List B.query} {outerPrior : List A.query}
    (outerQuery : A.query)
    {history : RandomSystems.Ambient.DDC.History A B}
    (context : RandomSystems.Ambient.Internal.PrefixContext converter system
      (Attachment.innerHistory outerPrior outerQuery) history innerPrior)
    (aligned : history.lastOuter = outerQuery)
    {reply : Option (A.answer history.lastOuter)}
    (responds : Sum.inr reply ∈ converter history) :
    aligned ▸ reply =
      Attachment.innerReplyAt (applySystem converter system) outerPrior outerQuery := by
  let outerHistory := Attachment.innerHistory outerPrior outerQuery
  have historyAligned :
      history.lastOuter = outerHistory.last := by
    simpa [outerHistory] using aligned
  have attached :=
    RandomSystems.Ambient.Internal.PrefixContext.finish context historyAligned
      responds
  have leftToRaw : HEq (aligned ▸ reply) reply :=
    eqRec_heq (φ := fun query => Option (A.answer query)) aligned reply
  have alignedToRaw : HEq
      (cast (congrArg (fun query => Option (A.answer query)) historyAligned)
        reply) reply :=
    cast_heq
      (congrArg (fun query => Option (A.answer query)) historyAligned) reply
  have rawToAttached : HEq reply
      (applySystem converter system outerHistory) :=
    alignedToRaw.symm.trans (heq_of_eq attached)
  have queriedToAttached : HEq
      (Attachment.innerReplyAt (applySystem converter system)
        outerPrior outerQuery)
      (applySystem converter system outerHistory) := by
    unfold Attachment.innerReplyAt
    apply HEq.trans (cast_heq _ _)
    apply heq_of_eq
    congr 1
  exact eq_of_heq
    (leftToRaw.trans (rawToAttached.trans queriedToAttached.symm))

/-- Evaluation of the well-founded inner dialogue returns the same reply as
functional DDS attachment and hands a valid prefix to its continuation. -/
theorem evaluateFrom_resolveQuery
    {converter : RandomSystems.Ambient.DDC A B} {system : DDS B}
    {previous : Option (Answered converter)} {innerPrior : List B.query}
    {outerPrior : List A.query}
    (context : EvaluationContext converter system previous innerPrior outerPrior)
    (outerQuery : A.query)
    (continuation : Option (A.answer outerQuery) → Answered converter →
      Observation B R)
    (result : Option (A.answer outerQuery) → R)
    (continuationCorrect :
      ∀ (reply : Option (A.answer outerQuery))
        (endpoint : Answered converter) (nextInnerPrior : List B.query),
        EvaluationContext converter system (some endpoint) nextInnerPrior
            (outerPrior ++ [outerQuery]) →
          Observation.evaluateFrom (continuation reply endpoint) system
              nextInnerPrior = result reply) :
    Observation.evaluateFrom
        (resolveQuery converter outerQuery continuation
          (beginQuery converter previous outerQuery))
        system innerPrior =
      result (Attachment.innerReplyAt (applySystem converter system)
        outerPrior outerQuery) := by
  let started := beginQuery converter previous outerQuery
  have startContext : RandomSystems.Ambient.Internal.PrefixContext converter system
      (Attachment.innerHistory outerPrior outerQuery) started.history innerPrior :=
    beginQuery_context context outerQuery
  unfold resolveQuery
  change Observation.evaluateFrom
      (resolveFrom converter outerQuery continuation started.history
        started.admissible started.aligned) system innerPrior = _
  have resolveCorrect : ∀
      (history : RandomSystems.Ambient.DDC.History A B)
      (admissible : RandomSystems.Ambient.DDC.Raw.Admissible
        converter.toFun history)
      (aligned : history.lastOuter = outerQuery)
      (currentInnerPrior : List B.query),
      RandomSystems.Ambient.Internal.PrefixContext converter system
          (Attachment.innerHistory outerPrior outerQuery) history
          currentInnerPrior →
        Observation.evaluateFrom
            (resolveFrom converter outerQuery continuation history
              admissible aligned) system currentInnerPrior =
          result (Attachment.innerReplyAt (applySystem converter system)
            outerPrior outerQuery) := by
    intro history
    induction history using converter.branchFinite.induction with
    | h history innerInduction =>
        intro admissible aligned currentInnerPrior currentContext
        have selected := converter.response_mem history admissible
        cases responseEqual : converter.response history admissible with
        | inl innerQuery =>
            rw [resolveFrom, WellFounded.fix_eq]
            simp only [responseEqual]
            have responds : Sum.inl innerQuery ∈ converter history := by
              simpa only [responseEqual] using selected
            let reply :=
              Attachment.innerReplyAt system currentInnerPrior innerQuery
            rw [Observation.evaluateFrom_query]
            exact innerInduction (history.snocInner innerQuery reply)
              ⟨innerQuery, reply, responds, rfl⟩
              (.afterInner admissible responds reply)
              (by simpa using aligned)
              (currentInnerPrior ++ [innerQuery])
              (RandomSystems.Ambient.Internal.PrefixContext.afterInner
                currentContext responds)
        | inr outerReply =>
            rw [resolveFrom, WellFounded.fix_eq]
            simp only [responseEqual]
            have responds : Sum.inr outerReply ∈ converter history := by
              simpa only [responseEqual] using selected
            let endpoint : Answered converter :=
              { history := history
                admissible := admissible
                reply := outerReply
                responds := responds }
            have nextContext : EvaluationContext converter system (some endpoint)
                currentInnerPrior (outerPrior ++ [outerQuery]) := by
              have outerQueries :
                  (Attachment.innerHistory outerPrior outerQuery).queries =
                    outerPrior ++ [outerQuery] := rfl
              exact outerQueries ▸
                EvaluationContext.answered endpoint currentInnerPrior
                  (Attachment.innerHistory outerPrior outerQuery) currentContext
            rw [continuationCorrect (aligned ▸ outerReply) endpoint
              currentInnerPrior nextContext]
            rw [selected_outer_reply_eq outerQuery currentContext aligned responds]
  exact resolveCorrect started.history started.admissible started.aligned
    innerPrior startContext

/-- Compiling an outer observation and evaluating it on the inner DDS is
exactly evaluation of the original observation on functional attachment. -/
theorem evaluateFrom_compileFrom
    {converter : RandomSystems.Ambient.DDC A B} {system : DDS B}
    (observation : Observation A R)
    {previous : Option (Answered converter)} {innerPrior : List B.query}
    {outerPrior : List A.query}
    (context : EvaluationContext converter system previous innerPrior outerPrior) :
    Observation.evaluateFrom (compileFrom converter observation previous)
        system innerPrior =
      Observation.evaluateFrom observation (applySystem converter system)
        outerPrior := by
  induction observation generalizing previous innerPrior outerPrior with
  | value result => rfl
  | query outerQuery continuation inductionHypothesis =>
      rw [Observation.evaluateFrom_query]
      change Observation.evaluateFrom
          (resolveQuery converter outerQuery
            (fun reply endpoint =>
              compileFrom converter (continuation reply) (some endpoint))
            (beginQuery converter previous outerQuery))
          system innerPrior = _
      exact evaluateFrom_resolveQuery context outerQuery
        (fun reply endpoint =>
          compileFrom converter (continuation reply) (some endpoint))
        (fun reply => Observation.evaluateFrom (continuation reply)
          (applySystem converter system) (outerPrior ++ [outerQuery]))
        (by
          intro reply endpoint nextInnerPrior nextContext
          exact inductionHypothesis reply nextContext)

/-- Root observation factorization for every current branch-finite DDC. -/
theorem evaluate_compile
    (converter : RandomSystems.Ambient.DDC A B)
    (observation : Observation A R) (system : DDS B) :
    Observation.evaluate (compile converter observation) system =
      Observation.evaluate observation (applySystem converter system) := by
  exact evaluateFrom_compileFrom observation EvaluationContext.initial

/-- Forwarding compilation is observationally the identity. -/
theorem evaluate_compile_forwarding
    (observation : Observation A R) (system : DDS A) :
    Observation.evaluate
        (compile (RandomSystems.Ambient.DDC.forwarding A) observation) system =
      Observation.evaluate observation system := by
  rw [evaluate_compile,
    RandomSystems.Ambient.applySystem_forwarding_eq]

/-- Serial compilation fuses for every deterministic inner system. -/
theorem evaluate_compile_serial
    {A₁ B₁ C₁ : Interface.{u, v}}
    (outer : RandomSystems.Ambient.DDC A₁ B₁)
    (inner : RandomSystems.Ambient.DDC B₁ C₁)
    (observation : Observation A₁ R) (system : DDS C₁) :
    Observation.evaluate
        (compile (RandomSystems.Ambient.DDC.serial outer inner) observation)
        system =
      Observation.evaluate (compile inner (compile outer observation)) system := by
  calc
    Observation.evaluate
        (compile (RandomSystems.Ambient.DDC.serial outer inner) observation)
        system =
        Observation.evaluate observation
          (applySystem (RandomSystems.Ambient.DDC.serial outer inner) system) :=
      evaluate_compile _ _ _
    _ = Observation.evaluate observation
          (applySystem outer (applySystem inner system)) := by
      rw [RandomSystems.Ambient.DDC.applySystem_serial_eq]
    _ = Observation.evaluate (compile outer observation)
          (applySystem inner system) :=
      (evaluate_compile outer observation (applySystem inner system)).symm
    _ = Observation.evaluate (compile inner (compile outer observation)) system :=
      (evaluate_compile inner (compile outer observation) system).symm

end Correctness

end DDC


end RandomSystem.Internal

namespace RandomSystem

noncomputable section

open Probability
open RandomSystems.Ambient
open RandomSystem.Internal

variable {A B : Interface.{u, v}}

namespace Internal.Router

/-- Relabel every query and query-selected optional reply in a transcript. -/
def mapTranscript (equivalence : A.Equiv B)
    (transcript : RandomSystem.Internal.Core.Transcript A) : RandomSystem.Internal.Core.Transcript B :=
  transcript.map equivalence.innerReply

/-- The graph of relabeling a cumulative random system along an interface
equivalence. -/
def Relabeled (equivalence : A.Equiv B)
    (source : RandomSystem A) (target : RandomSystem B) : Prop :=
  ∀ transcript, target.mass (mapTranscript equivalence transcript) =
    source.mass transcript

@[simp]
theorem mapTranscript_innerReply_symm (equivalence : A.Equiv B)
    (transcript : RandomSystem.Internal.Core.Transcript B) :
    mapTranscript equivalence
        (transcript.map equivalence.innerReply.symm) = transcript := by
  unfold mapTranscript
  rw [List.map_map]
  have inverse : equivalence.innerReply ∘ equivalence.innerReply.symm = id := by
    funext reply
    exact equivalence.innerReply.apply_symm_apply reply
  rw [inverse, List.map_id]

namespace Relabeled

/-- Relabeling along an interface equivalence has a unique target. -/
theorem target_eq (equivalence : A.Equiv B) (source : RandomSystem A)
    {left right : RandomSystem B}
    (leftRelabeled : Relabeled equivalence source left)
    (rightRelabeled : Relabeled equivalence source right) :
    left = right := by
  apply RandomSystem.ext
  intro transcript
  let sourceTranscript := transcript.map equivalence.innerReply.symm
  have leftMass := leftRelabeled sourceTranscript
  have rightMass := rightRelabeled sourceTranscript
  rw [mapTranscript_innerReply_symm] at leftMass rightMass
  exact leftMass.trans rightMass.symm

end Relabeled

end Internal.Router

variable {C : Interface.{w, z}}

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), says: “A converter α,
when applied as an interface i of a resource, induces a function Φ → Φ.”
Every branch-finite DDC induces that deterministic lower action directly on
cumulative random systems: an outer cylinder receives the mass of its finite
functional preimage. -/
noncomputable def applyDDC (converter : RandomSystems.Ambient.DDC A C)
    (behavior : RandomSystem C) : RandomSystem A where
  mass := fun transcript =>
    Observation.distribution behavior
      (DDC.compile converter (Observation.accepts transcript)) true
  mass_nonneg := fun transcript =>
    Observation.nonNeg_distributionFrom behavior
      (DDC.compile converter (Observation.accepts transcript)) [] true
  mass_nil := by
    rw [show Observation.accepts ([] : RandomSystem.Internal.Core.Transcript A) =
      .value true from rfl, DDC.compile_value]
    simp [Observation.distribution, Observation.distributionFrom,
      behavior.mass_nil]
  extensionLaw := fun transcript query =>
    Observation.successProjection
      (Observation.distribution behavior
        (DDC.compile converter (Observation.replyAfter transcript query)))
  extensionLaw_apply := by
    intro transcript query reply
    let law := Observation.distribution behavior
      (DDC.compile converter (Observation.replyAfter transcript query))
    calc
      Observation.successProjection law reply = law (some reply) :=
        Observation.successProjection_apply law reply
      _ = Distribution.fTransform
          (Observation.selectsValue (some reply)) law true :=
        (Observation.fTransform_selectsValue_true law (some reply)).symm
      _ = Observation.distribution behavior
          (Observation.map (Observation.selectsValue (some reply))
            (DDC.compile converter
              (Observation.replyAfter transcript query))) true := by
        rw [Observation.distribution_map]
      _ = Observation.distribution behavior
          (DDC.compile converter
            (Observation.map (Observation.selectsValue (some reply))
              (Observation.replyAfter transcript query))) true := by
        rw [DDC.compile_map]
      _ = Observation.distribution behavior
          (DDC.compile converter
            (Observation.accepts
              (transcript ++ [⟨query, reply⟩]))) true := by
        rw [Observation.map_eq_some_replyAfter]
  extensionLaw_weight := by
    intro transcript query
    let law := Observation.distribution behavior
      (DDC.compile converter (Observation.replyAfter transcript query))
    calc
      (Observation.successProjection law).weight =
          law.mass (fun candidate => candidate.isSome = true) :=
        Observation.successProjection_weight law
      _ = Distribution.fTransform Option.isSome law true :=
        (Distribution.fTransform_apply_eq_mass Option.isSome law true).symm
      _ = Observation.distribution behavior
          (Observation.map Option.isSome
            (DDC.compile converter
              (Observation.replyAfter transcript query))) true := by
        rw [Observation.distribution_map]
      _ = Observation.distribution behavior
          (DDC.compile converter
            (Observation.map Option.isSome
              (Observation.replyAfter transcript query))) true := by
        rw [DDC.compile_map]
      _ = Observation.distribution behavior
          (DDC.compile converter
            (Observation.afterTranscript transcript
              (Observation.map (fun _ => true)
                (Observation.replyObservation query)))) true := by
        rw [Observation.map_isSome_replyAfter]
      _ = Observation.distribution behavior
          (DDC.compile converter (Observation.accepts transcript)) true := by
        exact DDC.distributionFrom_compileFrom_afterTranscript_const_true
          behavior converter transcript (Observation.replyObservation query)
          none []

/-- A DDC acts on a cumulative random system by converter attachment. -/
noncomputable instance instHSMulDDCRandomSystem :
    HSMul (RandomSystems.Ambient.DDC A C)
      (RandomSystem C) (RandomSystem A) where
  hSMul := applyDDC

@[simp]
theorem smul_eq_applyDDC
    (converter : RandomSystems.Ambient.DDC A C)
    (behavior : RandomSystem C) :
    converter • behavior = applyDDC converter behavior :=
  rfl

@[simp]
theorem applyDDC_mass (converter : RandomSystems.Ambient.DDC A C)
    (behavior : RandomSystem C) (transcript : RandomSystem.Internal.Core.Transcript A) :
    (applyDDC converter behavior).mass transcript =
      Observation.distribution behavior
        (DDC.compile converter (Observation.accepts transcript)) true :=
  rfl

end

end RandomSystem

namespace RandomSystem.Internal.Observation

noncomputable section

open Probability
open RandomSystems.Ambient
open RandomSystem.Internal.Core

variable {A : Interface.{u, v}} {B : Interface.{w, z}} {R : Type p}

/-- The inner probability of one compiled enumerated leaf is the outer
cylinder mass assigned by direct DDC action. -/
theorem distribution_compile_enumerate_applyDDC
    (converter : RandomSystems.Ambient.DDC A B) (behavior : RandomSystem B)
    (observation : Observation A R) (leaf : Leaf observation) :
    distribution behavior (DDC.compile converter (enumerate observation)) leaf =
      (RandomSystem.applyDDC converter behavior).mass leaf.transcript := by
  let law := distribution behavior
    (DDC.compile converter (enumerate observation))
  calc
    law leaf = Distribution.fTransform (selectsValue leaf) law true :=
      (fTransform_selectsValue_true law leaf).symm
    _ = distribution behavior
        (map (selectsValue leaf)
          (DDC.compile converter (enumerate observation))) true := by
      rw [distribution_map]
    _ = distribution behavior
        (DDC.compile converter
          (map (selectsValue leaf) (enumerate observation))) true := by
      rw [DDC.compile_map]
    _ = distribution behavior
        (DDC.compile converter (accepts leaf.transcript)) true := by
      exact DDC.distributionFrom_compileFrom_select_leaf
        behavior converter leaf none []
    _ = (RandomSystem.applyDDC converter behavior).mass leaf.transcript := by
      rfl

/-- Enumerating outer leaves commutes exactly with direct DDC action. -/
theorem distribution_enumerate_applyDDC
    (converter : RandomSystems.Ambient.DDC A B) (behavior : RandomSystem B)
    (observation : Observation A R) :
    distribution (RandomSystem.applyDDC converter behavior) (enumerate observation) =
      distribution behavior (DDC.compile converter (enumerate observation)) := by
  apply Finsupp.ext
  intro leaf
  rw [distribution, distributionFrom_enumerate_apply]
  simp only [List.nil_append]
  exact (distribution_compile_enumerate_applyDDC converter behavior observation leaf).symm

/-- Every finite outer observation factors exactly through DDC
precomposition on every cumulative random system. -/
theorem distribution_applyDDC
    (converter : RandomSystems.Ambient.DDC A B) (behavior : RandomSystem B)
    (observation : Observation A R) :
    distribution (RandomSystem.applyDDC converter behavior) observation =
      distribution behavior (DDC.compile converter observation) := by
  calc
    distribution (RandomSystem.applyDDC converter behavior) observation =
        distribution (RandomSystem.applyDDC converter behavior)
          (map Leaf.result (enumerate observation)) := by
      rw [map_result_enumerate]
    _ = Distribution.fTransform Leaf.result
          (distribution (RandomSystem.applyDDC converter behavior)
            (enumerate observation)) :=
      distribution_map _ _ _
    _ = Distribution.fTransform Leaf.result
          (distribution behavior
            (DDC.compile converter (enumerate observation))) := by
      rw [distribution_enumerate_applyDDC]
    _ = distribution behavior
          (map Leaf.result
            (DDC.compile converter (enumerate observation))) := by
      rw [distribution_map]
    _ = distribution behavior
          (DDC.compile converter
            (map Leaf.result (enumerate observation))) := by
      rw [DDC.compile_map]
    _ = distribution behavior (DDC.compile converter observation) := by
      rw [map_result_enumerate]

/-- Exact functional relabeling of a transcript matcher. -/
theorem evaluateFrom_accepts_mapTranscript
    {C D : Interface.{u, v}} (equivalence : C.Equiv D)
    (system : DDS C) (prior : List C.query)
    (target : RandomSystem.Internal.Core.Transcript C) :
    evaluateFrom
        (accepts (RandomSystem.Internal.Router.mapTranscript equivalence target))
        (RandomSystems.Ambient.DDS.relabel equivalence system)
        (prior.map equivalence.queries) =
      evaluateFrom (accepts target) system prior := by
  classical
  induction target generalizing prior with
  | nil => rfl
  | cons first remaining inductionHypothesis =>
      rcases first with ⟨query, expected⟩
      rw [RandomSystem.Internal.Router.mapTranscript]
      simp only [List.map_cons, Interface.Equiv.innerReply_apply]
      rw [accepts, afterTranscript_cons, evaluateFrom_query,
        RandomSystems.Ambient.DDS.innerReplyAt_relabel]
      rw [accepts, afterTranscript_cons, evaluateFrom_query]
      by_cases equal : Attachment.innerReplyAt system prior query = expected
      · rw [if_pos equal]
        have mappedEqual :
            (Attachment.innerReplyAt system prior query).map
                (equivalence.answers query) =
              expected.map (equivalence.answers query) := by rw [equal]
        rw [if_pos mappedEqual]
        simpa [accepts, RandomSystem.Internal.Router.mapTranscript,
          List.map_append] using
          inductionHypothesis (prior ++ [query])
      · rw [if_neg equal]
        have mappedDifferent :
            (Attachment.innerReplyAt system prior query).map
                (equivalence.answers query) ≠
              expected.map (equivalence.answers query) := by
          intro mappedEqual
          exact equal (Option.map_injective
            (equivalence.answers query).injective
            mappedEqual)
        rw [if_neg mappedDifferent]
        rfl

theorem evaluate_accepts_mapTranscript
    {C D : Interface.{u, v}} (equivalence : C.Equiv D)
    (system : DDS C) (target : RandomSystem.Internal.Core.Transcript C) :
    evaluate (accepts (RandomSystem.Internal.Router.mapTranscript equivalence target))
        (RandomSystems.Ambient.DDS.relabel equivalence system) =
      evaluate (accepts target) system :=
  evaluateFrom_accepts_mapTranscript equivalence system [] target

end

end RandomSystem.Internal.Observation

namespace RandomSystem

noncomputable section

open RandomSystems.Ambient
open RandomSystem.Internal

variable {A B C : Interface.{u, v}}

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), says the identity converter
“induces the identity function Φ → Φ”. -/
@[simp]
theorem applyDDC_forwarding_eq (behavior : RandomSystem A) :
    applyDDC (RandomSystems.Ambient.DDC.forwarding A) behavior = behavior := by
  apply RandomSystem.ext
  intro transcript
  calc
    (applyDDC (RandomSystems.Ambient.DDC.forwarding A) behavior).mass
        transcript =
        Observation.distribution behavior
          (RandomSystem.Internal.DDC.compile
            (RandomSystems.Ambient.DDC.forwarding A)
            (Observation.accepts transcript)) true := rfl
    _ = Observation.distribution behavior
        (Observation.accepts transcript) true := by
      exact congrArg (fun law => law true)
        (Observation.distribution_eq_of_evaluate_eq behavior
          (RandomSystem.Internal.DDC.compile
            (RandomSystems.Ambient.DDC.forwarding A)
            (Observation.accepts transcript))
          (Observation.accepts transcript)
          (fun system =>
            RandomSystem.Internal.DDC.Correctness.evaluate_compile_forwarding
              (Observation.accepts transcript) system))
    _ = behavior.mass transcript :=
      Observation.distribution_accepts_true behavior transcript

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), requires
“(β ◦ α)ⁱ R = βⁱ (αⁱ R)”. -/
theorem applyDDC_serial_eq (outer : RandomSystems.Ambient.DDC A B)
    (inner : RandomSystems.Ambient.DDC B C) (behavior : RandomSystem C) :
    applyDDC (RandomSystems.Ambient.DDC.serial outer inner) behavior =
      applyDDC outer (applyDDC inner behavior) := by
  apply RandomSystem.ext
  intro transcript
  calc
    (applyDDC (RandomSystems.Ambient.DDC.serial outer inner) behavior).mass
        transcript =
        Observation.distribution behavior
          (RandomSystem.Internal.DDC.compile
            (RandomSystems.Ambient.DDC.serial outer inner)
            (Observation.accepts transcript)) true := rfl
    _ = Observation.distribution behavior
        (RandomSystem.Internal.DDC.compile inner
          (RandomSystem.Internal.DDC.compile outer
            (Observation.accepts transcript))) true := by
      exact congrArg (fun law => law true)
        (Observation.distribution_eq_of_evaluate_eq behavior _ _
          (fun system =>
            RandomSystem.Internal.DDC.Correctness.evaluate_compile_serial
              outer inner (Observation.accepts transcript) system))
    _ = Observation.distribution (applyDDC inner behavior)
        (RandomSystem.Internal.DDC.compile outer
          (Observation.accepts transcript)) true := by
      rw [Observation.distribution_applyDDC]
    _ = (applyDDC outer (applyDDC inner behavior)).mass transcript := rfl

/-- The action of the DDC induced by an interface equivalence is exactly
relabeling of cumulative transcript masses. -/
theorem Internal.Router.applyDDC_toDDC_relabels (equivalence : A.Equiv B)
    (behavior : RandomSystem A) :
    Internal.Router.Relabeled equivalence behavior
      (applyDDC equivalence.toDDC behavior) := by
  intro transcript
  rw [applyDDC_mass]
  calc
    Observation.distribution behavior
        (RandomSystem.Internal.DDC.compile equivalence.toDDC
          (Observation.accepts
            (Internal.Router.mapTranscript equivalence transcript))) true =
        Observation.distribution behavior
          (Observation.accepts transcript) true := by
      exact congrArg (fun law => law true)
        (Observation.distribution_eq_of_evaluate_eq behavior _ _
          (fun system => by
            calc
              Observation.evaluate
                  (RandomSystem.Internal.DDC.compile equivalence.toDDC
                    (Observation.accepts
                      (Internal.Router.mapTranscript equivalence transcript))) system =
                  Observation.evaluate
                    (Observation.accepts
                      (Internal.Router.mapTranscript equivalence transcript))
                    (RandomSystems.Ambient.applySystem
                      equivalence.toDDC system) :=
                RandomSystem.Internal.DDC.Correctness.evaluate_compile
                  equivalence.toDDC _ system
              _ = Observation.evaluate
                    (Observation.accepts
                      (Internal.Router.mapTranscript equivalence transcript))
                    (RandomSystems.Ambient.DDS.relabel equivalence system) := by
                rw [RandomSystems.Ambient.DDC.applySystem_toDDC_eq]
              _ = Observation.evaluate (Observation.accepts transcript)
                    system :=
                Observation.evaluate_accepts_mapTranscript
                  equivalence system transcript))
    _ = behavior.mass transcript :=
      Observation.distribution_accepts_true behavior transcript

end

end RandomSystem

namespace RandomSystem

open RandomSystem.Internal
open RandomSystem.Internal.Core

variable {A : Interface.{u, v}}

/-- Cumulative interpretation commutes with deterministic converter
attachment. -/
@[simp]
theorem applyDDC_ofPDS_eq {B : Interface.{w, z}}
    (converter : RandomSystems.Ambient.DDC A B)
    (system : PDS B) :
    RandomSystem.applyDDC converter
        (PDS.toRandomSystem system) =
      PDS.toRandomSystem
        (PDS.apply converter system) := by
  apply RandomSystem.ext
  intro transcript
  rw [RandomSystem.applyDDC_mass,
    PDS.toRandomSystem_mass, RandomSystem.Internal.distribution_toRandomSystem,
    Distribution.fTransform_apply_eq_mass]
  unfold PDS.cylinderMass
  change system.1.mass (fun deterministicSystem =>
      Observation.evaluate
        (RandomSystem.Internal.DDC.compile converter
          (Observation.accepts transcript)) deterministicSystem = true) =
    (Distribution.fTransform
      (RandomSystems.Ambient.applySystem converter) system.1).mass
        (fun deterministicSystem =>
          RandomSystem.Internal.Core.Agrees deterministicSystem transcript)
  rw [Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro deterministicSystem
  rw [RandomSystem.Internal.DDC.Correctness.evaluate_compile]
  exact RandomSystems.Ambient.RandomSystem.Internal.evaluate_accepts_eq_true_iff
    (RandomSystems.Ambient.applySystem converter deterministicSystem) transcript


namespace Internal

/-- Direct converter attachment is non-expanding for the internal finite-tree
presentation of the distance. -/
theorem treeAdvantage_applyDDC_le {B : Interface.{w, z}}
    (converter : RandomSystems.Ambient.DDC A B)
    (left right : RandomSystem B) :
    treeAdvantage (RandomSystem.applyDDC converter left)
        (RandomSystem.applyDDC converter right) ≤
      treeAdvantage left right := by
  apply RandomSystem.Internal.Metric.observationDistance_map_le
    (law := treeLaw) (law' := treeLaw)
    (mapResource := RandomSystem.applyDDC converter)
    (mapTest := RandomSystem.Internal.DDC.compile converter)
  intro behavior observation
  apply Subtype.ext
  exact Observation.distribution_applyDDC converter behavior observation

end Internal

/-- Data processing for the public existing-DDE advantage follows from exact
finite-observation factorization. -/
theorem advantage_applyDDC_le {B : Interface.{w, z}}
    (converter : RandomSystems.Ambient.DDC A B)
    (left right : RandomSystem B) :
    advantage (RandomSystem.applyDDC converter left)
        (RandomSystem.applyDDC converter right) ≤
      advantage left right := by
  rw [Internal.advantage_eq_treeAdvantage,
    Internal.advantage_eq_treeAdvantage]
  exact Internal.treeAdvantage_applyDDC_le converter left right



/-- Maurer--Renner 2016, Definition 2 (printed p. 11), says: “A metric d on Φ
is called non-expanding if d(αR, αS) ≤ d(R, S).” -/
theorem edist_applyDDC_le {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (left right : RandomSystem B) :
    edist (applyDDC converter left) (applyDDC converter right) ≤
      edist left right := by
  rw [edist_eq_ofReal_advantage, edist_eq_ofReal_advantage]
  exact ENNReal.ofReal_le_ofReal
    (advantage_applyDDC_le converter left right)

end RandomSystem

namespace DDC

open CategoryTheory

local instance : LargeCategory Interface := Interface.ddcCategory

/-- Categorical DDC morphisms act on cumulative random systems by attachment. -/
noncomputable scoped instance homAction
    {A B : Interface.{u, v}} :
    HSMul (A ⟶ B) (RandomSystem B) (RandomSystem A) where
  hSMul converter system := RandomSystem.applyDDC converter system

/-- Categorical DDC morphisms act on normalized PDSs by attachment. -/
noncomputable scoped instance homActionPDS
    {A B : Interface.{u, v}} :
    HSMul (A ⟶ B) (PDS B) (PDS A) where
  hSMul converter system := PDS.apply converter system

/-- The categorical action of a bundled DDC is its PDS attachment. -/
theorem asHom_smul_pds_eq_apply
    {A B : Interface.{u, v}}
    (converter : DDC A B) (system : PDS B) :
    (DDC.asHom converter • system : PDS A) =
      PDS.apply converter system :=
  rfl

/-- Serial composition acts on normalized PDSs by successive attachment. -/
theorem comp_smul_pds
    {A B C : Interface.{u, v}}
    (outer : A ⟶ B) (inner : B ⟶ C) (system : PDS C) :
    ((outer ≫ inner) • system : PDS A) =
      outer • (inner • system) :=
  PDS.apply_serial_eq outer inner system

/-- Cumulative interpretation commutes with the categorical PDS action. -/
theorem smul_toRandomSystem_pds
    {A B : Interface.{u, v}}
    (converter : A ⟶ B) (system : PDS B) :
    converter • PDS.toRandomSystem system =
      PDS.toRandomSystem (converter • system) :=
  RandomSystem.applyDDC_ofPDS_eq converter system

/-- Serial composition acts by successive converter attachment. -/
@[simp]
theorem comp_smul
    {A B C : Interface.{u, v}}
    (outer : A ⟶ B) (inner : B ⟶ C) (system : RandomSystem C) :
    ((outer ≫ inner) • system : RandomSystem A) =
      outer • (inner • system) := by
  exact RandomSystem.applyDDC_serial_eq outer inner system

end DDC

end

end RandomSystems.Ambient

namespace RandomSystems.DomainFilter

open Ambient
open scoped Ambient.DDC

universe u v

/-- A domain filter acts on a cumulative random system through its canonical
deterministic converter. -/
noncomputable instance instHSMulRandomSystem
    {X : Type u} {Y : Type v} :
    HSMul (DomainFilter X)
      (RandomSystem (Interface.single X Y))
      (RandomSystem (Interface.single X Y)) where
  hSMul restriction system :=
    RandomSystem.applyDDC (restriction.toDDC (Y := Y)) system

/-- Domain-filter attachment normalizes to the action of its canonical
deterministic converter morphism. -/
@[rs_normalization]
theorem smul_randomSystem_eq
    {X : Type u} {Y : Type v}
    (restriction : DomainFilter X)
    (system : RandomSystem (Interface.single X Y)) :
    restriction • system =
      DDC.asHom (restriction.toDDC (Y := Y)) • system :=
  rfl

end RandomSystems.DomainFilter
