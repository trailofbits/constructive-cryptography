/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Serial
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Interface relabeling

An interface equivalence relabels queries and the answer fibre selected by each
query.  This module proves that the induced relabeling of DDC histories,
responses, converters, and attached DDSs preserves the underlying functions.

Jost, Definition 2.2.1 (printed p. 16), encodes each interface address “as
part of the inputs.”  Relabeling is a type-safe change of those addresses; it
is a Lean structural theorem, not an additional converter axiom in Jost or
Maurer--Renner 2016. Serial naturality follows from the definitions of DDC
relabeling and serial composition.
-/

namespace RandomSystems.Ambient

universe u v w z

open DDC.Internal

namespace DDC

open Internal

namespace Internal

/-- Relabel a possibly rejected outer reply into the answer fibre selected by
the relabelled outer history. -/
def relabelOuterReply {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) :
    Option (A.answer history.lastOuter) ≃
      Option (C.answer (DDC.History.relabel outer inner history).lastOuter) :=
  (outer.answers history.lastOuter).optionCongr.trans
    (_root_.Equiv.cast (congrArg
      (fun query => Option (C.answer query))
      (DDC.History.lastOuter_relabel outer inner history).symm))

/-- Relabel a response at the corresponding complete received history. -/
def relabelResponse {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) :
    DDC.Response history ≃
      DDC.Response (DDC.History.relabel outer inner history) :=
  _root_.Equiv.sumCongr inner.queries
    (relabelOuterReply outer inner history)

@[simp]
theorem relabelResponse_inner {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) (query : B.query) :
    relabelResponse outer inner history (Sum.inl query) =
      Sum.inl (inner.queries query) := by
  rfl

@[simp]
theorem relabelResponse_outer {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B)
    (reply : Option (A.answer history.lastOuter)) :
    relabelResponse outer inner history (Sum.inr reply) =
      Sum.inr (relabelOuterReply outer inner history reply) := by
  rfl

/-- The response equivalence at an arbitrary target history. -/
private def relabelResponseAt {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D) :
    DDC.Response
        ((DDC.History.relabelEquiv outer inner).symm targetHistory) ≃
      DDC.Response targetHistory :=
  let histories := DDC.History.relabelEquiv outer inner
  let sourceHistory := histories.symm targetHistory
  (relabelResponse outer inner sourceHistory).trans
    (_root_.Equiv.cast (congrArg (fun history => DDC.Response history)
      (histories.apply_symm_apply targetHistory)))

private theorem cast_converterResponse_inner
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : DDC.History A B} (equal : left = right)
    (query : B.query) :
    cast (congrArg (fun history => DDC.Response history) equal)
        (Sum.inl query) =
      (Sum.inl query : DDC.Response right) := by
  cases equal
  rfl

private theorem cast_converterResponse_outer
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : DDC.History A B} (equal : left = right)
    (reply : Option (A.answer left.lastOuter)) :
    cast (congrArg (fun history => DDC.Response history) equal)
        (Sum.inr reply) =
      Sum.inr (cast (congrArg
        (fun history => Option (A.answer history.lastOuter)) equal) reply) := by
  cases equal
  rfl

private def relabelRaw {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) : DDC.Raw C D :=
  fun targetHistory =>
    let histories := DDC.History.relabelEquiv outer inner
    let sourceHistory := histories.symm targetHistory
    Part.map (relabelResponseAt outer inner targetHistory)
      (converter sourceHistory)

private theorem mem_relabelRaw_iff {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) (targetHistory : DDC.History C D)
    (targetResponse : DDC.Response targetHistory) :
    targetResponse ∈ relabelRaw outer inner converter targetHistory ↔
      ∃ sourceResponse ∈ converter
          ((DDC.History.relabelEquiv outer inner).symm targetHistory),
        relabelResponseAt outer inner targetHistory sourceResponse =
          targetResponse := by
  rw [relabelRaw, Part.mem_map_iff]

private theorem mem_relabelRaw_iff_symm {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) (targetHistory : DDC.History C D)
    (targetResponse : DDC.Response targetHistory) :
    targetResponse ∈ relabelRaw outer inner converter targetHistory ↔
      (relabelResponseAt outer inner targetHistory).symm targetResponse ∈
        converter
          ((DDC.History.relabelEquiv outer inner).symm targetHistory) := by
  rw [mem_relabelRaw_iff]
  constructor
  · rintro ⟨sourceResponse, responds, equal⟩
    have sourceEqual : sourceResponse =
        (relabelResponseAt outer inner targetHistory).symm targetResponse := by
      apply (relabelResponseAt outer inner targetHistory).injective
      rw [equal, (relabelResponseAt outer inner targetHistory).apply_symm_apply]
    exact sourceEqual ▸ responds
  · intro responds
    exact ⟨(relabelResponseAt outer inner targetHistory).symm targetResponse,
      responds,
      (relabelResponseAt outer inner targetHistory).apply_symm_apply
        targetResponse⟩

@[simp]
private theorem relabelResponseAt_symm_inner
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D) (query : D.query) :
    (relabelResponseAt outer inner targetHistory).symm (Sum.inl query) =
      Sum.inl (inner.queries.symm query) := by
  apply (relabelResponseAt outer inner targetHistory).injective
  rw [(relabelResponseAt outer inner targetHistory).apply_symm_apply]
  unfold relabelResponseAt
  change Sum.inl query =
    cast (congrArg (fun history => DDC.Response history)
      ((DDC.History.relabelEquiv outer inner).apply_symm_apply
        targetHistory))
      (Sum.inl (inner.queries (inner.queries.symm query)))
  rw [inner.queries.apply_symm_apply]
  exact (cast_converterResponse_inner (A := C) (B := D)
    ((DDC.History.relabelEquiv outer inner).apply_symm_apply
      targetHistory) query).symm

@[simp]
private theorem relabelResponseAt_inner
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D) (query : B.query) :
    relabelResponseAt outer inner targetHistory (Sum.inl query) =
      Sum.inl (inner.queries query) := by
  unfold relabelResponseAt
  change cast (congrArg (fun history => DDC.Response history)
      ((DDC.History.relabelEquiv outer inner).apply_symm_apply
        targetHistory))
      (Sum.inl (inner.queries query)) = Sum.inl (inner.queries query)
  exact cast_converterResponse_inner (A := C) (B := D)
    ((DDC.History.relabelEquiv outer inner).apply_symm_apply
      targetHistory) (inner.queries query)

private theorem exists_relabelResponseAt_outer
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D)
    (reply : Option (A.answer
      ((DDC.History.relabelEquiv outer inner).symm
        targetHistory).lastOuter)) :
    ∃ targetReply : Option (C.answer targetHistory.lastOuter),
      relabelResponseAt outer inner targetHistory (Sum.inr reply) =
        Sum.inr targetReply := by
  cases equal : relabelResponseAt outer inner targetHistory
      (Sum.inr reply) with
  | inl query =>
      have inverseEqual := congrArg
        (relabelResponseAt outer inner targetHistory).symm equal
      rw [(relabelResponseAt outer inner targetHistory).symm_apply_apply,
        relabelResponseAt_symm_inner] at inverseEqual
      cases inverseEqual
  | inr targetReply => exact ⟨targetReply, rfl⟩

private theorem exists_relabelResponseAt_symm_outer
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (targetHistory : DDC.History C D)
    (reply : Option (C.answer targetHistory.lastOuter)) :
    ∃ sourceReply : Option (A.answer
        ((DDC.History.relabelEquiv outer inner).symm
          targetHistory).lastOuter),
      (relabelResponseAt outer inner targetHistory).symm (Sum.inr reply) =
        Sum.inr sourceReply := by
  cases equal : (relabelResponseAt outer inner targetHistory).symm
      (Sum.inr reply) with
  | inl query =>
      have forwardEqual := congrArg
        (relabelResponseAt outer inner targetHistory) equal
      rw [(relabelResponseAt outer inner targetHistory).apply_symm_apply,
        relabelResponseAt_inner] at forwardEqual
      cases forwardEqual
  | inr sourceReply => exact ⟨sourceReply, rfl⟩

private theorem relabelEquiv_symm_singleton
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (query : C.query) :
    (DDC.History.relabelEquiv outer inner).symm
        (DDC.History.singleton (B := D) query) =
      DDC.History.singleton (B := B) (outer.queries.symm query) := by
  apply (DDC.History.relabelEquiv outer inner).injective
  rw [(DDC.History.relabelEquiv outer inner).apply_symm_apply]
  change DDC.History.singleton (B := D) query =
    DDC.History.relabel outer inner
      (DDC.History.singleton (B := B) (outer.queries.symm query))
  rw [DDC.History.relabel_singleton]
  rw [outer.queries.apply_symm_apply]

private theorem relabelEquiv_symm_snocOuter
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History C D) (query : C.query) :
    (DDC.History.relabelEquiv outer inner).symm
        (history.snocOuter query) =
      ((DDC.History.relabelEquiv outer inner).symm history).snocOuter
        (outer.queries.symm query) := by
  apply (DDC.History.relabelEquiv outer inner).injective
  rw [(DDC.History.relabelEquiv outer inner).apply_symm_apply]
  change history.snocOuter query =
    DDC.History.relabel outer inner
      (((DDC.History.relabelEquiv outer inner).symm history).snocOuter
        (outer.queries.symm query))
  rw [DDC.History.relabel_snocOuter]
  have historyEqual :=
    (DDC.History.relabelEquiv outer inner).apply_symm_apply history
  change DDC.History.relabel outer inner
      ((DDC.History.relabelEquiv outer inner).symm history) = history
    at historyEqual
  rw [historyEqual, outer.queries.apply_symm_apply]

private theorem relabelEquiv_symm_snocInner
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History C D) (reply : InnerReply D) :
    (DDC.History.relabelEquiv outer inner).symm
        (history.snocInner reply.1 reply.2) =
      let sourceReply := inner.innerReply.symm reply
      ((DDC.History.relabelEquiv outer inner).symm history).snocInner
        sourceReply.1 sourceReply.2 := by
  let sourceReply := inner.innerReply.symm reply
  apply (DDC.History.relabelEquiv outer inner).injective
  rw [(DDC.History.relabelEquiv outer inner).apply_symm_apply]
  change history.snocInner reply.1 reply.2 =
    DDC.History.relabel outer inner
      (((DDC.History.relabelEquiv outer inner).symm history).snocInner
        sourceReply.1 sourceReply.2)
  rw [DDC.History.relabel_snocInner]
  have replyEqual : inner.innerReply sourceReply = reply :=
    inner.innerReply.apply_symm_apply reply
  have baseEqual :=
    (DDC.History.relabelEquiv outer inner).apply_symm_apply history
  change DDC.History.relabel outer inner
      ((DDC.History.relabelEquiv outer inner).symm history) = history
    at baseEqual
  rw [baseEqual]
  change history.snocInner reply.1 reply.2 =
    history.snocInner (inner.innerReply sourceReply).1
      (inner.innerReply sourceReply).2
  exact (congrArg
    (fun packed : InnerReply D =>
      history.snocInner packed.1 packed.2) replyEqual).symm

private theorem converter_mem_transport
    {A : Interface.{u, v}} {B : Interface.{w, z}} (converter : DDC A B)
    {left right : DDC.History A B} (equal : left = right)
    {response : DDC.Response right} (responds : response ∈ converter right) :
    cast (congrArg (fun history => DDC.Response history) equal.symm)
        response ∈ converter left := by
  cases equal
  exact responds

private theorem exists_cast_converterResponse_outer
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : DDC.History A B} (equal : left = right)
    (reply : Option (A.answer right.lastOuter)) :
    ∃ sourceReply : Option (A.answer left.lastOuter),
      cast (congrArg (fun history => DDC.Response history) equal.symm)
          (Sum.inr reply) =
        Sum.inr sourceReply := by
  cases equal
  exact ⟨reply, rfl⟩

private theorem admissible_relabel_of_admissible
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    {history : DDC.History A B}
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    DDC.Raw.Admissible (relabelRaw outer inner converter)
      (DDC.History.relabel outer inner history) := by
  induction admissible with
  | start query =>
      simpa using DDC.Raw.Admissible.start
        (raw := relabelRaw outer inner converter) (outer.queries query)
  | @afterInner history query prior responds reply inductionHypothesis =>
      let targetHistory := DDC.History.relabel outer inner history
      let sourceHistory :=
        (DDC.History.relabelEquiv outer inner).symm targetHistory
      have roundtrip : sourceHistory = history :=
        (DDC.History.relabelEquiv outer inner).symm_apply_apply history
      let transported : DDC.Response sourceHistory :=
        cast (congrArg (fun selected => DDC.Response selected)
          roundtrip.symm) (Sum.inl query)
      have transportedEqual : transported = Sum.inl query := by
        exact cast_converterResponse_inner (A := A) (B := B)
          roundtrip.symm query
      have transportedResponds : transported ∈ converter sourceHistory :=
        converter_mem_transport converter roundtrip responds
      have targetResponds : Sum.inl (inner.queries query) ∈
          relabelRaw outer inner converter targetHistory := by
        apply (mem_relabelRaw_iff_symm outer inner converter targetHistory
          (Sum.inl (inner.queries query))).mpr
        rw [relabelResponseAt_symm_inner,
          inner.queries.symm_apply_apply, ← transportedEqual]
        exact transportedResponds
      rw [DDC.History.relabel_snocInner]
      exact .afterInner inductionHypothesis targetResponds
        (reply.map (inner.answers query))
  | @afterOuter history prior reply responds query inductionHypothesis =>
      let targetHistory := DDC.History.relabel outer inner history
      let sourceHistory :=
        (DDC.History.relabelEquiv outer inner).symm targetHistory
      have roundtrip : sourceHistory = history :=
        (DDC.History.relabelEquiv outer inner).symm_apply_apply history
      let transported : DDC.Response sourceHistory :=
        cast (congrArg (fun selected => DDC.Response selected)
          roundtrip.symm) (Sum.inr reply)
      obtain ⟨sourceReply, transportedEqual⟩ :=
        exists_cast_converterResponse_outer roundtrip reply
      have transportedResponds : transported ∈ converter sourceHistory :=
        converter_mem_transport converter roundtrip responds
      obtain ⟨targetReply, targetEqual⟩ :=
        exists_relabelResponseAt_outer outer inner targetHistory sourceReply
      have targetResponds : Sum.inr targetReply ∈
          relabelRaw outer inner converter targetHistory := by
        apply (mem_relabelRaw_iff_symm outer inner converter targetHistory
          (Sum.inr targetReply)).mpr
        rw [← targetEqual,
          (relabelResponseAt outer inner targetHistory).symm_apply_apply,
          ← transportedEqual]
        exact transportedResponds
      rw [DDC.History.relabel_snocOuter]
      exact .afterOuter inductionHypothesis targetResponds
        (outer.queries query)

private theorem admissible_of_admissible_relabel
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    {history : DDC.History C D}
    (admissible : DDC.Raw.Admissible
      (relabelRaw outer inner converter) history) :
    DDC.Raw.Admissible converter.toFun
      ((DDC.History.relabelEquiv outer inner).symm history) := by
  induction admissible with
  | start query =>
      rw [relabelEquiv_symm_singleton]
      exact .start (outer.queries.symm query)
  | @afterInner history query prior responds reply inductionHypothesis =>
      have sourceResponds : Sum.inl (inner.queries.symm query) ∈
          converter
            ((DDC.History.relabelEquiv outer inner).symm history) := by
        simpa only [relabelResponseAt_symm_inner] using
          (mem_relabelRaw_iff_symm outer inner converter history
            (Sum.inl query)).mp responds
      let sourceReply := inner.innerReply.symm
        (⟨query, reply⟩ : InnerReply D)
      change DDC.Raw.Admissible converter.toFun
        ((DDC.History.relabelEquiv outer inner).symm
          (history.snocInner (⟨query, reply⟩ : InnerReply D).1
            (⟨query, reply⟩ : InnerReply D).2))
      rw [relabelEquiv_symm_snocInner outer inner history
        (⟨query, reply⟩ : InnerReply D)]
      exact .afterInner inductionHypothesis sourceResponds sourceReply.2
  | @afterOuter history prior reply responds query inductionHypothesis =>
      obtain ⟨sourceReply, sourceEqual⟩ :=
        exists_relabelResponseAt_symm_outer outer inner history reply
      have sourceResponds : Sum.inr sourceReply ∈
          converter
            ((DDC.History.relabelEquiv outer inner).symm history) := by
        have mapped := (mem_relabelRaw_iff_symm outer inner converter history
          (Sum.inr reply)).mp responds
        rw [sourceEqual] at mapped
        exact mapped
      rw [relabelEquiv_symm_snocOuter]
      exact .afterOuter inductionHypothesis sourceResponds
        (outer.queries.symm query)

private theorem admissible_relabelRaw_iff
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    (history : DDC.History C D) :
    DDC.Raw.Admissible (relabelRaw outer inner converter) history ↔
      DDC.Raw.Admissible converter.toFun
        ((DDC.History.relabelEquiv outer inner).symm history) := by
  constructor
  · exact admissible_of_admissible_relabel outer inner converter
  · intro admissible
    have mapped := admissible_relabel_of_admissible outer inner converter
      admissible
    exact (DDC.History.relabelEquiv outer inner).apply_symm_apply history ▸
      mapped

private theorem innerContinuation_relabelRaw
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    {after before : DDC.History C D}
    (continues : DDC.Raw.InnerContinuation
      (relabelRaw outer inner converter) after before) :
    DDC.Raw.InnerContinuation converter.toFun
      ((DDC.History.relabelEquiv outer inner).symm after)
      ((DDC.History.relabelEquiv outer inner).symm before) := by
  rcases continues with ⟨query, reply, responds, rfl⟩
  let sourceReply := inner.innerReply.symm
    (⟨query, reply⟩ : InnerReply D)
  have sourceResponds : Sum.inl sourceReply.1 ∈
      converter
        ((DDC.History.relabelEquiv outer inner).symm before) := by
    have mapped := (mem_relabelRaw_iff_symm outer inner converter before
      (Sum.inl query)).mp responds
    simpa [sourceReply] using mapped
  exact ⟨sourceReply.1, sourceReply.2, sourceResponds,
    relabelEquiv_symm_snocInner outer inner before
      (⟨query, reply⟩ : InnerReply D)⟩

private theorem relabelRaw_complete
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B) :
    DDC.Raw.Complete (relabelRaw outer inner converter) := by
  intro history admissible
  change (converter
    ((DDC.History.relabelEquiv outer inner).symm history)).Dom
  apply (converter.exactDomain _).mpr
  exact (admissible_relabelRaw_iff outer inner converter history).mp
    admissible

private theorem relabelRaw_branchFinite
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B) :
    DDC.Raw.BranchFinite (relabelRaw outer inner converter) := by
  apply WellFounded.mono
    (InvImage.wf (DDC.History.relabelEquiv outer inner).symm
      converter.branchFinite)
  intro after before continues
  exact innerContinuation_relabelRaw outer inner converter continues

end Internal

/-- Relabel both interfaces of a query-indexed DDC. -/
noncomputable def relabel
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B) :
    DDC C D :=
  DDC.ofRaw (relabelRaw outer inner converter)
    (relabelRaw_complete outer inner converter)
    (relabelRaw_branchFinite outer inner converter)

namespace Internal

theorem mem_relabel_iff_symm
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    (history : DDC.History C D)
    (response : DDC.Response history) :
    response ∈ relabel outer inner converter history ↔
      (relabelResponseAt outer inner history).symm response ∈
        converter
          ((DDC.History.relabelEquiv outer inner).symm history) := by
  change response ∈ DDC.Raw.canonicalize
      (relabelRaw outer inner converter) history ↔ _
  rw [DDC.Raw.mem_canonicalize_iff, mem_relabelRaw_iff_symm]
  constructor
  · exact And.right
  · intro responds
    exact ⟨(admissible_relabelRaw_iff outer inner converter history).mpr
        ((converter.exactDomain _).mp responds.1),
      responds⟩

end Internal

/-- One complete history together with its dependent converter response. -/
private abbrev BehaviorPoint (A : Interface.{u, v}) (B : Interface.{w, z}) :=
  Σ history : DDC.History A B, DDC.Response history

/-- Relabeling as one equivalence on complete history/response points. -/
private def relabelPoint
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) :
    BehaviorPoint A B ≃ BehaviorPoint C D :=
  _root_.Equiv.sigmaCongr (DDC.History.relabelEquiv outer inner)
    (relabelResponse outer inner)

private theorem cast_relabelResponse_refl
    {A : Interface.{u, v}} {B : Interface.{w, z}} (history : DDC.History A B)
    (response : DDC.Response history) :
    cast (congrArg (fun selected => DDC.Response selected)
        (DDC.History.relabel_refl history))
      (relabelResponse (.refl A) (.refl B) history response) = response := by
  cases response with
  | inl query =>
      exact cast_converterResponse_inner (A := A) (B := B)
        (DDC.History.relabel_refl history) query
  | inr reply =>
      let historyEqual := DDC.History.relabel_refl history
      rw [relabelResponse_outer, cast_converterResponse_outer]
      unfold relabelOuterReply
      change Sum.inr (cast _ (cast _ (Option.map id reply))) = Sum.inr reply
      rw [Option.map_id, cast_cast, cast_eq]
      · rfl
      · exact historyEqual

private theorem pack_relabelOuterReply
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B)
    (reply : Option (A.answer history.lastOuter)) :
    (⟨(DDC.History.relabel outer inner history).lastOuter,
        relabelOuterReply outer inner history reply⟩ : InnerReply C) =
      outer.innerReply ⟨history.lastOuter, reply⟩ := by
  apply Sigma.ext (DDC.History.lastOuter_relabel outer inner history)
  unfold relabelOuterReply Interface.Equiv.innerReply
  simp only [_root_.Equiv.trans_apply, _root_.Equiv.optionCongr_apply,
    _root_.Equiv.cast_apply]
  change cast _ (reply.map (outer.answers history.lastOuter)) ≍
    reply.map (outer.answers history.lastOuter)
  exact cast_heq
    (congrArg (fun query => Option (C.answer query))
      (DDC.History.lastOuter_relabel outer inner history).symm)
    (reply.map (outer.answers history.lastOuter))

private theorem innerReply_trans
    {A C E : Interface.{u, v}}
    (first : A.Equiv C) (second : C.Equiv E)
    (reply : InnerReply A) :
    second.innerReply (first.innerReply reply) =
      (first.trans second).innerReply reply := by
  rcases reply with ⟨query, reply⟩
  cases reply <;> rfl

private theorem pack_cast_outerReply
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {left right : DDC.History A B} (equal : left = right)
    (reply : Option (A.answer left.lastOuter)) :
    (⟨right.lastOuter,
        cast (congrArg
          (fun history => Option (A.answer history.lastOuter)) equal) reply⟩ :
      InnerReply A) = ⟨left.lastOuter, reply⟩ := by
  cases equal
  rfl

private theorem reply_eq_of_packed_eq
    {A : Interface.{u, v}} {query : A.query}
    {left right : Option (A.answer query)}
    (equal : (⟨query, left⟩ : InnerReply A) = ⟨query, right⟩) :
    left = right := by
  cases equal
  rfl

@[simp]
private theorem relabelPoint_apply
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B) (response : DDC.Response history) :
    relabelPoint outer inner ⟨history, response⟩ =
      ⟨DDC.History.relabel outer inner history,
        relabelResponse outer inner history response⟩ := by
  rfl

@[simp]
private theorem relabelPoint_refl
    {A : Interface.{u, v}} {B : Interface.{w, z}} (point : BehaviorPoint A B) :
    relabelPoint (.refl A) (.refl B) point = point := by
  rcases point with ⟨history, response⟩
  apply Sigma.ext (DDC.History.relabel_refl history)
  change relabelResponse (.refl A) (.refl B) history response ≍ response
  have transported := cast_heq
    (congrArg (fun selected => DDC.Response selected)
      (DDC.History.relabel_refl history))
    (relabelResponse (.refl A) (.refl B) history response)
  rw [cast_relabelResponse_refl] at transported
  exact transported.symm

private theorem cast_relabelResponse_trans
    {A C E : Interface.{u, v}} {B D F : Interface.{w, z}}
    (firstOuter : A.Equiv C) (firstInner : B.Equiv D)
    (secondOuter : C.Equiv E) (secondInner : D.Equiv F)
    (history : DDC.History A B) (response : DDC.Response history) :
    cast (congrArg (fun selected => DDC.Response selected)
        (DDC.History.relabel_trans firstOuter firstInner
          secondOuter secondInner history))
      (relabelResponse secondOuter secondInner
        (DDC.History.relabel firstOuter firstInner history)
        (relabelResponse firstOuter firstInner history response)) =
      relabelResponse (firstOuter.trans secondOuter)
        (firstInner.trans secondInner) history response := by
  cases response with
  | inl query =>
      exact cast_converterResponse_inner (A := E) (B := F)
        (DDC.History.relabel_trans firstOuter firstInner
          secondOuter secondInner history)
        (secondInner.queries (firstInner.queries query))
  | inr reply =>
      rw [relabelResponse_outer, relabelResponse_outer,
        relabelResponse_outer]
      let firstHistory := DDC.History.relabel firstOuter firstInner history
      let secondHistory :=
        DDC.History.relabel secondOuter secondInner firstHistory
      let composedHistory := DDC.History.relabel
        (firstOuter.trans secondOuter) (firstInner.trans secondInner) history
      let firstReply := relabelOuterReply firstOuter firstInner history reply
      let secondReply := relabelOuterReply secondOuter secondInner
        firstHistory firstReply
      let composedReply := relabelOuterReply (firstOuter.trans secondOuter)
        (firstInner.trans secondInner) history reply
      change cast (congrArg (fun selected => DDC.Response selected)
          (DDC.History.relabel_trans firstOuter firstInner
            secondOuter secondInner history))
          (Sum.inr secondReply) = Sum.inr composedReply
      rw [cast_converterResponse_outer (A := E) (B := F)
        (DDC.History.relabel_trans firstOuter firstInner
          secondOuter secondInner history) secondReply]
      have packedEqual :
          (⟨composedHistory.lastOuter,
              cast (congrArg
                (fun selected => Option (E.answer selected.lastOuter))
                (DDC.History.relabel_trans firstOuter firstInner
                  secondOuter secondInner history)) secondReply⟩ : InnerReply E) =
            ⟨composedHistory.lastOuter, composedReply⟩ := by
        calc
          _ = (⟨secondHistory.lastOuter, secondReply⟩ : InnerReply E) :=
            pack_cast_outerReply
              (DDC.History.relabel_trans firstOuter firstInner
                secondOuter secondInner history) secondReply
          _ = secondOuter.innerReply ⟨firstHistory.lastOuter, firstReply⟩ :=
            pack_relabelOuterReply secondOuter secondInner firstHistory firstReply
          _ = secondOuter.innerReply
                (firstOuter.innerReply ⟨history.lastOuter, reply⟩) := by
            rw [pack_relabelOuterReply firstOuter firstInner history reply]
          _ = (firstOuter.trans secondOuter).innerReply
                ⟨history.lastOuter, reply⟩ :=
            innerReply_trans firstOuter secondOuter ⟨history.lastOuter, reply⟩
          _ = (⟨composedHistory.lastOuter, composedReply⟩ : InnerReply E) :=
            (pack_relabelOuterReply (firstOuter.trans secondOuter)
              (firstInner.trans secondInner) history reply).symm
      exact congrArg Sum.inr (reply_eq_of_packed_eq packedEqual)

private theorem relabelPoint_trans
    {A C E : Interface.{u, v}} {B D F : Interface.{w, z}}
    (firstOuter : A.Equiv C) (firstInner : B.Equiv D)
    (secondOuter : C.Equiv E) (secondInner : D.Equiv F)
    (point : BehaviorPoint A B) :
    relabelPoint secondOuter secondInner
        (relabelPoint firstOuter firstInner point) =
      relabelPoint (firstOuter.trans secondOuter)
        (firstInner.trans secondInner) point := by
  rcases point with ⟨history, response⟩
  apply Sigma.ext (DDC.History.relabel_trans firstOuter firstInner
    secondOuter secondInner history)
  change relabelResponse secondOuter secondInner
      (DDC.History.relabel firstOuter firstInner history)
        (relabelResponse firstOuter firstInner history response) ≍
    relabelResponse (firstOuter.trans secondOuter)
      (firstInner.trans secondInner) history response
  have transported := cast_heq
    (congrArg (fun selected => DDC.Response selected)
      (DDC.History.relabel_trans firstOuter firstInner
        secondOuter secondInner history))
    (relabelResponse secondOuter secondInner
      (DDC.History.relabel firstOuter firstInner history)
      (relabelResponse firstOuter firstInner history response))
  rw [cast_relabelResponse_trans] at transported
  exact transported.symm

private abbrev HasResponse {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (point : BehaviorPoint A B) : Prop :=
  point.2 ∈ converter point.1

private theorem relabelPoint_symm_apply
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History C D)
    (response : DDC.Response history) :
    (relabelPoint outer inner).symm ⟨history, response⟩ =
      ⟨(DDC.History.relabelEquiv outer inner).symm history,
        (relabelResponseAt outer inner history).symm response⟩ := by
  apply (relabelPoint outer inner).injective
  rw [(relabelPoint outer inner).apply_symm_apply]
  let sourceHistory :=
    (DDC.History.relabelEquiv outer inner).symm history
  let sourceResponse :=
    (relabelResponseAt outer inner history).symm response
  let historyEqual :=
    (DDC.History.relabelEquiv outer inner).apply_symm_apply history
  apply Sigma.ext historyEqual.symm
  change response ≍ relabelResponse outer inner sourceHistory sourceResponse
  have responseEqual : relabelResponseAt outer inner history sourceResponse =
      response := (relabelResponseAt outer inner history).apply_symm_apply response
  unfold relabelResponseAt at responseEqual
  change cast (congrArg (fun selected => DDC.Response selected)
      historyEqual)
      (relabelResponse outer inner sourceHistory sourceResponse) = response
    at responseEqual
  have transported := cast_heq
    (congrArg (fun selected => DDC.Response selected) historyEqual)
    (relabelResponse outer inner sourceHistory sourceResponse)
  rw [responseEqual] at transported
  exact transported

private theorem mem_relabel_iff_point
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    (history : DDC.History C D)
    (response : DDC.Response history) :
    response ∈ relabel outer inner converter history ↔
      HasResponse converter
        ((relabelPoint outer inner).symm ⟨history, response⟩) := by
  rw [mem_relabel_iff_symm outer inner converter history response]
  rw [relabelPoint_symm_apply]

private theorem hasResponse_relabel_iff_point
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) (converter : DDC A B)
    (point : BehaviorPoint C D) :
    HasResponse (relabel outer inner converter) point ↔
      HasResponse converter ((relabelPoint outer inner).symm point) := by
  rcases point with ⟨history, response⟩
  exact mem_relabel_iff_point outer inner converter history response

private theorem relabelPoint_refl_eq
    {A : Interface.{u, v}} {B : Interface.{w, z}} :
    relabelPoint (.refl A) (.refl B) = _root_.Equiv.refl _ := by
  apply _root_.Equiv.ext
  exact relabelPoint_refl

private theorem relabelPoint_trans_eq
    {A C E : Interface.{u, v}} {B D F : Interface.{w, z}}
    (firstOuter : A.Equiv C) (firstInner : B.Equiv D)
    (secondOuter : C.Equiv E) (secondInner : D.Equiv F) :
    (relabelPoint firstOuter firstInner).trans
        (relabelPoint secondOuter secondInner) =
      relabelPoint (firstOuter.trans secondOuter)
        (firstInner.trans secondInner) := by
  apply _root_.Equiv.ext
  exact relabelPoint_trans firstOuter firstInner secondOuter secondInner

@[simp]
theorem relabel_refl
    {A : Interface.{u, v}} {B : Interface.{w, z}} (converter : DDC A B) :
    relabel (.refl A) (.refl B) converter = converter := by
  -- Reduce DDC equality to equality of graph membership.
  apply DDC.ext
  intro history response
  -- Pull membership back through the identity relabeling.
  rw [mem_relabel_iff_point]
  rw [relabelPoint_refl_eq]
  rfl

theorem relabel_trans
    {A C E : Interface.{u, v}} {B D F : Interface.{w, z}}
    (firstOuter : A.Equiv C) (firstInner : B.Equiv D)
    (secondOuter : C.Equiv E) (secondInner : D.Equiv F)
    (converter : DDC A B) :
    relabel secondOuter secondInner
        (relabel firstOuter firstInner converter) =
      relabel (firstOuter.trans secondOuter)
        (firstInner.trans secondInner) converter := by
  -- Reduce DDC equality to equality of graph membership.
  apply DDC.ext
  intro history response
  -- Pull nested relabeling and composed relabeling back to source coordinates.
  rw [mem_relabel_iff_point]
  rw [hasResponse_relabel_iff_point, mem_relabel_iff_point]
  -- Composition of the point equivalences identifies the two source points.
  have pointEqual := congrArg
    (fun equivalence : BehaviorPoint A B ≃ BehaviorPoint E F =>
      equivalence.symm ⟨history, response⟩)
    (relabelPoint_trans_eq firstOuter firstInner secondOuter secondInner)
  have nestedEqual :
      (relabelPoint firstOuter firstInner).symm
          ((relabelPoint secondOuter secondInner).symm ⟨history, response⟩) =
        (relabelPoint (firstOuter.trans secondOuter)
          (firstInner.trans secondInner)).symm ⟨history, response⟩ :=
    pointEqual
  rw [nestedEqual]

end DDC

namespace DDS

private theorem packed_relabel
    {A B : Interface.{u, v}} (equivalence : A.Equiv B)
    (system : DDS A) (history : _root_.RandomSystems.Ambient.History B) :
    (⟨history.last,
        RandomSystems.Ambient.DDS.relabel equivalence system history⟩ :
      InnerReply B) =
      equivalence.innerReply
        ⟨(_root_.RandomSystems.Ambient.History.map equivalence.queries.symm history).last,
          system (_root_.RandomSystems.Ambient.History.map equivalence.queries.symm history)⟩ := by
  classical
  unfold RandomSystems.Ambient.DDS.relabel Interface.Equiv.innerReply
  dsimp only
  apply Sigma.ext
  · change history.last =
      equivalence.queries
        (_root_.RandomSystems.Ambient.History.map equivalence.queries.symm history).last
    simp
  · exact cast_heq _ _

private theorem packed_innerReplyAt
    {A : Interface.{u, v}} (system : DDS A)
    (prior : List A.query) (query : A.query) :
    (⟨query, Attachment.innerReplyAt system prior query⟩ : InnerReply A) =
      ⟨(innerHistory prior query).last,
        system (innerHistory prior query)⟩ := by
  apply Sigma.ext (last_innerHistory prior query).symm
  unfold Attachment.innerReplyAt
  exact cast_heq _ _

private theorem innerReplyAt_relabel
    {A B : Interface.{u, v}} (equivalence : A.Equiv B)
    (system : DDS A) (prior : List A.query) (query : A.query) :
    Attachment.innerReplyAt
        (RandomSystems.Ambient.DDS.relabel equivalence system)
        (prior.map equivalence.queries) (equivalence.queries query) =
      (Attachment.innerReplyAt system prior query).map
        (equivalence.answers query) := by
  classical
  let targetHistory := innerHistory (prior.map equivalence.queries)
    (equivalence.queries query)
  let sourceHistory := _root_.RandomSystems.Ambient.History.map equivalence.queries.symm targetHistory
  have sourceEqual : sourceHistory = innerHistory prior query := by
    apply _root_.RandomSystems.Ambient.History.ext
    simp [sourceHistory, targetHistory, innerHistory,
      _root_.RandomSystems.Ambient.History.map, List.map_append]
  have packedEqual :
      (⟨equivalence.queries query,
          Attachment.innerReplyAt
            (RandomSystems.Ambient.DDS.relabel equivalence system)
            (prior.map equivalence.queries)
            (equivalence.queries query)⟩ : InnerReply B) =
        ⟨equivalence.queries query,
          (Attachment.innerReplyAt system prior query).map
            (equivalence.answers query)⟩ := by
    calc
      _ = (⟨targetHistory.last,
          RandomSystems.Ambient.DDS.relabel equivalence system
            targetHistory⟩ : InnerReply B) :=
        packed_innerReplyAt
          (RandomSystems.Ambient.DDS.relabel equivalence system)
          (prior.map equivalence.queries) (equivalence.queries query)
      _ = equivalence.innerReply
          ⟨sourceHistory.last, system sourceHistory⟩ :=
        packed_relabel equivalence system targetHistory
      _ = equivalence.innerReply
          ⟨(innerHistory prior query).last,
            system (innerHistory prior query)⟩ := by rw [sourceEqual]
      _ = equivalence.innerReply
          ⟨query, Attachment.innerReplyAt system prior query⟩ := by
        rw [packed_innerReplyAt system prior query]
      _ = _ := by rw [Interface.Equiv.innerReply_apply]
  exact DDC.reply_eq_of_packed_eq packedEqual

end DDS

namespace DDC

namespace Internal

private theorem packed_selectReply_relabel
    {A C : Interface.{u, v}} (outer : A.Equiv C)
    (query : A.query) (reply : InnerReply A) :
    (⟨outer.queries query,
        Attachment.selectReply (outer.queries query) (outer.innerReply reply)⟩ :
      InnerReply C) =
      outer.innerReply ⟨query, Attachment.selectReply query reply⟩ := by
  classical
  rcases reply with ⟨replyQuery, reply⟩
  by_cases equal : replyQuery = query
  · subst replyQuery
    rw [Interface.Equiv.innerReply_apply,
      Interface.Equiv.innerReply_apply]
    simp [Attachment.selectReply]
  · have mappedDifferent : outer.queries replyQuery ≠ outer.queries query :=
      fun mappedEqual => equal (outer.queries.injective mappedEqual)
    rw [Interface.Equiv.innerReply_apply,
      Interface.Equiv.innerReply_apply]
    simp [Attachment.selectReply, equal, mappedDifferent]

private theorem history_head_map
    {X Y : Interface.{u, v}} (function : X.query → Y.query)
    (history : _root_.RandomSystems.Ambient.History X) :
    (_root_.RandomSystems.Ambient.History.map function history).head = function history.head := by
  simp [_root_.RandomSystems.Ambient.History.head, _root_.RandomSystems.Ambient.History.map]

private theorem history_tail_map
    {X Y : Interface.{u, v}} (function : X.query → Y.query)
    (history : _root_.RandomSystems.Ambient.History X) :
    (_root_.RandomSystems.Ambient.History.map function history).tail = history.tail.map function := by
  simp [_root_.RandomSystems.Ambient.History.tail, _root_.RandomSystems.Ambient.History.map]

end Internal

end DDC

/-- Relabel a packed converter response without erasing its selected query. -/
private def relabelPackedResponse
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D) :
    Attachment.Response A B ≃ Attachment.Response C D :=
  _root_.Equiv.sumCongr inner.queries outer.innerReply

namespace DDC

namespace Internal

theorem mem_relabel_of_mem
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) (history : DDC.History A B)
    (response : DDC.Response history)
    (responds : response ∈ converter history) :
    relabelResponse outer inner history response ∈
      relabel outer inner converter
        (DDC.History.relabel outer inner history) := by
  rw [mem_relabel_iff_point]
  change HasResponse converter
    ((relabelPoint outer inner).symm
      (relabelPoint outer inner ⟨history, response⟩))
  rw [(relabelPoint outer inner).symm_apply_apply]
  exact responds

private theorem compatibleFrom_relabel
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) (system : DDS B)
    {history : DDC.History A B} {innerPrior : List B.query}
    {remainingOuter : List A.query}
    {inputs : List (ReceivedInput A B)}
    {responses : List (Attachment.Response A B)} {final : InnerReply A}
    (compatible : Attachment.CompatibleFrom converter system history innerPrior
      remainingOuter inputs responses final) :
    Attachment.CompatibleFrom (relabel outer inner converter) (DDS.relabel inner system)
      (DDC.History.relabel outer inner history)
      (innerPrior.map inner.queries) (remainingOuter.map outer.queries)
      (inputs.map (DDC.History.relabelInput outer inner))
      (responses.map (relabelPackedResponse outer inner))
      (outer.innerReply final) := by
  induction compatible with
  | @innerQuery history innerPrior remainingOuter query tailInputs
      tailResponses final responds tail inductionHypothesis =>
      have mappedResponds : Sum.inl (inner.queries query) ∈
          relabel outer inner converter
            (DDC.History.relabel outer inner history) :=
        mem_relabel_of_mem outer inner converter history (Sum.inl query)
          responds
      have mappedTail : Attachment.CompatibleFrom (relabel outer inner converter)
          (DDS.relabel inner system)
          ((DDC.History.relabel outer inner history).snocInner
            (inner.queries query)
            (Attachment.innerReplyAt (DDS.relabel inner system)
              (innerPrior.map inner.queries) (inner.queries query)))
          (innerPrior.map inner.queries ++ [inner.queries query])
          (remainingOuter.map outer.queries)
          (tailInputs.map (DDC.History.relabelInput outer inner))
          (tailResponses.map (relabelPackedResponse outer inner))
          (outer.innerReply final) := by
        simpa only [DDC.History.relabel_snocInner,
          DDS.innerReplyAt_relabel, List.map_append, List.map_singleton]
          using inductionHypothesis
      have result := Attachment.CompatibleFrom.innerQuery mappedResponds mappedTail
      simpa only [List.map_cons,
        DDC.History.lastInput_relabel, relabelPackedResponse,
        _root_.Equiv.sumCongr_apply] using result
  | @outerLast history innerPrior reply responds =>
      have mappedResponds :
          relabelResponse outer inner history (Sum.inr reply) ∈
            relabel outer inner converter
              (DDC.History.relabel outer inner history) :=
        mem_relabel_of_mem outer inner converter history (Sum.inr reply)
          responds
      have result := @Attachment.CompatibleFrom.outerLast C D
        (relabel outer inner converter) (DDS.relabel inner system)
        (DDC.History.relabel outer inner history)
        (innerPrior.map inner.queries)
        (relabelOuterReply outer inner history reply) mappedResponds
      simpa only [List.map_cons, List.map_nil,
        DDC.History.lastInput_relabel, relabelPackedResponse,
        relabelResponse_outer, _root_.Equiv.sumCongr_apply,
        pack_relabelOuterReply] using result
  | @outerNext history innerPrior reply nextOuter remainingOuter tailInputs
      tailResponses final responds tail inductionHypothesis =>
      have mappedResponds :
          relabelResponse outer inner history (Sum.inr reply) ∈
            relabel outer inner converter
              (DDC.History.relabel outer inner history) :=
        mem_relabel_of_mem outer inner converter history (Sum.inr reply)
          responds
      have mappedTail : Attachment.CompatibleFrom (relabel outer inner converter)
          (DDS.relabel inner system)
          ((DDC.History.relabel outer inner history).snocOuter
            (outer.queries nextOuter))
          (innerPrior.map inner.queries) (remainingOuter.map outer.queries)
          (tailInputs.map (DDC.History.relabelInput outer inner))
          (tailResponses.map (relabelPackedResponse outer inner))
          (outer.innerReply final) := by
        simpa only [DDC.History.relabel_snocOuter,
          List.map_append, List.map_singleton] using inductionHypothesis
      have result := Attachment.CompatibleFrom.outerNext mappedResponds mappedTail
      simpa only [List.map_cons, List.map_nil,
        DDC.History.lastInput_relabel, relabelPackedResponse,
        relabelResponse_outer, _root_.Equiv.sumCongr_apply,
        pack_relabelOuterReply] using result

end Internal

/-- Relabeling before attachment and attaching before relabeling define the
same DDS. -/
theorem applySystem_relabel_eq
    {A C : Interface.{u, v}} {B D : Interface.{w, z}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) (system : DDS B) :
    applySystem (relabel outer inner converter) (DDS.relabel inner system) =
      DDS.relabel outer (applySystem converter system) := by
  -- Compare the two DDSs on an arbitrary nonempty outer history.
  apply DDS.ext
  intro targetHistory
  -- Pull the target history back through the outer-interface equivalence.
  let sourceHistory := _root_.RandomSystems.Ambient.History.map outer.queries.symm targetHistory
  -- Choose the unique compatible attachment transcript at the source history.
  obtain ⟨sourceTranscript, sourceCompatible⟩ :=
    Attachment.exists_compatible converter system sourceHistory
  -- Relabel every query, answer, and final response in that transcript.
  let mappedTranscript : Attachment.Transcript C D :=
    { inputs := sourceTranscript.inputs.map
        (DDC.History.relabelInput outer inner)
      responses := sourceTranscript.responses.map
        (relabelPackedResponse outer inner)
      final := outer.innerReply sourceTranscript.final }
  -- Compatibility is preserved pointwise by the two interface equivalences.
  have mappedFrom := compatibleFrom_relabel outer inner converter system
    sourceCompatible
  have startEqual : DDC.History.relabel outer inner
      (DDC.History.singleton (B := B) sourceHistory.head) =
      DDC.History.singleton (B := D) targetHistory.head := by
    rw [DDC.History.relabel_singleton]
    rw [show outer.queries sourceHistory.head = targetHistory.head by
      simp [sourceHistory, history_head_map]]
  have remainingEqual : sourceHistory.tail.map outer.queries =
      targetHistory.tail := by
    simp [sourceHistory, history_tail_map]
  have mappedCompatible : Attachment.Compatible
      (relabel outer inner converter) (DDS.relabel inner system)
      targetHistory mappedTranscript := by
    unfold Attachment.Compatible
    change Attachment.CompatibleFrom (relabel outer inner converter)
      (DDS.relabel inner system)
      (DDC.History.singleton (B := D) targetHistory.head) []
      targetHistory.tail mappedTranscript.inputs mappedTranscript.responses
      mappedTranscript.final
    rw [← startEqual, ← remainingEqual]
    exact mappedFrom
  -- Characterize the source attachment by its compatible transcript.
  have sourceFinalQuery : sourceTranscript.final.1 = sourceHistory.last :=
    Attachment.Compatible.final_query_eq_last sourceCompatible
  have sourceApplied :
      applySystem converter system sourceHistory =
        Attachment.selectReply sourceHistory.last sourceTranscript.final := by
    apply (applySystem_eq_iff converter system sourceHistory _).mpr
    exact ⟨sourceTranscript, sourceCompatible,
      (Attachment.selectReply_heq_second sourceHistory.last
        sourceTranscript.final sourceFinalQuery).symm⟩
  -- Relabeling the selected final answer gives the target DDS answer.
  let sourceOutput := Attachment.selectReply sourceHistory.last sourceTranscript.final
  have queryEqual : outer.queries sourceHistory.last = targetHistory.last := by
    simp [sourceHistory]
  have packedEqual :
      (⟨targetHistory.last,
          Attachment.selectReply targetHistory.last mappedTranscript.final⟩ : InnerReply C) =
        ⟨targetHistory.last,
          DDS.relabel outer (applySystem converter system) targetHistory⟩ := by
    calc
      _ = (⟨outer.queries sourceHistory.last,
          Attachment.selectReply (outer.queries sourceHistory.last)
            (outer.innerReply sourceTranscript.final)⟩ : InnerReply C) := by
        exact congrArg
          (fun query => (⟨query,
            Attachment.selectReply query (outer.innerReply sourceTranscript.final)⟩ :
              InnerReply C)) queryEqual.symm
      _ = outer.innerReply ⟨sourceHistory.last, sourceOutput⟩ :=
        packed_selectReply_relabel outer sourceHistory.last
          sourceTranscript.final
      _ = outer.innerReply
          ⟨sourceHistory.last,
            applySystem converter system sourceHistory⟩ := by
        rw [sourceApplied]
      _ = (⟨targetHistory.last,
          DDS.relabel outer (applySystem converter system) targetHistory⟩ :
            InnerReply C) :=
        (DDS.packed_relabel outer (applySystem converter system)
          targetHistory).symm
  have selectedEqual :
      Attachment.selectReply targetHistory.last mappedTranscript.final =
        DDS.relabel outer (applySystem converter system) targetHistory :=
    reply_eq_of_packed_eq packedEqual
  have targetFinalQuery : mappedTranscript.final.1 = targetHistory.last :=
    Attachment.Compatible.final_query_eq_last mappedCompatible
  -- The mapped compatible transcript therefore characterizes the target attachment.
  apply (applySystem_eq_iff (relabel outer inner converter)
    (DDS.relabel inner system) targetHistory _).mpr
  exact ⟨mappedTranscript, mappedCompatible,
    (Attachment.selectReply_heq_second targetHistory.last
      mappedTranscript.final targetFinalQuery).symm.trans
        (heq_of_eq selectedEqual)⟩

end DDC

namespace Interface.Equiv

/-- The DDC induced by an interface equivalence is obtained by relabeling
forwarding at the outer interface and leaving the inner interface unchanged. -/
noncomputable def toDDC {A B : Interface.{u, v}}
    (equivalence : A.Equiv B) : DDC B A :=
  DDC.relabel equivalence (.refl A) (DDC.forwarding A)

end Interface.Equiv

namespace DDC

open Internal

@[simp]
theorem toDDC_refl (A : Interface.{u, v}) :
    (Interface.Equiv.refl A).toDDC = forwarding A := by
  exact relabel_refl (forwarding A)

/-- Attachment of the DDC induced by an interface equivalence is exactly
DDS relabeling. -/
theorem applySystem_toDDC_eq
    {A B : Interface.{u, v}} (equivalence : A.Equiv B)
    (system : DDS A) :
    applySystem equivalence.toDDC system = DDS.relabel equivalence system := by
  unfold Interface.Equiv.toDDC
  calc
    applySystem (relabel equivalence (.refl A) (forwarding A)) system =
        applySystem (relabel equivalence (.refl A) (forwarding A))
          (DDS.relabel (.refl A) system) := by
            -- Insert identity relabeling of the inner DDS.
            rw [DDS.relabel_refl]
    _ = DDS.relabel equivalence (applySystem (forwarding A) system) :=
      -- Move simultaneous relabeling through attachment.
      applySystem_relabel_eq equivalence (.refl A) (forwarding A) system
    _ = DDS.relabel equivalence system := by
      -- Forwarding attachment is the identity.
      rw [applySystem_forwarding_eq]

namespace Internal

namespace AttemptedHistory

/-- Relabel every query and every reply in its query-selected answer fibre in
a canonical attempted history. -/
private def relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D) :
    AttemptedHistory A B → AttemptedHistory C D
  | .start query => .start (outer.queries query)
  | .afterInner prior query reply =>
      .afterInner (relabel outer inner prior) (inner.queries query)
        (reply.map (inner.answers query))
  | .afterOuter prior query =>
      .afterOuter (relabel outer inner prior) (outer.queries query)

private theorem toReceived_relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : AttemptedHistory A B) :
    (relabel outer inner history).toReceived =
      DDC.History.relabel outer inner history.toReceived := by
  induction history with
  | start query =>
      exact (DDC.History.relabel_singleton outer inner query).symm
  | afterInner prior query reply inductionHypothesis =>
      rw [relabel, AttemptedHistory.toReceived, inductionHypothesis]
      exact (DDC.History.relabel_snocInner outer inner
        prior.toReceived query reply).symm
  | afterOuter prior query inductionHypothesis =>
      rw [relabel, AttemptedHistory.toReceived, inductionHypothesis]
      exact (DDC.History.relabel_snocOuter outer inner
        prior.toReceived query).symm

end AttemptedHistory

namespace PackedResponse

/-- Relabel a serial response without erasing the selected query. -/
private def relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D) :
    PackedResponse A B → PackedResponse C D :=
  _root_.Equiv.sumCongr inner.queries outer.innerReply

end PackedResponse

theorem packed_outer_relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B)
    (reply : Option (A.answer history.lastOuter)) :
    (⟨(DDC.History.relabel outer inner history).lastOuter,
        relabelOuterReply outer inner history reply⟩ : InnerReply C) =
      outer.innerReply ⟨history.lastOuter, reply⟩ := by
  apply Sigma.ext (DDC.History.lastOuter_relabel outer inner history)
  unfold relabelOuterReply Interface.Equiv.innerReply
  simp only [_root_.Equiv.trans_apply, _root_.Equiv.optionCongr_apply,
    _root_.Equiv.cast_apply]
  change cast _ (reply.map (outer.answers history.lastOuter)) ≍
    reply.map (outer.answers history.lastOuter)
  exact cast_heq
    (congrArg (fun query => Option (C.answer query))
      (DDC.History.lastOuter_relabel outer inner history).symm)
    (reply.map (outer.answers history.lastOuter))

private theorem innerClosed_relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B)
    (history : Option (DDC.History A B))
    (closed : InnerClosed converter history) :
    InnerClosed (DDC.relabel outer inner converter)
      (history.map (DDC.History.relabel outer inner)) := by
  cases history with
  | none => trivial
  | some history =>
      obtain ⟨reply, responds⟩ := closed
      exact ⟨relabelOuterReply outer inner history reply,
        DDC.Internal.mem_relabel_of_mem outer inner converter history
          (Sum.inr reply) responds⟩

private theorem admissible_relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (converter : DDC A B) (history : DDC.History A B)
    (admissible : DDC.Raw.Admissible converter.toFun history) :
    DDC.Raw.Admissible (DDC.relabel outer inner converter).toFun
      (DDC.History.relabel outer inner history) := by
  have sourceResponds := converter.response_mem history admissible
  have targetResponds := DDC.Internal.mem_relabel_of_mem outer inner converter history
    _ sourceResponds
  exact ((DDC.relabel outer inner converter).exactDomain _).mp
    targetResponds.1

private theorem PrefixEndpointValid.relabel
    {A B C A' B' C' : Interface.{u, v}}
    {outerConverter : DDC A B} {innerConverter : DDC B C}
    (outer : A.Equiv A') (middle : B.Equiv B') (inner : C.Equiv C')
    {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (valid : PrefixEndpointValid outerConverter innerConverter response
      outerHistory innerHistory) :
    PrefixEndpointValid
      (DDC.relabel outer middle outerConverter)
      (DDC.relabel middle inner innerConverter)
      (PackedResponse.relabel outer inner response)
      (DDC.History.relabel outer middle outerHistory)
      (innerHistory.map (DDC.History.relabel middle inner)) := by
  cases response with
  | inl query =>
      refine
        { outerAdmissible := admissible_relabel outer middle outerConverter
            outerHistory valid.outerAdmissible
          innerAdmissible := ?_
          exposedInner := ?_
          selectedOuter := ?_
          closedOuter := ?_ }
      · intro targetHistory mappedEqual
        cases sourceEqual : innerHistory with
        | none => simp [sourceEqual] at mappedEqual
        | some sourceHistory =>
            simp only [sourceEqual, Option.map_some] at mappedEqual
            have targetEqual : targetHistory =
                DDC.History.relabel middle inner sourceHistory := by
              exact Option.some.inj mappedEqual.symm
            subst targetHistory
            exact admissible_relabel middle inner innerConverter sourceHistory
              (valid.innerAdmissible sourceHistory sourceEqual)
      · intro targetQuery responseEqual
        have queryEqual : inner.queries query = targetQuery :=
          Sum.inl.inj responseEqual
        subst targetQuery
        obtain ⟨sourceHistory, sourceEqual, innerResponds, outerResponds⟩ :=
          valid.exposedInner query rfl
        have mappedInnerResponds := DDC.Internal.mem_relabel_of_mem middle inner
          innerConverter sourceHistory (Sum.inl query) innerResponds
        have mappedOuterResponds := DDC.Internal.mem_relabel_of_mem outer middle
          outerConverter outerHistory
            (Sum.inl sourceHistory.lastOuter) outerResponds
        have linkedEqual :
            (Sum.inl (DDC.History.relabel middle inner
                sourceHistory).lastOuter :
              DDC.Response
                (DDC.History.relabel outer middle outerHistory)) =
              relabelResponse outer middle outerHistory
                (Sum.inl sourceHistory.lastOuter) := by
          change Sum.inl (DDC.History.relabel middle inner
              sourceHistory).lastOuter =
            Sum.inl (middle.queries sourceHistory.lastOuter)
          exact congrArg Sum.inl
            (DDC.History.lastOuter_relabel middle inner sourceHistory)
        refine ⟨DDC.History.relabel middle inner sourceHistory, ?_,
          mappedInnerResponds, linkedEqual.symm ▸ mappedOuterResponds⟩
        simp [sourceEqual]
      · intro targetReply impossible
        cases impossible
      · intro targetReply impossible
        cases impossible
  | inr packedReply =>
      rcases packedReply with ⟨sourceQuery, sourceReply⟩
      have sourceQueryEqual : sourceQuery = outerHistory.lastOuter :=
        valid.selectedOuter ⟨sourceQuery, sourceReply⟩ rfl
      subst sourceQuery
      obtain ⟨sourceResponds, sourceClosed⟩ :=
        valid.closedOuter sourceReply rfl
      refine
        { outerAdmissible := admissible_relabel outer middle outerConverter
            outerHistory valid.outerAdmissible
          innerAdmissible := ?_
          exposedInner := ?_
          selectedOuter := ?_
          closedOuter := ?_ }
      · intro targetHistory mappedEqual
        cases sourceEqual : innerHistory with
        | none => simp [sourceEqual] at mappedEqual
        | some sourceHistory =>
            simp only [sourceEqual, Option.map_some] at mappedEqual
            have targetEqual : targetHistory =
                DDC.History.relabel middle inner sourceHistory := by
              exact Option.some.inj mappedEqual.symm
            subst targetHistory
            exact admissible_relabel middle inner innerConverter sourceHistory
              (valid.innerAdmissible sourceHistory sourceEqual)
      · intro targetQuery impossible
        cases impossible
      · intro targetReply responseEqual
        have packedEqual := Sum.inr.inj responseEqual
        have queryEqual := congrArg Sigma.fst packedEqual
        exact queryEqual.symm.trans
          (DDC.History.lastOuter_relabel outer middle outerHistory).symm
      · intro targetReply responseEqual
        have packedEqual :
            (⟨(DDC.History.relabel outer middle
                  outerHistory).lastOuter,
                relabelOuterReply outer middle outerHistory sourceReply⟩ :
              InnerReply A') =
              ⟨(DDC.History.relabel outer middle
                  outerHistory).lastOuter, targetReply⟩ :=
          (packed_outer_relabel outer middle outerHistory sourceReply).trans
            (Sum.inr.inj responseEqual)
        have replyEqual :
            relabelOuterReply outer middle outerHistory sourceReply =
              targetReply :=
          eq_of_heq (Sigma.mk.inj_iff.mp packedEqual).2
        have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
          outerConverter outerHistory (Sum.inr sourceReply) sourceResponds
        have targetResponds : Sum.inr targetReply ∈
            DDC.relabel outer middle outerConverter
              (DDC.History.relabel outer middle outerHistory) := by
          exact congrArg Sum.inr replyEqual ▸ mappedResponds
        exact ⟨targetResponds,
          innerClosed_relabel middle inner innerConverter innerHistory
            sourceClosed⟩

private theorem OuterPrefixFactorization.relabel
    {A B C A' B' C' : Interface.{u, v}}
    {outerConverter : DDC A B} {innerConverter : DDC B C}
    (outer : A.Equiv A') (middle : B.Equiv B') (inner : C.Equiv C')
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outerConverter innerConverter
      outerHistory innerHistory response finalOuter finalInner) :
    OuterPrefixFactorization
      (DDC.relabel outer middle outerConverter)
      (DDC.relabel middle inner innerConverter)
      (DDC.History.relabel outer middle outerHistory)
      (innerHistory.map (DDC.History.relabel middle inner))
      (PackedResponse.relabel outer inner response)
      (DDC.History.relabel outer middle finalOuter)
      (finalInner.map (DDC.History.relabel middle inner)) := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory innerHistory response finalOuter finalInner
          factorization =>
        InnerPrefixFactorization
          (DDC.relabel outer middle outerConverter)
          (DDC.relabel middle inner innerConverter)
          (DDC.History.relabel outer middle outerHistory)
          (DDC.History.relabel middle inner innerHistory)
          (PackedResponse.relabel outer inner response)
          (DDC.History.relabel outer middle finalOuter)
          (finalInner.map (DDC.History.relabel middle inner))) with
  | outerReply responds =>
      rename_i currentOuter currentInner reply
      have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ responds
      have mapped := OuterPrefixFactorization.outerReply
        (inner := DDC.relabel middle inner innerConverter)
        (innerHistory := currentInner.map
          (DDC.History.relabel middle inner)) mappedResponds
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply, packed_outer_relabel] using mapped
  | outerQueryFirst responds tail inductionHypothesis =>
      have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ responds
      have mapped := OuterPrefixFactorization.outerQueryFirst
        (inner := DDC.relabel middle inner innerConverter)
        mappedResponds inductionHypothesis
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.relabel_singleton] using mapped
  | outerQueryNext closed responds tail inductionHypothesis =>
      have mappedClosed := innerClosed_relabel middle inner innerConverter
        _ closed
      have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ responds
      rw [DDC.History.relabel_snocOuter] at inductionHypothesis
      have mapped := OuterPrefixFactorization.outerQueryNext mappedClosed
        mappedResponds inductionHypothesis
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.relabel_snocOuter] using mapped
  | innerQuery linked responds =>
      rename_i currentOuter currentInner query
      have mappedLinked := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ linked
      have mappedResponds := DDC.Internal.mem_relabel_of_mem middle inner
        innerConverter _ _ responds
      have linkedResponseEqual :
          (Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter :
            DDC.Response (DDC.History.relabel outer middle
              currentOuter)) =
            relabelResponse outer middle currentOuter
              (Sum.inl currentInner.lastOuter) := by
        change Sum.inl (DDC.History.relabel middle inner
            currentInner).lastOuter =
          Sum.inl (middle.queries currentInner.lastOuter)
        exact congrArg Sum.inl
          (DDC.History.lastOuter_relabel middle inner currentInner)
      have linkedAtMappedLast :
          Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter ∈
            DDC.relabel outer middle outerConverter
              (DDC.History.relabel outer middle currentOuter) := by
        exact linkedResponseEqual.symm ▸ mappedLinked
      have mapped := InnerPrefixFactorization.innerQuery linkedAtMappedLast
        mappedResponds
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.lastOuter_relabel] using mapped
  | innerReply linked responds tail inductionHypothesis =>
      rename_i currentOuter currentInner reply response finalOuter finalInner
      have mappedLinked := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ linked
      have mappedResponds := DDC.Internal.mem_relabel_of_mem middle inner
        innerConverter _ _ responds
      have linkedResponseEqual :
          (Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter :
            DDC.Response (DDC.History.relabel outer middle
              currentOuter)) =
            relabelResponse outer middle currentOuter
              (Sum.inl currentInner.lastOuter) := by
        change Sum.inl (DDC.History.relabel middle inner
            currentInner).lastOuter =
          Sum.inl (middle.queries currentInner.lastOuter)
        exact congrArg Sum.inl
          (DDC.History.lastOuter_relabel middle inner currentInner)
      have linkedAtMappedLast :
          Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter ∈
            DDC.relabel outer middle outerConverter
              (DDC.History.relabel outer middle currentOuter) := by
        exact linkedResponseEqual.symm ▸ mappedLinked
      have nextOuterEqual :
          DDC.History.relabel outer middle
              (currentOuter.snocInner currentInner.lastOuter reply) =
            (DDC.History.relabel outer middle currentOuter).snocInner
              (DDC.History.relabel middle inner currentInner).lastOuter
              (relabelOuterReply middle inner currentInner reply) := by
        rw [DDC.History.relabel_snocInner]
        let appendReply := fun packed : InnerReply B' =>
          (DDC.History.relabel outer middle currentOuter).snocInner
            packed.1 packed.2
        have packedEqual := packed_outer_relabel middle inner currentInner reply
        change appendReply
            (middle.innerReply ⟨currentInner.lastOuter, reply⟩) =
          appendReply ⟨(DDC.History.relabel middle inner
            currentInner).lastOuter,
            relabelOuterReply middle inner currentInner reply⟩
        exact congrArg appendReply packedEqual.symm
      rw [nextOuterEqual] at inductionHypothesis
      have mapped := InnerPrefixFactorization.innerReply linkedAtMappedLast
        mappedResponds inductionHypothesis
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.lastOuter_relabel,
        DDC.History.relabel_snocInner] using mapped

private theorem InnerPrefixFactorization.relabel
    {A B C A' B' C' : Interface.{u, v}}
    {outerConverter : DDC A B} {innerConverter : DDC B C}
    (outer : A.Equiv A') (middle : B.Equiv B') (inner : C.Equiv C')
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outerConverter innerConverter
      outerHistory innerHistory response finalOuter finalInner) :
    InnerPrefixFactorization
      (DDC.relabel outer middle outerConverter)
      (DDC.relabel middle inner innerConverter)
      (DDC.History.relabel outer middle outerHistory)
      (DDC.History.relabel middle inner innerHistory)
      (PackedResponse.relabel outer inner response)
      (DDC.History.relabel outer middle finalOuter)
      (finalInner.map (DDC.History.relabel middle inner)) := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory innerHistory response finalOuter finalInner
          factorization =>
        OuterPrefixFactorization
          (DDC.relabel outer middle outerConverter)
          (DDC.relabel middle inner innerConverter)
          (DDC.History.relabel outer middle outerHistory)
          (innerHistory.map (DDC.History.relabel middle inner))
          (PackedResponse.relabel outer inner response)
          (DDC.History.relabel outer middle finalOuter)
          (finalInner.map (DDC.History.relabel middle inner))) with
  | outerReply responds =>
      rename_i currentOuter currentInner reply
      have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ responds
      have mapped := OuterPrefixFactorization.outerReply
        (inner := DDC.relabel middle inner innerConverter)
        (innerHistory := currentInner.map
          (DDC.History.relabel middle inner)) mappedResponds
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply, packed_outer_relabel] using mapped
  | outerQueryFirst responds tail inductionHypothesis =>
      have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ responds
      have mapped := OuterPrefixFactorization.outerQueryFirst
        (inner := DDC.relabel middle inner innerConverter)
        mappedResponds inductionHypothesis
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.relabel_singleton] using mapped
  | outerQueryNext closed responds tail inductionHypothesis =>
      have mappedClosed := innerClosed_relabel middle inner innerConverter
        _ closed
      have mappedResponds := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ responds
      rw [DDC.History.relabel_snocOuter] at inductionHypothesis
      have mapped := OuterPrefixFactorization.outerQueryNext mappedClosed
        mappedResponds inductionHypothesis
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.relabel_snocOuter] using mapped
  | innerQuery linked responds =>
      rename_i currentOuter currentInner query
      have mappedLinked := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ linked
      have mappedResponds := DDC.Internal.mem_relabel_of_mem middle inner
        innerConverter _ _ responds
      have linkedResponseEqual :
          (Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter :
            DDC.Response (DDC.History.relabel outer middle
              currentOuter)) =
            relabelResponse outer middle currentOuter
              (Sum.inl currentInner.lastOuter) := by
        change Sum.inl (DDC.History.relabel middle inner
            currentInner).lastOuter =
          Sum.inl (middle.queries currentInner.lastOuter)
        exact congrArg Sum.inl
          (DDC.History.lastOuter_relabel middle inner currentInner)
      have linkedAtMappedLast :
          Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter ∈
            DDC.relabel outer middle outerConverter
              (DDC.History.relabel outer middle currentOuter) := by
        exact linkedResponseEqual.symm ▸ mappedLinked
      have mapped := InnerPrefixFactorization.innerQuery linkedAtMappedLast
        mappedResponds
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.lastOuter_relabel] using mapped
  | innerReply linked responds tail inductionHypothesis =>
      rename_i currentOuter currentInner reply response finalOuter finalInner
      have mappedLinked := DDC.Internal.mem_relabel_of_mem outer middle
        outerConverter _ _ linked
      have mappedResponds := DDC.Internal.mem_relabel_of_mem middle inner
        innerConverter _ _ responds
      have linkedResponseEqual :
          (Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter :
            DDC.Response (DDC.History.relabel outer middle
              currentOuter)) =
            relabelResponse outer middle currentOuter
              (Sum.inl currentInner.lastOuter) := by
        change Sum.inl (DDC.History.relabel middle inner
            currentInner).lastOuter =
          Sum.inl (middle.queries currentInner.lastOuter)
        exact congrArg Sum.inl
          (DDC.History.lastOuter_relabel middle inner currentInner)
      have linkedAtMappedLast :
          Sum.inl (DDC.History.relabel middle inner
              currentInner).lastOuter ∈
            DDC.relabel outer middle outerConverter
              (DDC.History.relabel outer middle currentOuter) := by
        exact linkedResponseEqual.symm ▸ mappedLinked
      have nextOuterEqual :
          DDC.History.relabel outer middle
              (currentOuter.snocInner currentInner.lastOuter reply) =
            (DDC.History.relabel outer middle currentOuter).snocInner
              (DDC.History.relabel middle inner currentInner).lastOuter
              (relabelOuterReply middle inner currentInner reply) := by
        rw [DDC.History.relabel_snocInner]
        let appendReply := fun packed : InnerReply B' =>
          (DDC.History.relabel outer middle currentOuter).snocInner
            packed.1 packed.2
        have packedEqual := packed_outer_relabel middle inner currentInner reply
        change appendReply
            (middle.innerReply ⟨currentInner.lastOuter, reply⟩) =
          appendReply ⟨(DDC.History.relabel middle inner
            currentInner).lastOuter,
            relabelOuterReply middle inner currentInner reply⟩
        exact congrArg appendReply packedEqual.symm
      rw [nextOuterEqual] at inductionHypothesis
      have mapped := InnerPrefixFactorization.innerReply linkedAtMappedLast
        mappedResponds inductionHypothesis
      simpa only [Option.map, PackedResponse.relabel,
        _root_.Equiv.sumCongr_apply,
        DDC.History.lastOuter_relabel,
        DDC.History.relabel_snocInner] using mapped

private theorem SerialFactorization.relabel
    {A B C A' B' C' : Interface.{u, v}}
    {outerConverter : DDC A B} {innerConverter : DDC B C}
    (outer : A.Equiv A') (middle : B.Equiv B') (inner : C.Equiv C')
    {history : AttemptedHistory A C}
    {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outerConverter innerConverter
      history response outerHistory innerHistory) :
    SerialFactorization
      (DDC.relabel outer middle outerConverter)
      (DDC.relabel middle inner innerConverter)
      (AttemptedHistory.relabel outer inner history)
      (PackedResponse.relabel outer inner response)
      (DDC.History.relabel outer middle outerHistory)
      (innerHistory.map (DDC.History.relabel middle inner)) := by
  induction factorization with
  | start middleFactorization valid =>
      exact SerialFactorization.start
        (middleFactorization.relabel outer middle inner)
        (valid.relabel outer middle inner)
  | afterInner previous middleFactorization valid inductionHypothesis =>
      have mappedMiddle := middleFactorization.relabel outer middle inner
      rw [DDC.History.relabel_snocInner] at mappedMiddle
      exact SerialFactorization.afterInner inductionHypothesis
        mappedMiddle
        (valid.relabel outer middle inner)
  | @afterOuter history previousReply currentOuter currentInner outerQuery
      response finalOuter finalInner previous middleFactorization valid inductionHypothesis =>
      have mappedMiddle := middleFactorization.relabel outer middle inner
      rw [DDC.History.relabel_snocOuter] at mappedMiddle
      let sourceReceived := history.toReceived
      let targetReceived :=
        (AttemptedHistory.relabel outer inner history).toReceived
      have receivedEqual : targetReceived =
          DDC.History.relabel outer inner sourceReceived :=
        AttemptedHistory.toReceived_relabel outer inner history
      have previousPackedEqual :
          PackedResponse.relabel outer inner
              (Sum.inr ⟨sourceReceived.lastOuter, previousReply⟩) =
            Sum.inr ⟨targetReceived.lastOuter,
              cast (congrArg
                (fun selected => Option (A'.answer selected.lastOuter))
                receivedEqual.symm)
                (relabelOuterReply outer inner sourceReceived previousReply)⟩ := by
        apply congrArg Sum.inr
        calc
          outer.innerReply ⟨sourceReceived.lastOuter, previousReply⟩ =
              ⟨(DDC.History.relabel outer inner
                    sourceReceived).lastOuter,
                relabelOuterReply outer inner sourceReceived previousReply⟩ :=
            (packed_outer_relabel outer inner sourceReceived
              previousReply).symm
          _ = ⟨targetReceived.lastOuter,
                cast (congrArg
                  (fun selected => Option (A'.answer selected.lastOuter))
                  receivedEqual.symm)
                  (relabelOuterReply outer inner sourceReceived
                    previousReply)⟩ := by
            apply Sigma.ext
              (congrArg DDC.History.lastOuter receivedEqual.symm)
            exact (cast_heq _ _).symm
      have adjustedPrevious : SerialFactorization
          (DDC.relabel outer middle outerConverter)
          (DDC.relabel middle inner innerConverter)
          (AttemptedHistory.relabel outer inner history)
          (Sum.inr ⟨targetReceived.lastOuter,
            cast (congrArg
              (fun selected => Option (A'.answer selected.lastOuter))
              receivedEqual.symm)
              (relabelOuterReply outer inner sourceReceived previousReply)⟩)
          (DDC.History.relabel outer middle currentOuter)
          (currentInner.map (DDC.History.relabel middle inner)) := by
        exact previousPackedEqual ▸ inductionHypothesis
      exact SerialFactorization.afterOuter adjustedPrevious
        mappedMiddle
        (valid.relabel outer middle inner)

private theorem packResponse_relabel
    {A B C D : Interface.{u, v}}
    (outer : A.Equiv C) (inner : B.Equiv D)
    (history : DDC.History A B)
    (response : DDC.Response history) :
    PackedResponse.relabel outer inner (packResponse history response) =
      packResponse (DDC.History.relabel outer inner history)
        (relabelResponse outer inner history response) := by
  cases response with
  | inl query => rfl
  | inr reply =>
      apply congrArg Sum.inr
      exact (packed_outer_relabel outer inner history reply).symm

private theorem mem_serial_relabel_of_mem
    {A B C A' B' C' : Interface.{u, v}}
    (outer : A.Equiv A') (middle : B.Equiv B') (inner : C.Equiv C')
    (outerConverter : DDC A B) (innerConverter : DDC B C)
    (history : DDC.History A C) (response : DDC.Response history)
    (responds : response ∈ DDC.serial outerConverter innerConverter history) :
    relabelResponse outer inner history response ∈
      DDC.serial (DDC.relabel outer middle outerConverter)
        (DDC.relabel middle inner innerConverter)
        (DDC.History.relabel outer inner history) := by
  rw [mem_serial_iff, mem_serialRaw_iff] at responds ⊢
  obtain ⟨attempted, historyEqual, finalOuter, finalInner, factorization⟩ :=
    responds
  subst history
  have mapped := factorization.relabel outer middle inner
  rw [packResponse_relabel] at mapped
  refine ⟨AttemptedHistory.relabel outer inner attempted, ?_,
    DDC.History.relabel outer middle finalOuter,
    finalInner.map (DDC.History.relabel middle inner), mapped⟩
  exact AttemptedHistory.toReceived_relabel outer inner attempted

private theorem eq_of_graph_subset
    {A B : Interface.{u, v}} (left right : DDC A B)
    (subset : ∀ history response,
      response ∈ right history → response ∈ left history) :
    left = right := by
  have admissible : ∀ {history},
      DDC.Raw.Admissible left.toFun history →
        DDC.Raw.Admissible right.toFun history := by
    intro history legal
    induction legal with
    | start query => exact .start query
    | afterInner leftPrior leftResponds reply inductionHypothesis =>
        rename_i history query
        have rightResponds := right.response_mem history inductionHypothesis
        have responseEqual : right.response history inductionHypothesis =
            Sum.inl query :=
          Part.mem_unique (subset history _ rightResponds) leftResponds
        exact .afterInner inductionHypothesis
          (responseEqual ▸ rightResponds) reply
    | afterOuter leftPrior leftResponds query inductionHypothesis =>
        rename_i history reply
        have rightResponds := right.response_mem history inductionHypothesis
        have responseEqual : right.response history inductionHypothesis =
            Sum.inr reply :=
          Part.mem_unique (subset history _ rightResponds) leftResponds
        exact .afterOuter inductionHypothesis
          (responseEqual ▸ rightResponds) query
  apply DDC.ext
  intro history response
  constructor
  · intro leftResponds
    have rightAdmissible := admissible
      ((left.exactDomain history).mp leftResponds.1)
    have rightResponds := right.response_mem history rightAdmissible
    have responseEqual : right.response history rightAdmissible = response :=
      Part.mem_unique (subset history _ rightResponds) leftResponds
    exact responseEqual ▸ rightResponds
  · exact subset history response

private theorem transport_mem
    {A B : Interface.{u, v}} (converter : DDC A B)
    {left right : DDC.History A B} (equal : left = right)
    (response : DDC.Response left)
    (responds : response ∈ converter left) :
    cast (congrArg (fun history => DDC.Response history) equal) response ∈
      converter right := by
  cases equal
  exact responds

end Internal

/-- Serial composition is natural under simultaneous relabeling of its three
interfaces. -/
theorem relabel_serial_eq
    {A B C A' B' C' : Interface.{u, v}}
    (outer : A.Equiv A') (middle : B.Equiv B') (inner : C.Equiv C')
    (outerConverter : DDC A B) (innerConverter : DDC B C) :
    serial (relabel outer middle outerConverter)
        (relabel middle inner innerConverter) =
      relabel outer inner (serial outerConverter innerConverter) := by
  -- It suffices to prove inclusion of the two canonical deterministic graphs.
  apply eq_of_graph_subset
  intro targetHistory targetResponse responds
  -- Pull the target history and response back to the source interfaces.
  have sourceResponds :=
    (mem_relabel_iff_symm outer inner
      (serial outerConverter innerConverter) targetHistory targetResponse).mp
      responds
  let histories := DDC.History.relabelEquiv outer inner
  let sourceHistory := histories.symm targetHistory
  let responses := relabelResponseAt outer inner targetHistory
  let sourceResponse := responses.symm targetResponse
  -- Relabel the source serial factorization componentwise.
  have mapped := mem_serial_relabel_of_mem outer middle inner
    outerConverter innerConverter sourceHistory sourceResponse sourceResponds
  have historyEqual : DDC.History.relabel outer inner sourceHistory =
      targetHistory := by
    exact histories.apply_symm_apply targetHistory
  have responseEqual :
      cast (congrArg (fun selected => DDC.Response selected) historyEqual)
          (relabelResponse outer inner sourceHistory sourceResponse) =
        targetResponse := by
    exact responses.apply_symm_apply targetResponse
  have transported := transport_mem
    (serial (relabel outer middle outerConverter)
      (relabel middle inner innerConverter))
    historyEqual _ mapped
  -- Transport the relabeled membership back to the original target indices.
  exact responseEqual ▸ transported

/-- Interface-equivalence DDCs compose in the same order as the underlying
interface equivalences. -/
theorem toDDC_trans
    {A B C : Interface.{u, v}}
    (first : A.Equiv B) (second : B.Equiv C) :
    serial second.toDDC first.toDDC = (first.trans second).toDDC := by
  -- Naturality rewrites serial composition as relabeling of forwarding.
  have natural := relabel_serial_eq second (.refl B) (.refl A)
    (forwarding B) first.toDDC
  have firstEquality :
      serial second.toDDC first.toDDC =
        relabel second (.refl A) first.toDDC := by
    simpa only [Interface.Equiv.toDDC, relabel_refl,
      forwarding_serial_eq] using natural
  rw [firstEquality]
  unfold Interface.Equiv.toDDC
  -- Composition of relabelings is composition of interface equivalences.
  rw [relabel_trans, Interface.Equiv.refl_trans]

@[simp]
theorem toDDC_symm_serial_eq
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    serial equivalence.symm.toDDC equivalence.toDDC = forwarding A := by
  -- Reduce the serial DDC to the composite interface equivalence.
  rw [toDDC_trans]
  -- An equivalence followed by its inverse is the identity.
  rw [Interface.Equiv.trans_symm, toDDC_refl]

@[simp]
theorem toDDC_serial_symm_eq
    {A B : Interface.{u, v}} (equivalence : A.Equiv B) :
    serial equivalence.toDDC equivalence.symm.toDDC = forwarding B := by
  -- Reduce the serial DDC to the composite interface equivalence.
  rw [toDDC_trans]
  -- The inverse followed by the equivalence is the identity.
  rw [Interface.Equiv.symm_trans, toDDC_refl]

end DDC

end RandomSystems.Ambient
