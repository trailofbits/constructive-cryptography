import RandomSystems.Converter.Serial

set_option autoImplicit false

/-!
# Congruence for serial converter composition

Two inner converters may be substituted below the same outer converter when
they agree on every inner state reachable through the serial interaction.
-/

namespace RandomSystems.Ambient.DDC

universe u v

namespace Internal

/-- The phase invariant at the endpoint of a serial factorization. -/
def SerialPhaseAtEndpoint
    {A B C : Interface.{u, v}}
    (outerPhase : DDC.History A B → Option (DDC.History B C) → Prop)
    (innerPhase : DDC.History A B → DDC.History B C → Prop)
    (response : PackedResponse A C) (outerHistory : DDC.History A B)
    (innerHistory : Option (DDC.History B C)) : Prop :=
  match response with
  | Sum.inl _ => ∃ history, innerHistory = some history ∧
      innerPhase outerHistory history
  | Sum.inr _ => outerPhase outerHistory innerHistory

/-- Reachable-state conditions under which `left` may be replaced by `right`
below `outer` in serial composition. -/
structure SerialGate
    {A B C : Interface.{u, v}}
    (outer : DDC A B) (left right : DDC B C)
    (outerPhase : DDC.History A B → Option (DDC.History B C) → Prop)
    (innerPhase : DDC.History A B → DDC.History B C → Prop) : Prop where
  inner_eq : ∀ outerHistory innerHistory,
    innerPhase outerHistory innerHistory →
      left innerHistory = right innerHistory
  outer_query_first : ∀ {outerHistory query},
    outerPhase outerHistory none →
      Sum.inl query ∈ outer outerHistory →
      innerPhase outerHistory (DDC.History.singleton query)
  outer_query_next : ∀ {outerHistory innerHistory query},
    outerPhase outerHistory (some innerHistory) →
      Sum.inl query ∈ outer outerHistory →
      innerPhase outerHistory (innerHistory.snocOuter query)
  inner_query : ∀ {outerHistory innerHistory query},
    innerPhase outerHistory innerHistory →
      Sum.inl query ∈ left innerHistory →
      ∀ reply : Option (C.answer query),
        innerPhase outerHistory (innerHistory.snocInner query reply)
  inner_reply : ∀ {outerHistory innerHistory}
      {reply : Option (B.answer innerHistory.lastOuter)},
    innerPhase outerHistory innerHistory →
      Sum.inr reply ∈ left innerHistory →
      outerPhase
        (outerHistory.snocInner innerHistory.lastOuter reply)
        (some innerHistory)
  outer_next : ∀ {outerHistory innerHistory}
      {reply : Option (A.answer outerHistory.lastOuter)},
    outerPhase outerHistory innerHistory →
      Sum.inr reply ∈ outer outerHistory →
      ∀ query, outerPhase (outerHistory.snocOuter query) innerHistory
  initial : ∀ query,
    outerPhase (DDC.History.singleton query) none

theorem SerialGate.symm
    {A B C : Interface.{u, v}}
    {outer : DDC A B} {left right : DDC B C}
    {outerPhase : DDC.History A B → Option (DDC.History B C) → Prop}
    {innerPhase : DDC.History A B → DDC.History B C → Prop}
    (gate : SerialGate outer left right outerPhase innerPhase) :
    SerialGate outer right left outerPhase innerPhase := by
  refine
    { inner_eq := fun outerHistory innerHistory phase =>
        (gate.inner_eq outerHistory innerHistory phase).symm
      outer_query_first := gate.outer_query_first
      outer_query_next := gate.outer_query_next
      inner_query := ?_
      inner_reply := ?_
      outer_next := gate.outer_next
      initial := gate.initial }
  · intro outerHistory innerHistory query phase responds reply
    apply gate.inner_query phase _ reply
    rw [gate.inner_eq outerHistory innerHistory phase]
    exact responds
  · intro outerHistory innerHistory reply phase responds
    apply gate.inner_reply phase
    rw [gate.inner_eq outerHistory innerHistory phase]
    exact responds

theorem OuterPrefixFactorization.congr_inner_of_gate
    {A B C : Interface.{u, v}}
    {outer : DDC A B} {left right : DDC B C}
    {outerPhase : DDC.History A B → Option (DDC.History B C) → Prop}
    {innerPhase : DDC.History A B → DDC.History B C → Prop}
    (gate : SerialGate outer left right outerPhase innerPhase)
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : OuterPrefixFactorization outer left outerHistory
      innerHistory response finalOuter finalInner)
    (phase : outerPhase outerHistory innerHistory)
    (rightClosed : InnerClosed right innerHistory) :
    ∃ transported : OuterPrefixFactorization outer right outerHistory
        innerHistory response finalOuter finalInner,
      SerialPhaseAtEndpoint outerPhase innerPhase response
        finalOuter finalInner := by
  induction factorization using OuterPrefixFactorization.rec
      (motive_2 := fun outerHistory innerHistory response finalOuter finalInner
          _ =>
        innerPhase outerHistory innerHistory →
          ∃ transported : InnerPrefixFactorization outer right outerHistory
              innerHistory response finalOuter finalInner,
            SerialPhaseAtEndpoint outerPhase innerPhase response
              finalOuter finalInner) with
  | outerReply responds =>
      exact ⟨OuterPrefixFactorization.outerReply responds, phase⟩
  | outerQueryFirst responds tail inductionHypothesis =>
      obtain ⟨tail', endpoint⟩ :=
        inductionHypothesis (gate.outer_query_first phase responds)
      exact ⟨OuterPrefixFactorization.outerQueryFirst responds tail', endpoint⟩
  | outerQueryNext leftClosed responds tail inductionHypothesis =>
      obtain ⟨tail', endpoint⟩ :=
        inductionHypothesis (gate.outer_query_next phase responds)
      exact ⟨OuterPrefixFactorization.outerQueryNext rightClosed responds tail',
        endpoint⟩
  | @innerQuery outerHistory innerHistory query linked responds currentPhase =>
      have responds' : Sum.inl query ∈ right innerHistory := by
        rw [← gate.inner_eq outerHistory innerHistory currentPhase]
        exact responds
      exact ⟨InnerPrefixFactorization.innerQuery linked responds',
        ⟨innerHistory, rfl, currentPhase⟩⟩
  | @innerReply outerHistory innerHistory reply response finalOuter finalInner
      linked responds tail inductionHypothesis currentPhase =>
      have responds' : Sum.inr reply ∈ right innerHistory := by
        rw [← gate.inner_eq outerHistory innerHistory currentPhase]
        exact responds
      obtain ⟨tail', endpoint⟩ := inductionHypothesis
        (gate.inner_reply currentPhase responds) ⟨reply, responds'⟩
      exact ⟨InnerPrefixFactorization.innerReply linked responds' tail', endpoint⟩

theorem InnerPrefixFactorization.congr_inner_of_gate
    {A B C : Interface.{u, v}}
    {outer : DDC A B} {left right : DDC B C}
    {outerPhase : DDC.History A B → Option (DDC.History B C) → Prop}
    {innerPhase : DDC.History A B → DDC.History B C → Prop}
    (gate : SerialGate outer left right outerPhase innerPhase)
    {outerHistory : DDC.History A B}
    {innerHistory : DDC.History B C}
    {response : PackedResponse A C}
    {finalOuter : DDC.History A B}
    {finalInner : Option (DDC.History B C)}
    (factorization : InnerPrefixFactorization outer left outerHistory
      innerHistory response finalOuter finalInner)
    (phase : innerPhase outerHistory innerHistory) :
    ∃ transported : InnerPrefixFactorization outer right outerHistory
        innerHistory response finalOuter finalInner,
      SerialPhaseAtEndpoint outerPhase innerPhase response
        finalOuter finalInner := by
  induction factorization using InnerPrefixFactorization.rec
      (motive_1 := fun outerHistory innerHistory response finalOuter finalInner
          _ =>
        outerPhase outerHistory innerHistory →
          InnerClosed right innerHistory →
          ∃ transported : OuterPrefixFactorization outer right outerHistory
              innerHistory response finalOuter finalInner,
            SerialPhaseAtEndpoint outerPhase innerPhase response
              finalOuter finalInner) with
  | @outerReply outerHistory innerHistory reply responds currentPhase
      rightClosed =>
      exact ⟨OuterPrefixFactorization.outerReply responds, currentPhase⟩
  | @outerQueryFirst outerHistory query response finalOuter finalInner
      responds tail inductionHypothesis currentPhase rightClosed =>
      obtain ⟨tail', endpoint⟩ :=
        inductionHypothesis (gate.outer_query_first currentPhase responds)
      exact ⟨OuterPrefixFactorization.outerQueryFirst responds tail', endpoint⟩
  | @outerQueryNext outerHistory innerHistory query response finalOuter
      finalInner leftClosed responds tail inductionHypothesis currentPhase
      rightClosed =>
      obtain ⟨tail', endpoint⟩ :=
        inductionHypothesis (gate.outer_query_next currentPhase responds)
      exact ⟨OuterPrefixFactorization.outerQueryNext rightClosed responds tail',
        endpoint⟩
  | @innerQuery outerHistory innerHistory query linked responds =>
      have responds' : Sum.inl query ∈ right innerHistory := by
        rw [← gate.inner_eq outerHistory innerHistory phase]
        exact responds
      exact ⟨InnerPrefixFactorization.innerQuery linked responds',
        ⟨innerHistory, rfl, phase⟩⟩
  | @innerReply outerHistory innerHistory reply response finalOuter finalInner
      linked responds tail inductionHypothesis =>
      have responds' : Sum.inr reply ∈ right innerHistory := by
        rw [← gate.inner_eq outerHistory innerHistory phase]
        exact responds
      obtain ⟨tail', endpoint⟩ := inductionHypothesis
        (gate.inner_reply phase responds) ⟨reply, responds'⟩
      exact ⟨InnerPrefixFactorization.innerReply linked responds' tail', endpoint⟩

theorem SerialFactorization.congr_inner_of_gate
    {A B C : Interface.{u, v}}
    {outer : DDC A B} {left right : DDC B C}
    {outerPhase : DDC.History A B → Option (DDC.History B C) → Prop}
    {innerPhase : DDC.History A B → DDC.History B C → Prop}
    (gate : SerialGate outer left right outerPhase innerPhase)
    {history : AttemptedHistory A C} {response : PackedResponse A C}
    {outerHistory : DDC.History A B}
    {innerHistory : Option (DDC.History B C)}
    (factorization : SerialFactorization outer left history response
      outerHistory innerHistory) :
    ∃ transported : SerialFactorization outer right history response
        outerHistory innerHistory,
      SerialPhaseAtEndpoint outerPhase innerPhase response
        outerHistory innerHistory := by
  induction factorization with
  | @start outerQuery response finalOuter finalInner middle valid =>
      obtain ⟨middle', endpoint⟩ :=
        middle.congr_inner_of_gate gate (gate.initial outerQuery) trivial
      have valid' : PrefixEndpointValid outer right response
          finalOuter finalInner :=
        middle'.endpointValid (.start outerQuery)
          (by intro inner impossible; cases impossible) trivial
      exact ⟨SerialFactorization.start middle' valid', endpoint⟩
  | @afterInner history query currentOuter currentInner reply response
      finalOuter finalInner previous middle valid inductionHypothesis =>
      obtain ⟨previous', previousPhase⟩ := inductionHypothesis
      obtain ⟨phaseInner, innerEqual, currentPhase⟩ := previousPhase
      cases Option.some.inj innerEqual
      obtain ⟨sourceInner, sourceInnerEqual, sourceResponds, sourceLinked⟩ :=
        previous.endpointValid.exposedInner query rfl
      cases Option.some.inj sourceInnerEqual
      have rightResponds : Sum.inl query ∈ right currentInner := by
        rw [← gate.inner_eq currentOuter currentInner currentPhase]
        exact sourceResponds
      have nextPhase : innerPhase currentOuter
          (currentInner.snocInner query reply) :=
        gate.inner_query currentPhase sourceResponds reply
      obtain ⟨middle', endpoint⟩ :=
        middle.congr_inner_of_gate gate nextPhase
      have currentValid := previous'.endpointValid
      have nextInnerAdmissible : DDC.Raw.Admissible right.toFun
          (currentInner.snocInner query reply) :=
        .afterInner (currentValid.innerAdmissible currentInner rfl)
          rightResponds reply
      have valid' : PrefixEndpointValid outer right response
          finalOuter finalInner :=
        middle'.endpointValid currentValid.outerAdmissible
          nextInnerAdmissible
      exact ⟨SerialFactorization.afterInner previous' middle' valid', endpoint⟩
  | @afterOuter history previousReply currentOuter currentInner outerQuery
      response finalOuter finalInner previous middle valid inductionHypothesis =>
      obtain ⟨previous', previousPhase⟩ := inductionHypothesis
      let packed : DDC.History.InnerReply A :=
        ⟨history.toReceived.lastOuter, previousReply⟩
      have selected := previous.endpointValid.selectedOuter packed rfl
      let currentReply : Option (A.answer currentOuter.lastOuter) :=
        Attachment.selectReply currentOuter.lastOuter packed
      have packedEqual :
          (⟨currentOuter.lastOuter, currentReply⟩ :
            DDC.History.InnerReply A) = packed :=
        pack_selectReply_eq currentOuter.lastOuter packed selected
      have responseEqual :
          (Sum.inr packed : PackedResponse A C) =
            Sum.inr ⟨currentOuter.lastOuter, currentReply⟩ :=
        congrArg Sum.inr packedEqual.symm
      obtain ⟨outerResponds, leftClosed⟩ :=
        previous.endpointValid.closedOuter currentReply responseEqual
      obtain ⟨_, rightClosed⟩ :=
        previous'.endpointValid.closedOuter currentReply responseEqual
      have nextPhase : outerPhase (currentOuter.snocOuter outerQuery)
          currentInner :=
        gate.outer_next previousPhase outerResponds outerQuery
      obtain ⟨middle', endpoint⟩ :=
        middle.congr_inner_of_gate gate nextPhase rightClosed
      have previousValid := previous'.endpointValid
      have nextOuterAdmissible : DDC.Raw.Admissible outer.toFun
          (currentOuter.snocOuter outerQuery) :=
        .afterOuter previousValid.outerAdmissible outerResponds outerQuery
      have valid' : PrefixEndpointValid outer right response
          finalOuter finalInner :=
        middle'.endpointValid nextOuterAdmissible
          previousValid.innerAdmissible rightClosed
      exact ⟨SerialFactorization.afterOuter previous' middle' valid', endpoint⟩

end Internal

/-- Serial composition is congruent when the two inner converters agree on
all states reachable under the supplied phase invariants. -/
theorem serial_congr_right_of_gate
    {A B C : Interface.{u, v}}
    {outer : DDC A B} {left right : DDC B C}
    {outerPhase : DDC.History A B → Option (DDC.History B C) → Prop}
    {innerPhase : DDC.History A B → DDC.History B C → Prop}
    (gate : Internal.SerialGate outer left right outerPhase innerPhase) :
    serial outer left = serial outer right := by
  apply DDC.ext
  intro history response
  rw [mem_serial_iff, mem_serial_iff,
    Internal.mem_serialRaw_iff, Internal.mem_serialRaw_iff]
  constructor
  · rintro ⟨attempted, historyEqual, finalOuter, finalInner,
      factorization⟩
    obtain ⟨transported, _⟩ := factorization.congr_inner_of_gate gate
    exact ⟨attempted, historyEqual, finalOuter, finalInner, transported⟩
  · rintro ⟨attempted, historyEqual, finalOuter, finalInner,
      factorization⟩
    obtain ⟨transported, _⟩ :=
      factorization.congr_inner_of_gate gate.symm
    exact ⟨attempted, historyEqual, finalOuter, finalInner, transported⟩

end RandomSystems.Ambient.DDC
