/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.ApplySystem
import Probability.StatisticalDistance
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Query-indexed DDE observation

Lanzenberger, Definition 2.11 (printed p. 14), says that a DDE “is a partial
function” and requires its domain to be “prefix-closed.” The DDE below is the
ambient attempted-history presentation: `Option` represents partiality, but
prefix closure is not bundled into the function type. It is therefore not the
literal source carrier. An observation of length `n` is the pure functional
interaction of a DDS and a DDE for `n` rounds.

For a branch-finite DDC and each selected DDS, every finite outer observation
factors through one finite inner branch. A finite PDS support later supplies a
common maximum for the two laws being compared. This proves data processing
without an operational machine or a converter-specific absorption assumption.
Jost, Theorem 2.2.11 (printed p. 22), uses “the distinguisher that first
attaches π to the given resource and then executes D.” Liu Zhang,
*Multi-Party Computation: Definitions, Enhanced Security Guarantees and
Efficiency*, Lemma 4.2.3 (printed p. 35), likewise uses “the distinguisher that
first attaches α at interface i of the given resource, and then executes D.”
The factorization below supplies that precomposition for this functional
carrier.
-/

namespace RandomSystems.Ambient

open Probability (Distribution)

universe u v w z

/-- A finite query-indexed observation history. -/
abbrev Transcript (A : Interface.{u, v}) :=
  List (DDC.History.InnerReply A)

/-- A query-indexed DDE. `none` means that the DDE stops after the supplied
transcript; prefix closure is not bundled into this function type. -/
abbrev DDE (A : Interface.{u, v}) : Type (max u v) :=
  Transcript A → Option A.query

/-- The attempted queries contained in a complete observation history. -/
def transcriptInputs {A : Interface.{u, v}}
    (observations : Transcript A) : List A.query :=
  observations.map Sigma.fst

/-- The first `rounds` values of a pure functional DDS/DDE interaction.
Once the DDE returns `none`, the observation history remains fixed. -/
def transcript {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) : Nat → Transcript A
  | 0 => []
  | rounds + 1 =>
      let current := transcript system environment rounds
      match environment current with
      | none => current
      | some query => current ++
          [⟨query, Attachment.innerReplyAt system (transcriptInputs current) query⟩]

@[simp]
theorem transcript_zero {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) :
    transcript system environment 0 = [] :=
  rfl

theorem transcript_succ {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) (rounds : Nat) :
    transcript system environment (rounds + 1) =
      match environment (transcript system environment rounds) with
      | none => transcript system environment rounds
      | some query => transcript system environment rounds ++
          [⟨query, Attachment.innerReplyAt system
            (transcriptInputs (transcript system environment rounds)) query⟩] :=
  rfl

/-- Persistent stopping follows directly from the functional definition. -/
theorem transcript_succ_eq_of_stops {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) (rounds : Nat)
    (stops : environment (transcript system environment rounds) = none) :
    transcript system environment (rounds + 1) =
      transcript system environment rounds := by
  rw [transcript_succ, stops]

def extendTranscript {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A)
    (current : Transcript A) : Transcript A :=
  match environment current with
  | none => current
  | some query =>
      current ++ [⟨query,
        Attachment.innerReplyAt system (transcriptInputs current) query⟩]

def continueTranscript {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) :
    Nat → Transcript A → Transcript A
  | 0, current => current
  | rounds + 1, current =>
      extendTranscript system environment
        (continueTranscript system environment rounds current)

theorem continueTranscript_succ_first {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) (rounds : Nat)
    (current : Transcript A) :
    continueTranscript system environment (rounds + 1) current =
      continueTranscript system environment rounds
        (extendTranscript system environment current) := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [continueTranscript, inductionHypothesis]
      rfl

theorem transcript_eq_continue {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) (rounds : Nat) :
    transcript system environment rounds =
      continueTranscript system environment rounds [] := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [transcript_succ, inductionHypothesis]
      rfl

theorem continueTranscript_eq_of_fixed {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A)
    (current : Transcript A)
    (fixed : extendTranscript system environment current = current) :
    ∀ rounds, continueTranscript system environment rounds current = current := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [continueTranscript, inductionHypothesis, fixed]

/-- Every entry in the dependent transcript is tagged by the corresponding
attempted DDS query. -/
theorem transcriptInputs_succ_of_query {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) (rounds : Nat)
    (query : A.query)
    (queries : environment (transcript system environment rounds) =
      some query) :
    transcriptInputs (transcript system environment (rounds + 1)) =
      transcriptInputs (transcript system environment rounds) ++ [query] := by
  simp [transcript_succ, queries, transcriptInputs]

/-- A finite-path, possibly infinitely branching mathematical observation
tree.  Each branch is selected by the answer in the queried fibre. -/
inductive ObservationTree (A : Interface.{u, v}) (R : Type w)
  | leaf (value : R)
  | query (input : A.query)
      (after : Option (A.answer input) → ObservationTree A R)

namespace ObservationTree

variable {A : Interface.{u, v}} {R : Type w}

/-- Evaluate one observation tree against a DDS, starting after `prior`. -/
noncomputable def evaluate (tree : ObservationTree A R) (system : DDS A)
    (prior : List A.query) : R :=
  ObservationTree.rec
    (motive := fun _ => DDS A → List A.query → R)
    (fun value _ _ => value)
    (fun query _ evaluateAfter system prior =>
      let reply := Attachment.innerReplyAt system prior query
      evaluateAfter reply system (prior ++ [query]))
    tree system prior

/-- Read the next query selected by a complete tagged answer history.  A
history with a mismatched query tag lies off the represented tree and stops. -/
noncomputable def toDDE (tree : ObservationTree A R) : DDE A := by
  classical
  exact ObservationTree.rec
    (motive := fun _ => DDE A)
    (fun _ _ => none)
    (fun query _ proceed replies =>
      match replies with
      | [] => some query
      | reply :: remaining =>
          if equal : reply.1 = query then
            proceed (equal ▸ reply.2) remaining
          else none)
    tree

/-- The unique linear branch selected by one concrete DDS. -/
noncomputable def branchTranscript (tree : ObservationTree A R) (system : DDS A)
    (prior : List A.query) : Transcript A :=
  ObservationTree.rec
    (motive := fun _ => DDS A → List A.query → Transcript A)
    (fun _ _ _ => [])
    (fun query _ evaluateAfter system prior =>
      let reply := Attachment.innerReplyAt system prior query
      ⟨query, reply⟩ :: evaluateAfter reply system (prior ++ [query]))
    tree system prior

/-- Read the leaf reached by a complete tagged answer history. -/
noncomputable def resultFromTranscript (tree : ObservationTree A R) :
    Transcript A → Option R := by
  classical
  exact ObservationTree.rec
    (motive := fun _ => Transcript A → Option R)
    (fun value _ => some value)
    (fun query _ proceed replies =>
      match replies with
      | [] => none
      | reply :: remaining =>
          if equal : reply.1 = query then
            proceed (equal ▸ reply.2) remaining
          else none)
    tree

@[simp]
theorem branchTranscript_leaf (value : R) (system : DDS A)
    (prior : List A.query) :
    branchTranscript (.leaf value) system prior = [] :=
  rfl

@[simp]
theorem branchTranscript_query (query : A.query)
    (after : Option (A.answer query) → ObservationTree A R)
    (system : DDS A) (prior : List A.query) :
    branchTranscript (.query query after) system prior =
      let reply := Attachment.innerReplyAt system prior query
      ⟨query, reply⟩ ::
        branchTranscript (after reply) system (prior ++ [query]) :=
  rfl

@[simp]
theorem toDDE_nil_query (query : A.query)
    (after : Option (A.answer query) → ObservationTree A R) :
    toDDE (.query query after) [] = some query := by
  simp [toDDE]

@[simp]
theorem toDDE_cons_query (query : A.query)
    (after : Option (A.answer query) → ObservationTree A R)
    (reply : Option (A.answer query)) (remaining : Transcript A) :
    toDDE (.query query after) (⟨query, reply⟩ :: remaining) =
      toDDE (after reply) remaining := by
  classical
  simp [toDDE]

@[simp]
theorem resultFromTranscript_cons_query (query : A.query)
    (after : Option (A.answer query) → ObservationTree A R)
    (reply : Option (A.answer query)) (remaining : Transcript A) :
    resultFromTranscript (.query query after)
        (⟨query, reply⟩ :: remaining) =
      resultFromTranscript (after reply) remaining := by
  classical
  simp [resultFromTranscript]

@[simp]
theorem evaluate_query (query : A.query)
    (after : Option (A.answer query) → ObservationTree A R)
    (system : DDS A) (prior : List A.query) :
    evaluate (.query query after) system prior =
      let reply := Attachment.innerReplyAt system prior query
      evaluate (after reply) system (prior ++ [query]) :=
  rfl

theorem toDDE_branchTranscript (tree : ObservationTree A R)
    (system : DDS A) (prior : List A.query) :
    toDDE tree (branchTranscript tree system prior) = none := by
  induction tree generalizing prior with
  | leaf value => rfl
  | query query after inductionHypothesis =>
      let reply := Attachment.innerReplyAt system prior query
      rw [branchTranscript_query, toDDE_cons_query]
      exact inductionHypothesis reply (prior ++ [query])

theorem toDDE_branchTranscript_take
    (tree : ObservationTree A R) (system : DDS A)
    (prior : List A.query) (round : Nat)
    (within : round < (branchTranscript tree system prior).length) :
    toDDE tree ((branchTranscript tree system prior).take round) =
      some ((branchTranscript tree system prior)[round].1) := by
  induction tree generalizing prior round with
  | leaf value => simp at within
  | query query after inductionHypothesis =>
      let reply := Attachment.innerReplyAt system prior query
      cases round with
      | zero => rfl
      | succ round =>
          have tailWithin : round <
              (branchTranscript (after reply) system
                (prior ++ [query])).length := by
            simpa only [branchTranscript_query, List.length_cons,
              Nat.succ_lt_succ_iff] using within
          simp only [branchTranscript_query, List.take_succ_cons,
            toDDE_cons_query, List.getElem_cons_succ]
          exact inductionHypothesis reply (prior ++ [query]) round tailWithin

theorem branchTranscript_get_reply
    (tree : ObservationTree A R) (system : DDS A)
    (prior : List A.query) (round : Nat)
    (within : round < (branchTranscript tree system prior).length) :
    (branchTranscript tree system prior)[round].2 =
      Attachment.innerReplyAt system
        (prior ++ transcriptInputs
          ((branchTranscript tree system prior).take round))
        ((branchTranscript tree system prior)[round].1) := by
  induction tree generalizing prior round with
  | leaf value => simp at within
  | query query after inductionHypothesis =>
      let reply := Attachment.innerReplyAt system prior query
      cases round with
      | zero =>
          have first :
              (branchTranscript (.query query after) system prior)[0] =
                ⟨query, reply⟩ := by
            simp only [branchTranscript_query, List.getElem_cons_zero]
            rfl
          rw [first]
          simp only [List.take_zero, transcriptInputs, List.map_nil,
            List.append_nil]
          rfl
      | succ round =>
          have tailWithin : round <
              (branchTranscript (after reply) system
                (prior ++ [query])).length := by
            simpa only [branchTranscript_query, List.length_cons,
              Nat.succ_lt_succ_iff] using within
          have tailEqual := inductionHypothesis reply (prior ++ [query])
            round tailWithin
          have current :
              (branchTranscript (.query query after) system prior)[round + 1] =
                (branchTranscript (after reply) system
                  (prior ++ [query]))[round] := by
            simp only [branchTranscript_query, List.getElem_cons_succ]
            rfl
          rw [current]
          dsimp only [reply] at tailEqual
          simpa only [branchTranscript_query, List.take_succ_cons,
            transcriptInputs, List.map_cons, List.map_take,
            List.append_assoc, List.singleton_append] using tailEqual

theorem resultFromTranscript_branchTranscript
    (tree : ObservationTree A R) (system : DDS A)
    (prior : List A.query) :
    resultFromTranscript tree (branchTranscript tree system prior) =
      some (evaluate tree system prior) := by
  induction tree generalizing prior with
  | leaf value => rfl
  | query query after inductionHypothesis =>
      let reply := Attachment.innerReplyAt system prior query
      rw [branchTranscript_query, resultFromTranscript_cons_query,
        evaluate_query]
      exact inductionHypothesis reply (prior ++ [query])

theorem transcript_toDDE_eq_take
    (tree : ObservationTree A R) (system : DDS A) (rounds : Nat) :
    transcript system tree.toDDE rounds =
      (branchTranscript tree system []).take rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [transcript_succ, inductionHypothesis]
      by_cases within : rounds < (branchTranscript tree system []).length
      · rw [toDDE_branchTranscript_take tree system [] rounds within]
        simp only
        have replyEqual :=
          branchTranscript_get_reply tree system [] rounds within
        simp only [List.nil_append] at replyEqual
        rw [← replyEqual]
        simpa only [Sigma.eta] using List.take_append_getElem within
      · have lengthLe : (branchTranscript tree system []).length ≤ rounds :=
          Nat.le_of_not_gt within
        have successorLengthLe :
            (branchTranscript tree system []).length ≤ rounds + 1 :=
          lengthLe.trans (Nat.le_succ rounds)
        rw [(List.take_eq_self_iff _).mpr lengthLe,
          toDDE_branchTranscript tree system [],
          (List.take_eq_self_iff _).mpr successorLengthLe]

end ObservationTree

namespace Internal

/-- Transport the converter's outer reply to the query selected by the outer
history represented at the same observation node. -/
def alignedOuterReply
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {outerHistory : History A} {history : DDC.History A B}
    (aligned : history.lastOuter = outerHistory.last)
    (reply : Option (A.answer history.lastOuter)) : DDC.History.InnerReply A :=
  ⟨outerHistory.last,
    cast (congrArg (fun query => Option (A.answer query)) aligned) reply⟩

/-- One finite outer observation represented as an inner observation tree.
This relation is purely between complete functions and finite histories. -/
inductive RepresentsObservation
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (environment : DDE A) :
    Nat → History A → DDC.History A B → List B.query →
      Transcript A →
      ObservationTree B (Transcript A) → Prop
  | noRounds {outerHistory history innerPrior outerTranscript} :
      RepresentsObservation converter environment 0 outerHistory history
        innerPrior outerTranscript (.leaf outerTranscript)
  | innerQuery {remaining outerHistory history innerPrior outerTranscript query}
      {after : Option (B.answer query) →
        ObservationTree B (Transcript A)}
      (responds : Sum.inl query ∈ converter history)
      (branches : ∀ reply,
        RepresentsObservation converter environment remaining outerHistory
          (history.snocInner query reply) (innerPrior ++ [query])
          outerTranscript (after reply)) :
      RepresentsObservation converter environment remaining outerHistory
        history innerPrior outerTranscript (.query query after)
  | outerLast {outerHistory history innerPrior outerTranscript reply}
      (aligned : history.lastOuter = outerHistory.last)
      (responds : Sum.inr reply ∈ converter history) :
      RepresentsObservation converter environment 1 outerHistory history
        innerPrior outerTranscript
        (.leaf (outerTranscript ++
          [alignedOuterReply aligned reply]))
  | outerStop {remaining outerHistory history innerPrior outerTranscript reply}
      (aligned : history.lastOuter = outerHistory.last)
      (responds : Sum.inr reply ∈ converter history)
      (stops : environment
        (outerTranscript ++ [alignedOuterReply aligned reply]) = none) :
      RepresentsObservation converter environment (remaining + 2)
        outerHistory history innerPrior outerTranscript
        (.leaf (outerTranscript ++
          [alignedOuterReply aligned reply]))
  | outerNext {remaining outerHistory history innerPrior outerTranscript reply
      nextOuter tree}
      (aligned : history.lastOuter = outerHistory.last)
      (responds : Sum.inr reply ∈ converter history)
      (continues : environment
        (outerTranscript ++ [alignedOuterReply aligned reply]) =
          some nextOuter)
      (tail : RepresentsObservation converter environment (remaining + 1)
        (History.snoc outerHistory nextOuter)
        (history.snocOuter nextOuter) innerPrior
        (outerTranscript ++ [alignedOuterReply aligned reply]) tree) :
      RepresentsObservation converter environment (remaining + 2)
        outerHistory history innerPrior outerTranscript tree

theorem exists_representsObservationFrom
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (environment : DDE A) :
    ∀ (remaining : Nat) (outerHistory : History A)
      (history : DDC.History A B) (innerPrior : List B.query)
      (outerTranscript : Transcript A),
      history.lastOuter = outerHistory.last →
      DDC.Raw.Admissible converter.toFun history →
      ∃ tree, RepresentsObservation converter environment remaining
        outerHistory history innerPrior outerTranscript tree := by
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining outerInduction =>
      intro outerHistory history
      induction history using converter.branchFinite.induction with
      | h history innerInduction =>
          intro innerPrior outerTranscript aligned admissible
          cases remaining with
          | zero =>
              exact ⟨.leaf outerTranscript,
                RepresentsObservation.noRounds⟩
          | succ remaining =>
              cases responseEqual : converter.response history admissible with
              | inl query =>
                  have responds : Sum.inl query ∈ converter history :=
                    responseEqual ▸ converter.response_mem history admissible
                  have branchExists : ∀ reply : Option (B.answer query),
                      ∃ tree, RepresentsObservation converter environment
                        (remaining + 1) outerHistory
                        (history.snocInner query reply)
                        (innerPrior ++ [query]) outerTranscript tree := by
                    intro reply
                    have nextAdmissible : DDC.Raw.Admissible converter.toFun
                        (history.snocInner query reply) :=
                      .afterInner admissible responds reply
                    have descends : DDC.Raw.InnerContinuation converter.toFun
                        (history.snocInner query reply) history :=
                      ⟨query, reply, responds, rfl⟩
                    exact innerInduction _ descends (innerPrior ++ [query])
                      outerTranscript (by simpa using aligned) nextAdmissible
                  let after := fun reply => (branchExists reply).choose
                  have branches : ∀ reply,
                      RepresentsObservation converter environment
                        (remaining + 1) outerHistory
                        (history.snocInner query reply)
                        (innerPrior ++ [query]) outerTranscript (after reply) :=
                    fun reply => (branchExists reply).choose_spec
                  exact ⟨.query query after,
                    RepresentsObservation.innerQuery responds branches⟩
              | inr reply =>
                  have responds : Sum.inr reply ∈ converter history :=
                    responseEqual ▸ converter.response_mem history admissible
                  cases remaining with
                  | zero =>
                      exact ⟨.leaf (outerTranscript ++
                          [alignedOuterReply aligned reply]),
                        RepresentsObservation.outerLast aligned responds⟩
                  | succ remaining =>
                      let extended := outerTranscript ++
                        [alignedOuterReply aligned reply]
                      cases continuesEqual : environment extended with
                      | none =>
                          exact ⟨.leaf extended,
                            RepresentsObservation.outerStop aligned responds
                              continuesEqual⟩
                      | some nextOuter =>
                          have nextAdmissible : DDC.Raw.Admissible
                              converter.toFun (history.snocOuter nextOuter) :=
                            .afterOuter admissible responds nextOuter
                          have decreases : remaining + 1 < remaining + 2 := by
                            omega
                          obtain ⟨tree, tail⟩ := outerInduction
                            (remaining + 1) decreases
                            (History.snoc outerHistory nextOuter)
                            (history.snocOuter nextOuter) innerPrior extended
                            (by simp) nextAdmissible
                          exact ⟨tree,
                            RepresentsObservation.outerNext aligned responds
                              continuesEqual tail⟩

def appendOuterHistory {A : Interface.{u, v}}
    (history : History A) (remaining : List A.query) : History A :=
  ⟨history.1 ++ remaining, by simp [history.2]⟩

@[simp]
theorem appendOuterHistory_nil {A : Interface.{u, v}}
    (history : History A) : appendOuterHistory history [] = history := by
  apply History.ext
  simp [appendOuterHistory]

theorem appendOuterHistory_cons {A : Interface.{u, v}}
    (history : History A) (next : A.query) (remaining : List A.query) :
    appendOuterHistory history (next :: remaining) =
      appendOuterHistory (History.snoc history next) remaining := by
  apply History.ext
  simp [appendOuterHistory, History.snoc, List.append_assoc]

/-- Every compatible suffix at the current histories closes to a compatible
full transcript at the corresponding extended outer history. -/
def PrefixContext {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B)
    (outerHistory : History A) (history : DDC.History A B)
    (innerPrior : List B.query) : Prop :=
  ∀ (remaining : List A.query) (inputs : List (DDC.History.Input A B))
    (responses : List (Attachment.Response A B)) (final : DDC.History.InnerReply A),
    Attachment.CompatibleFrom converter system history innerPrior remaining
        inputs responses final →
      ∃ full : Attachment.Transcript A B,
        Attachment.Compatible converter system (appendOuterHistory outerHistory remaining)
          full ∧ full.final = final

theorem PrefixContext.start
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (system : DDS B) (firstOuter : A.query) :
    PrefixContext converter system (History.singleton firstOuter)
      (DDC.History.singleton firstOuter) [] := by
  intro remaining inputs responses final compatible
  let full : Attachment.Transcript A B :=
    { inputs := inputs
      responses := responses
      final := final }
  refine ⟨full, ?_, rfl⟩
  change Attachment.CompatibleFrom converter system
    (DDC.History.singleton
      (History.head (appendOuterHistory
        (History.singleton firstOuter) remaining))) []
    (History.tail
      (appendOuterHistory (History.singleton firstOuter) remaining))
    inputs responses final
  simpa [appendOuterHistory, History.singleton, History.head,
    History.tail] using compatible

theorem PrefixContext.afterInner
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {system : DDS B}
    {outerHistory : History A} {history : DDC.History A B}
    {innerPrior : List B.query}
    (context : PrefixContext converter system outerHistory history innerPrior)
    {query : B.query} (responds : Sum.inl query ∈ converter history) :
    PrefixContext converter system outerHistory
      (history.snocInner query (Attachment.innerReplyAt system innerPrior query))
      (innerPrior ++ [query]) := by
  intro remaining inputs responses final compatible
  exact context remaining (history.lastInput :: inputs)
    (Sum.inl query :: responses) final
    (Attachment.CompatibleFrom.innerQuery responds compatible)

theorem PrefixContext.afterOuter
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {system : DDS B}
    {outerHistory : History A} {history : DDC.History A B}
    {innerPrior : List B.query}
    (context : PrefixContext converter system outerHistory history innerPrior)
    {reply : Option (A.answer history.lastOuter)}
    (responds : Sum.inr reply ∈ converter history)
    (nextOuter : A.query) :
    PrefixContext converter system
      (History.snoc outerHistory nextOuter)
      (history.snocOuter nextOuter) innerPrior := by
  intro remaining inputs responses final compatible
  obtain ⟨full, fullCompatible, finalEqual⟩ :=
    context (nextOuter :: remaining) (history.lastInput :: inputs)
      (Sum.inr ⟨history.lastOuter, reply⟩ :: responses) final
      (Attachment.CompatibleFrom.outerNext responds compatible)
  refine ⟨full, ?_, finalEqual⟩
  rw [appendOuterHistory_cons] at fullCompatible
  exact fullCompatible

theorem innerReplyAt_eq_of_history
    {A : Interface.{u, v}} (system : DDS A)
    (prior : List A.query) (history : History A)
    (equal : Attachment.innerHistory prior history.last = history) :
    Attachment.innerReplyAt system prior history.last = system history := by
  apply DDC.History.reply_eq_of_packed_eq
  calc
    (⟨history.last, Attachment.innerReplyAt system prior history.last⟩ : DDC.History.InnerReply A) =
        ⟨(Attachment.innerHistory prior history.last).last,
          system (Attachment.innerHistory prior history.last)⟩ :=
      Attachment.packed_innerReplyAt system prior history.last
    _ = ⟨history.last, system history⟩ := by rw [equal]

theorem transport_option_eq_cast
    {Q : Type u} (answer : Q → Type v) {left right : Q}
    (equal : left = right) (reply : Option (answer left)) :
    equal ▸ reply =
      cast (congrArg (fun query => Option (answer query)) equal) reply := by
  cases equal
  rfl

theorem PrefixContext.finish
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {system : DDS B}
    {outerHistory : History A} {history : DDC.History A B}
    {innerPrior : List B.query}
    (context : PrefixContext converter system outerHistory history innerPrior)
    (aligned : history.lastOuter = outerHistory.last)
    {reply : Option (A.answer history.lastOuter)}
    (responds : Sum.inr reply ∈ converter history) :
    (alignedOuterReply aligned reply).2 =
      applySystem converter system outerHistory := by
  obtain ⟨full, compatible, finalEqual⟩ :=
    context [] [history.lastInput]
      [Sum.inr ⟨history.lastOuter, reply⟩]
      ⟨history.lastOuter, reply⟩
      (Attachment.CompatibleFrom.outerLast responds)
  rw [appendOuterHistory_nil] at compatible
  have selected : Attachment.selectReply outerHistory.last full.final =
      (alignedOuterReply aligned reply).2 := by
    rw [finalEqual]
    classical
    unfold Attachment.selectReply alignedOuterReply
    rw [dif_pos aligned]
    exact transport_option_eq_cast A.answer aligned reply
  have finalQuery :=
    Attachment.Compatible.final_query_eq_last (compatible := compatible)
  have selectedFinal := Attachment.selectReply_heq_second
    outerHistory.last full.final finalQuery
  have finalEqual : HEq full.final.2 (alignedOuterReply aligned reply).2 :=
    selectedFinal.symm.trans (heq_of_eq selected)
  exact ((applySystem_eq_iff converter system outerHistory _).mpr
    ⟨full, compatible, finalEqual⟩).symm

theorem RepresentsObservation.evaluate_eq_continue
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    {converter : DDC A B} {environment : DDE A}
    {remaining : Nat} {outerHistory : History A}
    {history : DDC.History A B} {innerPrior : List B.query}
    {outerTranscript : Transcript A}
    {tree : ObservationTree B (Transcript A)}
    (represents : RepresentsObservation converter environment remaining
      outerHistory history innerPrior outerTranscript tree)
    (system : DDS B)
    (context : PrefixContext converter system outerHistory history innerPrior)
    (inputsEqual : transcriptInputs outerTranscript ++
        [outerHistory.last] = outerHistory.1)
    (nextOuter : environment outerTranscript = some outerHistory.last) :
    tree.evaluate system innerPrior =
      continueTranscript (applySystem converter system) environment remaining
        outerTranscript := by
  induction represents with
  | noRounds => rfl
  | @innerQuery remaining outerHistory history innerPrior outerTranscript
      query after responds branches inductionHypothesis =>
      let reply := Attachment.innerReplyAt system innerPrior query
      rw [ObservationTree.evaluate_query]
      exact inductionHypothesis reply
        (PrefixContext.afterInner context responds) inputsEqual nextOuter
  | @outerLast outerHistory history innerPrior outerTranscript reply aligned
      responds =>
      let outerReply := alignedOuterReply aligned reply
      have outerReplyEta :
          (⟨outerHistory.last, outerReply.2⟩ : DDC.History.InnerReply A) = outerReply := by
        rfl
      have replyEqual : outerReply.2 =
          applySystem converter system outerHistory :=
        PrefixContext.finish context aligned responds
      have historyEqual :
          Attachment.innerHistory (transcriptInputs outerTranscript) outerHistory.last =
            outerHistory :=
        History.ext inputsEqual
      have systemReplyEqual :
          Attachment.innerReplyAt (applySystem converter system)
              (transcriptInputs outerTranscript) outerHistory.last =
            outerReply.2 :=
        (innerReplyAt_eq_of_history _ _ _ historyEqual).trans replyEqual.symm
      change outerTranscript ++ [outerReply] =
        extendTranscript (applySystem converter system) environment
          outerTranscript
      simp only [extendTranscript, nextOuter, systemReplyEqual]
      rw [outerReplyEta]
  | @outerStop remaining outerHistory history innerPrior outerTranscript reply
      aligned responds stops =>
      let outerReply := alignedOuterReply aligned reply
      have outerReplyEta :
          (⟨outerHistory.last, outerReply.2⟩ : DDC.History.InnerReply A) = outerReply := by
        rfl
      have replyEqual : outerReply.2 =
          applySystem converter system outerHistory :=
        PrefixContext.finish context aligned responds
      have historyEqual :
          Attachment.innerHistory (transcriptInputs outerTranscript) outerHistory.last =
            outerHistory :=
        History.ext inputsEqual
      have systemReplyEqual :
          Attachment.innerReplyAt (applySystem converter system)
              (transcriptInputs outerTranscript) outerHistory.last =
            outerReply.2 :=
        (innerReplyAt_eq_of_history _ _ _ historyEqual).trans replyEqual.symm
      let extended := outerTranscript ++ [outerReply]
      have firstExtension :
          extendTranscript (applySystem converter system) environment
            outerTranscript = extended := by
        simp only [extendTranscript, nextOuter, systemReplyEqual, extended]
        rw [outerReplyEta]
      have fixed :
          extendTranscript (applySystem converter system) environment extended =
            extended := by
        unfold extendTranscript
        rw [stops]
      change extended = continueTranscript _ _ (remaining + 2) outerTranscript
      rw [show remaining + 2 = (remaining + 1) + 1 by omega,
        continueTranscript_succ_first, firstExtension,
        continueTranscript_eq_of_fixed _ _ _ fixed]
  | @outerNext remaining outerHistory history innerPrior outerTranscript reply
      nextOuterValue tree aligned responds continues tail inductionHypothesis =>
      let outerReply := alignedOuterReply aligned reply
      have outerReplyEta :
          (⟨outerHistory.last, outerReply.2⟩ : DDC.History.InnerReply A) = outerReply := by
        rfl
      have replyEqual : outerReply.2 =
          applySystem converter system outerHistory :=
        PrefixContext.finish context aligned responds
      have historyEqual :
          Attachment.innerHistory (transcriptInputs outerTranscript) outerHistory.last =
            outerHistory :=
        History.ext inputsEqual
      have systemReplyEqual :
          Attachment.innerReplyAt (applySystem converter system)
              (transcriptInputs outerTranscript) outerHistory.last =
            outerReply.2 :=
        (innerReplyAt_eq_of_history _ _ _ historyEqual).trans replyEqual.symm
      let extended := outerTranscript ++ [outerReply]
      have firstExtension :
          extendTranscript (applySystem converter system) environment
            outerTranscript = extended := by
        simp only [extendTranscript, nextOuter, systemReplyEqual, extended]
        rw [outerReplyEta]
      have nextInputsEqual :
          transcriptInputs extended ++
              [(History.snoc outerHistory nextOuterValue).last] =
            (History.snoc outerHistory nextOuterValue).1 := by
        have appended := congrArg (fun values => values ++ [nextOuterValue])
          inputsEqual
        simpa only [extended, outerReply, alignedOuterReply, transcriptInputs,
          List.map_append, List.map_cons, List.map_nil,
          History.last_snoc, History.coe_snoc,
          List.append_assoc] using appended
      have tailEqual := inductionHypothesis
        (PrefixContext.afterOuter context responds nextOuterValue)
        nextInputsEqual
        (by simpa only [History.last_snoc] using continues)
      change tree.evaluate system innerPrior =
        continueTranscript _ _ (remaining + 2) outerTranscript
      rw [show remaining + 2 = (remaining + 1) + 1 by omega,
        continueTranscript_succ_first, firstExtension]
      exact tailEqual

theorem transcript_eq_nil_of_initial_stop
    {A : Interface.{u, v}} (system : DDS A) (environment : DDE A)
    (stops : environment [] = none) :
    ∀ rounds, transcript system environment rounds = [] := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [transcript_succ, inductionHypothesis]
      simp [stops]

end Internal

structure ObservationFactorization
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (environment : DDE A) (outerRounds : Nat) where
  tree : ObservationTree B (Transcript A)
  correct : ∀ system : DDS B,
    tree.evaluate system [] =
      transcript (applySystem converter system) environment outerRounds

noncomputable def observationFactorization
    {A : Interface.{u, v}} {B : Interface.{w, z}}
    (converter : DDC A B) (environment : DDE A) (outerRounds : Nat) :
    ObservationFactorization converter environment outerRounds := by
  classical
  cases outerRounds with
  | zero =>
      exact
        { tree := .leaf []
          correct := fun _ => rfl }
  | succ remaining =>
      cases nextOuter : environment [] with
      | none =>
          exact
            { tree := .leaf []
              correct := fun system =>
                (Internal.transcript_eq_nil_of_initial_stop
                  (applySystem converter system) environment nextOuter
                  (remaining + 1)).symm }
      | some firstOuter =>
          let outerHistory := History.singleton firstOuter
          let history := DDC.History.singleton (B := B) firstOuter
          have startAdmissible : DDC.Raw.Admissible converter.toFun history :=
            .start firstOuter
          let existence := Internal.exists_representsObservationFrom converter environment
            (remaining + 1) outerHistory history [] [] (by rfl)
              startAdmissible
          let tree := existence.choose
          have represents := existence.choose_spec
          refine
            { tree := tree
              correct := ?_ }
          intro system
          have evaluates := Internal.RepresentsObservation.evaluate_eq_continue
            represents system
            (Internal.PrefixContext.start converter system firstOuter)
            (by rfl)
            (by
              change environment [] = some firstOuter
              exact nextOuter)
          exact evaluates.trans
            (transcript_eq_continue (applySystem converter system)
              environment (remaining + 1)).symm

namespace DDC.Internal

/-- The inner DDE induced by one finite outer observation. -/
noncomputable def composeDDEAt
    {A : Interface.{u, v}} {B : Interface.{w, z}} (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat) : DDE B :=
  (observationFactorization converter environment outerRounds).tree.toDDE

/-- Recover the represented outer transcript from a complete inner
transcript. -/
noncomputable def composedTranscriptAt
    {A : Interface.{u, v}} {B : Interface.{w, z}} (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat)
    (innerTranscript : Transcript B) : Transcript A :=
  ((observationFactorization converter environment outerRounds).tree
    |>.resultFromTranscript innerTranscript).getD []

/-- The finite branch length selected by one concrete inner DDS. -/
noncomputable def innerRoundsFor
    {A : Interface.{u, v}} {B : Interface.{w, z}} (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat) (system : DDS B) : Nat :=
  (ObservationTree.branchTranscript
    (observationFactorization converter environment outerRounds).tree
    system []).length

/-- DDE absorption: the outer transcript after attachment is a
deterministic function of one sufficiently long inner transcript. -/
theorem transcript_applySystem_of_innerRounds_le
    {A : Interface.{u, v}} {B : Interface.{w, z}} (converter : DDC A B)
    (environment : DDE A) (outerRounds innerRounds : Nat)
    (system : DDS B)
    (enough : DDC.Internal.innerRoundsFor converter environment outerRounds system ≤
      innerRounds) :
    transcript (applySystem converter system) environment outerRounds =
      DDC.Internal.composedTranscriptAt converter environment outerRounds
        (transcript system (DDC.Internal.composeDDEAt converter environment outerRounds)
          innerRounds) := by
  -- Select the finite observation tree determined by the converter and outer DDE.
  let factorization :=
    observationFactorization converter environment outerRounds
  -- The chosen inner-round bound exposes the entire branch for this DDS.
  have innerTranscript :
      transcript system factorization.tree.toDDE innerRounds =
        ObservationTree.branchTranscript factorization.tree system [] := by
    rw [ObservationTree.transcript_toDDE_eq_take]
    exact (List.take_eq_self_iff _).mpr enough
  -- Decode that complete branch and apply the factorization equation.
  rw [DDC.Internal.composeDDEAt, DDC.Internal.composedTranscriptAt]
  change transcript (applySystem converter system) environment outerRounds =
    (ObservationTree.resultFromTranscript factorization.tree
      (transcript system factorization.tree.toDDE innerRounds)).getD []
  rw [innerTranscript,
    ObservationTree.resultFromTranscript_branchTranscript]
  exact (factorization.correct system).symm

end DDC.Internal

/-- The finite transcript law is ordinary deterministic pushforward. -/
noncomputable def trLaw {A : Interface.{u, v}}
    (environment : DDE A) (rounds : Nat)
    (law : Distribution (DDS A)) : Distribution (Transcript A) :=
  Distribution.fTransform (fun system => transcript system environment rounds)
    law

/-- Every finite observation satisfies data processing. -/
theorem statDist_trLaw_le {A : Interface.{u, v}}
    (environment : DDE A) (rounds : Nat)
    (left right : Distribution (DDS A)) :
    Probability.statDist (trLaw environment rounds left)
        (trLaw environment rounds right) ≤
      Probability.statDist left right :=
  Probability.statDist_fTransform_le left right
    (fun system => transcript system environment rounds)


end RandomSystems.Ambient
