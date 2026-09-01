/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Observation
import RandomSystems.Converter.Serial
import Probability.Lift
import Probability.StatisticalDistance
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false

/-!
# Cumulative random systems at query-indexed interfaces

Liu--Maurer, Definition 2 (printed p. 8), says: “An (X,Y)-random
system R is a sequence of conditional probability distributions.” The carrier
below stores the equivalent cumulative cylinder masses. This removes the
arbitrary choice of a conditional law at a probability-zero history. Attempted
queries and the optional rejection reply none remain observable.

A normalized finite-support law over deterministic systems is retained only as
presentation data. Its direct interpretation in the cumulative carrier
identifies exactly finite functional-DDE observational equivalence; it is not a
second resource carrier. Maurer--Renner 2016 leaves the carrier abstract but
requires converter attachment to be total, serial, and non-expanding. Jost's
inside-query bound is a sufficient specialization; branch-finiteness of the
current DDCs is used by the separate deterministic-action module.
-/

namespace RandomSystems.Ambient

noncomputable section

open Probability
open scoped ENNReal

universe u v w z p q

/-- A normalized finite-support probability law over query-indexed DDSs. -/
abbrev PDS (A : Interface.{u, v}) :=
  Distribution.ProbDist (DDS A)

namespace PDS

variable {A : Interface.{u, v}} {B : Interface.{w, z}}

/-- The normalized point law concentrated on one DDS. -/
def ofDDS (system : DDS A) : PDS A :=
  ⟨Finsupp.single system 1, Distribution.isProbDist_single system⟩

/-- The normalized law obtained by sampling a total answer function uniformly
and viewing it as a DDS. -/
def uniformFunction (A : Interface.{u, v})
    [Fintype ((query : A.query) → A.answer query)]
    [Nonempty ((query : A.query) → A.answer query)] : PDS A :=
  ⟨Distribution.fTransform DDS.ofFunction
      (Distribution.uniform ((query : A.query) → A.answer query)),
    Distribution.fTransform_isProbDist DDS.ofFunction
      Distribution.uniform_isProbDist⟩

@[simp]
theorem coe_uniformFunction (A : Interface.{u, v})
    [Fintype ((query : A.query) → A.answer query)]
    [Nonempty ((query : A.query) → A.answer query)] :
    (uniformFunction A : Distribution (DDS A)) =
      Distribution.fTransform DDS.ofFunction
        (Distribution.uniform ((query : A.query) → A.answer query)) :=
  rfl

/-- Deterministic transformation of a normalized PDS. -/
def fTransform (transform : DDS A → DDS B) (system : PDS A) : PDS B :=
  ⟨Distribution.fTransform transform system.1,
    Distribution.fTransform_isProbDist transform system.2⟩

@[simp]
theorem fTransform_ofDDS_eq
    (transform : DDS A → DDS B) (system : DDS A) :
    fTransform transform (ofDDS system) = ofDDS (transform system) := by
  apply Subtype.ext
  simp [fTransform, ofDDS, Distribution.fTransform]

@[simp]
theorem fTransform_id_eq (system : PDS A) :
    fTransform id system = system := by
  apply Subtype.ext
  exact Distribution.fTransform_id system.1

theorem fTransform_comp_eq {C : Interface.{p, q}}
    (outer : DDS B → DDS C) (inner : DDS A → DDS B) (system : PDS A) :
    fTransform outer (fTransform inner system) =
      fTransform (outer ∘ inner) system := by
  apply Subtype.ext
  exact Distribution.fTransform_fTransform outer inner system.1

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when
applied as an interface i of a resource, induces a function Φ → Φ.” Here the
function on normalized PDSs is the pushforward of deterministic attachment. -/
def apply (converter : DDC A B) (system : PDS B) : PDS A :=
  fTransform (applySystem converter) system

@[simp]
theorem apply_ofDDS_eq (converter : DDC A B) (system : DDS B) :
    apply converter (ofDDS system) = ofDDS (applySystem converter system) :=
  fTransform_ofDDS_eq _ _

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), says that the identity
converter “induces the identity function Φ → Φ”. -/
@[simp]
theorem apply_forwarding_eq (system : PDS A) :
    apply (DDC.forwarding A) system = system := by
  -- Replace deterministic forwarding attachment by the identity function.
  unfold apply
  rw [show applySystem (DDC.forwarding A) = id by
    funext deterministicSystem
    exact applySystem_forwarding_eq A deterministicSystem]
  -- Pushforward by the identity leaves the normalized law unchanged.
  exact fTransform_id_eq system

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), requires
“(β ◦ α)ⁱ R = βⁱ (αⁱ R)”. -/
theorem apply_serial_eq {A B C : Interface.{u, v}}
    (outer : DDC A B) (inner : DDC B C) (system : PDS C) :
    apply (DDC.serial outer inner) system =
      apply outer (apply inner system) := by
  -- Combine the two deterministic distribution transformations.
  unfold apply
  rw [fTransform_comp_eq]
  -- The underlying deterministic functions agree by serial attachment.
  congr 1
  funext deterministicSystem
  exact DDC.applySystem_serial_eq outer inner deterministicSystem

/-- The finite transcript law observed from a normalized PDS. -/
def trLaw (environment : DDE A) (rounds : Nat)
    (system : PDS A) : Distribution (Transcript A) :=
  RandomSystems.Ambient.trLaw environment rounds system.1

theorem trLaw_weight_eq_one (environment : DDE A)
    (rounds : Nat) (system : PDS A) :
    (trLaw environment rounds system).weight = 1 := by
  rw [trLaw, RandomSystems.Ambient.trLaw,
    Distribution.weight_fTransform]
  exact system.2.weight_eq

def commonInnerRounds (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat)
    (left right : PDS B) : Nat := by
  classical
  exact (left.1.support ∪ right.1.support).sup
    (DDC.Internal.innerRoundsFor converter environment outerRounds)

theorem innerRoundsFor_le_commonInnerRounds_left
    (converter : DDC A B) (environment : DDE A) (outerRounds : Nat)
    (left right : PDS B) {system : DDS B}
    (supported : system ∈ left.1.support) :
    DDC.Internal.innerRoundsFor converter environment outerRounds system ≤
      commonInnerRounds converter environment outerRounds left right := by
  classical
  rw [commonInnerRounds]
  exact Finset.le_sup
    (f := DDC.Internal.innerRoundsFor converter environment outerRounds)
    (Finset.mem_union_left right.1.support supported)

theorem innerRoundsFor_le_commonInnerRounds_right
    (converter : DDC A B) (environment : DDE A) (outerRounds : Nat)
    (left right : PDS B) {system : DDS B}
    (supported : system ∈ right.1.support) :
    DDC.Internal.innerRoundsFor converter environment outerRounds system ≤
      commonInnerRounds converter environment outerRounds left right := by
  classical
  rw [commonInnerRounds]
  exact Finset.le_sup
    (f := DDC.Internal.innerRoundsFor converter environment outerRounds)
    (Finset.mem_union_right left.1.support supported)

theorem trLaw_apply_of_support (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat)
    (left right system : PDS B)
    (side : ∀ deterministicSystem ∈ system.1.support,
      DDC.Internal.innerRoundsFor converter environment outerRounds
          deterministicSystem ≤
        commonInnerRounds converter environment outerRounds left right) :
    trLaw environment outerRounds (apply converter system) =
      Distribution.fTransform
        (DDC.Internal.composedTranscriptAt converter environment outerRounds)
        (trLaw
          (DDC.Internal.composeDDEAt converter environment outerRounds)
          (commonInnerRounds converter environment outerRounds left right)
          system) := by
  unfold PDS.trLaw RandomSystems.Ambient.trLaw apply fTransform
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro deterministicSystem supported
  exact DDC.Internal.transcript_applySystem_of_innerRounds_le converter environment
    outerRounds _ deterministicSystem (side deterministicSystem supported)

/-- The ambient distinguishing advantage obtained by taking the supremum over
total DDEs and finite observation lengths.

Lanzenberger, Definition 2.26 (printed p. 18), says that “the supremum is over
all compatible `(Y,X)`-DDE.”  His definition applies to two systems with the
same domain; the ambient definition below instead observes optional answers
on every attempted history. -/
noncomputable def advantage (left right : PDS A) : ℝ :=
  sSup (Set.range fun observation : DDE A × Nat =>
    Probability.statDist
      (trLaw observation.1 observation.2 left)
      (trLaw observation.1 observation.2 right))

lemma statDist_trLaw_le_advantage
    (left right : PDS A) (environment : DDE A) (rounds : Nat) :
    Probability.statDist (trLaw environment rounds left)
        (trLaw environment rounds right) ≤
      advantage left right := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro value ⟨⟨candidate, count⟩, rfl⟩
    calc
      Probability.statDist
          (trLaw candidate count left) (trLaw candidate count right) ≤
        (trLaw candidate count left).weight :=
          Probability.statDist_le_weight
            (by
              unfold trLaw RandomSystems.Ambient.trLaw
              exact left.2.nonNeg.fTransform _)
            (by
              unfold trLaw RandomSystems.Ambient.trLaw
              exact right.2.nonNeg.fTransform _)
      _ = 1 := trLaw_weight_eq_one candidate count left
  · exact ⟨(environment, rounds), rfl⟩

lemma advantage_nonneg (left right : PDS A) :
    0 ≤ advantage left right := by
  apply Real.sSup_nonneg
  rintro value ⟨⟨environment, rounds⟩, rfl⟩
  exact Probability.statDist_nonneg _ _

@[simp]
theorem advantage_self (system : PDS A) : advantage system system = 0 :=
  le_antisymm
    (Real.sSup_le (by
      rintro value ⟨⟨environment, rounds⟩, rfl⟩
      simp [Probability.statDist_self]) le_rfl)
    (advantage_nonneg system system)

theorem advantage_comm (left right : PDS A) :
    advantage left right = advantage right left := by
  unfold advantage
  apply congrArg sSup
  apply congrArg Set.range
  funext observation
  rw [Probability.statDist_symm_of_eq_weight _ _ (by
    rw [trLaw_weight_eq_one, trLaw_weight_eq_one])]

theorem advantage_triangle (left middle right : PDS A) :
    advantage left right ≤ advantage left middle + advantage middle right := by
  apply Real.sSup_le
  · rintro value ⟨⟨environment, rounds⟩, rfl⟩
    exact (Probability.statDist_triangle _ _ _).trans
      (add_le_add
        (statDist_trLaw_le_advantage left middle environment rounds)
        (statDist_trLaw_le_advantage middle right environment rounds))
  · exact add_nonneg (advantage_nonneg left middle)
      (advantage_nonneg middle right)

/-- Maurer--Renner 2016, Definition 2 (printed p. 11): “A metric d on Φ is
called non-expanding if d(αR, αS) ≤ d(R, S)”. -/
theorem advantage_apply_le (converter : DDC A B) (left right : PDS B) :
    advantage (apply converter left) (apply converter right) ≤
      advantage left right := by
  -- Fix an arbitrary outer environment and finite observation length.
  apply Real.sSup_le
  · rintro value ⟨⟨environment, rounds⟩, rfl⟩
    change Probability.statDist
      (trLaw environment rounds (apply converter left))
      (trLaw environment rounds (apply converter right)) ≤ advantage left right
  -- Factor both attached transcript laws through one common inner observation.
    rw [trLaw_apply_of_support converter environment rounds left right left
        (fun system supported =>
          innerRoundsFor_le_commonInnerRounds_left converter environment rounds
            left right supported),
      trLaw_apply_of_support converter environment rounds left right right
        (fun system supported =>
          innerRoundsFor_le_commonInnerRounds_right converter environment rounds
            left right supported)]
    calc
      Probability.statDist
          (Distribution.fTransform
            (DDC.Internal.composedTranscriptAt converter environment rounds)
            (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
              (commonInnerRounds converter environment rounds left right) left))
          (Distribution.fTransform
            (DDC.Internal.composedTranscriptAt converter environment rounds)
            (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
              (commonInnerRounds converter environment rounds left right)
              right)) ≤
          Probability.statDist
            (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
              (commonInnerRounds converter environment rounds left right)
              left)
            (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
              (commonInnerRounds converter environment rounds left right)
              right) :=
        Probability.statDist_fTransform_le _ _
          (DDC.Internal.composedTranscriptAt converter environment rounds)
      _ ≤ advantage left right :=
        statDist_trLaw_le_advantage left right
          (DDC.Internal.composeDDEAt converter environment rounds)
          (commonInnerRounds converter environment rounds left right)
  · exact advantage_nonneg left right

/-- Lanzenberger, Definition 2.17 (printed p. 16), requires agreement “for all
compatible `(Y,X)`-DDE.” This ambient relation retains the transcript-law
clause; the literal carrier separately retains the common-domain clause. -/
def equivalent (left right : PDS A) : Prop :=
  ∀ environment : DDE A, ∀ rounds : Nat,
    trLaw environment rounds left = trLaw environment rounds right

@[refl]
theorem equivalent_refl (system : PDS A) : equivalent system system :=
  fun _ _ => rfl

@[symm]
theorem equivalent_symm {left right : PDS A}
    (hypothesis : equivalent left right) : equivalent right left :=
  fun environment rounds => (hypothesis environment rounds).symm

@[trans]
theorem equivalent_trans {left middle right : PDS A}
    (first : equivalent left middle) (second : equivalent middle right) :
    equivalent left right :=
  fun environment rounds =>
    (first environment rounds).trans (second environment rounds)

/-- Finite-observation equivalence under total DDEs is preserved by DDC
attachment. -/
theorem equivalent_apply (converter : DDC A B)
    {left right : PDS B} (hypothesis : equivalent left right) :
    equivalent (apply converter left) (apply converter right) := by
  -- Fix an outer DDE and a finite observation length.
  intro environment rounds
  -- Factor both attached observations through one common inner DDE horizon.
  rw [trLaw_apply_of_support converter environment rounds left right left
      (fun system supported =>
        innerRoundsFor_le_commonInnerRounds_left converter environment rounds
          left right supported),
    trLaw_apply_of_support converter environment rounds left right right
      (fun system supported =>
        innerRoundsFor_le_commonInnerRounds_right converter environment rounds
          left right supported),
    hypothesis (DDC.Internal.composeDDEAt converter environment rounds)
      (commonInnerRounds converter environment rounds left right)]

theorem advantage_congr {left left' right right' : PDS A}
    (leftEquivalent : equivalent left left')
    (rightEquivalent : equivalent right right') :
    advantage left right = advantage left' right' := by
  unfold advantage
  apply congrArg sSup
  apply congrArg Set.range
  funext observation
  rw [leftEquivalent observation.1 observation.2,
    rightEquivalent observation.1 observation.2]

theorem equivalent_iff_advantage_eq_zero {left right : PDS A} :
    equivalent left right ↔ advantage left right = 0 := by
  constructor
  · intro hypothesis
    exact (advantage_congr hypothesis (equivalent_refl right)).trans
      (advantage_self right)
  · intro advantageZero environment rounds
    have distanceLe : Probability.statDist
        (trLaw environment rounds left)
        (trLaw environment rounds right) ≤ 0 :=
      (statDist_trLaw_le_advantage left right environment rounds).trans_eq
        advantageZero
    have distanceZero : Probability.statDist
        (trLaw environment rounds left)
        (trLaw environment rounds right) = 0 := by
      exact le_antisymm distanceLe (Probability.statDist_nonneg _ _)
    have reverseZero : Probability.statDist
        (trLaw environment rounds right)
        (trLaw environment rounds left) = 0 := by
      rw [Probability.statDist_symm_of_eq_weight _ _ (by
        rw [trLaw_weight_eq_one, trLaw_weight_eq_one])]
      exact distanceZero
    apply Finsupp.ext
    intro value
    have forward := Distribution.max_sub_eq_zero_of_statDist_eq_zero
      distanceZero value
    have reverse := Distribution.max_sub_eq_zero_of_statDist_eq_zero
      reverseZero value
    have forwardLe : trLaw environment rounds left value -
        trLaw environment rounds right value ≤ 0 :=
      (le_max_left _ _).trans_eq forward
    have reverseLe : trLaw environment rounds right value -
        trLaw environment rounds left value ≤ 0 :=
      (le_max_left _ _).trans_eq reverse
    linarith


end PDS

/-! ## Internal deterministic-cylinder presentation -/

namespace RandomSystem.Internal.Core

/-- A finite attempted-query transcript with optional answers. -/
abbrev Transcript (A : Interface.{u, v}) :=
  RandomSystems.Ambient.Transcript A

/-- The query sequence carried by a transcript. -/
abbrev inputs {A : Interface.{u, v}} (transcript : Transcript A) : List A.query :=
  RandomSystems.Ambient.transcriptInputs transcript

/-- The reply transcript selected by a deterministic system for a fixed query
sequence, after the supplied prior query sequence. -/
def answersFrom {A : Interface.{u, v}} (system : DDS A) :
    List A.query → List A.query → Transcript A
  | _, [] => []
  | prior, query :: remaining =>
      ⟨query, Attachment.innerReplyAt system prior query⟩ ::
        answersFrom system (prior ++ [query]) remaining

/-- The reply transcript selected by a deterministic system for a fixed query
sequence. -/
def answers {A : Interface.{u, v}} (system : DDS A)
    (queries : List A.query) : Transcript A :=
  answersFrom system [] queries

@[simp]
theorem answersFrom_nil {A : Interface.{u, v}} (system : DDS A)
    (prior : List A.query) : answersFrom system prior [] = [] :=
  rfl

@[simp]
theorem answersFrom_cons {A : Interface.{u, v}} (system : DDS A)
    (prior : List A.query) (query : A.query) (remaining : List A.query) :
    answersFrom system prior (query :: remaining) =
      ⟨query, Attachment.innerReplyAt system prior query⟩ ::
        answersFrom system (prior ++ [query]) remaining :=
  rfl

@[simp]
theorem inputs_answersFrom {A : Interface.{u, v}} (system : DDS A)
    (prior queries : List A.query) :
    inputs (answersFrom system prior queries) = queries := by
  induction queries generalizing prior with
  | nil => rfl
  | cons query remaining inductionHypothesis =>
      simp only [answersFrom_cons, inputs,
        RandomSystems.Ambient.transcriptInputs, List.map_cons]
      congr 1
      simpa [inputs, RandomSystems.Ambient.transcriptInputs] using
        inductionHypothesis (prior ++ [query])

@[simp]
theorem inputs_answers {A : Interface.{u, v}} (system : DDS A)
    (queries : List A.query) : inputs (answers system queries) = queries :=
  inputs_answersFrom system [] queries

@[simp]
theorem length_answersFrom {A : Interface.{u, v}} (system : DDS A)
    (prior queries : List A.query) :
    (answersFrom system prior queries).length = queries.length := by
  have equal := congrArg List.length
    (inputs_answersFrom system prior queries)
  simpa [inputs, RandomSystems.Ambient.transcriptInputs] using equal

@[simp]
theorem length_answers {A : Interface.{u, v}} (system : DDS A)
    (queries : List A.query) :
    (answers system queries).length = queries.length :=
  length_answersFrom system [] queries

theorem answersFrom_append {A : Interface.{u, v}} (system : DDS A)
    (prior left right : List A.query) :
    answersFrom system prior (left ++ right) =
      answersFrom system prior left ++
        answersFrom system (prior ++ left) right := by
  induction left generalizing prior with
  | nil => simp [answersFrom]
  | cons query remaining inductionHypothesis =>
      simp only [List.cons_append, answersFrom_cons]
      rw [inductionHypothesis (prior ++ [query])]
      congr 1
      simp only [List.singleton_append, List.append_assoc]

/-- A deterministic system agrees with every answer recorded by a transcript. -/
def Agrees {A : Interface.{u, v}} (system : DDS A)
    (transcript : Transcript A) : Prop :=
  answers system (inputs transcript) = transcript

@[simp]
theorem agrees_nil {A : Interface.{u, v}} (system : DDS A) :
    Agrees system [] :=
  rfl

theorem agrees_append_singleton_iff {A : Interface.{u, v}}
    (system : DDS A) (transcript : Transcript A) (query : A.query)
    (reply : Option (A.answer query)) :
    Agrees system (transcript ++ [⟨query, reply⟩]) ↔
      Agrees system transcript ∧
        Attachment.innerReplyAt system (inputs transcript) query = reply := by
  unfold Agrees answers
  rw [show inputs (transcript ++ [⟨query, reply⟩]) =
      inputs transcript ++ [query] by
    simp [inputs, RandomSystems.Ambient.transcriptInputs]]
  rw [answersFrom_append]
  simp only [answersFrom_cons, answersFrom_nil]
  change
    answersFrom system [] (inputs transcript) ++
        [⟨query, Attachment.innerReplyAt system (inputs transcript) query⟩] =
      transcript ++ [⟨query, reply⟩] ↔ _
  constructor
  · intro equal
    have lengthEqual :
        (answersFrom system [] (inputs transcript)).length = transcript.length := by
      have queryLengths := congrArg List.length
        (inputs_answersFrom system [] (inputs transcript))
      calc
        (answersFrom system [] (inputs transcript)).length =
            (inputs (answersFrom system [] (inputs transcript))).length := by
              simp [inputs, RandomSystems.Ambient.transcriptInputs]
        _ = (inputs transcript).length := queryLengths
        _ = transcript.length := by
          simp [inputs, RandomSystems.Ambient.transcriptInputs]
    have parts := List.append_inj equal lengthEqual
    exact ⟨parts.1, by simpa using parts.2⟩
  · rintro ⟨prefixEqual, finalEqual⟩
    rw [prefixEqual, finalEqual]

/-- A deterministic observation transcript records exactly the replies of the
observed DDS along its realized query sequence. -/
theorem agrees_transcript {A : Interface.{u, v}} (system : DDS A)
    (environment : DDE A) (rounds : Nat) :
    Agrees system
      (RandomSystems.Ambient.transcript system environment rounds) := by
  induction rounds with
  | zero => exact agrees_nil system
  | succ rounds inductionHypothesis =>
      rw [RandomSystems.Ambient.transcript_succ]
      cases selected : environment
          (RandomSystems.Ambient.transcript system environment rounds) with
      | none => exact inductionHypothesis
      | some query =>
          apply (agrees_append_singleton_iff system _ query _).2
          exact ⟨inductionHypothesis, rfl⟩

/-- Once a complete realized transcript is fixed, any DDS agreeing with all
its recorded replies induces the same observation transcript. -/
theorem transcript_eq_of_agrees {A : Interface.{u, v}}
    (left right : DDS A) (environment : DDE A) (rounds : Nat)
    (agrees : Agrees right
      (RandomSystems.Ambient.transcript left environment rounds)) :
    RandomSystems.Ambient.transcript right environment rounds =
      RandomSystems.Ambient.transcript left environment rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      let current :=
        RandomSystems.Ambient.transcript left environment rounds
      cases selected : environment current with
      | none =>
          have agreesCurrent : Agrees right current := by
            simpa [current, RandomSystems.Ambient.transcript_succ, selected]
              using agrees
          have currentEqual := inductionHypothesis agreesCurrent
          simp [RandomSystems.Ambient.transcript_succ, current,
            currentEqual, selected]
      | some query =>
          have agreesExtended :
              Agrees right
                (current ++ [⟨query,
                  Attachment.innerReplyAt left (inputs current) query⟩]) := by
            simpa [current, RandomSystems.Ambient.transcript_succ, selected]
              using agrees
          have parts :=
            (agrees_append_singleton_iff right current query
              (Attachment.innerReplyAt left (inputs current) query)).1
              agreesExtended
          have currentEqual := inductionHypothesis parts.1
          simp [RandomSystems.Ambient.transcript_succ, current,
            currentEqual, selected, parts.2]

/-- A transcript is reachable when some deterministic system produces it
against the fixed environment and finite horizon. -/
def Reachable {A : Interface.{u, v}} (environment : DDE A)
    (rounds : Nat) (transcript : Transcript A) : Prop :=
  ∃ system : DDS A,
    RandomSystems.Ambient.transcript system environment rounds = transcript

theorem transcript_eq_iff_reachable_and_agrees {A : Interface.{u, v}}
    (system : DDS A) (environment : DDE A) (rounds : Nat)
    (value : Transcript A) :
    RandomSystems.Ambient.transcript system environment rounds = value ↔
      Reachable environment rounds value ∧ Agrees system value := by
  constructor
  · intro equal
    constructor
    · exact ⟨system, equal⟩
    · simpa [equal] using agrees_transcript system environment rounds
  · rintro ⟨⟨witness, witnessEqual⟩, agrees⟩
    have agreesWitness :
        Agrees system
          (RandomSystems.Ambient.transcript witness environment rounds) := by
      simpa [witnessEqual] using agrees
    exact (transcript_eq_of_agrees witness system environment rounds
      agreesWitness).trans witnessEqual

/-- A finite query schedule, independent of the replies already observed. -/
def querySchedule {A : Interface.{u, v}} (queries : List A.query) : DDE A :=
  fun transcript => queries[transcript.length]?

/-- A fixed query schedule exposes exactly the deterministic answer function
on the corresponding query prefix. -/
theorem transcript_querySchedule_eq_answers_take
    {A : Interface.{u, v}} (system : DDS A) (queries : List A.query)
    (rounds : Nat) (within : rounds ≤ queries.length) :
    RandomSystems.Ambient.transcript system (querySchedule queries) rounds =
      answers system (queries.take rounds) := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      have roundLt : rounds < queries.length := by omega
      have previousWithin : rounds ≤ queries.length := Nat.le_of_lt roundLt
      rw [RandomSystems.Ambient.transcript_succ,
        inductionHypothesis previousWithin]
      have selected :
          querySchedule queries (answers system (queries.take rounds)) =
            some queries[rounds] := by
        rw [querySchedule, length_answers, List.length_take,
          Nat.min_eq_left previousWithin,
          List.getElem?_eq_getElem roundLt]
      rw [selected, List.take_succ_eq_append_getElem roundLt]
      unfold answers
      rw [answersFrom_append]
      simp

theorem transcript_querySchedule_eq_answers
    {A : Interface.{u, v}} (system : DDS A) (queries : List A.query) :
    RandomSystems.Ambient.transcript system (querySchedule queries)
        queries.length =
      answers system queries := by
  simpa using transcript_querySchedule_eq_answers_take system queries
    queries.length (Nat.le_refl _)

theorem transcript_querySchedule_eq_iff_agrees
    {A : Interface.{u, v}} (system : DDS A) (value : Transcript A) :
    RandomSystems.Ambient.transcript system (querySchedule (inputs value))
        value.length = value ↔
      Agrees system value := by
  rw [show value.length = (inputs value).length by
    simp [inputs, RandomSystems.Ambient.transcriptInputs],
    transcript_querySchedule_eq_answers]
  rfl


end RandomSystem.Internal.Core

/-- Liu--Maurer, Definition 2 (printed p. 8), says: “An (X,Y)-random
system R is a sequence of conditional probability distributions.” This
canonical cumulative form stores the mass of every finite attempted-history
cylinder. The one-reply law is uniquely fixed by its pointwise cylinder-mass
equation, including the rejection reply none. -/
structure RandomSystem (A : Interface.{u, v}) where
  mass : Transcript A → ℝ
  mass_nonneg : ∀ transcript, 0 ≤ mass transcript
  mass_nil : mass [] = 1
  extensionLaw :
    (transcript : Transcript A) → (query : A.query) →
      Distribution (Option (A.answer query))
  extensionLaw_apply : ∀ transcript query reply,
    extensionLaw transcript query reply =
      mass (transcript ++ [⟨query, reply⟩])
  extensionLaw_weight : ∀ transcript query,
    (extensionLaw transcript query).weight = mass transcript

namespace RandomSystem

variable {A : Interface.{u, v}}

/-- Cumulative random systems are determined by their cylinder masses. -/
@[ext]
theorem ext {left right : RandomSystem A}
    (equal : ∀ transcript, left.mass transcript = right.mass transcript) :
    left = right := by
  have massEqual : left.mass = right.mass := funext equal
  have extensionEqual : left.extensionLaw = right.extensionLaw := by
    funext transcript query
    apply Finsupp.ext
    intro reply
    rw [left.extensionLaw_apply, right.extensionLaw_apply, equal]
  cases left
  cases right
  simp_all

/-- The pointwise one-reply cylinder equation. -/
theorem extension_mass (system : RandomSystem A) (transcript : Transcript A)
    (query : A.query) (reply : Option (A.answer query)) :
    system.extensionLaw transcript query reply =
      system.mass (transcript ++ [⟨query, reply⟩]) :=
  system.extensionLaw_apply transcript query reply

/-- All optional replies partition the current cylinder. -/
theorem flow (system : RandomSystem A) (transcript : Transcript A)
    (query : A.query) :
    (system.extensionLaw transcript query).weight = system.mass transcript :=
  system.extensionLaw_weight transcript query

end RandomSystem

namespace PDS

open RandomSystem.Internal.Core

variable {A : Interface.{u, v}}

/-- Cylinder mass of normalized finite presentation data. -/
def cylinderMass (system : PDS A)
    (transcript : Transcript A) : ℝ :=
  system.1.mass fun deterministicSystem => Agrees deterministicSystem transcript

/-- The finite law of the next reply inside one cylinder. -/
def extensionLaw (system : PDS A)
    (transcript : Transcript A) (query : A.query) :
    Distribution (Option (A.answer query)) :=
  Distribution.fTransform
    (fun deterministicSystem =>
      Attachment.innerReplyAt deterministicSystem (inputs transcript) query)
    (system.1.restrict fun deterministicSystem =>
      Agrees deterministicSystem transcript)

theorem extensionLaw_apply (system : PDS A)
    (transcript : Transcript A) (query : A.query)
    (reply : Option (A.answer query)) :
    extensionLaw system transcript query reply =
      cylinderMass system (transcript ++ [⟨query, reply⟩]) := by
  rw [extensionLaw, Distribution.fTransform_apply_eq_mass,
    Distribution.mass_restrict]
  unfold cylinderMass
  apply Distribution.mass_congr
  intro deterministicSystem
  rw [agrees_append_singleton_iff]
  constructor
  · rintro ⟨nextEqual, prefixAgrees⟩
    exact ⟨prefixAgrees, nextEqual⟩
  · rintro ⟨prefixAgrees, nextEqual⟩
    exact ⟨nextEqual, prefixAgrees⟩

theorem extensionLaw_weight (system : PDS A)
    (transcript : Transcript A) (query : A.query) :
    (extensionLaw system transcript query).weight =
      cylinderMass system transcript := by
  rw [extensionLaw, Distribution.weight_fTransform,
    Distribution.weight_restrict]
  rfl

/-- Interpret a normalized finite-support PDS as a cumulative random system. -/
def toRandomSystem (system : PDS A) : RandomSystem A where
  mass := cylinderMass system
  mass_nonneg := fun transcript =>
    system.2.nonNeg.mass_nonneg fun deterministicSystem =>
      Agrees deterministicSystem transcript
  mass_nil := by
    rw [cylinderMass]
    simpa only [agrees_nil] using
      (Distribution.mass_true system.1).trans system.2.weight_eq
  extensionLaw := extensionLaw system
  extensionLaw_apply := extensionLaw_apply system
  extensionLaw_weight := extensionLaw_weight system

@[simp]
theorem toRandomSystem_mass (system : PDS A)
    (transcript : Transcript A) :
    (toRandomSystem system).mass transcript = cylinderMass system transcript :=
  rfl

/-- A reachable transcript atom has exactly its cylinder mass. -/
theorem trLaw_apply_eq_cylinderMass
    (system : PDS A)
    (environment : DDE A) (rounds : Nat) (value : Transcript A)
    (reachable : Reachable environment rounds value) :
    trLaw environment rounds system value =
      cylinderMass system value := by
  rw [trLaw, RandomSystems.Ambient.trLaw,
    Distribution.fTransform_apply_eq_mass]
  unfold cylinderMass
  apply Distribution.mass_congr
  intro deterministicSystem
  rw [transcript_eq_iff_reachable_and_agrees]
  simp [reachable]

/-- An unreachable transcript atom has zero observation mass. -/
theorem trLaw_apply_eq_zero
    (system : PDS A)
    (environment : DDE A) (rounds : Nat) (value : Transcript A)
    (unreachable : ¬ Reachable environment rounds value) :
    trLaw environment rounds system value = 0 := by
  rw [trLaw, RandomSystems.Ambient.trLaw,
    Distribution.fTransform_apply_eq_mass]
  apply Distribution.mass_eq_zero_of_forall_not
  intro deterministicSystem equal
  exact unreachable ⟨deterministicSystem, equal⟩

/-- Equality of cumulative random systems implies equality under every finite DDE
observation. -/
theorem equivalent_of_toRandomSystem_eq
    {left right : PDS A}
    (equal : toRandomSystem left = toRandomSystem right) :
    equivalent left right := by
  intro environment rounds
  apply Finsupp.ext
  intro value
  by_cases reachable : Reachable environment rounds value
  · rw [trLaw_apply_eq_cylinderMass left environment rounds value reachable,
      trLaw_apply_eq_cylinderMass right environment rounds value reachable]
    exact congrArg (fun behavior => behavior.mass value) equal
  · rw [trLaw_apply_eq_zero left environment rounds value reachable,
      trLaw_apply_eq_zero right environment rounds value reachable]

/-- Every cylinder is exposed by the DDE that asks its query sequence. -/
theorem cylinderMass_eq_trLaw_querySchedule_apply
    (system : PDS A) (value : Transcript A) :
    cylinderMass system value =
      trLaw (querySchedule (inputs value))
        value.length system value := by
  rw [trLaw, RandomSystems.Ambient.trLaw,
    Distribution.fTransform_apply_eq_mass]
  unfold cylinderMass
  apply Distribution.mass_congr
  intro deterministicSystem
  exact (transcript_querySchedule_eq_iff_agrees
    deterministicSystem value).symm

/-- Presentation-level finite-observation equivalence implies equality of cumulative
behavior. -/
theorem toRandomSystem_eq_of_equivalent
    {left right : PDS A}
    (equivalent : equivalent left right) :
    toRandomSystem left = toRandomSystem right := by
  apply RandomSystem.ext
  intro value
  rw [toRandomSystem_mass, toRandomSystem_mass,
    cylinderMass_eq_trLaw_querySchedule_apply,
    cylinderMass_eq_trLaw_querySchedule_apply,
    equivalent (querySchedule (inputs value)) value.length]

/-- The cumulative interpretation identifies exactly the presentation-level
finite-observation equivalence classes. -/
theorem toRandomSystem_eq_iff {left right : PDS A} :
    toRandomSystem left = toRandomSystem right ↔
      equivalent left right :=
  ⟨equivalent_of_toRandomSystem_eq, toRandomSystem_eq_of_equivalent⟩

end PDS


namespace RandomSystem

variable {A : Interface.{u, v}}

/-- Interpret normalized finite-support PDS presentation data in the sole
cumulative random-system carrier. This is a constructor/interpretation, not a
peer resource carrier. -/
def ofPDS (system : PDS A) : RandomSystem A :=
  PDS.toRandomSystem system

/-- Two finite PDS presentations denote the same cumulative random system
exactly when every finite functional-DDE transcript law agrees. -/
theorem ofPDS_eq_iff {left right : PDS A} :
    ofPDS left = ofPDS right ↔ PDS.equivalent left right :=
  PDS.toRandomSystem_eq_iff

/-- Interpret one deterministic DDS as a point-mass cumulative random system. -/
def ofDDS (system : DDS A) : RandomSystem A :=
  ofPDS (PDS.ofDDS system)

end RandomSystem


/-! ## Internal finite observations -/

namespace RandomSystem.Internal

noncomputable section

open Probability

/-- A finite-path functional observation. Its branches are selected by the
optional answer to the displayed query. -/
inductive Observation (A : Interface.{u, v}) (R : Type w)
  | value (result : R)
  | query (input : A.query)
      (continuation : Option (A.answer input) → Observation A R)

/-- Once a cylinder has zero mass, every longer cylinder below it has zero
mass. -/
theorem mass_append_eq_zero {A : Interface.{u, v}} (behavior : RandomSystem A)
    (prior suffix : RandomSystem.Internal.Core.Transcript A)
    (zero : behavior.mass prior = 0) :
    behavior.mass (prior ++ suffix) = 0 := by
  induction suffix generalizing prior with
  | nil => simpa using zero
  | cons reply remaining inductionHypothesis =>
      rcases reply with ⟨query, answer⟩
      have extensionNonNeg :
          (behavior.extensionLaw prior query).NonNeg := fun candidate => by
        rw [behavior.extensionLaw_apply]
        exact behavior.mass_nonneg _
      have childLe : behavior.mass (prior ++ [⟨query, answer⟩]) ≤
          behavior.mass prior := by
        calc
          behavior.mass (prior ++ [⟨query, answer⟩]) =
              behavior.extensionLaw prior query answer := by
            rw [behavior.extensionLaw_apply]
          _ = (behavior.extensionLaw prior query).mass
              (fun candidate => candidate = answer) := by
            rw [Distribution.mass_singleton]
          _ ≤ (behavior.extensionLaw prior query).weight :=
            Distribution.mass_le_weight extensionNonNeg _
          _ = behavior.mass prior := behavior.extensionLaw_weight prior query
      have childZero : behavior.mass (prior ++ [⟨query, answer⟩]) = 0 :=
        le_antisymm (childLe.trans_eq zero) (behavior.mass_nonneg _)
      rw [show prior ++ ⟨query, answer⟩ :: remaining =
          (prior ++ [⟨query, answer⟩]) ++ remaining by simp]
      exact inductionHypothesis _ childZero

namespace Observation

variable {A : Interface.{u, v}} {R : Type w}

/-- Functional evaluation against one deterministic system after a fixed
attempted-query prefix. -/
def evaluateFrom : Observation A R → DDS A → List A.query → R
  | .value result, _, _ => result
  | .query input continuation, system, prior =>
      let reply := Attachment.innerReplyAt system prior input
      evaluateFrom (continuation reply) system (prior ++ [input])

/-- Functional evaluation from the empty query prefix. -/
def evaluate (observation : Observation A R) (system : DDS A) : R :=
  evaluateFrom observation system []

@[simp]
theorem evaluateFrom_value (result : R) (system : DDS A)
    (prior : List A.query) :
    evaluateFrom (.value result) system prior = result :=
  rfl

@[simp]
theorem evaluateFrom_query (input : A.query)
    (continuation : Option (A.answer input) → Observation A R)
    (system : DDS A) (prior : List A.query) :
    evaluateFrom (.query input continuation) system prior =
      evaluateFrom
        (continuation (Attachment.innerReplyAt system prior input))
        system (prior ++ [input]) :=
  rfl

/-- Deterministic relabeling of observation results. -/
def map {S : Type*} (function : R → S) : Observation A R → Observation A S
  | .value result => .value (function result)
  | .query input continuation =>
      .query input fun reply => map function (continuation reply)

@[simp]
theorem map_value {S : Type*} (function : R → S) (result : R) :
    map function (.value result : Observation A R) = .value (function result) :=
  rfl

@[simp]
theorem map_query {S : Type*} (function : R → S) (input : A.query)
    (continuation : Option (A.answer input) → Observation A R) :
    map function (.query input continuation) =
      .query input fun reply => map function (continuation reply) :=
  rfl

theorem map_map {S T : Type*} (outer : S → T) (inner : R → S)
    (observation : Observation A R) :
    map outer (map inner observation) = map (outer ∘ inner) observation := by
  induction observation with
  | value result => rfl
  | query input continuation inductionHypothesis =>
      rw [map_query, map_query, map_query]
      apply congrArg (Observation.query input)
      funext reply
      exact inductionHypothesis reply

/-- A leaf of one finite observation, retaining its complete reply branch. -/
inductive Leaf : Observation A R → Type (max u v w)
  | value (result : R) : Leaf (.value result)
  | query {input : A.query}
      {continuation : Option (A.answer input) → Observation A R}
      (reply : Option (A.answer input))
      (leaf : Leaf (continuation reply)) :
      Leaf (.query input continuation)

namespace Leaf

/-- Result carried by a selected observation leaf. -/
def result {observation : Observation A R} : Leaf observation → R
  | .value result => result
  | .query _ leaf => leaf.result

/-- Complete query/reply transcript leading to a selected observation leaf. -/
def transcript {observation : Observation A R} :
    Leaf observation → RandomSystem.Internal.Core.Transcript A
  | .value _ => []
  | .query reply leaf => ⟨_, reply⟩ :: leaf.transcript

end Leaf

/-- Override one complete attempted-query history by one prescribed optional
reply. -/
noncomputable def setReply (system : DDS A) (prior : List A.query)
    (query : A.query) (reply : Option (A.answer query)) : DDS A := by
  classical
  exact Function.update system (Attachment.innerHistory prior query)
    (cast (congrArg (fun selected => Option (A.answer selected))
      (Attachment.last_innerHistory prior query).symm) reply)

@[simp]
theorem innerReplyAt_setReply (system : DDS A) (prior : List A.query)
    (query : A.query) (reply : Option (A.answer query)) :
    Attachment.innerReplyAt (setReply system prior query reply) prior query =
      reply := by
  classical
  unfold Attachment.innerReplyAt setReply
  let attachmentHistory : History A :=
    { queries := prior ++ [query], nonempty := by simp }
  change cast _
      (Function.update system (Attachment.innerHistory prior query)
        (cast _ reply) attachmentHistory) = reply
  have historiesEqual : attachmentHistory =
      Attachment.innerHistory prior query := by
    apply History.ext
    rfl
  cases historiesEqual
  simp [Function.update, attachmentHistory, Attachment.innerHistory]
  apply eq_of_heq
  exact (cast_heq _ _).trans (cast_heq _ _)

theorem setReply_apply_of_queries_ne (system : DDS A)
    (setPrior : List A.query) (setQuery : A.query)
    (setValue : Option (A.answer setQuery)) (history : History A)
    (different : history.queries ≠ setPrior ++ [setQuery]) :
    setReply system setPrior setQuery setValue history = system history := by
  classical
  have historiesDifferent : history ≠
      Attachment.innerHistory setPrior setQuery := by
    intro equal
    exact different (congrArg History.queries equal)
  simp [setReply, Function.update, historiesDifferent]

theorem innerReplyAt_setReply_of_queries_ne (system : DDS A)
    (setPrior : List A.query) (setQuery : A.query)
    (setValue : Option (A.answer setQuery))
    (prior : List A.query) (query : A.query)
    (different : prior ++ [query] ≠ setPrior ++ [setQuery]) :
    Attachment.innerReplyAt (setReply system setPrior setQuery setValue)
        prior query =
      Attachment.innerReplyAt system prior query := by
  unfold Attachment.innerReplyAt
  congr 1
  apply setReply_apply_of_queries_ne
  exact different

/-- Changing a reply at a history no longer affects observations that already
start strictly below that history. -/
theorem answersFrom_setReply_of_length_le (system : DDS A)
    (setPrior : List A.query) (setQuery : A.query)
    (setValue : Option (A.answer setQuery))
    (prior queries : List A.query)
    (past : (setPrior ++ [setQuery]).length ≤ prior.length) :
    RandomSystem.Internal.Core.answersFrom
        (setReply system setPrior setQuery setValue) prior queries =
      RandomSystem.Internal.Core.answersFrom system prior queries := by
  have setLength : setPrior.length + 1 ≤ prior.length := by
    simpa only [List.length_append, List.length_singleton] using past
  induction queries generalizing prior with
  | nil => rfl
  | cons query remaining inductionHypothesis =>
      simp only [RandomSystem.Internal.Core.answersFrom_cons]
      have different : prior ++ [query] ≠ setPrior ++ [setQuery] := by
        intro equal
        have lengths := congrArg List.length equal
        simp only [List.length_append, List.length_singleton] at lengths
        omega
      rw [innerReplyAt_setReply_of_queries_ne _ _ _ _ _ _ different]
      exact congrArg (List.cons ⟨query,
        Attachment.innerReplyAt system prior query⟩)
        (inductionHypothesis (prior ++ [query])
          (by
            simp only [List.length_append, List.length_singleton]
            exact Nat.le_trans setLength (Nat.le_succ prior.length))
          (by
            simp only [List.length_append, List.length_singleton]
            exact Nat.le_trans setLength (Nat.le_succ prior.length)))

/-- Extend a deterministic reply table so that it realizes one prescribed
finite transcript below the given query prefix. -/
noncomputable def realizeFrom (system : DDS A) :
    List A.query → RandomSystem.Internal.Core.Transcript A → DDS A
  | _, [] => system
  | prior, first :: remaining =>
      setReply (realizeFrom system (prior ++ [first.1]) remaining)
        prior first.1 first.2

/-- The finite table extension realizes exactly its prescribed transcript. -/
theorem answersFrom_realizeFrom (system : DDS A) (prior : List A.query)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    RandomSystem.Internal.Core.answersFrom (realizeFrom system prior transcript) prior
        (RandomSystem.Internal.Core.inputs transcript) =
      transcript := by
  induction transcript generalizing prior with
  | nil => rfl
  | cons first remaining inductionHypothesis =>
      rcases first with ⟨query, reply⟩
      simp only [realizeFrom]
      change RandomSystem.Internal.Core.answersFrom
          (setReply (realizeFrom system (prior ++ [query]) remaining)
            prior query reply)
          prior (query :: RandomSystem.Internal.Core.inputs remaining) =
        ⟨query, reply⟩ :: remaining
      rw [RandomSystem.Internal.Core.answersFrom_cons, innerReplyAt_setReply]
      rw [answersFrom_setReply_of_length_le]
      · exact congrArg (List.cons ⟨query, reply⟩)
          (inductionHypothesis (prior ++ [query]))
      · simp

/-- Every finite transcript has a deterministic realization below any fixed
query prefix. -/
theorem exists_answersFrom_eq (prior : List A.query)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    ∃ system : DDS A,
      RandomSystem.Internal.Core.answersFrom system prior (RandomSystem.Internal.Core.inputs transcript) =
        transcript := by
  let rejecting : DDS A := fun _ => none
  exact ⟨realizeFrom rejecting prior transcript,
    answersFrom_realizeFrom rejecting prior transcript⟩

/-- A DDS realizing a selected leaf transcript evaluates the observation to
the result carried by that leaf. -/
theorem evaluateFrom_eq_leaf_result
    {observation : Observation A R} (leaf : Leaf observation)
    (system : DDS A) (prior : List A.query)
    (realizes : RandomSystem.Internal.Core.answersFrom system prior
      (RandomSystem.Internal.Core.inputs leaf.transcript) = leaf.transcript) :
    evaluateFrom observation system prior = leaf.result := by
  induction leaf generalizing prior with
  | value result => rfl
  | @query query continuation selectedReply leaf inductionHypothesis =>
      change RandomSystem.Internal.Core.answersFrom system prior
          (query :: RandomSystem.Internal.Core.inputs leaf.transcript) =
        ⟨query, selectedReply⟩ :: leaf.transcript at realizes
      rw [RandomSystem.Internal.Core.answersFrom_cons] at realizes
      have headEqual := congrArg List.head? realizes
      have replyEqual : Attachment.innerReplyAt system prior query =
          selectedReply := by
        simpa using headEqual
      rw [evaluateFrom_query, replyEqual]
      apply inductionHypothesis (prior ++ [query])
      exact List.cons.inj realizes |>.2

/-- An override at an earlier query history does not change evaluation that
already starts below it. -/
theorem evaluateFrom_setReply_of_length_le (observation : Observation A R)
    (system : DDS A) (setPrior : List A.query) (setQuery : A.query)
    (setValue : Option (A.answer setQuery)) (prior : List A.query)
    (past : (setPrior ++ [setQuery]).length ≤ prior.length) :
    evaluateFrom observation (setReply system setPrior setQuery setValue)
        prior =
      evaluateFrom observation system prior := by
  induction observation generalizing prior with
  | value result => rfl
  | query query continuation inductionHypothesis =>
      rw [evaluateFrom_query, evaluateFrom_query]
      have different : prior ++ [query] ≠ setPrior ++ [setQuery] := by
        intro equal
        have lengths := congrArg List.length equal
        simp only [List.length_append, List.length_singleton] at past lengths
        omega
      rw [innerReplyAt_setReply_of_queries_ne _ _ _ _ _ _ different]
      apply inductionHypothesis
      simp only [List.length_append, List.length_singleton] at past ⊢
      omega

/-- The leaf selected by one deterministic DDS. -/
def selectedLeaf : (observation : Observation A R) →
    DDS A → List A.query → Leaf observation
  | @Observation.value _ _ result, _, _ => .value result
  | @Observation.query _ _ input continuation, system, prior =>
      let reply := Attachment.innerReplyAt system prior input
      .query reply
        (selectedLeaf (continuation reply) system (prior ++ [input]))

/-- The selected leaf records exactly the replies of the selecting DDS. -/
theorem answersFrom_selectedLeaf (observation : Observation A R)
    (system : DDS A) (prior : List A.query) :
    RandomSystem.Internal.Core.answersFrom system prior
        (RandomSystem.Internal.Core.inputs (selectedLeaf observation system prior).transcript) =
      (selectedLeaf observation system prior).transcript := by
  induction observation generalizing prior with
  | value result =>
      change RandomSystem.Internal.Core.answersFrom system prior [] = []
      rfl
  | query query continuation inductionHypothesis =>
      simp only [selectedLeaf]
      change RandomSystem.Internal.Core.answersFrom system prior
          (query :: RandomSystem.Internal.Core.inputs
            (selectedLeaf
              (continuation (Attachment.innerReplyAt system prior query))
              system (prior ++ [query])).transcript) = _
      rw [RandomSystem.Internal.Core.answersFrom_cons]
      exact congrArg (List.cons
        ⟨query, Attachment.innerReplyAt system prior query⟩)
        (inductionHypothesis
          (Attachment.innerReplyAt system prior query) (prior ++ [query]))

/-- The selected leaf carries the functional evaluation result. -/
theorem selectedLeaf_result (observation : Observation A R)
    (system : DDS A) (prior : List A.query) :
    (selectedLeaf observation system prior).result =
      evaluateFrom observation system prior := by
  exact (evaluateFrom_eq_leaf_result
    (selectedLeaf observation system prior) system prior
    (answersFrom_selectedLeaf observation system prior)).symm

/-- One canonical leaf, used only to choose a reference result in a finite
extensionality proof. -/
def referenceLeaf : (observation : Observation A R) → Leaf observation
  | @Observation.value _ _ result => .value result
  | @Observation.query _ _ _ continuation =>
      .query none (referenceLeaf (continuation none))

theorem append_cons_ne_append_cons {Q : Type*}
    (common : List Q) {left right : Q} (different : left ≠ right)
    (leftTail rightTail : List Q) :
    common ++ left :: leftTail ≠ common ++ right :: rightTail := by
  intro equal
  have tailsEqual : left :: leftTail = right :: rightTail :=
    List.append_cancel_left equal
  exact different (List.cons.inj tailsEqual).1

/-- An override on one divergent query branch leaves every reply strictly
below the other branch unchanged. -/
theorem answersFrom_setReply_of_diverged_below (system : DDS A)
    (common : List A.query) {leftFirst rightFirst : A.query}
    (different : leftFirst ≠ rightFirst)
    (setPrior : List A.query) (setQuery : A.query)
    (setValue : Option (A.answer setQuery))
    (setBranch : ∃ tail,
      setPrior ++ [setQuery] = common ++ rightFirst :: tail)
    (prior : List A.query)
    (leftBranch : ∃ tail, prior = common ++ leftFirst :: tail)
    (queries : List A.query) :
    RandomSystem.Internal.Core.answersFrom
        (setReply system setPrior setQuery setValue) prior queries =
      RandomSystem.Internal.Core.answersFrom system prior queries := by
  induction queries generalizing prior with
  | nil => rfl
  | cons query remaining inductionHypothesis =>
      simp only [RandomSystem.Internal.Core.answersFrom_cons]
      have historiesDifferent : prior ++ [query] ≠
          setPrior ++ [setQuery] := by
        obtain ⟨leftTail, rfl⟩ := leftBranch
        obtain ⟨rightTail, setEqual⟩ := setBranch
        rw [setEqual]
        simpa only [List.append_assoc, List.cons_append] using
          append_cons_ne_append_cons common different
            (leftTail ++ [query]) rightTail
      rw [innerReplyAt_setReply_of_queries_ne _ _ _ _ _ _
        historiesDifferent]
      congr 1
      apply inductionHypothesis (prior ++ [query])
      obtain ⟨leftTail, leftEqual⟩ := leftBranch
      refine ⟨leftTail ++ [query], ?_⟩
      simp [leftEqual, List.append_assoc]

/-- An override at the first cell of one query branch leaves the complete
reply transcript of a different first query unchanged. -/
theorem answersFrom_setReply_of_first_ne (system : DDS A)
    (common : List A.query) {leftFirst rightFirst : A.query}
    (different : leftFirst ≠ rightFirst)
    (setPrior : List A.query) (setQuery : A.query)
    (setValue : Option (A.answer setQuery))
    (setBranch : ∃ tail,
      setPrior ++ [setQuery] = common ++ rightFirst :: tail)
    (remaining : List A.query) :
    RandomSystem.Internal.Core.answersFrom
        (setReply system setPrior setQuery setValue) common
        (leftFirst :: remaining) =
      RandomSystem.Internal.Core.answersFrom system common (leftFirst :: remaining) := by
  simp only [RandomSystem.Internal.Core.answersFrom_cons]
  have historiesDifferent : common ++ [leftFirst] ≠
      setPrior ++ [setQuery] := by
    obtain ⟨rightTail, setEqual⟩ := setBranch
    rw [setEqual]
    exact append_cons_ne_append_cons common different [] rightTail
  rw [innerReplyAt_setReply_of_queries_ne _ _ _ _ _ _ historiesDifferent]
  congr 1
  exact answersFrom_setReply_of_diverged_below system common different
    setPrior setQuery setValue setBranch (common ++ [leftFirst])
    ⟨[], rfl⟩ remaining

/-- Extending a deterministic table only along one divergent branch leaves
the complete transcript of the other branch unchanged. -/
theorem answersFrom_realizeFrom_of_diverged_below (system : DDS A)
    (common : List A.query) {leftFirst rightFirst : A.query}
    (different : leftFirst ≠ rightFirst)
    (setPrior : List A.query)
    (setBranch : ∃ tail, setPrior = common ++ rightFirst :: tail)
    (rightTranscript : RandomSystem.Internal.Core.Transcript A)
    (leftRemaining : List A.query) :
    RandomSystem.Internal.Core.answersFrom
        (realizeFrom system setPrior rightTranscript) common
        (leftFirst :: leftRemaining) =
      RandomSystem.Internal.Core.answersFrom system common (leftFirst :: leftRemaining) := by
  induction rightTranscript generalizing setPrior with
  | nil => rfl
  | cons first remaining inductionHypothesis =>
      rcases first with ⟨query, reply⟩
      simp only [realizeFrom]
      calc
        RandomSystem.Internal.Core.answersFrom
            (setReply
              (realizeFrom system (setPrior ++ [query]) remaining)
              setPrior query reply)
            common (leftFirst :: leftRemaining) =
            RandomSystem.Internal.Core.answersFrom
              (realizeFrom system (setPrior ++ [query]) remaining)
              common (leftFirst :: leftRemaining) :=
          answersFrom_setReply_of_first_ne _ common different
            setPrior query reply
            (by
              obtain ⟨tail, rfl⟩ := setBranch
              exact ⟨tail ++ [query], by simp [List.append_assoc]⟩)
            leftRemaining
        _ = RandomSystem.Internal.Core.answersFrom system common
            (leftFirst :: leftRemaining) := by
          apply inductionHypothesis (setPrior ++ [query])
          obtain ⟨tail, rfl⟩ := setBranch
          exact ⟨tail ++ [query], by simp [List.append_assoc]⟩

/-- Realizing one nonempty transcript leaves a transcript beginning with a
different first query unchanged. -/
theorem answersFrom_realizeFrom_of_first_ne (system : DDS A)
    (prior : List A.query) {leftFirst rightFirst : A.query}
    (different : leftFirst ≠ rightFirst)
    (rightReply : Option (A.answer rightFirst))
    (rightRemaining : RandomSystem.Internal.Core.Transcript A)
    (leftRemaining : List A.query) :
    RandomSystem.Internal.Core.answersFrom
        (realizeFrom system prior
          (⟨rightFirst, rightReply⟩ :: rightRemaining))
        prior (leftFirst :: leftRemaining) =
      RandomSystem.Internal.Core.answersFrom system prior (leftFirst :: leftRemaining) := by
  simp only [realizeFrom]
  calc
    RandomSystem.Internal.Core.answersFrom
        (setReply
          (realizeFrom system (prior ++ [rightFirst]) rightRemaining)
          prior rightFirst rightReply)
        prior (leftFirst :: leftRemaining) =
        RandomSystem.Internal.Core.answersFrom
          (realizeFrom system (prior ++ [rightFirst]) rightRemaining)
          prior (leftFirst :: leftRemaining) :=
      answersFrom_setReply_of_first_ne _ prior different prior rightFirst
        rightReply ⟨[], rfl⟩ leftRemaining
    _ = RandomSystem.Internal.Core.answersFrom system prior
        (leftFirst :: leftRemaining) :=
      answersFrom_realizeFrom_of_diverged_below system prior different
        (prior ++ [rightFirst]) ⟨[], rfl⟩ rightRemaining leftRemaining

/-- Two prescribed transcripts with different first queries have one common
deterministic realization. -/
theorem exists_answersFrom_eq_pair_of_first_ne
    (prior : List A.query)
    {leftFirst rightFirst : A.query} (different : leftFirst ≠ rightFirst)
    (leftReply : Option (A.answer leftFirst))
    (rightReply : Option (A.answer rightFirst))
    (leftRemaining rightRemaining : RandomSystem.Internal.Core.Transcript A) :
    ∃ system : DDS A,
      RandomSystem.Internal.Core.answersFrom system prior
          (leftFirst :: RandomSystem.Internal.Core.inputs leftRemaining) =
          ⟨leftFirst, leftReply⟩ :: leftRemaining ∧
        RandomSystem.Internal.Core.answersFrom system prior
          (rightFirst :: RandomSystem.Internal.Core.inputs rightRemaining) =
          ⟨rightFirst, rightReply⟩ :: rightRemaining := by
  let rejecting : DDS A := fun _ => none
  let rightTranscript : RandomSystem.Internal.Core.Transcript A :=
    ⟨rightFirst, rightReply⟩ :: rightRemaining
  let leftTranscript : RandomSystem.Internal.Core.Transcript A :=
    ⟨leftFirst, leftReply⟩ :: leftRemaining
  let withRight := realizeFrom rejecting prior rightTranscript
  let combined := realizeFrom withRight prior leftTranscript
  refine ⟨combined, answersFrom_realizeFrom withRight prior leftTranscript, ?_⟩
  calc
    RandomSystem.Internal.Core.answersFrom combined prior
        (rightFirst :: RandomSystem.Internal.Core.inputs rightRemaining) =
        RandomSystem.Internal.Core.answersFrom withRight prior
          (rightFirst :: RandomSystem.Internal.Core.inputs rightRemaining) := by
      unfold combined leftTranscript
      exact answersFrom_realizeFrom_of_first_ne withRight prior
        (Ne.symm different) leftReply leftRemaining
        (RandomSystem.Internal.Core.inputs rightRemaining)
    _ = ⟨rightFirst, rightReply⟩ :: rightRemaining := by
      exact answersFrom_realizeFrom rejecting prior rightTranscript

/-- The same observation with its selected leaf retained as the result. -/
def enumerate : (observation : Observation A R) →
    Observation A (Leaf observation)
  | .value result => .value (.value result)
  | .query input continuation =>
      .query input fun reply =>
        map (Leaf.query reply) (enumerate (continuation reply))

/-- Forgetting the selected leaf recovers the original observation. -/
theorem map_result_enumerate (observation : Observation A R) :
    map Leaf.result (enumerate observation) = observation := by
  induction observation with
  | value result => rfl
  | query input continuation inductionHypothesis =>
      rw [enumerate, map_query]
      apply congrArg (Observation.query input)
      funext reply
      rw [map_map]
      change map Leaf.result (enumerate (continuation reply)) =
        continuation reply
      exact inductionHypothesis reply

/-- The distribution of the leaves of an observation below a fixed cylinder.
Each recursive branch already carries its cumulative cylinder mass, so the
definition is a finite sum rather than a product of conditional kernels. -/
def distributionFrom (behavior : RandomSystem A) :
    Observation A R → RandomSystem.Internal.Core.Transcript A → Distribution R
  | .value result, transcript =>
      Finsupp.single result (behavior.mass transcript)
  | .query input continuation, transcript =>
      (behavior.extensionLaw transcript input).sum fun reply _ =>
        distributionFrom behavior (continuation reply)
          (transcript ++ [⟨input, reply⟩])

/-- Root observation law. -/
def distribution (behavior : RandomSystem A) (observation : Observation A R) :
    Distribution R :=
  distributionFrom behavior observation []

@[simp]
theorem distributionFrom_value (behavior : RandomSystem A) (result : R)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    distributionFrom behavior (.value result) transcript =
      Finsupp.single result (behavior.mass transcript) :=
  rfl

@[simp]
theorem distributionFrom_query (behavior : RandomSystem A) (input : A.query)
    (continuation : Option (A.answer input) → Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    distributionFrom behavior (.query input continuation) transcript =
      (behavior.extensionLaw transcript input).sum fun reply _ =>
        distributionFrom behavior (continuation reply)
          (transcript ++ [⟨input, reply⟩]) :=
  rfl

theorem weight_distributionFrom (behavior : RandomSystem A)
    (observation : Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    (distributionFrom behavior observation transcript).weight =
      behavior.mass transcript := by
  induction observation generalizing transcript with
  | value result =>
      simp [distributionFrom, Distribution.weight]
  | query input continuation inductionHypothesis =>
      rw [distributionFrom]
      change
        (Finsupp.sum (behavior.extensionLaw transcript input)
          (fun reply _ => distributionFrom behavior (continuation reply)
            (transcript ++ [⟨input, reply⟩]))).weight = _
      rw [Finsupp.sum, Distribution.weight_finset_sum]
      calc
        ∑ reply ∈ (behavior.extensionLaw transcript input).support,
            (distributionFrom behavior (continuation reply)
              (transcript ++ [⟨input, reply⟩])).weight =
            ∑ reply ∈ (behavior.extensionLaw transcript input).support,
              behavior.extensionLaw transcript input reply := by
                apply Finset.sum_congr rfl
                intro reply membership
                rw [inductionHypothesis reply,
                  ← behavior.extensionLaw_apply transcript input reply]
        _ = (behavior.extensionLaw transcript input).weight := by
          rfl
        _ = behavior.mass transcript :=
          behavior.extensionLaw_weight transcript input

theorem nonNeg_distributionFrom (behavior : RandomSystem A)
    (observation : Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    (distributionFrom behavior observation transcript).NonNeg := by
  intro result
  induction observation generalizing transcript with
  | value value =>
      classical
      simp only [distributionFrom, Finsupp.single_apply]
      split
      · exact behavior.mass_nonneg transcript
      · exact le_rfl
  | query input continuation inductionHypothesis =>
      rw [distributionFrom]
      simp only [Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply]
      exact Finset.sum_nonneg fun reply membership =>
        inductionHypothesis reply (transcript ++ [⟨input, reply⟩])

theorem distributionFrom_map {S : Type*} (behavior : RandomSystem A)
    (function : R → S) (observation : Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    distributionFrom behavior (map function observation) transcript =
      Distribution.fTransform function
        (distributionFrom behavior observation transcript) := by
  induction observation generalizing transcript with
  | value result =>
      classical
      simp [map, distributionFrom, Distribution.fTransform]
  | query input continuation inductionHypothesis =>
      rw [map, distributionFrom, distributionFrom]
      change
        Finsupp.sum (behavior.extensionLaw transcript input)
            (fun reply _ => distributionFrom behavior
              (map function (continuation reply))
              (transcript ++ [⟨input, reply⟩])) =
          Distribution.fTransform function
            (Finsupp.sum (behavior.extensionLaw transcript input)
              (fun reply _ => distributionFrom behavior
                (continuation reply) (transcript ++ [⟨input, reply⟩])))
      rw [Finsupp.sum, Finsupp.sum,
        Distribution.fTransform_finset_sum]
      apply Finset.sum_congr rfl
      intro reply membership
      exact inductionHypothesis reply (transcript ++ [⟨input, reply⟩])

theorem distribution_map {S : Type*} (behavior : RandomSystem A)
    (function : R → S) (observation : Observation A R) :
    distribution behavior (map function observation) =
      Distribution.fTransform function (distribution behavior observation) :=
  distributionFrom_map behavior function observation []

theorem distribution_isProbDist (behavior : RandomSystem A)
    (observation : Observation A R) :
    (distribution behavior observation).isProbDist := by
  constructor
  · exact nonNeg_distributionFrom behavior observation []
  · rw [distribution, weight_distributionFrom, behavior.mass_nil]

/-- A finite observation that is pointwise constant on deterministic systems
has the corresponding one-point law on every cumulative random system. -/
theorem distributionFrom_eq_single_of_evaluateFrom_eq
    (behavior : RandomSystem A) (observation : Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A) (value : R)
    (constant : ∀ system : DDS A,
      evaluateFrom observation system (RandomSystem.Internal.Core.inputs transcript) =
        value) :
    distributionFrom behavior observation transcript =
      Finsupp.single value (behavior.mass transcript) := by
  induction observation generalizing transcript with
  | value result =>
      let rejecting : DDS A := fun _ => none
      have resultEqual : result = value := constant rejecting
      subst result
      rfl
  | query input continuation inductionHypothesis =>
      classical
      have branchConstant : ∀ reply, ∀ system : DDS A,
          evaluateFrom (continuation reply) system
              (RandomSystem.Internal.Core.inputs transcript ++ [input]) = value := by
        intro reply system
        let prescribed := setReply system (RandomSystem.Internal.Core.inputs transcript)
          input reply
        have selected := constant prescribed
        rw [evaluateFrom_query, innerReplyAt_setReply] at selected
        calc
          evaluateFrom (continuation reply) system
              (RandomSystem.Internal.Core.inputs transcript ++ [input]) =
              evaluateFrom (continuation reply) prescribed
                (RandomSystem.Internal.Core.inputs transcript ++ [input]) :=
            (evaluateFrom_setReply_of_length_le
              (continuation reply) system (RandomSystem.Internal.Core.inputs transcript)
              input reply (RandomSystem.Internal.Core.inputs transcript ++ [input])
              (by simp)).symm
          _ = value := selected
      have branchLaw : ∀ reply,
          distributionFrom behavior (continuation reply)
              (transcript ++ [⟨input, reply⟩]) =
            Finsupp.single value
              (behavior.mass (transcript ++ [⟨input, reply⟩])) := by
        intro reply
        apply inductionHypothesis reply
        intro system
        simpa [RandomSystem.Internal.Core.inputs,
          RandomSystems.Ambient.transcriptInputs] using
          branchConstant reply system
      rw [distributionFrom]
      apply Finsupp.ext
      intro candidate
      rw [Finsupp.sum_apply, Finsupp.single_apply]
      by_cases equal : candidate = value
      · subst candidate
        rw [if_pos rfl]
        calc
          (behavior.extensionLaw transcript input).sum
              (fun reply _ =>
                distributionFrom behavior (continuation reply)
                  (transcript ++ [⟨input, reply⟩]) value) =
              (behavior.extensionLaw transcript input).sum
                (fun reply _ =>
                  behavior.mass (transcript ++ [⟨input, reply⟩])) := by
            apply Finsupp.sum_congr
            intro reply membership
            rw [branchLaw reply, Finsupp.single_apply, if_pos rfl]
          _ = (behavior.extensionLaw transcript input).sum
              (fun _ weight => weight) := by
            apply Finsupp.sum_congr
            intro reply membership
            rw [behavior.extensionLaw_apply]
          _ = behavior.mass transcript :=
            behavior.extensionLaw_weight transcript input
      · rw [if_neg (Ne.symm equal)]
        rw [Finsupp.sum]
        apply Finset.sum_eq_zero
        intro reply membership
        rw [branchLaw reply, Finsupp.single_apply,
          if_neg (Ne.symm equal)]

/-- Finite observations that define the same functional on every deterministic
DDS have the same law on every cumulative random system. -/
theorem distributionFrom_eq_of_evaluateFrom_eq
    (behavior : RandomSystem A) (left right : Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A)
    (equal : ∀ system : DDS A,
      evaluateFrom left system (RandomSystem.Internal.Core.inputs transcript) =
        evaluateFrom right system (RandomSystem.Internal.Core.inputs transcript)) :
    distributionFrom behavior left transcript =
      distributionFrom behavior right transcript := by
  induction left generalizing right transcript with
  | value leftValue =>
      cases right with
      | value rightValue =>
          let rejecting : DDS A := fun _ => none
          have valuesEqual : leftValue = rightValue := equal rejecting
          subst rightValue
          rfl
      | query rightInput rightContinuation =>
          have rightConstant : ∀ system : DDS A,
              evaluateFrom (.query rightInput rightContinuation) system
                  (RandomSystem.Internal.Core.inputs transcript) = leftValue := by
            intro system
            exact (equal system).symm
          exact (distributionFrom_eq_single_of_evaluateFrom_eq behavior
            (.query rightInput rightContinuation) transcript leftValue
            rightConstant).symm
  | query leftInput leftContinuation inductionHypothesis =>
      cases right with
      | value rightValue =>
          exact distributionFrom_eq_single_of_evaluateFrom_eq behavior
            (.query leftInput leftContinuation) transcript rightValue equal
      | query rightInput rightContinuation =>
          classical
          by_cases sameInput : leftInput = rightInput
          · subst rightInput
            rw [distributionFrom, distributionFrom]
            apply Finsupp.sum_congr
            intro reply membership
            let childTranscript : RandomSystem.Internal.Core.Transcript A :=
              transcript ++ [⟨leftInput, reply⟩]
            change distributionFrom behavior (leftContinuation reply)
                childTranscript =
              distributionFrom behavior (rightContinuation reply)
                childTranscript
            apply inductionHypothesis reply (rightContinuation reply)
              childTranscript
            intro system
            let prescribed := setReply system
              (RandomSystem.Internal.Core.inputs transcript) leftInput reply
            have selected := equal prescribed
            rw [evaluateFrom_query, evaluateFrom_query,
              innerReplyAt_setReply] at selected
            have leftUnchanged := evaluateFrom_setReply_of_length_le
              (leftContinuation reply) system (RandomSystem.Internal.Core.inputs transcript)
              leftInput reply (RandomSystem.Internal.Core.inputs transcript ++ [leftInput])
              (by simp)
            have rightUnchanged := evaluateFrom_setReply_of_length_le
              (rightContinuation reply) system (RandomSystem.Internal.Core.inputs transcript)
              leftInput reply (RandomSystem.Internal.Core.inputs transcript ++ [leftInput])
              (by simp)
            simpa [childTranscript, RandomSystem.Internal.Core.inputs,
              RandomSystems.Ambient.transcriptInputs] using
              leftUnchanged.symm.trans (selected.trans rightUnchanged)
          · let leftReference := referenceLeaf (leftContinuation none)
            let rightReference := referenceLeaf (rightContinuation none)
            have leafResultsEqual : ∀
                (leftReply : Option (A.answer leftInput))
                (leftLeaf : Leaf (leftContinuation leftReply))
                (rightReply : Option (A.answer rightInput))
                (rightLeaf : Leaf (rightContinuation rightReply)),
                leftLeaf.result = rightLeaf.result := by
              intro leftReply leftLeaf rightReply rightLeaf
              obtain ⟨system, realizesLeft, realizesRight⟩ :=
                exists_answersFrom_eq_pair_of_first_ne
                  (RandomSystem.Internal.Core.inputs transcript) sameInput leftReply
                  rightReply leftLeaf.transcript rightLeaf.transcript
              calc
                leftLeaf.result = evaluateFrom
                    (.query leftInput leftContinuation) system
                    (RandomSystem.Internal.Core.inputs transcript) :=
                  (evaluateFrom_eq_leaf_result
                    (Leaf.query leftReply leftLeaf) system
                    (RandomSystem.Internal.Core.inputs transcript) realizesLeft).symm
                _ = evaluateFrom (.query rightInput rightContinuation) system
                    (RandomSystem.Internal.Core.inputs transcript) := equal system
                _ = rightLeaf.result :=
                  evaluateFrom_eq_leaf_result
                    (Leaf.query rightReply rightLeaf) system
                    (RandomSystem.Internal.Core.inputs transcript) realizesRight
            have referencesEqual : leftReference.result =
                rightReference.result :=
              leafResultsEqual none leftReference none rightReference
            have leftConstant : ∀ system : DDS A,
                evaluateFrom (.query leftInput leftContinuation) system
                    (RandomSystem.Internal.Core.inputs transcript) =
                  leftReference.result := by
              intro system
              rw [evaluateFrom_query]
              let reply := Attachment.innerReplyAt system
                (RandomSystem.Internal.Core.inputs transcript) leftInput
              let leaf := selectedLeaf (leftContinuation reply) system
                (RandomSystem.Internal.Core.inputs transcript ++ [leftInput])
              calc
                evaluateFrom (leftContinuation reply) system
                    (RandomSystem.Internal.Core.inputs transcript ++ [leftInput]) =
                    leaf.result := by
                  exact (selectedLeaf_result (leftContinuation reply) system
                    (RandomSystem.Internal.Core.inputs transcript ++ [leftInput])).symm
                _ = rightReference.result :=
                  leafResultsEqual reply leaf none rightReference
                _ = leftReference.result := referencesEqual.symm
            have rightConstant : ∀ system : DDS A,
                evaluateFrom (.query rightInput rightContinuation) system
                    (RandomSystem.Internal.Core.inputs transcript) =
                  leftReference.result := by
              intro system
              rw [evaluateFrom_query]
              let reply := Attachment.innerReplyAt system
                (RandomSystem.Internal.Core.inputs transcript) rightInput
              let leaf := selectedLeaf (rightContinuation reply) system
                (RandomSystem.Internal.Core.inputs transcript ++ [rightInput])
              calc
                evaluateFrom (rightContinuation reply) system
                    (RandomSystem.Internal.Core.inputs transcript ++ [rightInput]) =
                    leaf.result := by
                  exact (selectedLeaf_result (rightContinuation reply) system
                    (RandomSystem.Internal.Core.inputs transcript ++ [rightInput])).symm
                _ = leftReference.result :=
                  (leafResultsEqual none leftReference reply leaf).symm
            calc
              distributionFrom behavior
                  (.query leftInput leftContinuation) transcript =
                  Finsupp.single leftReference.result
                    (behavior.mass transcript) :=
                distributionFrom_eq_single_of_evaluateFrom_eq behavior
                  (.query leftInput leftContinuation) transcript
                  leftReference.result leftConstant
              _ = distributionFrom behavior
                  (.query rightInput rightContinuation) transcript :=
                (distributionFrom_eq_single_of_evaluateFrom_eq behavior
                  (.query rightInput rightContinuation) transcript
                  leftReference.result rightConstant).symm

/-- Root form of finite observational extensionality. -/
theorem distribution_eq_of_evaluate_eq
    (behavior : RandomSystem A) (left right : Observation A R)
    (equal : ∀ system : DDS A,
      evaluate left system = evaluate right system) :
    distribution behavior left = distribution behavior right :=
  distributionFrom_eq_of_evaluateFrom_eq behavior left right [] equal

/-- Match one displayed transcript and then continue with another finite
observation.  A mismatched answer returns `false`. -/
noncomputable def afterTranscript (target : RandomSystem.Internal.Core.Transcript A)
    (continuation : Observation A Bool) : Observation A Bool := by
  classical
  induction target with
  | nil => exact continuation
  | cons reply remaining inductionHypothesis =>
      exact .query reply.1 fun actual =>
        if equal : actual = reply.2 then inductionHypothesis else .value false

/-- Accept exactly one displayed transcript. -/
noncomputable def accepts (target : RandomSystem.Internal.Core.Transcript A) :
    Observation A Bool :=
  afterTranscript target (.value true)

/-- Match a displayed transcript, issue one further query, and return its
optional reply.  `none` in the outer option denotes failure to match the
displayed prefix. -/
noncomputable def replyAfter (target : RandomSystem.Internal.Core.Transcript A)
    (query : A.query) : Observation A (Option (Option (A.answer query))) := by
  classical
  induction target with
  | nil => exact .query query fun reply => .value (some reply)
  | cons expected remaining inductionHypothesis =>
      exact .query expected.1 fun actual =>
        if equal : actual = expected.2 then inductionHypothesis else .value none

/-- One total query returning the selected optional answer. -/
def replyObservation (query : A.query) :
    Observation A (Option (A.answer query)) :=
  .query query fun reply => .value reply

/-- Boolean selector for one concrete value. -/
noncomputable def selectsValue {T : Type*} (expected candidate : T) : Bool := by
  classical
  exact if candidate = expected then true else false

@[simp]
theorem afterTranscript_nil (continuation : Observation A Bool) :
    afterTranscript [] continuation = continuation :=
  rfl

@[simp]
theorem afterTranscript_cons (query : A.query)
    (expected : Option (A.answer query))
    (remaining : RandomSystem.Internal.Core.Transcript A)
    (continuation : Observation A Bool) :
    afterTranscript (⟨query, expected⟩ :: remaining) continuation =
      (by
        classical
        exact .query query fun actual =>
          if actual = expected then afterTranscript remaining continuation
          else .value false) := by
  classical
  rfl

@[simp]
theorem replyAfter_cons (prefixQuery : A.query)
    (expected : Option (A.answer prefixQuery))
    (remaining : RandomSystem.Internal.Core.Transcript A) (query : A.query) :
    replyAfter (⟨prefixQuery, expected⟩ :: remaining) query =
      (by
        classical
        exact .query prefixQuery fun actual =>
          if actual = expected then replyAfter remaining query else .value none) := by
  classical
  rfl

/-- Forgetting the concrete next reply records exactly whether the displayed
prefix matched; the final total query contributes no further condition. -/
theorem map_isSome_replyAfter (target : RandomSystem.Internal.Core.Transcript A)
    (query : A.query) :
    map Option.isSome (replyAfter target query) =
      afterTranscript target
        (map (fun _ => true) (replyObservation query)) := by
  classical
  induction target with
  | nil => rfl
  | cons expected remaining inductionHypothesis =>
      rcases expected with ⟨prefixQuery, expectedReply⟩
      rw [replyAfter_cons, afterTranscript_cons, map_query]
      apply congrArg (Observation.query prefixQuery)
      funext actual
      by_cases equal : actual = expectedReply
      · simp only [equal, if_pos, inductionHypothesis]
      · simp only [equal, if_false, map_value]
        rfl

/-- The predicate selecting one concrete next reply is the exact longer
transcript matcher. -/
theorem map_eq_some_replyAfter (target : RandomSystem.Internal.Core.Transcript A)
    (query : A.query) (expected : Option (A.answer query)) :
    map (fun candidate => selectsValue (some expected) candidate)
        (replyAfter target query) =
      accepts (target ++ [⟨query, expected⟩]) := by
  classical
  induction target with
  | nil =>
      change Observation.query query
          (fun actual => .value
            (selectsValue (some expected) (some actual))) =
        Observation.query query (fun actual =>
          if actual = expected then .value true else .value false)
      apply congrArg (Observation.query query)
      funext actual
      by_cases equal : actual = expected
      · subst actual
        simp [selectsValue]
      · simp [selectsValue, equal]
  | cons headReply remaining inductionHypothesis =>
      rcases headReply with ⟨prefixQuery, expectedReply⟩
      rw [replyAfter_cons, map_query, accepts]
      change _ = afterTranscript
        (⟨prefixQuery, expectedReply⟩ ::
          (remaining ++ [⟨query, expected⟩])) (.value true)
      rw [afterTranscript_cons]
      apply congrArg (Observation.query prefixQuery)
      funext actual
      by_cases equal : actual = expectedReply
      · simp only [equal, if_pos, inductionHypothesis]
        rfl
      · simp [equal, selectsValue]

/-- The `true` atom after applying a one-value selector is exactly the mass of
that value. -/
theorem fTransform_selectsValue_true {T : Type*}
    (law : Distribution T) (expected : T) :
    Distribution.fTransform (selectsValue expected) law true =
      law expected := by
  classical
  rw [Distribution.fTransform_apply_eq_mass]
  calc
    law.mass (fun candidate => selectsValue expected candidate = true) =
        law.mass (fun candidate => candidate = expected) := by
      apply Distribution.mass_congr
      intro candidate
      simp only [selectsValue]
      by_cases equal : candidate = expected <;> simp [equal]
    _ = law expected := Distribution.mass_singleton law expected

/-- Drop the failure atom of a prefix matcher and forget the outer success
tag. -/
noncomputable def successProjection {T : Type*} [Inhabited T]
    (law : Distribution (Option T)) : Distribution T :=
  Distribution.fTransform (fun candidate => candidate.getD default)
    (law.restrict fun candidate => candidate.isSome = true)

theorem successProjection_apply {T : Type*} [Inhabited T]
    (law : Distribution (Option T)) (value : T) :
    successProjection law value = law (some value) := by
  classical
  rw [successProjection, Distribution.fTransform_apply_eq_mass,
    Distribution.mass_restrict]
  calc
    law.mass (fun candidate =>
        candidate.getD default = value ∧ candidate.isSome = true) =
        law.mass (fun candidate => candidate = some value) := by
      apply Distribution.mass_congr
      intro candidate
      cases candidate <;> simp
    _ = law (some value) := Distribution.mass_singleton law (some value)

theorem successProjection_nonNeg {T : Type*} [Inhabited T]
    {law : Distribution (Option T)} (nonnegative : law.NonNeg) :
    (successProjection law).NonNeg :=
  (nonnegative.restrict _).fTransform _

theorem successProjection_weight {T : Type*} [Inhabited T]
    (law : Distribution (Option T)) :
    (successProjection law).weight =
      law.mass (fun candidate => candidate.isSome = true) := by
  rw [successProjection, Distribution.weight_fTransform,
    Distribution.weight_restrict]

/-- The probability of a selected observation leaf is exactly the cumulative
mass of its complete reply transcript. -/
theorem distributionFrom_enumerate_apply (behavior : RandomSystem A)
    {observation : Observation A R} (leaf : Leaf observation)
    (prior : RandomSystem.Internal.Core.Transcript A) :
    distributionFrom behavior (enumerate observation) prior leaf =
      behavior.mass (prior ++ leaf.transcript) := by
  classical
  induction leaf generalizing prior with
  | value result =>
      simp [enumerate, Leaf.transcript]
  | @query input continuation reply leaf inductionHypothesis =>
      rw [enumerate, distributionFrom, Finsupp.sum_apply]
      rw [Finsupp.sum_eq_single reply]
      · rw [distributionFrom_map]
        rw [Distribution.fTransform_injective_apply]
        · rw [inductionHypothesis]
          congr 1
          simp [Leaf.transcript]
        · intro left right equal
          injection equal
      · intro actual supported different
        rw [distributionFrom_map]
        apply Distribution.fTransform_apply_of_forall_ne
        intro candidate equal
        have : actual = reply := by
          injection equal
        exact different this
      · intro zero
        rw [distributionFrom_map]
        rw [Distribution.fTransform_injective_apply]
        · rw [inductionHypothesis]
          apply mass_append_eq_zero
          rw [← behavior.extensionLaw_apply]
          exact zero
        · intro left right equal
          injection equal

theorem distributionFrom_accepts_true (behavior : RandomSystem A)
    (prior target : RandomSystem.Internal.Core.Transcript A) :
    distributionFrom behavior (accepts target) prior true =
      behavior.mass (prior ++ target) := by
  classical
  induction target generalizing prior with
  | nil => simp [accepts, afterTranscript]
  | cons reply remaining inductionHypothesis =>
      rcases reply with ⟨query, expected⟩
      rw [accepts, afterTranscript_cons, distributionFrom, Finsupp.sum_apply]
      rw [Finsupp.sum_eq_single expected]
      · simp only [if_pos]
        change distributionFrom behavior (accepts remaining)
          (prior ++ [⟨query, expected⟩]) true = _
        rw [inductionHypothesis]
        congr 1
        simp
      · intro actual supported different
        simp [different]
      · intro zero
        simp only [if_pos]
        change distributionFrom behavior (accepts remaining)
          (prior ++ [⟨query, expected⟩]) true = 0
        rw [inductionHypothesis]
        apply mass_append_eq_zero
        rw [← behavior.extensionLaw_apply]
        exact zero

@[simp]
theorem distribution_accepts_true (behavior : RandomSystem A)
    (target : RandomSystem.Internal.Core.Transcript A) :
    distribution behavior (accepts target) true = behavior.mass target := by
  simpa [distribution] using distributionFrom_accepts_true behavior [] target

end Observation


end

end RandomSystem.Internal


/-! ## Internal observation-distance lemmas -/

namespace RandomSystem.Internal.Metric

open Probability
open Probability.Distribution
open scoped ENNReal

/-- On any finite-support carrier, statistical distance is attained by the
event on which the first law is pointwise larger. -/
theorem statDist_eq_mass_sub_mass_pos_support {A : Type*}
    (X Y : Distribution A) :
    Probability.statDist X Y =
      X.mass (fun a => Y a < X a) - Y.mass (fun a => Y a < X a) := by
  classical
  let support := X.support ∪ Y.support
  have differenceSupport : (X - Y).support ⊆ support :=
    Finsupp.support_sub
  rw [Probability.statDist_eq_sum_of_support_subset X Y differenceSupport,
    Distribution.mass_eq_sum_of_support_subset X Finset.subset_union_left
      (fun a => Y a < X a),
    Distribution.mass_eq_sum_of_support_subset Y Finset.subset_union_right
      (fun a => Y a < X a),
    ← Finset.sum_sub_distrib]
  symm
  calc
    ∑ a ∈ support.filter (fun a => Y a < X a), (X a - Y a) =
        ∑ a ∈ support.filter (fun a => Y a < X a),
          max (X a - Y a) 0 := by
      apply Finset.sum_congr rfl
      intro a member
      rw [Finset.mem_filter] at member
      exact (max_eq_left (sub_nonneg.mpr member.2.le)).symm
    _ = ∑ a ∈ support, max (X a - Y a) 0 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro a inSupport notInFilter
      have notLarger : ¬ Y a < X a := by
        intro larger
        exact notInFilter (Finset.mem_filter.mpr ⟨inSupport, larger⟩)
      rw [max_eq_right (sub_nonpos.mpr (not_lt.mp notLarger))]

/-- The canonical Boolean postprocessing attains statistical distance on any
finite-support carrier. -/
theorem statDist_fTransform_positive_eq {A : Type*}
    (X Y : Distribution A) :
    Probability.statDist
        (Distribution.fTransform (fun a => decide (Y a < X a)) X)
        (Distribution.fTransform (fun a => decide (Y a < X a)) Y) =
      Probability.statDist X Y := by
  classical
  apply le_antisymm
  · exact Probability.statDist_fTransform_le X Y
      (fun a => decide (Y a < X a))
  · rw [statDist_eq_mass_sub_mass_pos_support]
    calc
      X.mass (fun a => Y a < X a) - Y.mass (fun a => Y a < X a) =
          (Distribution.fTransform (fun a => decide (Y a < X a)) X).mass
              (fun result => result = true) -
            (Distribution.fTransform (fun a => decide (Y a < X a)) Y).mass
              (fun result => result = true) := by
        rw [Distribution.mass_fTransform, Distribution.mass_fTransform]
        apply congrArg₂ (fun left right : ℝ => left - right)
        · apply Distribution.mass_congr
          intro a
          simp [decide_eq_true_eq]
        · apply Distribution.mass_congr
          intro a
          simp [decide_eq_true_eq]
      _ ≤ Probability.statDist
          (Distribution.fTransform (fun a => decide (Y a < X a)) X)
          (Distribution.fTransform (fun a => decide (Y a < X a)) Y) :=
        Probability.mass_sub_mass_le_statDist _ _ _

/-! ## A generic observation supremum

This block isolates the metric argument from the representation of cumulative
random systems. The `treeLaw` declaration below supplies its concrete
instantiation.
-/

section ObservationMetric

variable {Resource Test Result : Type*}
variable (law : Resource → Test → ProbDist Result)

/-- Supremum statistical distance over one fixed family of tests. -/
noncomputable def observationDistance (left right : Resource) : ℝ :=
  sSup (Set.range fun test : Test =>
    statDist (law left test).1 (law right test).1)

lemma statDist_le_observationDistance
    (left right : Resource) (test : Test) :
    statDist (law left test).1 (law right test).1 ≤
      observationDistance law left right := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro value ⟨candidate, rfl⟩
    calc
      statDist (law left candidate).1 (law right candidate).1 ≤
          (law left candidate).1.weight :=
        statDist_le_weight
          (law left candidate).2.nonNeg
          (law right candidate).2.nonNeg
      _ = 1 := (law left candidate).2.weight_eq
  · exact ⟨test, rfl⟩

lemma observationDistance_nonneg (left right : Resource) :
    0 ≤ observationDistance law left right := by
  apply Real.sSup_nonneg
  rintro value ⟨test, rfl⟩
  exact statDist_nonneg _ _

@[simp]
theorem observationDistance_self (resource : Resource) :
    observationDistance law resource resource = 0 := by
  apply le_antisymm
  · exact Real.sSup_le (by
      rintro value ⟨test, rfl⟩
      simp [Probability.statDist_self]) le_rfl
  · exact observationDistance_nonneg law resource resource

theorem observationDistance_comm (left right : Resource) :
    observationDistance law left right = observationDistance law right left := by
  unfold observationDistance
  apply congrArg sSup
  apply congrArg Set.range
  funext test
  rw [Probability.statDist_symm_of_eq_weight _ _
    ((law left test).property.weight_eq.trans
      (law right test).property.weight_eq.symm)]

theorem observationDistance_triangle (left middle right : Resource) :
    observationDistance law left right ≤
      observationDistance law left middle + observationDistance law middle right := by
  apply Real.sSup_le
  · rintro value ⟨test, rfl⟩
    exact (Probability.statDist_triangle _ _ _).trans
      (add_le_add
        (statDist_le_observationDistance law left middle test)
        (statDist_le_observationDistance law middle right test))
  · exact add_nonneg
      (observationDistance_nonneg law left middle)
      (observationDistance_nonneg law middle right)

/-- Path tests separate a concrete random-system carrier precisely when equality of
all their output laws implies equality of resources. -/
def TestsSeparate : Prop :=
  ∀ {left right : Resource},
    (∀ test, law left test = law right test) → left = right

theorem statDist_eq_zero_of_probDist {A : Type*}
    (left right : ProbDist A)
    (h : statDist left.1 right.1 = 0) : left = right := by
  apply Subtype.ext
  apply Finsupp.ext
  intro a
  have hle : left.1 a ≤ right.1 a := by
    by_contra hnot
    have hpositive : 0 < max (left.1 a - right.1 a) 0 := by
      rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hnot))]
      linarith
    have hmem : a ∈ (left.1 - right.1).support := by
      rw [Finsupp.mem_support_iff, Finsupp.sub_apply]
      linarith
    have : 0 < statDist left.1 right.1 := by
      rw [Probability.statDist]
      exact hpositive.trans_le (Finset.single_le_sum
        (fun b _ => le_max_right (left.1 b - right.1 b) 0) hmem)
    linarith
  have hge : right.1 a ≤ left.1 a := by
    have hsym : statDist right.1 left.1 = 0 := by
      rw [Probability.statDist_symm_of_eq_weight _ _
        (right.property.weight_eq.trans left.property.weight_eq.symm), h]
    by_contra hnot
    have hpositive : 0 < max (right.1 a - left.1 a) 0 := by
      rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hnot))]
      linarith
    have hmem : a ∈ (right.1 - left.1).support := by
      rw [Finsupp.mem_support_iff, Finsupp.sub_apply]
      linarith
    have : 0 < statDist right.1 left.1 := by
      rw [Probability.statDist]
      exact hpositive.trans_le (Finset.single_le_sum
        (fun b _ => le_max_right (right.1 b - left.1 b) 0) hmem)
    linarith
  exact le_antisymm hle hge

theorem observationDistance_eq_zero_iff
    (separates : TestsSeparate law) (left right : Resource) :
    observationDistance law left right = 0 ↔ left = right := by
  constructor
  · intro equal
    apply separates
    intro test
    apply statDist_eq_zero_of_probDist
    exact le_antisymm
      ((statDist_le_observationDistance law left right test).trans_eq equal)
      (Probability.statDist_nonneg _ _)
  · rintro rfl
    exact observationDistance_self law left

/-- Data processing at the test-supremum level: attachment is non-expanding
when every outer test factors through one inner test. -/
theorem observationDistance_map_le
    {Resource' Test' : Type*}
    (law' : Resource' → Test' → ProbDist Result)
    (mapResource : Resource → Resource')
    (mapTest : Test' → Test)
    (factor : ∀ resource test,
      law' (mapResource resource) test = law resource (mapTest test))
    (left right : Resource) :
    observationDistance law' (mapResource left) (mapResource right) ≤
      observationDistance law left right := by
  apply Real.sSup_le
  · rintro value ⟨test, rfl⟩
    change statDist (law' (mapResource left) test).1
      (law' (mapResource right) test).1 ≤
        observationDistance law left right
    rw [factor left test, factor right test]
    exact statDist_le_observationDistance law left right (mapTest test)
  · exact observationDistance_nonneg law left right



end ObservationMetric

end RandomSystem.Internal.Metric


/-! ## Existing DDE observations and cumulative distance -/

open RandomSystem.Internal
open RandomSystem.Internal.Core
open scoped ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RandomSystem

variable {A : Interface.{u, v}}

namespace Internal

/-! ### Existing functional DDE observations

`Observation` is internal proof machinery.  The exposed observation family
below is the already-settled `Ambient.DDE` together with a finite number of
rounds.  Its output is the finite attempted-query transcript.
-/

/-- Functional interaction with an existing DDE, starting from a displayed
transcript. -/
def ddeObservationFrom (environment : DDE A) :
    Nat → RandomSystem.Internal.Core.Transcript A →
      Observation A (RandomSystem.Internal.Core.Transcript A)
  | 0, transcript => .value transcript
  | rounds + 1, transcript =>
      match environment transcript with
      | none => .value transcript
      | some query =>
          .query query fun reply =>
            ddeObservationFrom environment rounds
              (transcript ++ [⟨query, reply⟩])

/-- The root observation induced by an existing functional DDE and a finite
round count. -/
def ddeObservation (environment : DDE A) (rounds : Nat) :
    Observation A (RandomSystem.Internal.Core.Transcript A) :=
  ddeObservationFrom environment rounds []

def advanceTranscript (system : DDS A) (environment : DDE A)
    (transcript : RandomSystem.Internal.Core.Transcript A) : RandomSystem.Internal.Core.Transcript A :=
  match environment transcript with
  | none => transcript
  | some query => transcript ++ [⟨query,
      Attachment.innerReplyAt system (RandomSystem.Internal.Core.inputs transcript) query⟩]

def advanceTranscriptN (system : DDS A) (environment : DDE A) :
    Nat → RandomSystem.Internal.Core.Transcript A → RandomSystem.Internal.Core.Transcript A
  | 0, transcript => transcript
  | rounds + 1, transcript =>
      advanceTranscriptN system environment rounds
        (advanceTranscript system environment transcript)

theorem advanceTranscriptN_succ_last (system : DDS A)
    (environment : DDE A) (rounds : Nat)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    advanceTranscriptN system environment (rounds + 1) transcript =
      advanceTranscript system environment
        (advanceTranscriptN system environment rounds transcript) := by
  induction rounds generalizing transcript with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [advanceTranscriptN, inductionHypothesis]
      rfl

theorem advanceTranscriptN_eq_of_none (system : DDS A)
    (environment : DDE A) (rounds : Nat)
    (transcript : RandomSystem.Internal.Core.Transcript A)
    (stopped : environment transcript = none) :
    advanceTranscriptN system environment rounds transcript = transcript := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [advanceTranscriptN, advanceTranscript, stopped,
        inductionHypothesis]

theorem evaluateFrom_ddeObservationFrom
    (system : DDS A) (environment : DDE A) (rounds : Nat)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    Observation.evaluateFrom (ddeObservationFrom environment rounds transcript)
        system (RandomSystem.Internal.Core.inputs transcript) =
      advanceTranscriptN system environment rounds transcript := by
  induction rounds generalizing transcript with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [ddeObservationFrom]
      cases selected : environment transcript with
      | none =>
          simp only [Observation.evaluateFrom_value]
          exact (advanceTranscriptN_eq_of_none system environment
            (rounds + 1) transcript selected).symm
      | some query =>
          simp only [Observation.evaluateFrom_query]
          change Observation.evaluateFrom
              (ddeObservationFrom environment rounds
                (transcript ++ [⟨query,
                  Attachment.innerReplyAt system
                    (RandomSystem.Internal.Core.inputs transcript) query⟩]))
              system
              (RandomSystem.Internal.Core.inputs transcript ++ [query]) = _
          calc
            Observation.evaluateFrom
                (ddeObservationFrom environment rounds
                  (transcript ++ [⟨query,
                    Attachment.innerReplyAt system
                      (RandomSystem.Internal.Core.inputs transcript) query⟩]))
                system (RandomSystem.Internal.Core.inputs transcript ++ [query]) =
              advanceTranscriptN system environment rounds
                (transcript ++ [⟨query,
                  Attachment.innerReplyAt system
                    (RandomSystem.Internal.Core.inputs transcript) query⟩]) := by
                have inputsEqual : RandomSystem.Internal.Core.inputs
                    (transcript ++ [⟨query,
                      Attachment.innerReplyAt system
                        (RandomSystem.Internal.Core.inputs transcript) query⟩]) =
                    RandomSystem.Internal.Core.inputs transcript ++ [query] := by
                  simp [RandomSystem.Internal.Core.inputs,
                    RandomSystems.Ambient.transcriptInputs]
                rw [← inputsEqual]
                exact inductionHypothesis
                  (transcript ++ [⟨query,
                    Attachment.innerReplyAt system
                      (RandomSystem.Internal.Core.inputs transcript) query⟩])
            _ = advanceTranscriptN system environment (rounds + 1)
                transcript := by
              rw [advanceTranscriptN, advanceTranscript, selected]

theorem advanceTranscriptN_nil_eq_transcript
    (system : DDS A) (environment : DDE A) (rounds : Nat) :
    advanceTranscriptN system environment rounds [] =
      RandomSystems.Ambient.transcript system environment rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [advanceTranscriptN_succ_last, inductionHypothesis,
        RandomSystems.Ambient.transcript_succ]
      rfl

/-- The internal tree corresponding to an existing finite-round DDE returns
exactly the established attempted-query transcript. -/
theorem evaluate_ddeObservation (system : DDS A) (environment : DDE A)
    (rounds : Nat) :
    Observation.evaluate (ddeObservation environment rounds) system =
      RandomSystems.Ambient.transcript system environment rounds := by
  change Observation.evaluateFrom
      (ddeObservationFrom environment rounds []) system
        (RandomSystem.Internal.Core.inputs ([] : RandomSystem.Internal.Core.Transcript A)) = _
  rw [evaluateFrom_ddeObservationFrom,
    advanceTranscriptN_nil_eq_transcript]

end Internal

/-- The normalized finite transcript law selected by an existing DDE. -/
noncomputable def ddeLaw (behavior : RandomSystem A)
    (environment : DDE A) (rounds : Nat) :
    Distribution.ProbDist (RandomSystem.Internal.Core.Transcript A) :=
  ⟨Observation.distribution behavior
      (Internal.ddeObservation environment rounds),
    Observation.distribution_isProbDist behavior _⟩

namespace Internal

theorem mem_support_fTransform_of_mem_support_of_nonNeg
    {S T : Type*} {law : Distribution S} (nonnegative : law.NonNeg)
    (function : S → T) {value : S} (supported : value ∈ law.support) :
    function value ∈ (Distribution.fTransform function law).support := by
  rw [Finsupp.mem_support_iff, Distribution.fTransform_apply_eq_mass]
  intro fiberZero
  have atomLe : law value ≤
      law.mass (fun candidate => function candidate = function value) :=
    Distribution.apply_le_mass nonnegative rfl
  have atomZero : law value = 0 :=
    le_antisymm (atomLe.trans_eq fiberZero) (nonnegative value)
  exact (Finsupp.mem_support_iff.mp supported) atomZero

theorem evaluateFrom_accepts_eq_true_iff
    (system : DDS A) (prior : List A.query)
    (target : RandomSystem.Internal.Core.Transcript A) :
    Observation.evaluateFrom (Observation.accepts target) system prior = true ↔
      RandomSystem.Internal.Core.answersFrom system prior (RandomSystem.Internal.Core.inputs target) =
        target := by
  induction target generalizing prior with
  | nil =>
      rw [show Observation.accepts
        ([] : RandomSystem.Internal.Core.Transcript A) = .value true from rfl]
      simp [RandomSystem.Internal.Core.inputs, RandomSystems.Ambient.transcriptInputs]
  | cons reply remaining inductionHypothesis =>
      rcases reply with ⟨query, expected⟩
      rw [Observation.accepts, Observation.afterTranscript_cons,
        Observation.evaluateFrom_query]
      simp only [RandomSystem.Internal.Core.inputs,
        RandomSystems.Ambient.transcriptInputs, List.map_cons,
        RandomSystem.Internal.Core.answersFrom_cons]
      let actual := Attachment.innerReplyAt system prior query
      by_cases equal : actual = expected
      · simp only [actual, equal, if_pos]
        change
          Observation.evaluateFrom (Observation.accepts remaining) system
              (prior ++ [query]) = true ↔
            ⟨query, expected⟩ ::
                RandomSystem.Internal.Core.answersFrom system (prior ++ [query])
                  (RandomSystem.Internal.Core.inputs remaining) =
              ⟨query, expected⟩ :: remaining
        simp only [List.cons.injEq, true_and]
        exact inductionHypothesis (prior ++ [query])
      · simp only [actual, equal, if_false,
          Observation.evaluateFrom_value, Bool.false_eq_true]
        constructor
        · intro impossible
          contradiction
        · intro transcriptEqual
          have headEqual := congrArg List.head? transcriptEqual
          have actualEqual : actual = expected := by
            simpa [actual] using headEqual
          exact equal actualEqual

theorem evaluate_accepts_eq_true_iff
    (system : DDS A) (target : RandomSystem.Internal.Core.Transcript A) :
    Observation.evaluate (Observation.accepts target) system = true ↔
      RandomSystem.Internal.Core.Agrees system target := by
  exact evaluateFrom_accepts_eq_true_iff system [] target

/-- Internal finite observations of an embedded finite PDS are exactly the
deterministic pushforward of that PDS.  The displayed prefix restricts the
law to deterministic systems agreeing with it. -/
theorem distributionFrom_toRandomSystem
    (system : PDS A)
    {R : Type*} (observation : Observation A R)
    (transcript : RandomSystem.Internal.Core.Transcript A) :
    Observation.distributionFrom (PDS.toRandomSystem system)
        observation transcript =
      Distribution.fTransform
        (fun deterministicSystem =>
          Observation.evaluateFrom observation deterministicSystem
            (RandomSystem.Internal.Core.inputs transcript))
        (system.1.restrict fun deterministicSystem =>
          RandomSystem.Internal.Core.Agrees deterministicSystem transcript) := by
  induction observation generalizing transcript with
  | value result =>
      rw [Observation.distributionFrom_value]
      change Finsupp.single result
          (PDS.cylinderMass system transcript) =
        Distribution.fTransform (fun _ => result)
          (system.1.restrict fun deterministicSystem =>
            RandomSystem.Internal.Core.Agrees deterministicSystem transcript)
      rw [Distribution.fTransform_const_eq_single_weight,
        Distribution.weight_restrict]
      rfl
  | query query continuation inductionHypothesis =>
      classical
      apply Finsupp.ext
      intro result
      rw [Observation.distributionFrom_query]
      simp only [Finsupp.sum_apply]
      let priorLaw := system.1.restrict fun deterministicSystem =>
        RandomSystem.Internal.Core.Agrees deterministicSystem transcript
      let replyOf := fun deterministicSystem =>
        Attachment.innerReplyAt deterministicSystem
          (RandomSystem.Internal.Core.inputs transcript) query
      let replyLaw := Distribution.fTransform replyOf priorLaw
      have extensionLawEq :
          (PDS.toRandomSystem system).extensionLaw transcript query =
            replyLaw := by
        rfl
      rw [extensionLawEq]
      calc
        ∑ reply ∈ replyLaw.support,
            Observation.distributionFrom
                (PDS.toRandomSystem system) (continuation reply)
                (transcript ++ [⟨query, reply⟩]) result =
            ∑ reply ∈ replyLaw.support,
              priorLaw.mass (fun deterministicSystem =>
                Observation.evaluateFrom (continuation reply)
                    deterministicSystem
                    (RandomSystem.Internal.Core.inputs transcript ++ [query]) = result ∧
                  replyOf deterministicSystem = reply) := by
          apply Finset.sum_congr rfl
          intro reply supported
          rw [inductionHypothesis reply,
            Distribution.fTransform_apply_eq_mass,
            Distribution.mass_restrict]
          unfold priorLaw
          rw [Distribution.mass_restrict]
          apply Distribution.mass_congr
          intro deterministicSystem
          rw [RandomSystem.Internal.Core.agrees_append_singleton_iff]
          simp only [RandomSystem.Internal.Core.inputs,
            RandomSystems.Ambient.transcriptInputs, List.map_append,
            List.map_singleton]
          change
            (Observation.evaluateFrom (continuation reply)
                deterministicSystem
                (RandomSystem.Internal.Core.inputs transcript ++ [query]) = result ∧
              RandomSystem.Internal.Core.Agrees deterministicSystem transcript ∧
                replyOf deterministicSystem = reply) ↔ _
          constructor
          · rintro ⟨evaluates, agrees, replyEqual⟩
            exact ⟨⟨evaluates, replyEqual⟩, agrees⟩
          · rintro ⟨⟨evaluates, replyEqual⟩, agrees⟩
            exact ⟨evaluates, agrees, replyEqual⟩
        _ = priorLaw.mass (fun deterministicSystem =>
              Observation.evaluateFrom (.query query continuation)
                  deterministicSystem (RandomSystem.Internal.Core.inputs transcript) =
                result) := by
          have cover : ∀ deterministicSystem ∈ priorLaw.support,
              replyOf deterministicSystem ∈ replyLaw.support := by
            intro deterministicSystem supported
            exact mem_support_fTransform_of_mem_support_of_nonNeg
              (system.2.nonNeg.restrict _) replyOf supported
          rw [Distribution.mass_eq_sum_mass_fiber priorLaw
            (fun deterministicSystem =>
              Observation.evaluateFrom (.query query continuation)
                  deterministicSystem (RandomSystem.Internal.Core.inputs transcript) =
                result)
            replyOf replyLaw.support cover]
          apply Finset.sum_congr rfl
          intro reply supported
          apply Distribution.mass_congr
          intro deterministicSystem
          simp only [Observation.evaluateFrom_query]
          constructor
          · rintro ⟨evaluates, replyEqual⟩
            change Attachment.innerReplyAt deterministicSystem
              (RandomSystem.Internal.Core.inputs transcript) query = reply at replyEqual
            refine ⟨?_, replyEqual⟩
            rw [replyEqual]
            exact evaluates
          · rintro ⟨evaluates, replyEqual⟩
            change Attachment.innerReplyAt deterministicSystem
              (RandomSystem.Internal.Core.inputs transcript) query = reply at replyEqual
            refine ⟨?_, replyEqual⟩
            rw [replyEqual] at evaluates
            exact evaluates
        _ = Distribution.fTransform
              (fun deterministicSystem =>
                Observation.evaluateFrom (.query query continuation)
                  deterministicSystem (RandomSystem.Internal.Core.inputs transcript))
              priorLaw result :=
          (Distribution.fTransform_apply_eq_mass _ _ _).symm

/-- Root form of `distributionFrom_toRandomSystem`. -/
theorem distribution_toRandomSystem
    (system : PDS A)
    {R : Type*} (observation : Observation A R) :
    Observation.distribution (PDS.toRandomSystem system)
        observation =
      Distribution.fTransform (Observation.evaluate observation) system.1 := by
  rw [Observation.distribution]
  calc
    Observation.distributionFrom (PDS.toRandomSystem system)
        observation [] =
      Distribution.fTransform (Observation.evaluate observation)
        (system.1.restrict fun _ => True) := by
          rw [distributionFrom_toRandomSystem system observation []]
          congr 1
          apply Finsupp.ext
          intro deterministicSystem
          simp [Distribution.restrict_apply]
    _ = Distribution.fTransform (Observation.evaluate observation) system.1 := by
      congr 1
      apply Finsupp.ext
      intro deterministicSystem
      simp [Distribution.restrict_apply]

end Internal

/-- Existing finite-round DDE observation commutes exactly with the cumulative
interpretation of a finite PDS. -/
theorem ddeLaw_toRandomSystem
    (system : PDS A)
    (environment : DDE A) (rounds : Nat) :
    (ddeLaw (PDS.toRandomSystem system) environment rounds).1 =
      PDS.trLaw environment rounds system := by
  change Observation.distribution (PDS.toRandomSystem system)
      (Internal.ddeObservation environment rounds) = _
  rw [Internal.distribution_toRandomSystem]
  unfold PDS.trLaw RandomSystems.Ambient.trLaw
  apply Distribution.fTransform_congr
  intro deterministicSystem supported
  exact Internal.evaluate_ddeObservation deterministicSystem environment rounds

/-- The cumulative random-system advantage over existing functional DDEs and
finite observation lengths. Lanzenberger, Definition 2.26 (printed p. 18),
says: “the supremum is over all compatible `(Y,X)`-DDE.” -/
noncomputable def advantage (left right : RandomSystem A) : ℝ :=
  sSup (Set.range fun observation : DDE A × Nat =>
    Probability.statDist
      (ddeLaw left observation.1 observation.2).1
      (ddeLaw right observation.1 observation.2).1)

lemma statDist_ddeLaw_le_advantage
    (left right : RandomSystem A) (environment : DDE A) (rounds : Nat) :
    Probability.statDist (ddeLaw left environment rounds).1
        (ddeLaw right environment rounds).1 ≤
      advantage left right := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro value ⟨⟨candidate, count⟩, rfl⟩
    calc
      Probability.statDist
          (ddeLaw left candidate count).1
          (ddeLaw right candidate count).1 ≤
        (ddeLaw left candidate count).1.weight :=
          Probability.statDist_le_weight
            (ddeLaw left candidate count).2.nonNeg
            (ddeLaw right candidate count).2.nonNeg
      _ = 1 := (ddeLaw left candidate count).2.weight_eq
  · exact ⟨(environment, rounds), rfl⟩

lemma advantage_nonneg (left right : RandomSystem A) :
    0 ≤ advantage left right := by
  apply Real.sSup_nonneg
  rintro value ⟨⟨environment, rounds⟩, rfl⟩
  exact Probability.statDist_nonneg _ _

@[simp]
theorem advantage_self (behavior : RandomSystem A) :
    advantage behavior behavior = 0 := by
  apply le_antisymm
  · exact Real.sSup_le (by
      rintro value ⟨⟨environment, rounds⟩, rfl⟩
      simp [Probability.statDist_self]) le_rfl
  · exact advantage_nonneg behavior behavior

theorem advantage_comm (left right : RandomSystem A) :
    advantage left right = advantage right left := by
  unfold advantage
  apply congrArg sSup
  apply congrArg Set.range
  funext observation
  rw [Probability.statDist_symm_of_eq_weight _ _
    ((ddeLaw left observation.1 observation.2).property.weight_eq.trans
      (ddeLaw right observation.1 observation.2).property.weight_eq.symm)]

theorem advantage_triangle (left middle right : RandomSystem A) :
    advantage left right ≤ advantage left middle + advantage middle right := by
  apply Real.sSup_le
  · rintro value ⟨⟨environment, rounds⟩, rfl⟩
    exact (Probability.statDist_triangle _ _ _).trans
      (add_le_add
        (statDist_ddeLaw_le_advantage left middle environment rounds)
        (statDist_ddeLaw_le_advantage middle right environment rounds))
  · exact add_nonneg (advantage_nonneg left middle)
      (advantage_nonneg middle right)

/-- The cumulative interpretation is an exact isometry for finite presentation
advantage defined by the functional DDE carrier. -/
theorem advantage_toRandomSystem_eq
    (left right : PDS A) :
    advantage (PDS.toRandomSystem left)
        (PDS.toRandomSystem right) =
      PDS.advantage left right := by
  unfold advantage PDS.advantage
  apply congrArg sSup
  apply congrArg Set.range
  funext observation
  rw [ddeLaw_toRandomSystem, ddeLaw_toRandomSystem]

namespace Internal

/-! ### Internal branch-finite closure and its finite-horizon bound -/

/-- Uniformly truncate internal observation proof machinery.  A leaf is
retained at every horizon; a query at horizon zero receives the default
Boolean result. -/
noncomputable def truncate : Observation A Bool → Nat → Observation A Bool :=
  Observation.rec
    (motive := fun _ => Nat → Observation A Bool)
    (fun result _ => .value result)
    (fun query _ truncateAfter rounds =>
      match rounds with
      | 0 => .value false
      | rounds + 1 => .query query fun reply => truncateAfter reply rounds)

/-- For a pair of locally finite behaviors, every branch-finite internal
observation has a common finite horizon on the union of their reachable reply
supports. -/
noncomputable def commonRounds (left right : RandomSystem A) :
    Observation A Bool → RandomSystem.Internal.Core.Transcript A → Nat :=
  Observation.rec
    (motive := fun _ => RandomSystem.Internal.Core.Transcript A → Nat)
    (fun _ _ => 0)
    (fun query _ roundsAfter transcript =>
      1 + ((left.extensionLaw transcript query).support ∪
        (right.extensionLaw transcript query).support).sup
          (fun reply => roundsAfter reply
            (transcript ++ [⟨query, reply⟩])))

/-- Read the next query selected by an internal observation tree.  Histories
whose query tag does not match the tree lie outside the tree and stop. -/
noncomputable def nextQuery : Observation A Bool →
    RandomSystem.Internal.Core.Transcript A → Option A.query :=
  Observation.rec
    (motive := fun _ => RandomSystem.Internal.Core.Transcript A → Option A.query)
    (fun _ _ => none)
    (fun query _ next replies =>
      match replies with
      | [] => some query
      | reply :: remaining =>
          if equal : reply.1 = query then
            next (equal ▸ reply.2) remaining
          else none)

/-- Read the Boolean leaf selected by a complete on-tree transcript. -/
noncomputable def resultFromTranscript : Observation A Bool →
    RandomSystem.Internal.Core.Transcript A → Option Bool :=
  Observation.rec
    (motive := fun _ => RandomSystem.Internal.Core.Transcript A → Option Bool)
    (fun result _ => some result)
    (fun query _ resultAfter replies =>
      match replies with
      | [] => none
      | reply :: remaining =>
          if equal : reply.1 = query then
            resultAfter (equal ▸ reply.2) remaining
          else none)

/-- Existing DDE corresponding to one observation subtree below a displayed
prior transcript. -/
noncomputable def localDDE (observation : Observation A Bool)
    (prior : RandomSystem.Internal.Core.Transcript A) : DDE A :=
  fun transcript => nextQuery observation (transcript.drop prior.length)

/-- Terminal Boolean decoder for the same subtree and prior transcript. -/
noncomputable def localResult (observation : Observation A Bool)
    (prior : RandomSystem.Internal.Core.Transcript A) :
    RandomSystem.Internal.Core.Transcript A → Bool :=
  fun transcript =>
    (resultFromTranscript observation
      (transcript.drop prior.length)).getD false

theorem ddeObservationFrom_map_congr
    (first second : DDE A)
    (firstResult secondResult : RandomSystem.Internal.Core.Transcript A → Bool)
    (rounds : Nat) (current : RandomSystem.Internal.Core.Transcript A)
    (queriesEqual : ∀ suffix,
      first (current ++ suffix) = second (current ++ suffix))
    (resultsEqual : ∀ suffix,
      firstResult (current ++ suffix) = secondResult (current ++ suffix)) :
    Observation.map firstResult (ddeObservationFrom first rounds current) =
      Observation.map secondResult
        (ddeObservationFrom second rounds current) := by
  induction rounds generalizing current with
  | zero =>
      simpa [ddeObservationFrom] using resultsEqual []
  | succ rounds inductionHypothesis =>
      rw [ddeObservationFrom, ddeObservationFrom]
      have atCurrent := queriesEqual []
      simp only [List.append_nil] at atCurrent
      cases firstCurrent : first current with
      | none =>
          rw [firstCurrent] at atCurrent
          have secondCurrent : second current = none := atCurrent.symm
          rw [secondCurrent]
          simpa using resultsEqual []
      | some query =>
          rw [firstCurrent] at atCurrent
          have secondCurrent : second current = some query := atCurrent.symm
          rw [secondCurrent, Observation.map_query]
          apply congrArg (Observation.query query)
          funext reply
          apply inductionHypothesis
          · intro suffix
            simpa only [List.append_assoc, List.singleton_append] using
              queriesEqual (⟨query, reply⟩ :: suffix)
          · intro suffix
            simpa only [List.append_assoc, List.singleton_append] using
              resultsEqual (⟨query, reply⟩ :: suffix)

/-- Every uniformly truncated internal observation is exactly an existing DDE
observation followed by deterministic transcript postprocessing. -/
theorem map_ddeObservationFrom_local_eq_truncate
    (observation : Observation A Bool) (rounds : Nat)
    (prior : RandomSystem.Internal.Core.Transcript A) :
    Observation.map (localResult observation prior)
        (ddeObservationFrom (localDDE observation prior) rounds prior) =
      truncate observation rounds := by
  induction observation generalizing rounds prior with
  | value result =>
      cases rounds <;>
        simp [localDDE, localResult, nextQuery, resultFromTranscript,
          ddeObservationFrom, truncate]
  | query query continuation inductionHypothesis =>
      cases rounds with
      | zero =>
          simp [localResult, resultFromTranscript,
            ddeObservationFrom, truncate]
      | succ rounds =>
          rw [ddeObservationFrom]
          have atPrior : localDDE (.query query continuation) prior prior =
              some query := by
            simp [localDDE, nextQuery]
          rw [atPrior, Observation.map_query, truncate]
          apply congrArg (Observation.query query)
          funext reply
          let nextPrior := prior ++ [⟨query, reply⟩]
          calc
            Observation.map (localResult (.query query continuation) prior)
                (ddeObservationFrom (localDDE (.query query continuation) prior)
                  rounds nextPrior) =
              Observation.map (localResult (continuation reply) nextPrior)
                (ddeObservationFrom (localDDE (continuation reply) nextPrior)
                  rounds nextPrior) := by
                    apply ddeObservationFrom_map_congr
                    · intro suffix
                      unfold localDDE
                      have firstDrop :
                          ((nextPrior ++ suffix).drop prior.length) =
                            ⟨query, reply⟩ :: suffix := by
                        simp [nextPrior, List.append_assoc]
                      have secondDrop :
                          ((nextPrior ++ suffix).drop nextPrior.length) =
                            suffix := by
                        simp
                      rw [firstDrop, secondDrop]
                      simp [nextQuery]
                    · intro suffix
                      unfold localResult
                      have firstDrop :
                          ((nextPrior ++ suffix).drop prior.length) =
                            ⟨query, reply⟩ :: suffix := by
                        simp [nextPrior, List.append_assoc]
                      have secondDrop :
                          ((nextPrior ++ suffix).drop nextPrior.length) =
                            suffix := by
                        simp
                      rw [firstDrop, secondDrop]
                      simp [resultFromTranscript]
            _ = truncate (continuation reply) rounds :=
              inductionHypothesis reply rounds nextPrior

theorem distributionFrom_truncate_eq_of_side
    (left right behavior : RandomSystem A)
    (side : behavior = left ∨ behavior = right)
    (observation : Observation A Bool)
    (transcript : RandomSystem.Internal.Core.Transcript A) (rounds : Nat)
    (enough : commonRounds left right observation transcript ≤ rounds) :
    Observation.distributionFrom behavior (truncate observation rounds)
        transcript =
      Observation.distributionFrom behavior observation transcript := by
  induction observation generalizing transcript rounds with
  | value result =>
      simp [truncate]
  | query query continuation inductionHypothesis =>
      cases rounds with
      | zero =>
          simp [commonRounds] at enough
      | succ rounds =>
          rw [truncate, Observation.distributionFrom_query,
            Observation.distributionFrom_query]
          change
            Finsupp.sum (behavior.extensionLaw transcript query)
                (fun reply _ => Observation.distributionFrom behavior
                  (truncate (continuation reply) rounds)
                  (transcript ++ [⟨query, reply⟩])) =
              Finsupp.sum (behavior.extensionLaw transcript query)
                (fun reply _ => Observation.distributionFrom behavior
                  (continuation reply) (transcript ++ [⟨query, reply⟩]))
          apply Finsupp.sum_congr
          intro reply supported
          apply inductionHypothesis reply
          have inUnion : reply ∈
              (left.extensionLaw transcript query).support ∪
                (right.extensionLaw transcript query).support := by
            rcases side with rfl | rfl
            · exact Finset.mem_union_left _ supported
            · exact Finset.mem_union_right _ supported
          have childLe : commonRounds left right (continuation reply)
                (transcript ++ [⟨query, reply⟩]) ≤
              ((left.extensionLaw transcript query).support ∪
                (right.extensionLaw transcript query).support).sup
                  (fun candidate => commonRounds left right
                    (continuation candidate)
                    (transcript ++ [⟨query, candidate⟩])) :=
            Finset.le_sup
              (f := fun candidate => commonRounds left right
                (continuation candidate)
                (transcript ++ [⟨query, candidate⟩])) inUnion
          have supLe :
              ((left.extensionLaw transcript query).support ∪
                (right.extensionLaw transcript query).support).sup
                  (fun candidate => commonRounds left right
                    (continuation candidate)
                    (transcript ++ [⟨query, candidate⟩])) ≤ rounds := by
            change 1 +
                ((left.extensionLaw transcript query).support ∪
                  (right.extensionLaw transcript query).support).sup
                    (fun candidate => commonRounds left right
                      (continuation candidate)
                      (transcript ++ [⟨query, candidate⟩])) ≤
              rounds + 1 at enough
            omega
          exact childLe.trans supLe

theorem distribution_truncate_eq_left (left right : RandomSystem A)
    (observation : Observation A Bool)
    (rounds : Nat)
    (enough : commonRounds left right observation [] ≤ rounds) :
    Observation.distribution left (truncate observation rounds) =
      Observation.distribution left observation :=
  distributionFrom_truncate_eq_of_side left right left (Or.inl rfl)
    observation [] rounds enough

theorem distribution_truncate_eq_right (left right : RandomSystem A)
    (observation : Observation A Bool)
    (rounds : Nat)
    (enough : commonRounds left right observation [] ≤ rounds) :
    Observation.distribution right (truncate observation rounds) =
      Observation.distribution right observation :=
  distributionFrom_truncate_eq_of_side left right right (Or.inr rfl)
    observation [] rounds enough

/-- A normalized Boolean law obtained from internal finite-path proof
machinery. -/
noncomputable def treeLaw (behavior : RandomSystem A)
    (observation : Observation A Bool) : Distribution.ProbDist Bool :=
  ⟨Observation.distribution behavior observation,
    Observation.distribution_isProbDist behavior observation⟩

/-- Internal supremum over branch-finite Boolean observation trees.  The
public distance below is stated with the existing functional DDE and finite
rounds; the two are proved equal. -/
noncomputable def treeAdvantage (left right : RandomSystem A) : ℝ :=
  RandomSystem.Internal.Metric.observationDistance treeLaw left right

lemma treeAdvantage_nonneg (left right : RandomSystem A) :
    0 ≤ treeAdvantage left right :=
  RandomSystem.Internal.Metric.observationDistance_nonneg treeLaw left right

@[simp]
theorem treeAdvantage_self (behavior : RandomSystem A) :
    treeAdvantage behavior behavior = 0 :=
  RandomSystem.Internal.Metric.observationDistance_self treeLaw behavior

theorem treeAdvantage_comm (left right : RandomSystem A) :
    treeAdvantage left right = treeAdvantage right left :=
  RandomSystem.Internal.Metric.observationDistance_comm treeLaw left right

theorem treeAdvantage_triangle (left middle right : RandomSystem A) :
    treeAdvantage left right ≤
      treeAdvantage left middle + treeAdvantage middle right :=
  RandomSystem.Internal.Metric.observationDistance_triangle
    treeLaw left middle right

/-- Local finite support turns every branch-finite internal observation into
one existing DDE observation at a common finite horizon. -/
theorem treeAdvantage_le_advantage (left right : RandomSystem A) :
    treeAdvantage left right ≤ advantage left right := by
  unfold treeAdvantage RandomSystem.Internal.Metric.observationDistance
  apply Real.sSup_le
  · rintro value ⟨observation, rfl⟩
    change Probability.statDist (treeLaw left observation).1
      (treeLaw right observation).1 ≤ advantage left right
    let rounds := commonRounds left right observation []
    let environment := localDDE observation []
    let result := localResult observation []
    have enough : commonRounds left right observation [] ≤ rounds :=
      le_rfl
    have reconstructed :
        Observation.map result (ddeObservation environment rounds) =
          truncate observation rounds := by
      exact map_ddeObservationFrom_local_eq_truncate observation rounds []
    have leftLaw : (treeLaw left observation).1 =
        Distribution.fTransform result (ddeLaw left environment rounds).1 := by
      change Observation.distribution left observation =
        Distribution.fTransform result
          (Observation.distribution left (ddeObservation environment rounds))
      calc
        Observation.distribution left observation =
            Observation.distribution left (truncate observation rounds) :=
          (distribution_truncate_eq_left left right observation rounds enough).symm
        _ = Observation.distribution left
            (Observation.map result (ddeObservation environment rounds)) := by
          rw [reconstructed]
        _ = _ := Observation.distribution_map left result _
    have rightLaw : (treeLaw right observation).1 =
        Distribution.fTransform result (ddeLaw right environment rounds).1 := by
      change Observation.distribution right observation =
        Distribution.fTransform result
          (Observation.distribution right (ddeObservation environment rounds))
      calc
        Observation.distribution right observation =
            Observation.distribution right (truncate observation rounds) :=
          (distribution_truncate_eq_right left right observation rounds enough).symm
        _ = Observation.distribution right
            (Observation.map result (ddeObservation environment rounds)) := by
          rw [reconstructed]
        _ = _ := Observation.distribution_map right result _
    rw [leftLaw, rightLaw]
    calc
      Probability.statDist
        (Distribution.fTransform result (ddeLaw left environment rounds).1)
        (Distribution.fTransform result (ddeLaw right environment rounds).1) ≤
      Probability.statDist
        (ddeLaw left environment rounds).1
        (ddeLaw right environment rounds).1 :=
        Probability.statDist_fTransform_le _ _ result
      _ ≤ advantage left right :=
        statDist_ddeLaw_le_advantage left right environment rounds
  · exact advantage_nonneg left right

/-- Every fixed-round DDE transcript test is an internal observation followed
by its canonical Boolean hypothesis test. -/
theorem advantage_le_treeAdvantage (left right : RandomSystem A) :
    advantage left right ≤ treeAdvantage left right := by
  unfold advantage
  apply Real.sSup_le
  · rintro value ⟨⟨environment, rounds⟩, rfl⟩
    let leftTranscript := (ddeLaw left environment rounds).1
    let rightTranscript := (ddeLaw right environment rounds).1
    let distinguish := fun transcript =>
      decide (rightTranscript transcript < leftTranscript transcript)
    let observation : Observation A Bool :=
      Observation.map distinguish (ddeObservation environment rounds)
    have leftLaw : (treeLaw left observation).1 =
        Distribution.fTransform distinguish leftTranscript := by
      change Observation.distribution left observation = _
      exact Observation.distribution_map left distinguish _
    have rightLaw : (treeLaw right observation).1 =
        Distribution.fTransform distinguish rightTranscript := by
      change Observation.distribution right observation = _
      exact Observation.distribution_map right distinguish _
    calc
      Probability.statDist leftTranscript rightTranscript =
        Probability.statDist
          (Distribution.fTransform distinguish leftTranscript)
          (Distribution.fTransform distinguish rightTranscript) :=
        (RandomSystem.Internal.Metric.statDist_fTransform_positive_eq
          leftTranscript rightTranscript).symm
      _ = Probability.statDist
          (treeLaw left observation).1 (treeLaw right observation).1 := by
        rw [leftLaw, rightLaw]
      _ ≤ treeAdvantage left right :=
        RandomSystem.Internal.Metric.statDist_le_observationDistance
          treeLaw left right observation
  · exact treeAdvantage_nonneg left right

/-- The internal branch-finite closure does not enlarge the semantic test
class: local finite support gives exact equality with the existing DDE
supremum for every pair of cumulative random systems. -/
theorem advantage_eq_treeAdvantage (left right : RandomSystem A) :
    advantage left right = treeAdvantage left right :=
  le_antisymm (advantage_le_treeAdvantage left right)
    (treeAdvantage_le_advantage left right)


/-- The finite observation accepting exactly one displayed transcript. -/
noncomputable def accepts : RandomSystem.Internal.Core.Transcript A → Observation A Bool
  | [] => .value true
  | ⟨query, expected⟩ :: remaining =>
      .query query fun actual =>
        if actual = expected then accepts remaining else .value false

theorem distributionFrom_accepts_true (behavior : RandomSystem A)
    (prior target : RandomSystem.Internal.Core.Transcript A) :
    Observation.distributionFrom behavior (accepts target) prior true =
      behavior.mass (prior ++ target) := by
  induction target generalizing prior with
  | nil =>
      simp [accepts]
  | cons reply remaining inductionHypothesis =>
      rcases reply with ⟨query, expected⟩
      rw [accepts, Observation.distributionFrom, Finsupp.sum_apply]
      rw [Finsupp.sum_eq_single expected]
      · simp only [if_pos]
        rw [inductionHypothesis]
        congr 1
        simp
      · intro actual supported different
        simp [different]
      · intro zero
        simp only [if_pos]
        rw [inductionHypothesis]
        apply mass_append_eq_zero
        rw [← behavior.extensionLaw_apply]
        exact zero

theorem treeLaw_accepts_true (behavior : RandomSystem A)
    (target : RandomSystem.Internal.Core.Transcript A) :
    treeLaw behavior (accepts target) true = behavior.mass target := by
  exact distributionFrom_accepts_true behavior [] target

/-- Finite path observations separate cumulative random systems. -/
  theorem observations_separate :
    RandomSystem.Internal.Metric.TestsSeparate
      (treeLaw : RandomSystem A → Observation A Bool →
        Distribution.ProbDist Bool) := by
  intro left right equal
  apply RandomSystem.ext
  intro transcript
  have lawEqual := congrArg
    (fun law : Distribution.ProbDist Bool => law true)
    (equal (accepts transcript))
  simpa only [treeLaw_accepts_true] using lawEqual

theorem treeAdvantage_eq_zero_iff (left right : RandomSystem A) :
    treeAdvantage left right = 0 ↔ left = right :=
  RandomSystem.Internal.Metric.observationDistance_eq_zero_iff
    treeLaw observations_separate left right

end Internal

/-- Existing functional DDE observations separate cumulative random systems. -/
theorem advantage_eq_zero_iff (left right : RandomSystem A) :
    advantage left right = 0 ↔ left = right := by
  rw [Internal.advantage_eq_treeAdvantage,
    Internal.treeAdvantage_eq_zero_iff]

end RandomSystem

namespace RandomSystem

variable {A : Interface.{u, v}}

noncomputable instance : MetricSpace (RandomSystem A) where
  dist := advantage
  dist_self := advantage_self
  dist_comm := advantage_comm
  dist_triangle := advantage_triangle
  eq_of_dist_eq_zero {left right} equal :=
    (advantage_eq_zero_iff left right).mp equal

@[simp]
theorem dist_eq_advantage (left right : RandomSystem A) :
    dist left right = advantage left right :=
  rfl

@[simp]
theorem dist_ofPDS_eq (left right : PDS A) :
    dist (ofPDS left) (ofPDS right) = PDS.advantage left right :=
  advantage_toRandomSystem_eq left right

@[simp]
theorem dist_toRandomSystem_eq (left right : PDS A) :
    dist (PDS.toRandomSystem left) (PDS.toRandomSystem right) =
      PDS.advantage left right :=
  advantage_toRandomSystem_eq left right

theorem edist_eq_ofReal_advantage (left right : RandomSystem A) :
    edist left right = ENNReal.ofReal (advantage left right) := by
  rw [edist_dist, dist_eq_advantage]

@[simp]
theorem edist_ofPDS_eq (left right : PDS A) :
    edist (ofPDS left) (ofPDS right) =
      ENNReal.ofReal (PDS.advantage left right) := by
  rw [edist_dist, dist_ofPDS_eq]

end RandomSystem

end

end RandomSystems.Ambient
