/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.RandomSystem
import RandomSystems.Distance
import RandomSystems.RandomSystem

set_option autoImplicit false

/-!
# Fixed-interface Random Systems bridge

This module relates Lanzenberger's fixed `(X,Y)` DDS/PDS presentation to the
query-indexed Random Systems carrier at `Interface.single X Y`.  Rejection is
an ordinary optional reply and does not stop the observer.  The complete
attempted history remains the argument of every later DDS value.

Jost supplies the abstract interface-changing converter and attachment shape; it does not
identify that carrier with Lanzenberger's common-domain quotient. This module
is only the faithful carrier bridge needed to use the latter inside the former.
-/

namespace RandomSystems.CommonDomain

noncomputable section

universe u v

open Probability (Distribution)
open RandomSystems.Ambient

/-- Embed a partial DDS at the fixed interface `Interface.single X Y`.

Lanzenberger, Definition 2.9 (printed p. 13), defines a DDS as “a partial
function” whose domain is prefix-closed.  This embedding is its direct
optional-value representation: the original answer is returned on the
partial domain and `none` is returned outside it. -/
def embedDDS {X : Type u} {Y : Type v}
    (system : System.DDS X Y) :
    Ambient.DDS (Ambient.Interface.single X Y) :=
  fun history => Part.equivOption (system.1 history.queries)

/-- `embedDDS` rejects exactly the histories outside the partial DDS domain. -/
theorem embedDDS_eq_none_iff {X : Type u} {Y : Type v}
    (system : System.DDS X Y)
    (history : Ambient.History
      (Ambient.Interface.single X Y)) :
    embedDDS system history = none ↔ history.queries ∉ System.dom system := by
  classical
  exact Part.toOption_eq_none_iff

/-- `embedDDS` returns `some answer` exactly on the graph of the partial DDS. -/
theorem embedDDS_eq_some_iff {X : Type u} {Y : Type v}
    (system : System.DDS X Y)
    (history : Ambient.History
      (Ambient.Interface.single X Y)) (answer : Y) :
    embedDDS system history = some answer ↔
      answer ∈ system.1 history.queries := by
  classical
  exact Part.toOption_eq_some_iff

/-- Prefix closure makes rejection persistent along extensions of the complete
attempted history; it does not stop the DDE from issuing those attempts. -/
theorem embedDDS_eq_none_of_prefix {X : Type u} {Y : Type v}
    (system : System.DDS X Y)
    {short long : Ambient.History
      (Ambient.Interface.single X Y)}
    (isPrefix : short.queries <+: long.queries)
    (rejected : embedDDS system short = none) :
    embedDDS system long = none := by
  apply (embedDDS_eq_none_iff system long).mpr
  intro admitted
  exact (embedDDS_eq_none_iff system short).mp rejected
    (System.prefix_closed system isPrefix short.nonempty admitted)

/-- Direct optionalization is faithful to the original partial DDS. -/
theorem embedDDS_injective {X : Type u} {Y : Type v} :
    Function.Injective
      (embedDDS : System.DDS X Y →
        Ambient.DDS (Ambient.Interface.single X Y)) := by
  classical
  intro left right equal
  apply Subtype.ext
  apply PFun.ext
  intro history answer
  by_cases empty : history = []
  · subst history
    constructor
    · rintro ⟨defined, _⟩
      exact False.elim (System.empty_not_mem left defined)
    · rintro ⟨defined, _⟩
      exact False.elim (System.empty_not_mem right defined)
  · have atHistory := congrFun equal
        (⟨history, empty⟩ :
          Ambient.History (Ambient.Interface.single X Y))
    change Part.equivOption (left.1 history) =
      Part.equivOption (right.1 history) at atHistory
    have partialEqual : left.1 history = right.1 history := by
      exact Part.equivOption.injective atHistory
    rw [partialEqual]

/-- A query-indexed DDS is the direct optionalization of a partial DDS exactly
when definedness is inherited by every nonempty prefix. -/
theorem mem_range_embedDDS_iff {X : Type u} {Y : Type v}
    (system : Ambient.DDS (Ambient.Interface.single X Y)) :
    system ∈ Set.range (embedDDS : System.DDS X Y →
      Ambient.DDS (Ambient.Interface.single X Y)) ↔
      ∀ ⦃short long : Ambient.History
          (Ambient.Interface.single X Y)⦄,
        short.queries <+: long.queries → system long ≠ none →
          system short ≠ none := by
  constructor
  · rintro ⟨source, rfl⟩ short long isPrefix longDefined
    have longIn : long.queries ∈ System.dom source := by
      by_contra outside
      exact longDefined ((embedDDS_eq_none_iff source long).2 outside)
    have shortIn : short.queries ∈ System.dom source :=
      System.prefix_closed source isPrefix short.nonempty longIn
    intro rejected
    exact (embedDDS_eq_none_iff source short).1 rejected shortIn
  · intro prefixClosed
    let raw : System.Raw X Y := fun queries =>
      if nonempty : queries ≠ [] then
        Part.ofOption (system ⟨queries, nonempty⟩)
      else
        Part.none
    have valid : System.Valid raw := by
      constructor
      · simp [raw]
      · intro short long isPrefix shortNonempty longIn
        have longNonempty : long ≠ [] := by
          intro equal
          subst long
          simp [raw] at longIn
        have longSome : system
            (⟨long, longNonempty⟩ : Ambient.History
              (Ambient.Interface.single X Y)) ≠ none := by
          change (if nonempty : long ≠ [] then
            Part.ofOption (system ⟨long, nonempty⟩) else Part.none).Dom at longIn
          rw [dif_pos longNonempty, Part.ofOption_dom,
            Option.isSome_iff_ne_none] at longIn
          exact longIn
        have shortSome := prefixClosed
          (short := (⟨short, shortNonempty⟩ : Ambient.History
            (Ambient.Interface.single X Y)))
          (long := (⟨long, longNonempty⟩ : Ambient.History
            (Ambient.Interface.single X Y)))
          isPrefix longSome
        change (if nonempty : short ≠ [] then
          Part.ofOption (system ⟨short, nonempty⟩) else Part.none).Dom
        rw [dif_pos shortNonempty, Part.ofOption_dom,
          Option.isSome_iff_ne_none]
        exact shortSome
    refine ⟨⟨raw, valid⟩, ?_⟩
    apply Ambient.DDS.ext
    intro history
    change Part.equivOption (raw history.queries) = system history
    have raw_eq : raw history.queries =
        Part.ofOption (system ⟨history.queries, history.nonempty⟩) := by
      dsimp only [raw]
      split
      · rfl
      · rename_i empty
        exact False.elim (empty history.nonempty)
    rw [raw_eq]
    change Part.equivOption
        (Part.equivOption.symm
          (system ⟨history.queries, history.nonempty⟩)) = system history
    rw [Part.equivOption.apply_symm_apply]

/-- Embed a normalized law of partial DDSs by pushforward along `embedDDS`. -/
def embedPDS {X : Type u} {Y : Type v}
    (system : Distribution.ProbDist (System.DDS X Y)) :
    Ambient.PDS (Ambient.Interface.single X Y) :=
  ⟨Distribution.fTransform embedDDS system.1,
    Distribution.fTransform_isProbDist embedDDS system.2⟩

@[simp]
theorem embedPDS_law {X : Type u} {Y : Type v}
    (system : Distribution.ProbDist (System.DDS X Y)) :
    (embedPDS system : Distribution
      (Ambient.DDS (Ambient.Interface.single X Y))) =
        Distribution.fTransform embedDDS system.1 :=
  rfl

/-- Pushforward along the faithful DDS embedding is faithful on normalized
PDS presentations. -/
theorem embedPDS_injective {X : Type u} {Y : Type v} :
    Function.Injective
      (embedPDS : Distribution.ProbDist (System.DDS X Y) →
        Ambient.PDS (Ambient.Interface.single X Y)) := by
  intro left right equal
  apply Subtype.ext
  apply Finsupp.ext
  intro system
  have atSystem := congrArg
    (fun law : Distribution
      (Ambient.DDS (Ambient.Interface.single X Y)) =>
        law (embedDDS system))
    (congrArg Subtype.val equal)
  simpa only [embedPDS_law,
    Distribution.fTransform_injective_apply _ _ embedDDS_injective system]
    using atSystem

@[simp]
theorem innerReplyAt_embedDDS_eq {X : Type u} {Y : Type v}
    (system : System.DDS X Y) (prior : List X) (query : X) :
    Ambient.Attachment.innerReplyAt (embedDDS system) prior query =
      Part.equivOption (system.1 (prior ++ [query])) := by
  rfl

theorem innerReplyAt_embedDDS_eq_none_iff {X : Type u} {Y : Type v}
    (system : System.DDS X Y) (prior : List X) (query : X) :
    Ambient.Attachment.innerReplyAt (embedDDS system) prior query = none ↔
      prior ++ [query] ∉ System.dom system := by
  classical
  rw [innerReplyAt_embedDDS_eq]
  rw [show Part.equivOption (system.1 (prior ++ [query])) =
      @Part.toOption Y (system.1 (prior ++ [query]))
        (Classical.propDecidable _) by rfl]
  exact Part.toOption_eq_none_iff

private abbrev Reply {X : Type u} {Y : Type v} :=
  Ambient.DDC.History.InnerReply
    (Ambient.Interface.single X Y)

private def replyAnswer {X : Type u} {Y : Type v}
    (reply : Reply (X := X) (Y := Y)) : Option Y :=
  reply.2

/-- Tag every literal query-answer pair with its query and a successful
optional answer. -/
def encodeTranscript {X : Type u} {Y : Type v}
    (transcript : System.Transcript X Y) :
    Ambient.Transcript (Ambient.Interface.single X Y) :=
  transcript.map fun pair => ⟨pair.1, some pair.2⟩

/-- Decode a tagged transcript when every attempted query was accepted. -/
def decodeTranscript {X : Type u} {Y : Type v} :
    Ambient.Transcript (Ambient.Interface.single X Y) →
      Option (System.Transcript X Y)
  | [] => some []
  | reply :: replies =>
      match replyAnswer (X := X) (Y := Y) reply,
          decodeTranscript (X := X) (Y := Y) replies with
      | some answer, some tail => some ((reply.1, answer) :: tail)
      | _, _ => none

@[simp]
theorem decodeTranscript_encodeTranscript {X : Type u} {Y : Type v}
    (transcript : System.Transcript X Y) :
    decodeTranscript (encodeTranscript transcript) = some transcript := by
  induction transcript with
  | nil => simp [encodeTranscript, decodeTranscript]
  | cons pair transcript inductionHypothesis =>
      change (match some pair.2, decodeTranscript (encodeTranscript transcript) with
        | some answer, some tail => some ((pair.1, answer) :: tail)
        | _, _ => none) = some (pair :: transcript)
      rw [inductionHypothesis]

@[simp]
theorem transcriptInputs_encodeTranscript {X : Type u} {Y : Type v}
    (transcript : System.Transcript X Y) :
    Ambient.transcriptInputs (encodeTranscript transcript) =
      transcript.map Prod.fst := by
  simp only [Ambient.transcriptInputs, encodeTranscript, List.map_map]
  apply List.map_congr_left
  intro pair _
  rfl

private def decodeAnswers {X : Type u} {Y : Type v} :
    Ambient.Transcript (Ambient.Interface.single X Y) →
      Option (List Y)
  | [] => some []
  | reply :: replies =>
      match replyAnswer (X := X) (Y := Y) reply,
          decodeAnswers (X := X) (Y := Y) replies with
      | some answer, some answers => some (answer :: answers)
      | _, _ => none

@[simp]
private theorem decodeAnswers_encodeTranscript {X : Type u} {Y : Type v}
    (transcript : System.Transcript X Y) :
    decodeAnswers (encodeTranscript transcript) =
      some (transcript.map Prod.snd) := by
  induction transcript with
  | nil => simp [encodeTranscript, decodeAnswers]
  | cons pair transcript inductionHypothesis =>
      change (match some pair.2, decodeAnswers (encodeTranscript transcript) with
        | some answer, some answers => some (answer :: answers)
        | _, _ => none) = some (pair.2 :: transcript.map Prod.snd)
      rw [inductionHypothesis]

/-- Regard a literal DDE as a total query-indexed DDE on successful tagged
transcripts. -/
private noncomputable def liftDDE {X : Type u} {Y : Type v}
    (environment : System.DDE Y X) :
    Ambient.DDE (Ambient.Interface.single X Y) := by
  classical
  exact fun observations =>
    match decodeAnswers observations with
    | none => none
    | some answers => (environment.1 answers).toOption

/-- On a compatible literal interaction, finite query-indexed observation is
the tagged literal stage transcript. -/
private theorem transcript_liftDDE_embedDDS {X : Type u} {Y : Type v}
    (environment : System.DDE Y X) (system : System.DDS X Y)
    (compatible : System.Compatible environment system) :
    ∀ rounds,
      Ambient.transcript (embedDDS system) (liftDDE environment) rounds =
        encodeTranscript (System.trN environment system rounds) := by
  classical
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      rw [Ambient.transcript_succ, inductionHypothesis]
      by_cases environmentDefined :
          (System.trN environment system rounds).map Prod.snd ∈
            environment.1.Dom
      · let query := (environment.1
            ((System.trN environment system rounds).map Prod.snd)).get
            environmentDefined
        have queryMember : query ∈ environment.1
            ((System.trN environment system rounds).map Prod.snd) :=
          Part.get_mem environmentDefined
        have systemDefined :
            (System.trN environment system rounds).map Prod.fst ++ [query] ∈
              System.dom system :=
          compatible rounds query queryMember
        have liftedQuery :
            liftDDE environment
                (encodeTranscript (System.trN environment system rounds)) =
              some query := by
          rw [liftDDE, decodeAnswers_encodeTranscript]
          exact Part.toOption_eq_some_iff.mpr ⟨environmentDefined, rfl⟩
        rw [liftedQuery, System.trN_succ_of_query environmentDefined systemDefined]
        simp only [encodeTranscript, List.map_append, List.map_singleton]
        have entryEqual :
            (⟨query,
              Ambient.Attachment.innerReplyAt (embedDDS system)
                (Ambient.transcriptInputs
                  (encodeTranscript (System.trN environment system rounds)))
                query⟩ : Reply) =
              ⟨query, some (System.output system
                ((System.trN environment system rounds).map Prod.fst ++ [query])
                systemDefined)⟩ := by
          refine Sigma.ext rfl ?_
          apply heq_of_eq
          rw [transcriptInputs_encodeTranscript, innerReplyAt_embedDDS_eq]
          change (system.1
              ((System.trN environment system rounds).map Prod.fst ++ [query])).toOption =
            some (System.output system
              ((System.trN environment system rounds).map Prod.fst ++ [query])
              systemDefined)
          rw [Part.toOption_eq_some_iff]
          exact ⟨systemDefined, rfl⟩
        exact congrArg (fun entry =>
          (System.trN environment system rounds).map
              (fun pair => (⟨pair.1, some pair.2⟩ : Reply)) ++ [entry])
          entryEqual
      · have liftedStop :
            liftDDE environment
              (encodeTranscript (System.trN environment system rounds)) = none := by
          rw [liftDDE, decodeAnswers_encodeTranscript]
          exact Part.toOption_eq_none_iff.mpr environmentDefined
        rw [liftedStop, System.trN_succ_of_stop environmentDefined]

private noncomputable def stoppingBound {X : Type u} {Y : Type v}
    (environment : System.DDE Y X)
    (law : Distribution (System.DDS X Y))
    (stops : PDS.Stops environment law) : Nat := by
  classical
  exact law.support.sup fun system =>
    if supported : system ∈ law.support then Nat.find (stops system supported)
    else 0

private theorem stabilizes_at_stoppingBound {X : Type u} {Y : Type v}
    (environment : System.DDE Y X)
    (law : Distribution (System.DDS X Y))
    (stops : PDS.Stops environment law)
    {system : System.DDS X Y} (supported : system ∈ law.support) :
    System.trN environment system (stoppingBound environment law stops + 1) =
      System.trN environment system (stoppingBound environment law stops) := by
  classical
  let witness := stops system supported
  let first := Nat.find witness
  have firstLe : first ≤ stoppingBound environment law stops := by
    rw [stoppingBound]
    have leSup := Finset.le_sup
      (s := law.support)
      (f := fun deterministic =>
        if inSupport : deterministic ∈ law.support then
          Nat.find (stops deterministic inSupport)
        else 0) supported
    simpa [first, witness, supported] using leSup
  calc
    System.trN environment system (stoppingBound environment law stops + 1) =
        System.trN environment system first :=
      System.trN_eq_of_le (Nat.find_spec witness) _ (by omega)
    _ = System.trN environment system (stoppingBound environment law stops) :=
      (System.trN_eq_of_le (Nat.find_spec witness) _ firstLe).symm

private theorem stabilizes_at_of_stoppingBound_le {X : Type u} {Y : Type v}
    (environment : System.DDE Y X)
    (law : Distribution (System.DDS X Y))
    (stops : PDS.Stops environment law)
    {system : System.DDS X Y} (supported : system ∈ law.support)
    (rounds : Nat) (enough : stoppingBound environment law stops ≤ rounds) :
    System.trN environment system (rounds + 1) =
      System.trN environment system rounds := by
  let base := stoppingBound environment law stops
  have stable := stabilizes_at_stoppingBound environment law stops supported
  calc
    System.trN environment system (rounds + 1) =
        System.trN environment system base :=
      System.trN_eq_of_le stable _ (by omega)
    _ = System.trN environment system rounds :=
      (System.trN_eq_of_le stable _ enough).symm

/-- A compatible, stopping literal DDE observation is a deterministic
post-processing of one finite query-indexed observation. -/
private theorem literalTranscriptLaw_eq_decode_trLaw
    {X : Type u} {Y : Type v}
    (environment : System.DDE Y X)
    (presentation :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y)
    (compatible : PDS.Compatible environment presentation.law.1)
    (stops : PDS.Stops environment presentation.law.1)
    (rounds : Nat)
    (enough : stoppingBound environment presentation.law.1 stops ≤ rounds) :
    RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
        environment presentation =
      Distribution.fTransform decodeTranscript
        (Ambient.PDS.trLaw (liftDDE environment) rounds
          (embedPDS presentation.law)) := by
  classical
  unfold RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
    RandomSystems.PDS.trLaw Ambient.PDS.trLaw
    RandomSystems.Ambient.trLaw embedPDS
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro system supported
  change (System.tr environment system).toOption =
    decodeTranscript
      (Ambient.transcript (embedDDS system) (liftDDE environment) rounds)
  rw [transcript_liftDDE_embedDDS environment system
    (compatible system supported), decodeTranscript_encodeTranscript]
  have stable := stabilizes_at_of_stoppingBound_le environment
    presentation.law.1 stops supported rounds enough
  exact Part.toOption_eq_some_iff.mpr
    ⟨stops system supported,
      System.tr_get_eq_trN (stops system supported) stable⟩

private def fixedQueryDDE {X : Type u} {Y : Type v}
    (queries : List X) :
    Ambient.DDE (Ambient.Interface.single X Y) :=
  fun observations => queries[observations.length]?

private theorem transcriptInputs_fixedQueryDDE {X : Type u} {Y : Type v}
    (system : Ambient.DDS (Ambient.Interface.single X Y))
    (queries : List X) :
    ∀ rounds, rounds ≤ queries.length →
      Ambient.transcriptInputs
          (Ambient.transcript system (fixedQueryDDE queries) rounds) =
        queries.take rounds := by
  intro rounds enough
  induction rounds with
  | zero => rfl
  | succ rounds inductionHypothesis =>
      have beforeEnd : rounds < queries.length := by omega
      have inputs := inductionHypothesis (by omega)
      have lengthEqual :
          (Ambient.transcript system (fixedQueryDDE queries) rounds).length =
            rounds := by
        have lengths := congrArg List.length inputs
        simp only [Ambient.transcriptInputs, List.length_map] at lengths
        calc
          (Ambient.transcript system
              (fixedQueryDDE queries) rounds).length =
              (queries.take rounds).length := lengths
          _ = rounds := by
            rw [List.length_take, min_eq_left (by omega)]
      have queryEqual : fixedQueryDDE queries
          (Ambient.transcript system (fixedQueryDDE queries) rounds) =
          some queries[rounds] := by
        change queries[(Ambient.transcript system
          (fixedQueryDDE queries) rounds).length]? = some queries[rounds]
        rw [lengthEqual, List.getElem?_eq_getElem beforeEnd]
      rw [Ambient.transcriptInputs_succ_of_query _ _ rounds
        queries[rounds] queryEqual, inputs, List.take_add_one,
        List.getElem?_eq_getElem beforeEnd, Option.toList_some]

private def finalAccepted {X : Type u} {Y : Type v}
    (observations :
      Ambient.Transcript (Ambient.Interface.single X Y)) : Bool :=
  match observations.getLast? with
  | some reply => (replyAnswer reply).isSome
  | none => false

private noncomputable def domainMembership {X : Type u}
    (domain : Set (List X)) (history : List X) : Bool := by
  classical
  exact decide (history ∈ domain)

private theorem finalAccepted_fixedQueryDDE {X : Type u} {Y : Type v}
    (system : System.DDS X Y) (prior : List X) (query : X) :
    finalAccepted
        (Ambient.transcript (embedDDS system)
          (fixedQueryDDE (prior ++ [query])) (prior.length + 1)) =
      domainMembership (System.dom system) (prior ++ [query]) := by
  classical
  let observations := Ambient.transcript (embedDDS system)
    (fixedQueryDDE (prior ++ [query])) prior.length
  have inputs : Ambient.transcriptInputs observations = prior := by
    change Ambient.transcriptInputs
        (Ambient.transcript (embedDDS system)
          (fixedQueryDDE (prior ++ [query])) prior.length) = prior
    rw [transcriptInputs_fixedQueryDDE _ _ prior.length (by simp)]
    simp
  have nextQuery : fixedQueryDDE (Y := Y) (prior ++ [query]) observations =
      some query := by
    change (prior ++ [query])[observations.length]? = some query
    have lengthEqual : observations.length = prior.length := by
      have lengths := congrArg List.length inputs
      simpa [Ambient.transcriptInputs] using lengths
    rw [lengthEqual]
    simp
  rw [Ambient.transcript_succ,
    show Ambient.transcript (embedDDS system)
      (fixedQueryDDE (prior ++ [query])) prior.length = observations by rfl,
    nextQuery]
  simp only [finalAccepted, List.getLast?_append, List.getLast?_singleton,
    replyAnswer, Option.some_or]
  rw [inputs]
  change (Ambient.Attachment.innerReplyAt
      (embedDDS system) prior query).isSome = domainMembership _ _
  rw [innerReplyAt_embedDDS_eq]
  apply Bool.eq_iff_iff.mpr
  rw [show domainMembership (System.dom system) (prior ++ [query]) =
      @decide (prior ++ [query] ∈ System.dom system)
        (Classical.propDecidable _) by rfl,
    decide_eq_true_iff]
  rw [show Part.equivOption (system.1 (prior ++ [query])) =
      @Part.toOption Y (system.1 (prior ++ [query]))
        (Classical.propDecidable _) by rfl]
  change (system.1 (prior ++ [query])).toOption.isSome = true ↔
    (system.1 (prior ++ [query])).Dom
  exact Part.toOption_isSome _

private theorem finalAcceptedLaw_eq_single {X : Type u} {Y : Type v}
    (presentation :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y)
    (prior : List X) (query : X) :
    Distribution.fTransform finalAccepted
        (Ambient.PDS.trLaw (fixedQueryDDE (prior ++ [query]))
          (prior.length + 1) (embedPDS presentation.law)) =
      Finsupp.single
        (domainMembership presentation.domain (prior ++ [query])) 1 := by
  classical
  unfold Ambient.PDS.trLaw RandomSystems.Ambient.trLaw embedPDS
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  calc
    Distribution.fTransform
        ((finalAccepted ∘ fun system =>
          Ambient.transcript system (fixedQueryDDE (prior ++ [query]))
            (prior.length + 1)) ∘ embedDDS) presentation.law.1 =
        Distribution.fTransform
          (fun _ => domainMembership presentation.domain (prior ++ [query]))
          presentation.law.1 := by
      apply Distribution.fTransform_congr
      intro system supported
      change finalAccepted
          (Ambient.transcript (embedDDS system)
            (fixedQueryDDE (prior ++ [query])) (prior.length + 1)) = _
      rw [finalAccepted_fixedQueryDDE,
        presentation.hasDomain system supported]
    _ = Finsupp.single
          (domainMembership presentation.domain (prior ++ [query]))
          presentation.law.1.weight :=
      Distribution.fTransform_const_eq_single_weight _ _
    _ = _ := by rw [presentation.law.2.weight_eq]

private theorem probabilitySupport_nonempty {A : Type u}
    (law : Distribution.ProbDist A) : law.1.support.Nonempty := by
  rw [Finsupp.support_nonempty_iff]
  intro zero
  have weightOne := law.2.weight_eq
  rw [zero] at weightOne
  simp [Distribution.weight] at weightOne

private theorem literalEquivalent_of_ambientEquivalent
    {X : Type u} {Y : Type v}
    {left right :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y}
    (ambient : Ambient.PDS.equivalent
      (embedPDS left.law) (embedPDS right.law)) :
    RandomSystems.CommonDomain.ProbabilityPresentation.Equivalent
      left right := by
  classical
  constructor
  · apply Set.ext
    intro queries
    constructor
    · intro admittedLeft
      by_contra notAdmittedRight
      have nonempty : queries ≠ [] := by
        intro empty
        subst queries
        obtain ⟨system, supported⟩ := probabilitySupport_nonempty left.law
        exact System.empty_not_mem system
          (left.hasDomain system supported ▸ admittedLeft)
      rcases List.eq_nil_or_concat queries with empty | ⟨prior, query, equal⟩
      · exact False.elim (nonempty empty)
      · subst queries
        have admittedLeft' : prior ++ [query] ∈ left.domain := by
          simpa [List.concat_eq_append] using admittedLeft
        have notAdmittedRight' : prior ++ [query] ∉ right.domain := by
          simpa [List.concat_eq_append] using notAdmittedRight
        have lawEqual := congrArg
          (Distribution.fTransform (finalAccepted (X := X) (Y := Y)))
          (ambient (fixedQueryDDE (Y := Y) (prior ++ [query]))
            (prior.length + 1))
        rw [finalAcceptedLaw_eq_single left prior query,
          finalAcceptedLaw_eq_single right prior query] at lawEqual
        simp [domainMembership, admittedLeft', notAdmittedRight'] at lawEqual
        have pointEqual := congrArg
          (fun law : Distribution Bool => law true) lawEqual
        norm_num at pointEqual
    · intro admittedRight
      by_contra notAdmittedLeft
      have nonempty : queries ≠ [] := by
        intro empty
        subst queries
        obtain ⟨system, supported⟩ := probabilitySupport_nonempty right.law
        exact System.empty_not_mem system
          (right.hasDomain system supported ▸ admittedRight)
      rcases List.eq_nil_or_concat queries with empty | ⟨prior, query, equal⟩
      · exact False.elim (nonempty empty)
      · subst queries
        have admittedRight' : prior ++ [query] ∈ right.domain := by
          simpa [List.concat_eq_append] using admittedRight
        have notAdmittedLeft' : prior ++ [query] ∉ left.domain := by
          simpa [List.concat_eq_append] using notAdmittedLeft
        have lawEqual := congrArg
          (Distribution.fTransform (finalAccepted (X := X) (Y := Y)))
          (ambient (fixedQueryDDE (Y := Y) (prior ++ [query]))
            (prior.length + 1))
        rw [finalAcceptedLaw_eq_single left prior query,
          finalAcceptedLaw_eq_single right prior query] at lawEqual
        simp [domainMembership, notAdmittedLeft', admittedRight'] at lawEqual
        have pointEqual := congrArg
          (fun law : Distribution Bool => law true) lawEqual
        norm_num at pointEqual
  · intro environment admissible
    let rounds := max
      (stoppingBound environment left.law.1 admissible.1.2)
      (stoppingBound environment right.law.1 admissible.2.2)
    have leftStable :
        RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
            environment left =
          Distribution.fTransform decodeTranscript
            (Ambient.PDS.trLaw (liftDDE environment) rounds
              (embedPDS left.law)) :=
      literalTranscriptLaw_eq_decode_trLaw environment left
        admissible.1.1 admissible.1.2 rounds (le_max_left _ _)
    have rightStable :
        RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
            environment right =
          Distribution.fTransform decodeTranscript
            (Ambient.PDS.trLaw (liftDDE environment) rounds
              (embedPDS right.law)) :=
      literalTranscriptLaw_eq_decode_trLaw environment right
        admissible.2.1 admissible.2.2 rounds (le_max_right _ _)
    rw [leftStable, rightStable, ambient (liftDDE environment) rounds]

private def replayFrom {X : Type u} {Y : Type v}
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y)) :
    Ambient.Transcript (Ambient.Interface.single X Y) → List Y →
      Option (Ambient.Transcript
        (Ambient.Interface.single X Y))
  | history, [] => some history
  | history, answer :: answers =>
      match environment history with
      | none => none
      | some query =>
          replayFrom environment
            (history ++ [⟨query, some answer⟩]) answers

private def replay {X : Type u} {Y : Type v}
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (answers : List Y) :
    Option (Ambient.Transcript
      (Ambient.Interface.single X Y)) :=
  replayFrom environment [] answers

private theorem replayFrom_append {X : Type u} {Y : Type v}
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (history : Ambient.Transcript
      (Ambient.Interface.single X Y))
    (first second : List Y) :
    replayFrom environment history (first ++ second) =
      (replayFrom environment history first).bind
        (fun middle => replayFrom environment middle second) := by
  induction first generalizing history with
  | nil => rfl
  | cons answer answers inductionHypothesis =>
      simp only [List.cons_append, replayFrom]
      cases next : environment history with
      | none => rfl
      | some query =>
          exact inductionHypothesis
            (history ++ [⟨query, some answer⟩])

private theorem replayFrom_prefix {X : Type u} {Y : Type v}
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (history : Ambient.Transcript
      (Ambient.Interface.single X Y))
    (answers : List Y)
    {result : Ambient.Transcript
      (Ambient.Interface.single X Y)}
    (equal : replayFrom environment history answers = some result) :
    history <+: result := by
  induction answers generalizing history with
  | nil =>
      have historyEqual : history = result := by
        simpa [replayFrom] using equal
      exact historyEqual ▸ List.prefix_refl result
  | cons answer answers inductionHypothesis =>
      simp only [replayFrom] at equal
      cases next : environment history with
      | none => simp [next] at equal
      | some query =>
          simp only [next] at equal
          exact (List.prefix_append history [⟨query, some answer⟩]).trans
            (inductionHypothesis
              (history := history ++ [⟨query, some answer⟩]) equal)

private theorem replay_prefix_result {X : Type u} {Y : Type v}
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    {short long : List Y} (isPrefix : short <+: long)
    {longHistory : Ambient.Transcript
      (Ambient.Interface.single X Y)}
    (longEqual : replay environment long = some longHistory) :
    ∃ shortHistory,
      replay environment short = some shortHistory ∧
        shortHistory <+: longHistory := by
  obtain ⟨tail, rfl⟩ := isPrefix
  change replayFrom environment [] (short ++ tail) = some longHistory at longEqual
  rw [replayFrom_append] at longEqual
  change ∃ shortHistory,
    replayFrom environment [] short = some shortHistory ∧
      shortHistory <+: longHistory
  cases shortEqual : replayFrom environment [] short with
  | none => simp [shortEqual] at longEqual
  | some shortHistory =>
      simp only [shortEqual, Option.bind_some] at longEqual
      refine ⟨shortHistory, rfl, ?_⟩
      exact replayFrom_prefix environment shortHistory tail longEqual

private theorem transcriptInputs_prefix {A : Ambient.Interface.{u, v}}
    {short long : Ambient.Transcript A} (isPrefix : short <+: long) :
    Ambient.transcriptInputs short <+:
      Ambient.transcriptInputs long :=
  List.IsPrefix.map Sigma.fst isPrefix

@[simp]
private theorem transcriptInputs_append_reply
    {A : Ambient.Interface.{u, v}}
    (history : Ambient.Transcript A)
    (reply : Ambient.DDC.History.InnerReply A) :
    Ambient.transcriptInputs (history ++ [reply]) =
      Ambient.transcriptInputs history ++ [reply.1] := by
  simp [Ambient.transcriptInputs]

private def DomainPrefixClosed {X : Type u}
    (domain : Set (List X)) : Prop :=
  ∀ ⦃short long : List X⦄,
    short <+: long → short ≠ [] → long ∈ domain → short ∈ domain

private theorem probabilityPresentation_domainPrefixClosed
    {X : Type u} {Y : Type v}
    (presentation :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y) :
    DomainPrefixClosed presentation.domain := by
  obtain ⟨system, supported⟩ := probabilitySupport_nonempty presentation.law
  intro short long isPrefix nonempty inDomain
  rw [← presentation.hasDomain system supported] at inDomain ⊢
  exact System.prefix_closed system isPrefix nonempty inDomain

private noncomputable def restrictedQuery {X : Type u} {Y : Type v}
    (domain : Set (List X))
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (answers : List Y) : Option X := by
  classical
  if within : answers.length < rounds then
    match replay environment answers with
    | none => exact none
    | some history =>
        match environment history with
        | none => exact none
        | some query =>
            if (show List X from Ambient.transcriptInputs history) ++
                [(show X from query)] ∈ domain then
              exact some query
            else exact none
  else exact none

private theorem restrictedQuery_some_data {X : Type u} {Y : Type v}
    (domain : Set (List X))
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (answers : List Y) {query : X}
    (equal : restrictedQuery domain environment rounds answers = some query) :
    answers.length < rounds ∧
      ∃ history,
        replay environment answers = some history ∧
        environment history = some query ∧
        (show List X from Ambient.transcriptInputs history) ++
          [(show X from query)] ∈ domain := by
  classical
  unfold restrictedQuery at equal
  split at equal
  · rename_i within
    split at equal
    · simp at equal
    · rename_i history historyEqual
      split at equal
      · simp at equal
      · rename_i nextQuery nextEqual
        split at equal
        · rename_i admitted
          simp only [Option.some.injEq] at equal
          subst nextQuery
          exact ⟨within, history, historyEqual, nextEqual, admitted⟩
        · simp at equal
  · simp at equal

private theorem restrictedQuery_prefix {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) {short long : List Y} (isPrefix : short <+: long)
    {query : X}
    (defined : restrictedQuery domain environment rounds long = some query) :
    (restrictedQuery domain environment rounds short).isSome := by
  classical
  obtain ⟨longWithin, longHistory, longReplay, longNext, longAdmitted⟩ :=
    restrictedQuery_some_data domain environment rounds long defined
  have shortWithin : short.length < rounds :=
    lt_of_le_of_lt isPrefix.length_le longWithin
  obtain ⟨shortHistory, shortReplay, historiesPrefix⟩ :=
    replay_prefix_result environment isPrefix longReplay
  have shortReplayPublic := shortReplay
  change replayFrom environment [] short = some shortHistory at shortReplay
  obtain ⟨tail, rfl⟩ := isPrefix
  unfold restrictedQuery
  rw [dif_pos shortWithin, shortReplayPublic]
  simp only
  cases tail with
  | nil =>
      simp only [List.append_nil] at longReplay longNext longAdmitted
      rw [shortReplayPublic] at longReplay
      simp only [Option.some.injEq] at longReplay
      subst longHistory
      rw [longNext]
      simp only
      split
      · rfl
      · contradiction
  | cons answer tail =>
      have nextExists : ∃ nextQuery,
          environment shortHistory = some nextQuery := by
        change replayFrom environment [] (short ++ answer :: tail) =
          some longHistory at longReplay
        rw [replayFrom_append, shortReplay] at longReplay
        simp only [Option.bind_some, replayFrom] at longReplay
        cases next : environment shortHistory with
        | none => simp [next] at longReplay
        | some nextQuery => exact ⟨nextQuery, rfl⟩
      obtain ⟨nextQuery, nextEqual⟩ := nextExists
      rw [nextEqual]
      simp only
      have nextPrefix :
          (show List X from Ambient.transcriptInputs shortHistory) ++
              [(show X from nextQuery)] <+:
            (show List X from Ambient.transcriptInputs longHistory) ++
              [(show X from query)] := by
        have oneMore : shortHistory ++ [⟨nextQuery, some answer⟩] <+:
            longHistory := by
          change replayFrom environment [] (short ++ answer :: tail) =
            some longHistory at longReplay
          rw [replayFrom_append, shortReplay] at longReplay
          simp only [Option.bind_some, replayFrom, nextEqual] at longReplay
          exact replayFrom_prefix environment
            (shortHistory ++ [⟨nextQuery, some answer⟩]) tail longReplay
        have inputPrefix :
            Ambient.transcriptInputs
                (shortHistory ++ [⟨nextQuery, some answer⟩]) <+:
              Ambient.transcriptInputs longHistory :=
          transcriptInputs_prefix oneMore
        rw [transcriptInputs_append_reply] at inputPrefix
        exact inputPrefix.trans (List.prefix_append _ [query])
      have nextNonempty :
          (show List X from Ambient.transcriptInputs shortHistory) ++
              [(show X from nextQuery)] ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ (by simp)
      have admitted := domainPrefix nextPrefix nextNonempty longAdmitted
      have admittedRaw :
          (show List X from Ambient.transcriptInputs shortHistory) ++
              [(show X from nextQuery)] ∈ domain := admitted
      simp [admittedRaw]

private noncomputable def restrictDDE {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) : System.DDE Y X := by
  classical
  refine ⟨(fun answers => Part.ofOption
      (restrictedQuery domain environment rounds answers)), ?_⟩
  intro short long isPrefix longDefined
  change (Part.ofOption
    (restrictedQuery domain environment rounds long)).Dom at longDefined
  change (Part.ofOption
    (restrictedQuery domain environment rounds short)).Dom
  rw [Part.ofOption_dom, Option.isSome_iff_ne_none] at longDefined ⊢
  obtain ⟨query, equal⟩ := Option.ne_none_iff_exists'.mp longDefined
  exact Option.isSome_iff_ne_none.mp
    (restrictedQuery_prefix domain domainPrefix environment rounds isPrefix equal)

private theorem restrictDDE_halts {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) :
    System.DDE.Halts (restrictDDE domain domainPrefix environment rounds) := by
  refine ⟨rounds, ?_⟩
  intro answers lengthAtLeast inDomain
  change (Part.ofOption
    (restrictedQuery domain environment rounds answers)).Dom at inDomain
  rw [Part.ofOption_dom] at inDomain
  obtain ⟨query, queryEqual⟩ := Option.isSome_iff_exists.mp inDomain
  have data := restrictedQuery_some_data domain environment rounds answers
    queryEqual
  omega

private theorem replay_trN_restrictDDE {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (system : System.DDS X Y)
    (hasDomain : System.dom system = domain) :
    ∀ stage,
      replay environment
          ((System.trN (restrictDDE domain domainPrefix environment rounds)
            system stage).map Prod.snd) =
        some (encodeTranscript
          (System.trN (restrictDDE domain domainPrefix environment rounds)
            system stage)) := by
  intro stage
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      let literalEnvironment :=
        restrictDDE domain domainPrefix environment rounds
      let current := System.trN literalEnvironment system stage
      by_cases environmentDefined :
          current.map Prod.snd ∈ literalEnvironment.1.Dom
      · let query := (literalEnvironment.1 (current.map Prod.snd)).get
            environmentDefined
        have queryMember : query ∈
            literalEnvironment.1 (current.map Prod.snd) :=
          Part.get_mem environmentDefined
        change query ∈ Part.ofOption
          (restrictedQuery domain environment rounds (current.map Prod.snd))
            at queryMember
        rw [Part.mem_ofOption, Option.mem_def] at queryMember
        obtain ⟨history, replayEqual, nextEqual, admitted⟩ :=
          (restrictedQuery_some_data domain environment rounds _ queryMember).2
        have historyEqual : history = encodeTranscript current := by
          have currentReplay : replay environment (current.map Prod.snd) =
              some (encodeTranscript current) := inductionHypothesis
          rw [currentReplay] at replayEqual
          exact Option.some.inj replayEqual.symm
        have nextEqual' : environment (encodeTranscript current) = some query := by
          rwa [← historyEqual]
        have systemDefined : current.map Prod.fst ++ [query] ∈
            System.dom system := by
          rw [hasDomain]
          rw [historyEqual, transcriptInputs_encodeTranscript] at admitted
          exact admitted
        rw [System.trN_succ_of_query environmentDefined systemDefined]
        simp only [List.map_append, List.map_singleton, encodeTranscript]
        change replay environment
            (current.map Prod.snd ++
              [System.output system (current.map Prod.fst ++ [query])
                systemDefined]) = _
        rw [replay, replayFrom_append]
        change replayFrom environment [] (current.map Prod.snd) =
          some (encodeTranscript current) at inductionHypothesis
        rw [inductionHypothesis]
        simp only [Option.bind_some, replayFrom, nextEqual']
        rfl
      · rw [System.trN_succ_of_stop environmentDefined]
        exact inductionHypothesis

private theorem restrictDDE_compatible {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (system : System.DDS X Y)
    (hasDomain : System.dom system = domain) :
    System.Compatible
      (restrictDDE domain domainPrefix environment rounds) system := by
  intro stage query queryMember
  change query ∈ Part.ofOption
    (restrictedQuery domain environment rounds
      ((System.trN (restrictDDE domain domainPrefix environment rounds)
        system stage).map Prod.snd)) at queryMember
  rw [Part.mem_ofOption, Option.mem_def] at queryMember
  obtain ⟨history, replayEqual, _, admitted⟩ :=
    (restrictedQuery_some_data domain environment rounds _ queryMember).2
  have canonicalReplay := replay_trN_restrictDDE domain domainPrefix
    environment rounds system hasDomain stage
  rw [canonicalReplay] at replayEqual
  have historyEqual : history = encodeTranscript
      (System.trN (restrictDDE domain domainPrefix environment rounds)
        system stage) :=
    Option.some.inj replayEqual.symm
  rw [historyEqual, transcriptInputs_encodeTranscript] at admitted
  rw [hasDomain]
  exact admitted

private theorem restrictDDE_stops {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (law : Distribution (System.DDS X Y)) :
    PDS.Stops (restrictDDE domain domainPrefix environment rounds) law :=
  PDS.stops_of_halts
    (restrictDDE_halts domain domainPrefix environment rounds) law

private theorem trN_prefix_of_le {X : Type u} {Y : Type v}
    (environment : System.DDE Y X) (system : System.DDS X Y)
    {first second : Nat} (less : first ≤ second) :
    System.trN environment system first <+:
      System.trN environment system second := by
  induction second, less using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ second _ inductionHypothesis =>
      apply inductionHypothesis.trans
      rcases System.trExtend_eq_or_append environment system
          (System.trN environment system second) with
        unchanged | ⟨pair, appended⟩
      · simp [System.trN, unchanged]
      · rw [System.trN, appended]
        exact List.prefix_append (System.trN environment system second) [pair]

private theorem restrictDDE_stages_eq_of_final_eq
    {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (left right : System.DDS X Y)
    (leftDomain : System.dom left = domain)
    (rightDomain : System.dom right = domain)
    (finalEqual :
      System.trN (restrictDDE domain domainPrefix environment rounds)
          left rounds =
        System.trN (restrictDDE domain domainPrefix environment rounds)
          right rounds) :
    ∀ stage, stage ≤ rounds →
      System.trN (restrictDDE domain domainPrefix environment rounds)
          left stage =
        System.trN (restrictDDE domain domainPrefix environment rounds)
          right stage := by
  intro stage stageLe
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      have stageLe' : stage ≤ rounds := by omega
      have currentEqual := inductionHypothesis stageLe'
      let literalEnvironment :=
        restrictDDE domain domainPrefix environment rounds
      let leftCurrent := System.trN literalEnvironment left stage
      let rightCurrent := System.trN literalEnvironment right stage
      have currentEqual' : leftCurrent = rightCurrent := currentEqual
      have lengthEqual :
          (System.trN literalEnvironment left (stage + 1)).length =
            (System.trN literalEnvironment right (stage + 1)).length := by
        by_cases leftDefined :
            leftCurrent.map Prod.snd ∈ literalEnvironment.1.Dom
        · have rightDefined : rightCurrent.map Prod.snd ∈
              literalEnvironment.1.Dom := by
            rwa [← currentEqual']
          let query := (literalEnvironment.1
            (leftCurrent.map Prod.snd)).get leftDefined
          let rightQuery := (literalEnvironment.1
            (rightCurrent.map Prod.snd)).get rightDefined
          have leftQueryMember : query ∈
              literalEnvironment.1 (leftCurrent.map Prod.snd) :=
            Part.get_mem leftDefined
          have rightQueryMember : rightQuery ∈
              literalEnvironment.1 (rightCurrent.map Prod.snd) :=
            Part.get_mem rightDefined
          have leftCompatible := restrictDDE_compatible domain domainPrefix
            environment rounds left leftDomain
          have rightCompatible := restrictDDE_compatible domain domainPrefix
            environment rounds right rightDomain
          have leftSystemDefined := leftCompatible stage query leftQueryMember
          have rightSystemDefined :=
            rightCompatible stage rightQuery rightQueryMember
          rw [System.trN_succ_of_query leftDefined leftSystemDefined,
            System.trN_succ_of_query rightDefined rightSystemDefined]
          simp only [List.length_append, List.length_singleton]
          change leftCurrent.length + 1 = rightCurrent.length + 1
          exact congrArg (fun length => length + 1)
            (congrArg List.length currentEqual')
        · have rightUndefined : rightCurrent.map Prod.snd ∉
              literalEnvironment.1.Dom := by
            rwa [← currentEqual']
          rw [System.trN_succ_of_stop leftDefined,
            System.trN_succ_of_stop rightUndefined]
          change leftCurrent.length = rightCurrent.length
          exact congrArg List.length currentEqual'
      have leftPrefixFinal := trN_prefix_of_le literalEnvironment left
        (show stage + 1 ≤ rounds by omega)
      have rightPrefixFinal := trN_prefix_of_le literalEnvironment right
        (show stage + 1 ≤ rounds by omega)
      rw [finalEqual] at leftPrefixFinal
      rw [List.prefix_iff_eq_take] at leftPrefixFinal rightPrefixFinal
      rw [leftPrefixFinal, rightPrefixFinal, lengthEqual]

private theorem transcript_eq_encode_restricted_of_admitted
    {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (system : System.DDS X Y)
    (hasDomain : System.dom system = domain) :
    ∀ stage, stage ≤ rounds →
      (Ambient.transcriptInputs
          (Ambient.transcript (embedDDS system) environment stage) = [] ∨
        Ambient.transcriptInputs
          (Ambient.transcript (embedDDS system) environment stage) ∈
            domain) →
      Ambient.transcript (embedDDS system) environment stage =
        encodeTranscript
          (System.trN
            (restrictDDE domain domainPrefix environment rounds) system stage) := by
  intro stage stageLe admitted
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      let current := Ambient.transcript (embedDDS system) environment stage
      let literalEnvironment := restrictDDE domain domainPrefix environment rounds
      let literalCurrent := System.trN literalEnvironment system stage
      cases next : environment current with
      | none =>
          have previousAdmitted :
              Ambient.transcriptInputs current = [] ∨
                Ambient.transcriptInputs current ∈ domain := by
            simpa [current, Ambient.transcript_succ, next] using admitted
          have previousEqual := inductionHypothesis (by omega) previousAdmitted
          have replayEqual := replay_trN_restrictDDE domain domainPrefix
            environment rounds system hasDomain stage
          have restrictedNone :
              restrictedQuery domain environment rounds
                (literalCurrent.map Prod.snd) = none := by
            unfold restrictedQuery
            have within : (literalCurrent.map Prod.snd).length < rounds := by
              rw [List.length_map]
              have lengthLe : literalCurrent.length ≤ stage :=
                System.trN_length_le literalEnvironment system stage
              omega
            rw [dif_pos within]
            change replay environment (literalCurrent.map Prod.snd) =
              some (encodeTranscript literalCurrent) at replayEqual
            rw [replayEqual]
            simp only
            have nextEncoded : environment (encodeTranscript literalCurrent) =
                none := by
              rwa [← previousEqual]
            rw [nextEncoded]
          have literalStopped : literalCurrent.map Prod.snd ∉
              literalEnvironment.1.Dom := by
            change ¬(Part.ofOption
              (restrictedQuery domain environment rounds
                (literalCurrent.map Prod.snd))).Dom
            rw [Part.ofOption_dom, restrictedNone]
            simp
          rw [Ambient.transcript_succ, next,
            System.trN_succ_of_stop literalStopped]
          exact previousEqual
      | some query =>
          have currentInputs :
              Ambient.transcriptInputs
                (Ambient.transcript (embedDDS system) environment
                  (stage + 1)) =
                Ambient.transcriptInputs current ++ [query] :=
            Ambient.transcriptInputs_succ_of_query _ _ stage query next
          have nextAdmitted :
              Ambient.transcriptInputs current ++ [query] ∈ domain := by
            rw [currentInputs] at admitted
            rcases admitted with empty | inDomain
            · simp at empty
            · exact inDomain
          have previousAdmitted :
              Ambient.transcriptInputs current = [] ∨
                Ambient.transcriptInputs current ∈ domain := by
            by_cases empty : Ambient.transcriptInputs current = []
            · exact Or.inl empty
            · exact Or.inr (domainPrefix
                (List.prefix_append _ [query]) empty nextAdmitted)
          have previousEqual := inductionHypothesis (by omega) previousAdmitted
          have replayEqual := replay_trN_restrictDDE domain domainPrefix
            environment rounds system hasDomain stage
          have restrictedSome :
              restrictedQuery domain environment rounds
                (literalCurrent.map Prod.snd) = some query := by
            unfold restrictedQuery
            have within : (literalCurrent.map Prod.snd).length < rounds := by
              rw [List.length_map]
              have lengthLe : literalCurrent.length ≤ stage :=
                System.trN_length_le literalEnvironment system stage
              omega
            rw [dif_pos within]
            change replay environment (literalCurrent.map Prod.snd) =
              some (encodeTranscript literalCurrent) at replayEqual
            rw [replayEqual]
            simp only
            have nextEncoded : environment (encodeTranscript literalCurrent) =
                some query := by
              rwa [← previousEqual]
            rw [nextEncoded]
            simp only
            have inputsEqual := congrArg Ambient.transcriptInputs
              previousEqual
            rw [transcriptInputs_encodeTranscript] at inputsEqual
            split
            · rfl
            · rename_i notAdmitted
              exact False.elim (notAdmitted (by
                rw [transcriptInputs_encodeTranscript]
                rwa [← inputsEqual]))
          have literalDefined : literalCurrent.map Prod.snd ∈
              literalEnvironment.1.Dom := by
            change (Part.ofOption
              (restrictedQuery domain environment rounds
                (literalCurrent.map Prod.snd))).Dom
            rw [Part.ofOption_dom, restrictedSome]
            rfl
          let queryValue : X :=
            (literalEnvironment.1 (literalCurrent.map Prod.snd)).get
              literalDefined
          have literalQuery : queryValue = (show X from query) := by
            apply Part.get_eq_of_mem
            change (show X from query) ∈ Part.ofOption
              (restrictedQuery domain environment rounds
                (literalCurrent.map Prod.snd))
            rw [Part.mem_ofOption, Option.mem_def]
            exact restrictedSome
          have systemDefined : literalCurrent.map Prod.fst ++
                [(show X from query)] ∈
              System.dom system := by
            rw [hasDomain]
            have inputsEqual := congrArg Ambient.transcriptInputs
              previousEqual
            rw [transcriptInputs_encodeTranscript] at inputsEqual
            rwa [← inputsEqual]
          have systemDefinedValue : literalCurrent.map Prod.fst ++
                [queryValue] ∈ System.dom system := by
            rw [literalQuery]
            exact systemDefined
          rw [Ambient.transcript_succ, next,
            System.trN_succ_of_query literalDefined systemDefinedValue]
          simp only [encodeTranscript, List.map_append, List.map_singleton]
          rw [previousEqual]
          apply congrArg (fun entry => encodeTranscript literalCurrent ++ [entry])
          refine Sigma.ext literalQuery.symm ?_
          apply heq_of_eq
          rw [transcriptInputs_encodeTranscript]
          change Ambient.Attachment.innerReplyAt (embedDDS system)
              (literalCurrent.map Prod.fst) query =
            some (System.output system
              (literalCurrent.map Prod.fst ++ [queryValue])
              systemDefinedValue)
          rw [innerReplyAt_embedDDS_eq]
          change Part.equivOption
              (system.1 (literalCurrent.map Prod.fst ++
                [(show X from query)])) =
            some (System.output system
              (literalCurrent.map Prod.fst ++ [queryValue])
              systemDefinedValue)
          rw [show Part.equivOption
              (system.1 (literalCurrent.map Prod.fst ++
                [(show X from query)])) =
              @Part.toOption Y
                (system.1 (literalCurrent.map Prod.fst ++
                  [(show X from query)]))
                (Classical.propDecidable _) by rfl]
          exact (@Part.toOption_eq_some_iff Y
            (system.1 (literalCurrent.map Prod.fst ++
              [(show X from query)]))
            (Classical.propDecidable _)
            (System.output system
              (literalCurrent.map Prod.fst ++ [queryValue])
              systemDefinedValue)).mpr
            ⟨systemDefined, System.output_congr system
              (by rw [literalQuery]) systemDefined systemDefinedValue⟩

private theorem ambientTranscript_eq_of_restricted_final_eq
    {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment :
      Ambient.DDE (Ambient.Interface.single X Y))
    (rounds : Nat) (left right : System.DDS X Y)
    (leftDomain : System.dom left = domain)
    (rightDomain : System.dom right = domain)
    (finalEqual :
      System.trN (restrictDDE domain domainPrefix environment rounds)
          left rounds =
        System.trN (restrictDDE domain domainPrefix environment rounds)
          right rounds) :
    Ambient.transcript (embedDDS left) environment rounds =
      Ambient.transcript (embedDDS right) environment rounds := by
  have stageEqual := restrictDDE_stages_eq_of_final_eq domain domainPrefix
    environment rounds left right leftDomain rightDomain finalEqual
  have leftFactor := transcript_eq_encode_restricted_of_admitted domain
    domainPrefix environment rounds left leftDomain
  have rightFactor := transcript_eq_encode_restricted_of_admitted domain
    domainPrefix environment rounds right rightDomain
  have allStages : ∀ stage, stage ≤ rounds →
      Ambient.transcript (embedDDS left) environment stage =
        Ambient.transcript (embedDDS right) environment stage := by
    intro stage stageLe
    induction stage with
    | zero => rfl
    | succ stage inductionHypothesis =>
        have previousEqual := inductionHypothesis (by omega)
        let current := Ambient.transcript (embedDDS left) environment stage
        cases next : environment current with
        | none =>
            rw [Ambient.transcript_succ,
              Ambient.transcript_succ, next]
            have nextRight :
                environment
                    (Ambient.transcript (embedDDS right) environment stage) =
                  none := by
              rwa [← previousEqual]
            rw [nextRight, previousEqual]
        | some query =>
            have nextRight :
                environment
                    (Ambient.transcript (embedDDS right) environment stage) =
                  some query := by
              rwa [← previousEqual]
            by_cases admitted :
                Ambient.transcriptInputs current ++ [query] ∈ domain
            · have leftInputs :
                  Ambient.transcriptInputs
                    (Ambient.transcript (embedDDS left) environment
                      (stage + 1)) =
                    Ambient.transcriptInputs current ++ [query] :=
                Ambient.transcriptInputs_succ_of_query _ _ stage query next
              have rightInputs :
                  Ambient.transcriptInputs
                    (Ambient.transcript (embedDDS right) environment
                      (stage + 1)) =
                    Ambient.transcriptInputs current ++ [query] := by
                rw [Ambient.transcriptInputs_succ_of_query _ _ stage
                  query nextRight, ← previousEqual]
              have leftAdmitted :
                  Ambient.transcriptInputs
                    (Ambient.transcript (embedDDS left) environment
                      (stage + 1)) ∈ domain := by
                rwa [leftInputs]
              have rightAdmitted :
                  Ambient.transcriptInputs
                    (Ambient.transcript (embedDDS right) environment
                      (stage + 1)) ∈ domain := by
                rwa [rightInputs]
              exact (leftFactor (stage + 1) stageLe (Or.inr leftAdmitted)).trans
                ((congrArg encodeTranscript
                    (stageEqual (stage + 1) stageLe)).trans
                  (rightFactor (stage + 1) stageLe
                    (Or.inr rightAdmitted)).symm)
            · rw [Ambient.transcript_succ,
                Ambient.transcript_succ, next, nextRight, previousEqual]
              apply congrArg (fun reply =>
                Ambient.transcript (embedDDS right) environment stage ++
                  [reply])
              have leftRejected' :
                  Ambient.transcriptInputs
                      (Ambient.transcript (embedDDS right) environment stage) ++
                      [query] ∉ System.dom left := by
                rw [leftDomain, ← previousEqual]
                exact admitted
              have rightRejected' :
                  Ambient.transcriptInputs
                      (Ambient.transcript (embedDDS right) environment stage) ++
                      [query] ∉ System.dom right := by
                rw [rightDomain, ← previousEqual]
                exact admitted
              have leftReply :
                  Ambient.Attachment.innerReplyAt (embedDDS left)
                    (Ambient.transcriptInputs
                      (Ambient.transcript (embedDDS right) environment stage))
                    query = none :=
                (innerReplyAt_embedDDS_eq_none_iff left _ _).mpr leftRejected'
              have rightReply :
                  Ambient.Attachment.innerReplyAt (embedDDS right)
                    (Ambient.transcriptInputs
                      (Ambient.transcript (embedDDS right) environment stage))
                    query = none :=
                (innerReplyAt_embedDDS_eq_none_iff right _ _).mpr rightRejected'
              refine Sigma.ext rfl ?_
              apply heq_of_eq
              exact leftReply.trans rightReply.symm
  exact allStages rounds le_rfl

private noncomputable def observationOfLiteralTranscript
    {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment : Ambient.DDE
      (Ambient.Interface.single X Y)) (rounds : Nat)
    (literalTranscript : System.Transcript X Y) :
    Ambient.Transcript (Ambient.Interface.single X Y) := by
  classical
  if existsSystem : ∃ system : System.DDS X Y,
      System.dom system = domain ∧
        System.trN
          (restrictDDE domain domainPrefix environment rounds) system rounds =
            literalTranscript then
    exact Ambient.transcript (embedDDS existsSystem.choose)
      environment rounds
  else
    exact []

private noncomputable def observationOfOptionalLiteralTranscript
    {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment : Ambient.DDE
      (Ambient.Interface.single X Y)) (rounds : Nat) :
    Option (System.Transcript X Y) →
      Ambient.Transcript (Ambient.Interface.single X Y)
  | none => []
  | some literalTranscript =>
      observationOfLiteralTranscript domain domainPrefix environment rounds
        literalTranscript

private theorem observationOfOptionalLiteralTranscript_system
    {X : Type u} {Y : Type v}
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (environment : Ambient.DDE
      (Ambient.Interface.single X Y)) (rounds : Nat)
    (system : System.DDS X Y) (hasDomain : System.dom system = domain) :
    observationOfOptionalLiteralTranscript domain domainPrefix environment rounds
        (Part.equivOption
          (System.tr (restrictDDE domain domainPrefix environment rounds) system)) =
      Ambient.transcript (embedDDS system) environment rounds := by
  classical
  let literalEnvironment :=
    restrictDDE domain domainPrefix environment rounds
  have haltsAt : ∀ answers : List Y, rounds ≤ answers.length →
      answers ∉ literalEnvironment.1.Dom := by
    intro answers lengthAtLeast inDomain
    change (Part.ofOption
      (restrictedQuery domain environment rounds answers)).Dom at inDomain
    rw [Part.ofOption_dom] at inDomain
    obtain ⟨query, queryEqual⟩ := Option.isSome_iff_exists.mp inDomain
    have data := restrictedQuery_some_data domain environment rounds answers
      queryEqual
    omega
  have stable := System.trN_succ_eq_of_halts_bound haltsAt system
  have stops : System.Stops literalEnvironment system := ⟨rounds, stable⟩
  have transcriptValue :
      Part.equivOption (System.tr literalEnvironment system) =
        some (System.trN literalEnvironment system rounds) := by
    change @Part.toOption _ (System.tr literalEnvironment system)
        (Classical.propDecidable _) =
      some (System.trN literalEnvironment system rounds)
    exact Part.toOption_eq_some_iff.mpr
      ⟨stops, System.tr_get_eq_trN stops stable⟩
  rw [transcriptValue]
  simp only [observationOfOptionalLiteralTranscript]
  unfold observationOfLiteralTranscript
  split
  · rename_i existsSystem
    exact ambientTranscript_eq_of_restricted_final_eq domain domainPrefix
      environment rounds existsSystem.choose system
      existsSystem.choose_spec.1 hasDomain
      (existsSystem.choose_spec.2.trans rfl)
  · rename_i noSystem
    exact False.elim (noSystem ⟨system, hasDomain, rfl⟩)

private theorem trLaw_embedPDS_eq_map_transcriptLaw_of_domain
    {X : Type u} {Y : Type v}
    (presentation :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y)
    (domain : Set (List X)) (domainPrefix : DomainPrefixClosed domain)
    (hasDomain : ∀ system ∈ presentation.law.1.support,
      System.dom system = domain)
    (environment : Ambient.DDE
      (Ambient.Interface.single X Y)) (rounds : Nat) :
    Ambient.PDS.trLaw environment rounds (embedPDS presentation.law) =
      Distribution.fTransform
        (observationOfOptionalLiteralTranscript domain domainPrefix environment
          rounds)
        (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
          (restrictDDE domain domainPrefix environment rounds) presentation) := by
  classical
  unfold Ambient.PDS.trLaw RandomSystems.Ambient.trLaw embedPDS
    RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
    RandomSystems.PDS.trLaw
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro system supported
  exact (observationOfOptionalLiteralTranscript_system domain domainPrefix
    environment rounds system (hasDomain system supported)).symm

private theorem trLaw_embedPDS_eq_map_transcriptLaw
    {X : Type u} {Y : Type v}
    (presentation :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y)
    (environment : Ambient.DDE
      (Ambient.Interface.single X Y)) (rounds : Nat) :
    Ambient.PDS.trLaw environment rounds (embedPDS presentation.law) =
      Distribution.fTransform
        (observationOfOptionalLiteralTranscript presentation.domain
          (probabilityPresentation_domainPrefixClosed presentation)
          environment rounds)
        (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
          (restrictDDE presentation.domain
            (probabilityPresentation_domainPrefixClosed presentation)
            environment rounds) presentation) :=
  trLaw_embedPDS_eq_map_transcriptLaw_of_domain presentation
    presentation.domain
    (probabilityPresentation_domainPrefixClosed presentation)
    presentation.hasDomain environment rounds

private theorem embedPDS_equivalent_of_equivalent
    {X : Type u} {Y : Type v}
    {left right :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y}
    (equivalent :
      RandomSystems.CommonDomain.ProbabilityPresentation.Equivalent
        left right) :
    Ambient.PDS.equivalent (embedPDS left.law)
      (embedPDS right.law) := by
  -- Fix an ambient finite observation and restrict it to the shared literal domain.
  intro environment rounds
  let domainPrefix := probabilityPresentation_domainPrefixClosed left
  let literalEnvironment :=
    restrictDDE left.domain domainPrefix environment rounds
  have leftCompatible : RandomSystems.PDS.Compatible
      literalEnvironment left.law.1 := by
    intro system supported
    exact restrictDDE_compatible left.domain domainPrefix environment rounds
      system (left.hasDomain system supported)
  have rightCompatible : RandomSystems.PDS.Compatible
      literalEnvironment right.law.1 := by
    intro system supported
    exact restrictDDE_compatible left.domain domainPrefix environment rounds
      system (by rw [right.hasDomain system supported, equivalent.1])
  have leftStops := restrictDDE_stops left.domain domainPrefix environment rounds
    left.law.1
  have rightStops := restrictDDE_stops left.domain domainPrefix environment rounds
    right.law.1
  -- Literal equivalence identifies the two restricted transcript laws.
  have literalLawEqual := equivalent.2 literalEnvironment
    ⟨⟨leftCompatible, leftStops⟩, ⟨rightCompatible, rightStops⟩⟩
  rw [trLaw_embedPDS_eq_map_transcriptLaw left environment rounds]
  have rightFactor := trLaw_embedPDS_eq_map_transcriptLaw_of_domain right
    left.domain domainPrefix (fun system supported => by
      rw [right.hasDomain system supported, equivalent.1]) environment rounds
  rw [rightFactor, literalLawEqual]

/-- Lanzenberger, Definition 2.17 (printed p. 16), requires two PDSs to
"have the same domain" and gives equality of transcript laws under every
jointly compatible DDE.  Direct optionalization preserves and reflects that
relation against every finite query-indexed DDE observation. -/
theorem embedPDS_equivalent_iff {X : Type u} {Y : Type v}
    {left right :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y} :
    Ambient.PDS.equivalent (embedPDS left.law)
        (embedPDS right.law) ↔
      RandomSystems.CommonDomain.ProbabilityPresentation.Equivalent
        left right :=
  ⟨literalEquivalent_of_ambientEquivalent,
    embedPDS_equivalent_of_equivalent⟩

private theorem advantage_le_embedPDS_advantage
    {X : Type u} {Y : Type v}
    (left right :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y) :
    RandomSystems.PDS.advantage left.law.1 right.law.1 ≤
      Ambient.PDS.advantage (embedPDS left.law) (embedPDS right.law) := by
  -- Bound each compatible, stopping literal DDE separately.
  unfold RandomSystems.PDS.advantage
  refine iSup_le fun environment => ?_
  let rounds := max
    (stoppingBound environment.1 left.law.1 environment.2.1.2)
    (stoppingBound environment.1 right.law.1 environment.2.2.2)
  have leftEnough :
      stoppingBound environment.1 left.law.1 environment.2.1.2 ≤ rounds :=
    le_max_left _ _
  have rightEnough :
      stoppingBound environment.1 right.law.1 environment.2.2.2 ≤ rounds :=
    le_max_right _ _
  -- Decode one sufficiently long ambient transcript into the literal transcript.
  change ENNReal.ofReal
      (Probability.statDist
        (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
          environment.1 left)
        (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
          environment.1 right)) ≤
    Ambient.PDS.advantage (embedPDS left.law) (embedPDS right.law)
  rw [literalTranscriptLaw_eq_decode_trLaw environment.1 left
      environment.2.1.1 environment.2.1.2 rounds leftEnough,
    literalTranscriptLaw_eq_decode_trLaw environment.1 right
      environment.2.2.1 environment.2.2.2 rounds rightEnough]
  calc
    ENNReal.ofReal
        (Probability.statDist
          (Distribution.fTransform decodeTranscript
            (Ambient.PDS.trLaw (liftDDE environment.1) rounds
              (embedPDS left.law)))
          (Distribution.fTransform decodeTranscript
            (Ambient.PDS.trLaw (liftDDE environment.1) rounds
            (embedPDS right.law)))) ≤
      ENNReal.ofReal
        (Probability.statDist
          (Ambient.PDS.trLaw (liftDDE environment.1) rounds
            (embedPDS left.law))
          (Ambient.PDS.trLaw (liftDDE environment.1) rounds
            (embedPDS right.law))) :=
      -- Statistical distance cannot increase under transcript decoding.
      ENNReal.ofReal_le_ofReal
        (Probability.statDist_fTransform_le _ _ decodeTranscript)
    _ ≤ Ambient.PDS.advantage (embedPDS left.law)
        (embedPDS right.law) :=
      le_iSup_of_le (liftDDE environment.1)
        (le_iSup_of_le rounds le_rfl)

private theorem embedPDS_advantage_le_advantage_of_domain_eq
    {X : Type u} {Y : Type v}
    (left right :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y)
    (domainEqual : left.domain = right.domain) :
    Ambient.PDS.advantage (embedPDS left.law) (embedPDS right.law) ≤
      RandomSystems.PDS.advantage left.law.1 right.law.1 := by
  -- Bound each finite ambient DDE observation separately.
  unfold Ambient.PDS.advantage
  refine iSup_le fun environment => iSup_le fun rounds => ?_
  let domainPrefix := probabilityPresentation_domainPrefixClosed left
  let literalEnvironment :=
    restrictDDE left.domain domainPrefix environment rounds
  have leftCompatible : RandomSystems.PDS.Compatible
      literalEnvironment left.law.1 := by
    intro system supported
    exact restrictDDE_compatible left.domain domainPrefix environment rounds
      system (left.hasDomain system supported)
  have rightCompatible : RandomSystems.PDS.Compatible
      literalEnvironment right.law.1 := by
    intro system supported
    exact restrictDDE_compatible left.domain domainPrefix environment rounds
      system (by rw [right.hasDomain system supported, domainEqual])
  have leftStops := restrictDDE_stops left.domain domainPrefix environment rounds
    left.law.1
  have rightStops := restrictDDE_stops left.domain domainPrefix environment rounds
    right.law.1
  -- Both ambient transcript laws factor through the same restricted DDE.
  rw [trLaw_embedPDS_eq_map_transcriptLaw left environment rounds]
  have rightFactor := trLaw_embedPDS_eq_map_transcriptLaw_of_domain right
    left.domain domainPrefix (fun system supported => by
      rw [right.hasDomain system supported, domainEqual]) environment rounds
  rw [rightFactor]
  calc
    ENNReal.ofReal
        (Probability.statDist
          (Distribution.fTransform
            (observationOfOptionalLiteralTranscript left.domain domainPrefix
              environment rounds)
            (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
              literalEnvironment left))
          (Distribution.fTransform
            (observationOfOptionalLiteralTranscript left.domain domainPrefix
              environment rounds)
            (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
              literalEnvironment right))) ≤
      ENNReal.ofReal
        (Probability.statDist
          (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
            literalEnvironment left)
          (RandomSystems.CommonDomain.ProbabilityPresentation.transcriptLaw
            literalEnvironment right)) :=
      -- Statistical distance cannot increase under the common observation map.
      ENNReal.ofReal_le_ofReal
        (Probability.statDist_fTransform_le _ _
          (observationOfOptionalLiteralTranscript left.domain domainPrefix
            environment rounds))
    _ ≤ RandomSystems.PDS.advantage left.law.1 right.law.1 :=
      -- The restricted DDE is compatible with both common-domain presentations.
      le_iSup_of_le
        (⟨literalEnvironment, ⟨⟨leftCompatible, leftStops⟩,
          ⟨rightCompatible, rightStops⟩⟩⟩) le_rfl

/-- Lanzenberger, Definition 2.26 (printed p. 18), defines `Adv(S,T)` as the
supremum of transcript-law statistical distance over jointly compatible DDEs.
For two normalized presentations with one common domain, this is exactly the
finite attempted-history DDE advantage of their direct optionalizations. -/
theorem advantage_embedPDS_eq_Adv_of_domain_eq
    {X : Type u} {Y : Type v}
    (left right :
      RandomSystems.CommonDomain.ProbabilityPresentation X Y)
    (domainEqual : left.domain = right.domain) :
    Ambient.PDS.advantage (embedPDS left.law) (embedPDS right.law) =
      RandomSystems.CommonDomain.Presentation.Adv
        (D := left.domain)
        ⟨left.toPresentation, rfl⟩
        ⟨right.toPresentation, domainEqual.symm⟩ := by
  change Ambient.PDS.advantage (embedPDS left.law) (embedPDS right.law) =
    RandomSystems.PDS.advantage left.law.1 right.law.1
  exact le_antisymm
    (embedPDS_advantage_le_advantage_of_domain_eq left right domainEqual)
    (advantage_le_embedPDS_advantage left right)

end

end RandomSystems.CommonDomain

namespace RandomSystems.CommonDomain

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

namespace ProbabilityPresentation

/-- Map a normalized common-domain presentation to the query-indexed random
system represented by its direct optionalization. -/
def toAmbient (system : ProbabilityPresentation X Y) :
    Ambient.RandomSystem (Ambient.Interface.single X Y) :=
  Ambient.RandomSystem.ofPDS
    (RandomSystems.CommonDomain.embedPDS system.law)

@[simp]
theorem toAmbient_eq_iff {left right : ProbabilityPresentation X Y} :
    toAmbient left = toAmbient right ↔ Equivalent left right := by
  rw [toAmbient, toAmbient,
    Ambient.RandomSystem.ofPDS_eq_iff,
    RandomSystems.CommonDomain.embedPDS_equivalent_iff]

end ProbabilityPresentation

namespace ProbabilityRandomSystem

/-- Embed a normalized common-domain random system in the query-indexed
random-system carrier. -/
def toAmbient : ProbabilityRandomSystem X Y →
    Ambient.RandomSystem (Ambient.Interface.single X Y) :=
  Quotient.lift ProbabilityPresentation.toAmbient fun _ _ equivalent =>
    ProbabilityPresentation.toAmbient_eq_iff.mpr equivalent

@[simp]
theorem toAmbient_ofPresentation (system : ProbabilityPresentation X Y) :
    toAmbient (ofPresentation system) =
      ProbabilityPresentation.toAmbient system :=
  rfl

/-- Direct optionalization embeds normalized common-domain random systems
faithfully in the query-indexed random-system carrier. -/
theorem toAmbient_injective : Function.Injective
    (toAmbient : ProbabilityRandomSystem X Y →
      Ambient.RandomSystem (Ambient.Interface.single X Y)) := by
  intro left right equal
  induction left using Quotient.ind with
  | _ leftPresentation =>
      induction right using Quotient.ind with
      | _ rightPresentation =>
          apply ofPresentation_eq_iff.mpr
          apply ProbabilityPresentation.toAmbient_eq_iff.mp
          exact equal

/-- The normalized common-domain quotient carries the distance induced by its
faithful direct-optionalization embedding. -/
noncomputable instance : EMetricSpace (ProbabilityRandomSystem X Y) :=
  EMetricSpace.induced toAmbient toAmbient_injective inferInstance

@[simp]
theorem edist_eq_edist_toAmbient
    (left right : ProbabilityRandomSystem X Y) :
    edist left right = edist (toAmbient left) (toAmbient right) :=
  rfl

/-- Lanzenberger, Definition 2.26 (printed p. 18), takes the supremum over DDEs
“which are compatible with both `S` and `T`.”  On representatives with the
same common domain, the induced quotient distance is exactly `Adv`. -/
theorem edist_ofPresentation_of_domain_eq
    (left right : ProbabilityPresentation X Y)
    (domainEqual : left.domain = right.domain) :
    edist (ofPresentation left) (ofPresentation right) =
      RandomSystems.CommonDomain.Presentation.Adv
        (D := left.domain)
        ⟨left.toPresentation, rfl⟩
        ⟨right.toPresentation, domainEqual.symm⟩ := by
  rw [edist_eq_edist_toAmbient, toAmbient_ofPresentation,
    toAmbient_ofPresentation, ProbabilityPresentation.toAmbient,
    ProbabilityPresentation.toAmbient,
    Ambient.RandomSystem.edist_ofPDS_eq]
  exact RandomSystems.CommonDomain.advantage_embedPDS_eq_Adv_of_domain_eq
    left right domainEqual

end ProbabilityRandomSystem

end


end RandomSystems.CommonDomain
