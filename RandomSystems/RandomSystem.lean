import RandomSystems.Observation

set_option autoImplicit false

/-!
# Random systems

Lanzenberger, Definition 2.17 (printed p. 16): two PDSs are equivalent “if they
have the same domain” and their transcript distributions agree for every
compatible DDE.  Notation 2.19 on the same page uses “a random system, an
equivalence class of PDS.”

Lean provides both a normalized presentation and an arbitrary-mass
nonnegative presentation.  The latter supports linear arguments while using
the same common-domain observational quotient.
-/

namespace RandomSystems

noncomputable section

open Classical
open Probability (Distribution)

universe u v

variable {X : Type u} {Y : Type v}

namespace System

private def EnvConsistent (environment : DDE Y X) (transcript : Transcript X Y) : Prop :=
  ∀ k, (hk : k < transcript.length) →
    ∃ hdom : (transcript.take k).map Prod.snd ∈ environment.1.Dom,
      (environment.1 ((transcript.take k).map Prod.snd)).get hdom = transcript[k].1

private def SystemConsistent (system : DDS X Y) (transcript : Transcript X Y) : Prop :=
  ∀ k, (hk : k < transcript.length) →
    ∃ hdom : (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈ dom system,
      output system ((transcript.take k).map Prod.fst ++ [transcript[k].1]) hdom =
        transcript[k].2

private def FinalAt (environment : DDE Y X) (rounds : Nat)
    (transcript : Transcript X Y) : Prop :=
  transcript.length = rounds ∨
    (transcript.length < rounds ∧ transcript.map Prod.snd ∉ environment.1.Dom)

private theorem trN_consistent_of_compatible (system : DDS X Y) (environment : DDE Y X)
    (compatible : Compatible environment system) (rounds : Nat) :
    EnvConsistent environment (trN environment system rounds) ∧
      FinalAt environment rounds (trN environment system rounds) ∧
      SystemConsistent system (trN environment system rounds) := by
  induction rounds with
  | zero =>
      refine ⟨fun k hk => (by simp [trN] at hk), Or.inl rfl,
        fun k hk => (by simp [trN] at hk)⟩
  | succ rounds inductionHypothesis =>
      obtain ⟨environmentConsistent, finalAt, systemConsistent⟩ := inductionHypothesis
      by_cases environmentDomain :
          (trN environment system rounds).map Prod.snd ∈ environment.1.Dom
      · have queryMem := Part.get_mem environmentDomain
        have systemDomain := compatible rounds _ queryMem
        rw [trN_succ_of_query environmentDomain systemDomain]
        refine ⟨?_, Or.inl (by
          rcases finalAt with lengthEqual | ⟨_, stopped⟩
          · simp [lengthEqual]
          · exact absurd environmentDomain stopped), ?_⟩
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (trN environment system rounds).length with earlier | last
          · rw [List.take_append_of_le_length (le_of_lt earlier),
              List.getElem_append_left earlier]
            exact environmentConsistent k earlier
          · have kEqual : k = (trN environment system rounds).length := by omega
            subst kEqual
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            refine ⟨environmentDomain, ?_⟩
            simp
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (trN environment system rounds).length with earlier | last
          · rw [List.take_append_of_le_length (le_of_lt earlier),
              List.getElem_append_left earlier]
            exact systemConsistent k earlier
          · have kEqual : k = (trN environment system rounds).length := by omega
            subst kEqual
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            simpa only [Nat.sub_self, List.getElem_cons_zero] using
              (show ∃ hdom, output system
                  ((trN environment system rounds).map Prod.fst ++
                    [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                      environmentDomain]) hdom =
                    output system
                      ((trN environment system rounds).map Prod.fst ++
                        [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                          environmentDomain]) systemDomain from
                ⟨systemDomain, rfl⟩)
      · rw [trN_succ_of_stop environmentDomain]
        refine ⟨environmentConsistent, Or.inr ⟨?_, environmentDomain⟩,
          systemConsistent⟩
        rcases finalAt with lengthEqual | ⟨lengthLess, _⟩ <;> omega

private theorem trN_eq_of_consistent (system : DDS X Y) (environment : DDE Y X) :
    ∀ (rounds : Nat) (transcript : Transcript X Y),
      EnvConsistent environment transcript →
      FinalAt environment rounds transcript →
      SystemConsistent system transcript →
      trN environment system rounds = transcript := by
  intro rounds
  induction rounds with
  | zero =>
      intro transcript _ finalAt _
      rcases finalAt with lengthEqual | ⟨lengthLess, _⟩
      · simpa [trN] using (List.eq_nil_of_length_eq_zero lengthEqual).symm
      · omega
  | succ rounds inductionHypothesis =>
      intro transcript environmentConsistent finalAt systemConsistent
      rcases finalAt with lengthEqual | ⟨lengthLess, stopped⟩
      · have roundsLess : rounds < transcript.length := by omega
        have prefixEqual : trN environment system rounds = transcript.take rounds := by
          apply inductionHypothesis
          · intro k hk
            rw [List.length_take] at hk
            have kLess : k < transcript.length := by omega
            have kRounds : k ≤ rounds :=
              Nat.le_of_lt (lt_of_lt_of_le hk (min_le_left _ _))
            simpa only [List.take_take, min_eq_left kRounds,
              List.getElem_take] using environmentConsistent k kLess
          · exact Or.inl (by simp [List.length_take, show rounds ≤ transcript.length by omega])
          · intro k hk
            rw [List.length_take] at hk
            have kLess : k < transcript.length := by omega
            have kRounds : k ≤ rounds :=
              Nat.le_of_lt (lt_of_lt_of_le hk (min_le_left _ _))
            simpa only [List.take_take, min_eq_left kRounds,
              List.getElem_take] using systemConsistent k kLess
        obtain ⟨environmentDomain, queryEqual⟩ := environmentConsistent rounds roundsLess
        obtain ⟨systemDomain, answerEqual⟩ := systemConsistent rounds roundsLess
        have environmentDomain' :
            (trN environment system rounds).map Prod.snd ∈ environment.1.Dom := by
          rwa [prefixEqual]
        have queryEqual' :
            (environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain' = transcript[rounds].1 := by
          apply Part.get_eq_of_mem
          rw [prefixEqual]
          exact queryEqual ▸ Part.get_mem environmentDomain
        have systemDomain' :
            (trN environment system rounds).map Prod.fst ++
              [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain'] ∈ dom system := by
          rw [queryEqual']
          simpa only [prefixEqual] using systemDomain
        have answerEqual' :
            output system ((trN environment system rounds).map Prod.fst ++
              [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain']) systemDomain' = transcript[rounds].2 := by
          calc
            _ = output system ((transcript.take rounds).map Prod.fst ++
                [transcript[rounds].1]) systemDomain :=
              output_congr system (by rw [queryEqual', prefixEqual]) _ _
            _ = transcript[rounds].2 := answerEqual
        have pairEqual :
            ((environment.1 ((trN environment system rounds).map Prod.snd)).get
                environmentDomain',
              output system ((trN environment system rounds).map Prod.fst ++
                [(environment.1 ((trN environment system rounds).map Prod.snd)).get
                  environmentDomain']) systemDomain') = transcript[rounds] := by
          apply Prod.ext
          · exact queryEqual'
          · exact answerEqual'
        rw [trN_succ_of_query environmentDomain' systemDomain', pairEqual, prefixEqual]
        conv_rhs => rw [← List.take_length (l := transcript), lengthEqual]
        rw [List.take_add_one, List.getElem?_eq_getElem roundsLess]
        simp
      · have prefixEqual : trN environment system rounds = transcript := by
          apply inductionHypothesis transcript environmentConsistent
          · rcases Nat.lt_or_ge transcript.length rounds with less | greater
            · exact Or.inr ⟨less, stopped⟩
            · exact Or.inl (by omega)
          · exact systemConsistent
        rw [trN_succ_of_stop (by rwa [prefixEqual]), prefixEqual]

private def fixedQueries (queries : List X) : DDE Y X :=
  ⟨(fun answers : List Y =>
      (⟨answers.length < queries.length,
        fun h => queries[answers.length]⟩ : Part X)),
    by
      intro first second hprefix secondDomain
      exact lt_of_le_of_lt hprefix.length_le secondDomain⟩

@[simp]
private theorem fixedQueries_dom (queries : List X) (answers : List Y) :
    answers ∈ (fixedQueries (Y := Y) queries).1.Dom ↔
      answers.length < queries.length :=
  Iff.rfl

private theorem fixedQueries_get (queries : List X) (answers : List Y)
    (domain : answers ∈ (fixedQueries (Y := Y) queries).1.Dom) :
    ((fixedQueries (Y := Y) queries).1 answers).get domain = queries[answers.length] :=
  rfl

private theorem trN_fixedQueries (system : DDS X Y) (queries : List X)
    (admitted : queries = [] ∨ queries ∈ dom system) :
    ∀ rounds,
      (trN (fixedQueries (Y := Y) queries) system rounds).length =
          min rounds queries.length ∧
        (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.fst =
          queries.take rounds := by
  intro rounds
  induction rounds with
  | zero => simp [trN]
  | succ rounds inductionHypothesis =>
      obtain ⟨lengthEqual, inputsEqual⟩ := inductionHypothesis
      by_cases beforeEnd : rounds < queries.length
      · have environmentDomain :
            (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd ∈
              (fixedQueries (Y := Y) queries).1.Dom := by
          exact (fixedQueries_dom queries _).2 (by simpa [lengthEqual] using beforeEnd)
        have queryEqual :
            ((fixedQueries (Y := Y) queries).1
              ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).get
                environmentDomain = queries[rounds] := by
          have answerLengthEqual :
              ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd).length =
                rounds := by
            rw [List.length_map, lengthEqual, min_eq_left (Nat.le_of_lt beforeEnd)]
          simp only [fixedQueries_get, answerLengthEqual]
        have nextPrefix : queries.take (rounds + 1) ∈ dom system := by
          rcases admitted with empty | fullDomain
          · subst queries
            simp at beforeEnd
          · apply prefix_closed system (List.take_prefix _ _) (by
              intro empty
              have positive : 0 < (queries.take (rounds + 1)).length := by
                rw [List.length_take]
                omega
              rw [empty] at positive
              simp at positive)
              fullDomain
        have systemDomain :
            (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.fst ++
                [((fixedQueries (Y := Y) queries).1
                  ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).get
                    environmentDomain] ∈ dom system := by
          rw [inputsEqual, queryEqual]
          have takeEqual : queries.take (rounds + 1) =
              queries.take rounds ++ [queries[rounds]] := by
            rw [List.take_add_one, List.getElem?_eq_getElem beforeEnd,
              Option.toList_some]
          exact takeEqual ▸ nextPrefix
        rw [trN_succ_of_query environmentDomain systemDomain]
        constructor
        · simp only [List.length_append, List.length_singleton, lengthEqual]
          omega
        · simp only [List.map_append, inputsEqual, queryEqual, List.map_singleton]
          rw [List.take_add_one, List.getElem?_eq_getElem beforeEnd,
            Option.toList_some]
      · have atEnd : queries.length ≤ rounds := Nat.le_of_not_gt beforeEnd
        have environmentStopped :
            (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd ∉
              (fixedQueries (Y := Y) queries).1.Dom := by
          rw [fixedQueries_dom, List.length_map, lengthEqual,
            min_eq_right atEnd]
          omega
        rw [trN_succ_of_stop environmentStopped]
        constructor
        · rw [lengthEqual]
          omega
        · rw [inputsEqual, List.take_of_length_le atEnd,
            List.take_of_length_le (atEnd.trans (Nat.le_succ _))]

private theorem fixedQueries_compatible (system : DDS X Y) (queries : List X)
    (admitted : queries = [] ∨ queries ∈ dom system) :
    Compatible (fixedQueries (Y := Y) queries) system := by
  intro rounds query queryMem
  have invariant := trN_fixedQueries system queries admitted rounds
  have environmentDomain :
      (trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd ∈
        (fixedQueries (Y := Y) queries).1.Dom := Part.dom_iff_mem.mpr ⟨query, queryMem⟩
  have beforeEnd :
      (trN (fixedQueries (Y := Y) queries) system rounds).length < queries.length :=
    by
      simpa only [List.length_map] using
        (fixedQueries_dom queries
          ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).1
            environmentDomain
  have indexEqual :
      (trN (fixedQueries (Y := Y) queries) system rounds).length = rounds := by
    rw [invariant.1]
    omega
  have queryEqual : query = queries[rounds] := by
    have getIsQuery := Part.get_eq_of_mem queryMem environmentDomain
    have getIsFixed :
        ((fixedQueries (Y := Y) queries).1
          ((trN (fixedQueries (Y := Y) queries) system rounds).map Prod.snd)).get
            environmentDomain = queries[rounds] := by
      simp only [fixedQueries_get, List.length_map, indexEqual]
    exact getIsQuery.symm.trans getIsFixed
  rw [invariant.2, queryEqual]
  rcases admitted with empty | fullDomain
  · subst queries
    simp at beforeEnd
  · have nextPrefix := prefix_closed system (List.take_prefix (rounds + 1) queries) (by
      intro empty
      have positive : 0 < (queries.take (rounds + 1)).length := by
        rw [List.length_take]
        omega
      rw [empty] at positive
      simp at positive) fullDomain
    have takeEqual : queries.take (rounds + 1) =
        queries.take rounds ++ [queries[rounds]] := by
      rw [List.take_add_one,
        List.getElem?_eq_getElem (indexEqual ▸ beforeEnd), Option.toList_some]
    exact takeEqual ▸ nextPrefix

private theorem fixedQueries_stops (system : DDS X Y) (queries : List X)
    (admitted : queries = [] ∨ queries ∈ dom system) :
    Stops (fixedQueries (Y := Y) queries) system := by
  refine ⟨queries.length, trN_succ_of_stop ?_⟩
  rw [fixedQueries_dom, List.length_map]
  have invariant := (trN_fixedQueries system queries admitted queries.length).1
  omega

private theorem stopped_consistent_of_toOption_eq_some {environment : DDE Y X}
    {system : DDS X Y} (compatible : Compatible environment system)
    {transcript : Transcript X Y}
    (equal : (tr environment system).toOption = some transcript) :
    EnvConsistent environment transcript ∧
      transcript.map Prod.snd ∉ environment.1.Dom ∧
      SystemConsistent system transcript := by
  rw [Part.toOption_eq_some_iff] at equal
  obtain ⟨stops, valueEqual⟩ := equal
  have stable := Nat.find_spec stops
  have transcriptEqual : trN environment system (Nat.find stops) = transcript := by
    rw [← tr_get_eq_trN stops stable, valueEqual]
  have consistent := trN_consistent_of_compatible system environment compatible (Nat.find stops)
  refine ⟨transcriptEqual ▸ consistent.1, ?_, transcriptEqual ▸ consistent.2.2⟩
  have stopped := (trN_succ_eq_iff_of_compatible compatible (Nat.find stops)).1 stable
  rwa [transcriptEqual] at stopped

private theorem toOption_eq_some_iff_systemConsistent {environment : DDE Y X}
    {system : DDS X Y} (compatible : Compatible environment system)
    {transcript : Transcript X Y}
    (environmentConsistent : EnvConsistent environment transcript)
    (terminal : transcript.map Prod.snd ∉ environment.1.Dom) :
    (tr environment system).toOption = some transcript ↔
      SystemConsistent system transcript := by
  constructor
  · intro equal
    exact (stopped_consistent_of_toOption_eq_some compatible equal).2.2
  · intro systemConsistent
    have transcriptAtLength :
        trN environment system transcript.length = transcript :=
      trN_eq_of_consistent system environment transcript.length transcript
        environmentConsistent (Or.inl rfl) systemConsistent
    have stable : trN environment system (transcript.length + 1) =
        trN environment system transcript.length := by
      apply trN_succ_of_stop
      rwa [transcriptAtLength]
    rw [Part.toOption_eq_some_iff]
    let stops : Stops environment system := ⟨transcript.length, stable⟩
    exact ⟨stops, (tr_get_eq_trN stops stable).trans transcriptAtLength⟩

private theorem fixedQueries_envConsistent (transcript : Transcript X Y) :
    EnvConsistent (fixedQueries (Y := Y) (transcript.map Prod.fst)) transcript := by
  intro k hk
  have domain : (transcript.take k).map Prod.snd ∈
      (fixedQueries (Y := Y) (transcript.map Prod.fst)).1.Dom := by
    rw [fixedQueries_dom, List.length_map, List.length_take,
      List.length_map]
    omega
  refine ⟨domain, ?_⟩
  have indexEqual : ((transcript.take k).map Prod.snd).length = k := by
    rw [List.length_map, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have hkMap : k < (transcript.map Prod.fst).length := by simpa using hk
  calc
    ((fixedQueries (Y := Y) (transcript.map Prod.fst)).1
        ((transcript.take k).map Prod.snd)).get domain =
        (transcript.map Prod.fst)[k]'hkMap := by
          simp only [fixedQueries_get, indexEqual]
    _ = transcript[k].1 := by simp

private theorem fixedQueries_terminal (transcript : Transcript X Y) :
    transcript.map Prod.snd ∉
      (fixedQueries (Y := Y) (transcript.map Prod.fst)).1.Dom := by
  rw [fixedQueries_dom, List.length_map, List.length_map]
  exact Nat.not_lt_of_ge le_rfl

private theorem transcript_fiber_eq_fixedQueries {environment : DDE Y X}
    {system : DDS X Y} (environmentCompatible : Compatible environment system)
    {transcript : Transcript X Y}
    (environmentConsistent : EnvConsistent environment transcript)
    (terminal : transcript.map Prod.snd ∉ environment.1.Dom)
    (queriesAdmitted : transcript.map Prod.fst = [] ∨
      transcript.map Prod.fst ∈ dom system) :
    (tr environment system).toOption = some transcript ↔
      (tr (fixedQueries (Y := Y) (transcript.map Prod.fst)) system).toOption =
        some transcript := by
  rw [toOption_eq_some_iff_systemConsistent environmentCompatible
      environmentConsistent terminal,
    toOption_eq_some_iff_systemConsistent
      (fixedQueries_compatible system _ queriesAdmitted)
      (fixedQueries_envConsistent transcript) (fixedQueries_terminal transcript)]

end System

namespace CommonDomain

/-- A common-domain nonnegative PDS presentation.  Definition 2.14 (printed
p. 15) requires that “all DDS in the support of `S` have the same domain.”
This presentation permits arbitrary nonnegative mass, as does Definition
2.14. -/
structure Presentation (X : Type u) (Y : Type v) where
  law : Distribution (System.DDS X Y)
  nonnegative : law.NonNeg
  domain : Set (List X)
  hasDomain : PDS.HasDomain law domain

namespace Presentation

instance : Coe (Presentation X Y) (Distribution (System.DDS X Y)) :=
  ⟨law⟩

@[ext]
theorem ext {left right : Presentation X Y}
    (law : left.law = right.law) (domain : left.domain = right.domain) :
    left = right := by
  cases left
  cases right
  cases law
  cases domain
  rfl

/-- Every explicitly tagged presentation satisfies the existential
common-domain clause on its underlying law. -/
theorem hasFixedDomain (system : Presentation X Y) :
    PDS.HasFixedDomain system.law :=
  ⟨system.domain, system.hasDomain⟩

/-- Lanzenberger, Definition 2.17, footnote 5 (printed p. 16): “`tr(S, e)`
denotes the `tr(·, e)`-transformation of the distribution `S`.” -/
def transcriptLaw (environment : System.DDE Y X)
    (system : Presentation X Y) :
    Distribution (Option (System.Transcript X Y)) :=
  PDS.trLaw environment system.law

/-- Lanzenberger, Definition 2.17 (printed p. 16): “they have the same domain”
and `tr(S, e) = tr(T, e)` for every jointly compatible DDE.  Lean additionally
requires stopping because its transcript function is partial. -/
def Equivalent (left right : Presentation X Y) : Prop :=
  left.domain = right.domain ∧
    ∀ environment : System.DDE Y X,
      ((PDS.Compatible environment left.law ∧
          PDS.Stops environment left.law) ∧
        (PDS.Compatible environment right.law ∧
          PDS.Stops environment right.law)) →
        transcriptLaw environment left = transcriptLaw environment right

@[refl]
theorem equivalent_refl (system : Presentation X Y) : Equivalent system system :=
  ⟨rfl, fun _ _ => rfl⟩

@[symm]
theorem equivalent_symm {left right : Presentation X Y}
    (equivalent : Equivalent left right) : Equivalent right left :=
  ⟨equivalent.1.symm, fun environment admissible =>
    (equivalent.2 environment ⟨admissible.2, admissible.1⟩).symm⟩

private theorem transcriptLaw_none (system : Presentation X Y)
    (environment : System.DDE Y X) (stops : PDS.Stops environment system.law) :
    transcriptLaw environment system none = 0 := by
  rw [transcriptLaw, PDS.trLaw, Distribution.fTransform_apply_eq_mass]
  calc
    system.law.mass (fun deterministic =>
        (System.tr environment deterministic).toOption = none) =
        system.law.mass (fun _ => False) := by
      apply Distribution.mass_congr_of_support
      intro deterministic inSupport
      constructor
      · intro equal
        exact (Part.toOption_eq_none_iff.mp equal) (stops deterministic inSupport)
      · intro false
        exact false.elim
    _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)

private theorem queries_admitted_of_observed (system : Presentation X Y)
    (environment : System.DDE Y X) {deterministic : System.DDS X Y}
    (inSupport : deterministic ∈ system.law.support)
    {transcript : System.Transcript X Y}
    (observed : (System.tr environment deterministic).toOption = some transcript) :
    transcript.map Prod.fst = [] ∨ transcript.map Prod.fst ∈ system.domain := by
  rw [Part.toOption_eq_some_iff] at observed
  obtain ⟨stops, valueEqual⟩ := observed
  have stable := Nat.find_spec stops
  have transcriptEqual : System.trN environment deterministic (Nat.find stops) =
      transcript := by
    rw [← System.tr_get_eq_trN stops stable, valueEqual]
  rcases System.trN_map_fst_mem_dom_or_nil environment deterministic (Nat.find stops) with
    empty | admitted
  · exact Or.inl (by
      rw [transcriptEqual] at empty
      simp [empty])
  · right
    rw [← system.hasDomain deterministic inSupport]
    rwa [transcriptEqual] at admitted

private theorem queries_admitted_on_support (system : Presentation X Y)
    {queries : List X} (admitted : queries = [] ∨ queries ∈ system.domain)
    {deterministic : System.DDS X Y} (inSupport : deterministic ∈ system.law.support) :
    queries = [] ∨ queries ∈ System.dom deterministic := by
  rcases admitted with empty | inDomain
  · exact Or.inl empty
  · exact Or.inr (by rwa [system.hasDomain deterministic inSupport])

private theorem fixedQueries_admissible (system : Presentation X Y) {queries : List X}
    (admitted : queries = [] ∨ queries ∈ system.domain) :
    PDS.Compatible (System.fixedQueries (Y := Y) queries) system.law ∧
      PDS.Stops (System.fixedQueries (Y := Y) queries) system.law := by
  constructor
  · intro deterministic inSupport
    exact System.fixedQueries_compatible deterministic queries
      (queries_admitted_on_support system admitted inSupport)
  · intro deterministic inSupport
    exact System.fixedQueries_stops deterministic queries
      (queries_admitted_on_support system admitted inSupport)

private theorem transcriptLaw_apply_eq_fixedQueries (system : Presentation X Y)
    (environment : System.DDE Y X)
    (compatible : PDS.Compatible environment system.law)
    {transcript : System.Transcript X Y}
    (environmentConsistent : System.EnvConsistent environment transcript)
    (terminal : transcript.map Prod.snd ∉ environment.1.Dom)
    (admitted : transcript.map Prod.fst = [] ∨
      transcript.map Prod.fst ∈ system.domain) :
    transcriptLaw environment system (some transcript) =
      transcriptLaw (System.fixedQueries (Y := Y) (transcript.map Prod.fst))
        system (some transcript) := by
  rw [transcriptLaw, transcriptLaw, PDS.trLaw, PDS.trLaw,
    Distribution.fTransform_apply_eq_mass,
    Distribution.fTransform_apply_eq_mass]
  apply Distribution.mass_congr_of_support
  intro deterministic inSupport
  exact System.transcript_fiber_eq_fixedQueries
    (compatible deterministic inSupport) environmentConsistent terminal
    (queries_admitted_on_support system admitted inSupport)

private theorem transcriptLaw_apply_eq_zero_of_no_support (system : Presentation X Y)
    (environment : System.DDE Y X) {transcript : System.Transcript X Y}
    (noneObserved : ∀ deterministic ∈ system.law.support,
      (System.tr environment deterministic).toOption ≠ some transcript) :
    transcriptLaw environment system (some transcript) = 0 := by
  rw [transcriptLaw, PDS.trLaw, Distribution.fTransform_apply_eq_mass]
  calc
    system.law.mass (fun deterministic =>
        (System.tr environment deterministic).toOption = some transcript) =
        system.law.mass (fun _ => False) := by
      apply Distribution.mass_congr_of_support
      intro deterministic inSupport
      exact iff_false_intro (noneObserved deterministic inSupport)
    _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)

/-- Transitivity of Definition 2.17 equivalence.  Lemma 2.18 (printed p. 16)
states that equivalence is characterized by compatible non-adaptive DDEs; the
proof below realizes that reduction with the fixed query sequence of each
observed transcript. -/
@[trans]
theorem equivalent_trans {left middle right : Presentation X Y}
    (first : Equivalent left middle) (second : Equivalent middle right) :
    Equivalent left right := by
  refine ⟨first.1.trans second.1, fun environment admissible => ?_⟩
  apply Finsupp.ext
  intro observedValue
  cases observedValue with
  | none =>
      -- Stopping makes the undefined-transcript cell empty on both sides.
      rw [transcriptLaw_none left environment admissible.1.2,
        transcriptLaw_none right environment admissible.2.2]
  | some transcript =>
      by_cases witness : ∃ deterministic,
          (deterministic ∈ left.law.support ∨ deterministic ∈ right.law.support) ∧
            (System.tr environment deterministic).toOption = some transcript
      -- A supported witness fixes the environment's answers and stopping point.
      · obtain ⟨deterministic, leftOrRight, observed⟩ := witness
        -- The observed pair sequence satisfies the DDE equations.
        have environmentConsistent : System.EnvConsistent environment transcript := by
          rcases leftOrRight with inLeft | inRight
          · exact (System.stopped_consistent_of_toOption_eq_some
              (admissible.1.1 deterministic inLeft) observed).1
          · exact (System.stopped_consistent_of_toOption_eq_some
              (admissible.2.1 deterministic inRight) observed).1
        -- Its final answer history is outside the DDE domain.
        have terminal : transcript.map Prod.snd ∉ environment.1.Dom := by
          rcases leftOrRight with inLeft | inRight
          · exact (System.stopped_consistent_of_toOption_eq_some
              (admissible.1.1 deterministic inLeft) observed).2.1
          · exact (System.stopped_consistent_of_toOption_eq_some
              (admissible.2.1 deterministic inRight) observed).2.1
        -- The observed query sequence lies in the shared common domain.
        have admittedLeft : transcript.map Prod.fst = [] ∨
            transcript.map Prod.fst ∈ left.domain := by
          rcases leftOrRight with inLeft | inRight
          · exact queries_admitted_of_observed left environment inLeft observed
          · have admittedRight :=
              queries_admitted_of_observed right environment inRight observed
            rwa [first.1, second.1]
        have admittedMiddle : transcript.map Prod.fst = [] ∨
            transcript.map Prod.fst ∈ middle.domain := by
          -- The first domain equality transfers admission to the middle law.
          rwa [← first.1]
        have admittedRight : transcript.map Prod.fst = [] ∨
            transcript.map Prod.fst ∈ right.domain := by
          -- The second domain equality transfers admission to the right law.
          rwa [← second.1]
        -- Use the non-adaptive DDE that asks exactly the observed queries.
        let fixed := System.fixedQueries (Y := Y) (transcript.map Prod.fst)
        -- The fixed-query DDE is compatible and stopping for all three laws.
        have fixedLeft := fixedQueries_admissible left admittedLeft
        have fixedMiddle := fixedQueries_admissible middle admittedMiddle
        have fixedRight := fixedQueries_admissible right admittedRight
        -- Factor the adaptive transcript cell through that fixed-query DDE,
        -- apply each equivalence, and then restore the adaptive DDE.
        calc
          transcriptLaw environment left (some transcript) =
              transcriptLaw fixed left (some transcript) :=
            transcriptLaw_apply_eq_fixedQueries left environment admissible.1.1
              environmentConsistent terminal admittedLeft
          _ = transcriptLaw fixed middle (some transcript) :=
            congrArg (fun law => law (some transcript))
              (first.2 fixed ⟨fixedLeft, fixedMiddle⟩)
          _ = transcriptLaw fixed right (some transcript) :=
            congrArg (fun law => law (some transcript))
              (second.2 fixed ⟨fixedMiddle, fixedRight⟩)
          _ = transcriptLaw environment right (some transcript) :=
            (transcriptLaw_apply_eq_fixedQueries right environment admissible.2.1
              environmentConsistent terminal admittedRight).symm
      -- With no supported witness, this transcript cell has zero mass at both ends.
      · have noneLeft : ∀ deterministic ∈ left.law.support,
            (System.tr environment deterministic).toOption ≠ some transcript := by
          intro deterministic inSupport equal
          exact witness ⟨deterministic, Or.inl inSupport, equal⟩
        -- The same absence statement holds on the right support.
        have noneRight : ∀ deterministic ∈ right.law.support,
            (System.tr environment deterministic).toOption ≠ some transcript := by
          intro deterministic inSupport equal
          exact witness ⟨deterministic, Or.inr inSupport, equal⟩
        rw [transcriptLaw_apply_eq_zero_of_no_support left environment noneLeft,
          transcriptLaw_apply_eq_zero_of_no_support right environment noneRight]

/-- The equivalence relation used by Notation 2.19 (printed p. 16) to form
random systems. -/
def equivalentSetoid (X : Type u) (Y : Type v) :
    Setoid (Presentation X Y) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- The zero PDS at an explicit common domain. -/
def zero (domain : Set (List X)) : Presentation X Y where
  law := 0
  nonnegative := by intro system; simp
  domain := domain
  hasDomain := by intro system inSupport; simp at inSupport

@[simp]
theorem equivalent_zero_iff {leftDomain rightDomain : Set (List X)} :
    Equivalent (zero (Y := Y) leftDomain) (zero rightDomain) ↔
      leftDomain = rightDomain := by
  constructor
  · exact fun equivalent => equivalent.1
  · intro equal
    subst rightDomain
    exact equivalent_refl _

end Presentation

/-- Lanzenberger, Notation 2.19 (printed p. 16): “a random system, an
equivalence class of PDS.”  This Lean carrier uses arbitrary-mass nonnegative
presentations with the same common-domain equivalence. -/
def RandomSystem (X : Type u) (Y : Type v) : Type (max u v) :=
  Quotient (Presentation.equivalentSetoid X Y)

namespace RandomSystem

/-- The random system presented by one arbitrary-mass common-domain PDS. -/
def ofPresentation (system : Presentation X Y) : RandomSystem X Y :=
  Quotient.mk (Presentation.equivalentSetoid X Y) system

@[simp]
theorem ofPresentation_eq_iff {left right : Presentation X Y} :
    ofPresentation left = ofPresentation right ↔
      Presentation.Equivalent left right := by
  exact ⟨Quotient.exact,
    Quotient.sound (s := Presentation.equivalentSetoid X Y)⟩

end RandomSystem

/-- Lanzenberger, Definition 2.14 (printed p. 15): “all DDS in the support of
`S` have the same domain.”  `ProbDist` imposes the additional probability-law
specialization from Definition 2.1: nonnegativity and weight one. -/
structure ProbabilityPresentation (X : Type u) (Y : Type v) where
  law : Distribution.ProbDist (System.DDS X Y)
  fixedDomain :
    ∃ domain : Set (List X),
      ∀ system ∈ law.1.support, System.dom system = domain

namespace ProbabilityPresentation

instance : Coe (ProbabilityPresentation X Y)
    (Distribution (System.DDS X Y)) :=
  ⟨fun system => system.law.1⟩

/-- The common domain of a normalized presentation. -/
noncomputable def domain (system : ProbabilityPresentation X Y) :
    Set (List X) :=
  Classical.choose system.fixedDomain

/-- Every deterministic system in the support presents `domain`. -/
theorem hasDomain (system : ProbabilityPresentation X Y) :
    PDS.HasDomain system.law.1 system.domain :=
  Classical.choose_spec system.fixedDomain

/-- Lanzenberger, Definition 2.17, footnote 5 (printed p. 16): “`tr(S, e)`
denotes the `tr(·, e)`-transformation of the distribution `S`.” -/
def transcriptLaw (environment : System.DDE Y X)
    (system : ProbabilityPresentation X Y) :
    Distribution (Option (System.Transcript X Y)) :=
  PDS.trLaw environment system.law.1

@[ext]
theorem ext {left right : ProbabilityPresentation X Y}
    (equal : left.law = right.law) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Lanzenberger, Definition 2.17 (printed p. 16): “they have the same domain”
and their transcript laws agree for every jointly compatible DDE.  Stopping is
explicit because Lean represents transcripts as partial values. -/
def Equivalent (left right : ProbabilityPresentation X Y) : Prop :=
  left.domain = right.domain ∧
    ∀ environment : System.DDE Y X,
      (PDS.Compatible environment left.law.1 ∧
          PDS.Stops environment left.law.1) ∧
        (PDS.Compatible environment right.law.1 ∧
          PDS.Stops environment right.law.1) →
        transcriptLaw environment left = transcriptLaw environment right

/-- Forget normalization while retaining the explicit common domain. -/
def toPresentation (system : ProbabilityPresentation X Y) : Presentation X Y where
  law := system.law.1
  nonnegative := system.law.2.nonNeg
  domain := system.domain
  hasDomain := system.hasDomain

/-- Normalized equivalence is arbitrary-mass equivalence after forgetting
normalization. -/
theorem equivalent_toPresentation_iff
    {left right : ProbabilityPresentation X Y} :
    Presentation.Equivalent left.toPresentation right.toPresentation ↔
      Equivalent left right :=
  Iff.rfl

@[refl]
theorem equivalent_refl (system : ProbabilityPresentation X Y) :
    Equivalent system system :=
  equivalent_toPresentation_iff.mp
    (Presentation.equivalent_refl system.toPresentation)

@[symm]
theorem equivalent_symm {left right : ProbabilityPresentation X Y}
    (equivalent : Equivalent left right) : Equivalent right left :=
  equivalent_toPresentation_iff.mp
    (Presentation.equivalent_symm
      (equivalent_toPresentation_iff.mpr equivalent))

@[trans]
theorem equivalent_trans {left middle right : ProbabilityPresentation X Y}
    (first : Equivalent left middle) (second : Equivalent middle right) :
    Equivalent left right :=
  equivalent_toPresentation_iff.mp
    (Presentation.equivalent_trans
      (equivalent_toPresentation_iff.mpr first)
      (equivalent_toPresentation_iff.mpr second))

/-- The setoid implementing Definition 2.17 equivalence (printed p. 16) for
normalized presentations. -/
def equivalentSetoid (X : Type u) (Y : Type v) :
    Setoid (ProbabilityPresentation X Y) where
  r := Equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

end ProbabilityPresentation

/-- The normalized specialization of Lanzenberger's Notation 2.19 (printed
p. 16): “a random system, an equivalence class of PDS.” -/
abbrev ProbabilityRandomSystem (X : Type u) (Y : Type v) :=
  Quotient (ProbabilityPresentation.equivalentSetoid X Y)

namespace ProbabilityRandomSystem

/-- Regard a normalized common-domain presentation as a probability random
system. -/
def ofPresentation (system : ProbabilityPresentation X Y) :
    ProbabilityRandomSystem X Y :=
  Quotient.mk (ProbabilityPresentation.equivalentSetoid X Y) system

@[simp]
theorem ofPresentation_eq_iff
    {left right : ProbabilityPresentation X Y} :
    ofPresentation left = ofPresentation right ↔
      ProbabilityPresentation.Equivalent left right := by
  exact ⟨Quotient.exact,
    Quotient.sound
      (s := ProbabilityPresentation.equivalentSetoid X Y)⟩

end ProbabilityRandomSystem

end CommonDomain

end

end RandomSystems
