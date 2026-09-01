/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem

set_option autoImplicit false

/-!
# Bounded common-domain observation restriction

Lanzenberger, Definition 2.14 (printed p. 15), fixes the standing scope:
“We always assume that `S` is finite.” The standalone Lean carrier permits
unbounded DDS domains, while every PDS law still has finite support. This
module supplies the literal DDE restriction needed to recover that finite
observation scope without changing the carrier.

Given a DDE, a reference DDS, and a finite round bound, the restriction keeps
exactly those queries whose reconstructed complete query history belongs to
the reference DDS domain. It therefore halts uniformly, is compatible with
every DDS having that domain, and preserves every compatible interaction that
has stabilized by the bound. No converter or ambient random-system structure
is involved.
-/

namespace RandomSystems

noncomputable section

open Classical
open Probability (Distribution)

universe u v

variable {X : Type u} {Y : Type v}

namespace System.DDE

/-- Definition 2.12 (printed p. 14) requires
“`xᵢ = e(y₁, ..., yᵢ₋₁)`.” For an admitted answer history,
`queryHistory` reconstructs all queries through the next query. -/
noncomputable def queryHistory (environment : DDE Y X) (answers : List Y)
    (defined : answers ∈ environment.1.Dom) : List X :=
  answers.inits.attach.map fun entry =>
    (environment.1 entry.1).get
      (environment.2 ((List.mem_inits _ _).mp entry.2) defined)

/-- The reconstructed query history has one entry for every answer prefix,
including the full answer history. -/
@[simp]
theorem queryHistory_length (environment : DDE Y X) (answers : List Y)
    (defined : answers ∈ environment.1.Dom) :
    (queryHistory environment answers defined).length = answers.length + 1 := by
  simp [queryHistory]

/-- A reconstructed query history contains at least its opening query. -/
theorem queryHistory_nonempty (environment : DDE Y X) (answers : List Y)
    (defined : answers ∈ environment.1.Dom) :
    queryHistory environment answers defined ≠ [] := by
  intro empty
  have lengthEqual := queryHistory_length environment answers defined
  rw [empty] at lengthEqual
  simp at lengthEqual

/-- The `k`-th reconstructed query is the DDE value at the first `k`
answers. -/
theorem queryHistory_getElem_eq (environment : DDE Y X) (answers : List Y)
    (defined : answers ∈ environment.1.Dom) (k : Nat)
    (within : k < answers.length + 1) :
    (queryHistory environment answers defined)[k]'(by
      rw [queryHistory_length]
      exact within) =
      (environment.1 (answers.take k)).get
        (environment.2 (List.take_prefix k answers) defined) := by
  simp [queryHistory]

/-- Definition 2.11 (printed p. 14) gives the DDE a “prefix-closed domain.”
Consequently, extending an admitted answer history only extends its
reconstructed query history. -/
theorem queryHistory_prefix (environment : DDE Y X)
    {short long : List Y} (isPrefix : short <+: long)
    (longDefined : long ∈ environment.1.Dom) :
    queryHistory environment short (environment.2 isPrefix longDefined) <+:
      queryHistory environment long longDefined := by
  apply List.prefix_iff_eq_take.mpr
  apply List.ext_getElem
  · simp [queryHistory_length, isPrefix.length_le]
  · intro k shortWithin _
    have within : k < short.length + 1 := by
      simpa [queryHistory_length] using shortWithin
    rw [List.getElem_take]
    rw [queryHistory_getElem_eq environment short _ k within]
    rw [queryHistory_getElem_eq environment long _ k (lt_of_lt_of_le within
      (Nat.add_le_add_right isPrefix.length_le 1))]
    obtain ⟨tail, rfl⟩ := isPrefix
    have takeEqual : short.take k = (short ++ tail).take k := by
      rw [List.take_append_of_le_length]
      omega
    have partEqual : environment.1 (short.take k) =
        environment.1 ((short ++ tail).take k) :=
      congrArg environment.1 takeEqual
    exact Part.get_eq_get_of_eq _ _ partEqual

/-- For a transcript satisfying the DDE equations, reconstruction gives its
recorded queries followed by the next query. -/
theorem queryHistory_eq_append_of_envConsistent
    (environment : DDE Y X) (transcript : Transcript X Y)
    (consistent : EnvConsistent environment transcript)
    (defined : transcript.map Prod.snd ∈ environment.1.Dom) :
    queryHistory environment (transcript.map Prod.snd) defined =
      transcript.map Prod.fst ++
        [(environment.1 (transcript.map Prod.snd)).get defined] := by
  apply List.ext_getElem
  · simp [queryHistory_length]
  · intro k leftWithin _
    have leftWithin' : k < transcript.length + 1 := by
      simpa [queryHistory_length] using leftWithin
    rw [queryHistory_getElem_eq environment _ _ k (by simpa using leftWithin')]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ leftWithin') with earlier | last
    · obtain ⟨historyDefined, queryEqual⟩ := consistent k earlier
      rw [List.getElem_append_left]
      · rw [List.getElem_map]
        simpa only [List.map_take] using queryEqual
      · simpa using earlier
    · subst k
      rw [List.getElem_append_right]
      · simp only [List.length_map, Nat.sub_self, List.getElem_cons_zero]
        have answersEqual :
            (transcript.map Prod.snd).take transcript.length =
              transcript.map Prod.snd := by simp
        exact Part.get_eq_get_of_eq _ _
          (congrArg environment.1 answersEqual)
      · simp

/-- An answer history is admitted by the bounded domain restriction exactly
when the original DDE is defined, the cutoff has not been reached, and the
complete query history belongs to the reference DDS domain. This is Lean
support for Definition 2.14's standing finite-system scope, not an additional
paper object. -/
def boundedDomainAdmissible (reference : DDS X Y) (environment : DDE Y X)
    (rounds : Nat) (answers : List Y) : Prop :=
  ∃ defined : answers ∈ environment.1.Dom,
    answers.length < rounds ∧
      queryHistory environment answers defined ∈ dom reference

/-- Admission by the bounded restriction implies admission by the original
DDE. -/
theorem mem_dom_of_boundedDomainAdmissible {reference : DDS X Y}
    {environment : DDE Y X} {rounds : Nat} {answers : List Y}
    (admitted : boundedDomainAdmissible reference environment rounds answers) :
    answers ∈ environment.1.Dom :=
  admitted.choose

/-- Restrict a literal DDE to one DDS domain and a finite round bound.
Prefix closure follows from the DDE answer-domain prefix law and the reference
DDS query-domain prefix law. -/
noncomputable def boundedDomainRestriction (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) : DDE Y X := by
  refine ⟨(fun answers =>
    ⟨boundedDomainAdmissible reference environment rounds answers,
      fun admitted => (environment.1 answers).get admitted.choose⟩), ?_⟩
  intro short long isPrefix longAdmitted
  obtain ⟨longDefined, longWithin, longDomain⟩ := longAdmitted
  let shortDefined : short ∈ environment.1.Dom :=
    environment.2 isPrefix longDefined
  refine ⟨shortDefined, lt_of_le_of_lt isPrefix.length_le longWithin, ?_⟩
  exact prefix_closed reference
    (queryHistory_prefix environment isPrefix longDefined)
    (queryHistory_nonempty environment short shortDefined) longDomain

/-- The restriction's answer domain is its explicit admissibility predicate. -/
@[simp]
theorem mem_boundedDomainRestriction_iff (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) (answers : List Y) :
    answers ∈ (boundedDomainRestriction reference environment rounds).1.Dom ↔
      boundedDomainAdmissible reference environment rounds answers :=
  Iff.rfl

/-- Every retained query is exactly the original DDE query. -/
theorem boundedDomainRestriction_get_eq (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) (answers : List Y)
    (admitted :
      answers ∈ (boundedDomainRestriction reference environment rounds).1.Dom) :
    ((boundedDomainRestriction reference environment rounds).1 answers).get admitted =
      (environment.1 answers).get
        (mem_dom_of_boundedDomainAdmissible admitted) :=
  rfl

/-- An answer history at or beyond the cutoff is outside the restricted DDE
domain. -/
theorem not_mem_boundedDomainRestriction_of_length (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) (answers : List Y)
    (lengthAtLeast : rounds ≤ answers.length) :
    answers ∉ (boundedDomainRestriction reference environment rounds).1.Dom := by
  intro admitted
  exact Nat.not_lt_of_ge lengthAtLeast admitted.choose_spec.1

/-- The bounded domain restriction halts at its explicit cutoff. -/
theorem boundedDomainRestriction_halts (reference : DDS X Y)
  (environment : DDE Y X) (rounds : Nat) :
    Halts (boundedDomainRestriction reference environment rounds) :=
  ⟨rounds, not_mem_boundedDomainRestriction_of_length reference environment rounds⟩

end System.DDE

namespace System

/-- Every finite transcript generated by a DDE satisfies its query equations,
without a compatibility assumption. Compatibility is needed only to rule out
a DDS-side undefined query. -/
theorem trN_envConsistent (system : DDS X Y) (environment : DDE Y X) :
    ∀ rounds, EnvConsistent environment (trN environment system rounds) := by
  intro rounds
  induction rounds with
  | zero =>
      intro k within
      simp [trN] at within
  | succ rounds inductionHypothesis =>
      by_cases environmentDefined :
          (trN environment system rounds).map Prod.snd ∈ environment.1.Dom
      · let query := (environment.1
            ((trN environment system rounds).map Prod.snd)).get
              environmentDefined
        by_cases systemDefined :
            (trN environment system rounds).map Prod.fst ++ [query] ∈ dom system
        · rw [trN_succ_of_query environmentDefined systemDefined]
          intro k within
          rw [List.length_append, List.length_singleton] at within
          rcases Nat.lt_or_ge k
              (trN environment system rounds).length with earlier | last
          · rw [List.take_append_of_le_length (le_of_lt earlier),
                List.getElem_append_left earlier]
            exact inductionHypothesis k earlier
          · have kEqual : k = (trN environment system rounds).length := by
              omega
            subst kEqual
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            refine ⟨environmentDefined, ?_⟩
            simp
        · show EnvConsistent environment
              (trExtend environment system (trN environment system rounds))
          rw [trExtend, dif_pos environmentDefined, dif_neg systemDefined]
          exact inductionHypothesis
      · rw [trN_succ_of_stop environmentDefined]
        exact inductionHypothesis

end System

namespace System.DDE

/-- A transcript satisfying the restricted DDE equations also satisfies the
original DDE equations because every retained query is unchanged. -/
theorem envConsistent_boundedDomainRestriction
    (reference : DDS X Y) (environment : DDE Y X) (rounds : Nat)
    (transcript : Transcript X Y)
    (consistent : EnvConsistent
      (boundedDomainRestriction reference environment rounds) transcript) :
    EnvConsistent environment transcript := by
  intro k within
  obtain ⟨restrictedDefined, queryEqual⟩ := consistent k within
  let originalDefined :
      (transcript.take k).map Prod.snd ∈ environment.1.Dom :=
    mem_dom_of_boundedDomainAdmissible restrictedDefined
  refine ⟨originalDefined, ?_⟩
  calc
    (environment.1 ((transcript.take k).map Prod.snd)).get originalDefined =
        ((boundedDomainRestriction reference environment rounds).1
          ((transcript.take k).map Prod.snd)).get restrictedDefined :=
      (boundedDomainRestriction_get_eq reference environment rounds _
        restrictedDefined).symm
    _ = transcript[k].1 := queryEqual

/-- The bounded restriction is compatible with every DDS having the reference
domain. The membership test uses the complete reconstructed query history, so
no output-specific branch can leave that domain. -/
theorem boundedDomainRestriction_compatible (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) (system : DDS X Y)
    (sameDomain : dom system = dom reference) :
    Compatible (boundedDomainRestriction reference environment rounds) system := by
  intro stage query queryMember
  obtain ⟨restrictedDefined, queryEqual⟩ := queryMember
  let originalDefined :
      (trN (boundedDomainRestriction reference environment rounds) system stage).map
          Prod.snd ∈ environment.1.Dom :=
    mem_dom_of_boundedDomainAdmissible restrictedDefined
  have consistent : EnvConsistent environment
      (trN (boundedDomainRestriction reference environment rounds) system stage) :=
    envConsistent_boundedDomainRestriction reference environment rounds _
      (trN_envConsistent system
        (boundedDomainRestriction reference environment rounds) stage)
  have historyEqual := queryHistory_eq_append_of_envConsistent environment _
    consistent originalDefined
  have admitted := restrictedDefined.choose_spec.2
  rw [historyEqual] at admitted
  have queryEqual' :
      (environment.1
        ((trN (boundedDomainRestriction reference environment rounds) system stage).map
          Prod.snd)).get originalDefined = query := by
    calc
      _ = ((boundedDomainRestriction reference environment rounds).1
          ((trN (boundedDomainRestriction reference environment rounds) system stage).map
            Prod.snd)).get restrictedDefined :=
        (boundedDomainRestriction_get_eq reference environment rounds _
          restrictedDefined).symm
      _ = query := queryEqual
  rw [queryEqual'] at admitted
  rwa [sameDomain]

/-- On a compatible DDS with the reference domain, restriction preserves
every transcript stage through the cutoff. -/
theorem trN_boundedDomainRestriction_eq (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) (system : DDS X Y)
    (sameDomain : dom system = dom reference)
    (compatible : Compatible environment system) :
    ∀ stage, stage ≤ rounds →
      trN (boundedDomainRestriction reference environment rounds) system stage =
        trN environment system stage := by
  intro stage within
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      have earlierWithin : stage ≤ rounds :=
        Nat.le_trans (Nat.le_succ stage) within
      have earlierEqual := inductionHypothesis earlierWithin
      change trExtend
          (boundedDomainRestriction reference environment rounds) system
          (trN (boundedDomainRestriction reference environment rounds) system stage) =
        trExtend environment system (trN environment system stage)
      rw [earlierEqual]
      let current := trN environment system stage
      change trExtend
          (boundedDomainRestriction reference environment rounds) system current =
        trExtend environment system current
      by_cases originalDefined : current.map Prod.snd ∈ environment.1.Dom
      · let query :=
          (environment.1 (current.map Prod.snd)).get originalDefined
        have systemDefined : current.map Prod.fst ++ [query] ∈ dom system :=
          compatible stage query (Part.get_mem originalDefined)
        have referenceDefined :
            current.map Prod.fst ++ [query] ∈ dom reference := by
          rwa [← sameDomain]
        have historyEqual := queryHistory_eq_append_of_envConsistent environment
          current (trN_envConsistent system environment stage) originalDefined
        have lengthWithin : (current.map Prod.snd).length < rounds := by
          rw [List.length_map]
          exact lt_of_le_of_lt (trN_length_le environment system stage)
            (Nat.lt_of_succ_le within)
        have admitted : boundedDomainAdmissible reference environment rounds
            (current.map Prod.snd) :=
          ⟨originalDefined, lengthWithin,
            historyEqual.symm ▸ referenceDefined⟩
        let restrictedDefined : current.map Prod.snd ∈
            (boundedDomainRestriction reference environment rounds).1.Dom :=
          admitted
        unfold trExtend
        rw [dif_pos restrictedDefined, dif_pos originalDefined,
          boundedDomainRestriction_get_eq]
      · have restrictedUndefined : current.map Prod.snd ∉
            (boundedDomainRestriction reference environment rounds).1.Dom := by
          intro admitted
          exact originalDefined (mem_dom_of_boundedDomainAdmissible admitted)
        unfold trExtend
        rw [dif_neg restrictedUndefined, dif_neg originalDefined]

/-- If the original compatible interaction has stabilized by the cutoff, the
restricted and original stopped transcripts are identical. -/
theorem tr_toOption_boundedDomainRestriction_eq (reference : DDS X Y)
    (environment : DDE Y X) (rounds : Nat) (system : DDS X Y)
    (sameDomain : dom system = dom reference)
    (compatible : Compatible environment system)
    (stable : trN environment system (rounds + 1) =
      trN environment system rounds) :
    (tr (boundedDomainRestriction reference environment rounds) system).toOption =
      (tr environment system).toOption := by
  have restrictedStable :
      trN (boundedDomainRestriction reference environment rounds) system
          (rounds + 1) =
        trN (boundedDomainRestriction reference environment rounds) system rounds :=
    trN_succ_eq_of_halts_bound
      (not_mem_boundedDomainRestriction_of_length reference environment rounds)
      system
  let restrictedStops : Stops
      (boundedDomainRestriction reference environment rounds) system :=
    ⟨rounds, restrictedStable⟩
  let originalStops : Stops environment system := ⟨rounds, stable⟩
  have restrictedValue :
      (tr (boundedDomainRestriction reference environment rounds) system).toOption =
        some (trN (boundedDomainRestriction reference environment rounds) system
          rounds) :=
    Part.toOption_eq_some_iff.mpr
      ⟨restrictedStops, tr_get_eq_trN restrictedStops restrictedStable⟩
  have originalValue : (tr environment system).toOption =
      some (trN environment system rounds) :=
    Part.toOption_eq_some_iff.mpr
      ⟨originalStops, tr_get_eq_trN originalStops stable⟩
  rw [restrictedValue, originalValue,
    trN_boundedDomainRestriction_eq reference environment rounds system
      sameDomain compatible rounds le_rfl]

end System.DDE

namespace PDS

/-- Lanzenberger, Definition 2.14 (printed p. 15): “We always assume that `S`
is finite.” On Lean's unbounded DDS carrier, finite Finsupp support and the
per-supported-DDS `Stops` witnesses yield one uniform stabilization bound. -/
noncomputable def stoppingBound (environment : System.DDE Y X)
    (law : PDS X Y) (stops : Stops environment law) : Nat :=
  law.support.sup fun system =>
    if supported : system ∈ law.support then
      Nat.find (stops system supported)
    else 0

/-- Every supported DDS has stabilized at the law's uniform stopping bound. -/
theorem trN_stoppingBound_succ_eq (environment : System.DDE Y X)
    (law : PDS X Y) (stops : Stops environment law)
    {system : System.DDS X Y} (supported : system ∈ law.support) :
    System.trN environment system (stoppingBound environment law stops + 1) =
      System.trN environment system (stoppingBound environment law stops) := by
  let witness := stops system supported
  let first := Nat.find witness
  have firstLe : first ≤ stoppingBound environment law stops := by
    change Nat.find (stops system supported) ≤ stoppingBound environment law stops
    rw [stoppingBound]
    have leSup := Finset.le_sup
      (s := law.support)
      (f := fun deterministic =>
        if inSupport : deterministic ∈ law.support then
          Nat.find (stops deterministic inSupport)
        else 0) supported
    simpa only [dif_pos supported] using leSup
  calc
    System.trN environment system (stoppingBound environment law stops + 1) =
        System.trN environment system first :=
      System.trN_eq_of_le (Nat.find_spec witness) _ (by omega)
    _ = System.trN environment system (stoppingBound environment law stops) :=
      (System.trN_eq_of_le (Nat.find_spec witness) _ firstLe).symm

/-- Every supported DDS remains stabilized at any later common bound. -/
theorem trN_succ_eq_of_stoppingBound_le (environment : System.DDE Y X)
    (law : PDS X Y) (stops : Stops environment law)
    {system : System.DDS X Y} (supported : system ∈ law.support)
    (rounds : Nat) (enough : stoppingBound environment law stops ≤ rounds) :
    System.trN environment system (rounds + 1) =
      System.trN environment system rounds := by
  let base := stoppingBound environment law stops
  have stable := trN_stoppingBound_succ_eq environment law stops supported
  calc
    System.trN environment system (rounds + 1) =
        System.trN environment system base :=
      System.trN_eq_of_le stable _ (by omega)
    _ = System.trN environment system rounds :=
      (System.trN_eq_of_le stable _ enough).symm

/-- Restricting a compatible DDE to the common DDS domain after a sufficient
uniform bound preserves the complete transcript law. -/
theorem trLaw_boundedDomainRestriction_eq (reference : System.DDS X Y)
    (environment : System.DDE Y X) (rounds : Nat) (law : PDS X Y)
    (hasReferenceDomain : ∀ system ∈ law.support,
      System.dom system = System.dom reference)
    (compatible : Compatible environment law) (stops : Stops environment law)
    (enough : stoppingBound environment law stops ≤ rounds) :
    trLaw (System.DDE.boundedDomainRestriction reference environment rounds) law =
      trLaw environment law := by
  unfold trLaw
  apply Distribution.fTransform_congr
  intro system supported
  exact System.DDE.tr_toOption_boundedDomainRestriction_eq reference environment
    rounds system (hasReferenceDomain system supported)
      (compatible system supported)
      (trN_succ_eq_of_stoppingBound_le environment law stops supported rounds
        enough)

end PDS

end

end RandomSystems
