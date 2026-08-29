/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Distance
import RandomSystems.Filter

/-!
# H-coefficient bounds for deterministic environments

Lanzenberger's proof of Lemma 2.18, Appendix A.1 (printed p. 88), says: “Let
`e′` be the environment which queries the inputs of `t̂`.”  The surrounding
argument factors a fixed transcript into its recorded system answers and its
recorded environment queries.

Lean states that factorization for partial, compatible, stopping DDEs.  The
environment-only factor can then be shared by two PDS laws in a pointwise
ratio bound.
-/

noncomputable section

open scoped ENNReal NNReal BigOperators

namespace RandomSystems

open Probability
open Classical

universe u v

variable {X : Type u} {Y : Type v}

namespace System

private def TranscriptEnvironmentConsistent (environment : DDE Y X)
    (transcript : Transcript X Y) : Prop :=
  ∀ k, (hk : k < transcript.length) →
    ∃ hdom : (transcript.take k).map Prod.snd ∈ environment.1.Dom,
      (environment.1 ((transcript.take k).map Prod.snd)).get hdom =
        transcript[k].1

private def TranscriptSystemConsistent (system : DDS X Y)
    (transcript : Transcript X Y) : Prop :=
  ∀ k, (hk : k < transcript.length) →
    ∃ hdom : (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈ dom system,
      output system ((transcript.take k).map Prod.fst ++ [transcript[k].1]) hdom =
        transcript[k].2

private def TranscriptFinalAt (environment : DDE Y X) (rounds : Nat)
    (transcript : Transcript X Y) : Prop :=
  transcript.length = rounds ∨
    (transcript.length < rounds ∧ transcript.map Prod.snd ∉ environment.1.Dom)

private theorem trN_consistent_of_compatible
    (system : DDS X Y) (environment : DDE Y X)
    (compatible : Compatible environment system) (rounds : Nat) :
    TranscriptEnvironmentConsistent environment (trN environment system rounds) ∧
      TranscriptFinalAt environment rounds (trN environment system rounds) ∧
      TranscriptSystemConsistent system (trN environment system rounds) := by
  -- Establish environment consistency, finality, and system consistency together.
  induction rounds with
  -- The empty transcript is consistent and has length zero.
  | zero =>
      refine ⟨fun k hk => (by simp [trN] at hk), Or.inl rfl,
        fun k hk => (by simp [trN] at hk)⟩
  | succ rounds inductionHypothesis =>
      obtain ⟨environmentConsistent, finalAt, systemConsistent⟩ :=
        inductionHypothesis
      by_cases environmentDomain :
          (trN environment system rounds).map Prod.snd ∈ environment.1.Dom
      -- A defined environment query is admitted by compatibility.
      · have queryMem := Part.get_mem environmentDomain
        have systemDomain := compatible rounds _ queryMem
        rw [trN_succ_of_query environmentDomain systemDomain]
        -- The appended pair preserves both consistency predicates.
        refine ⟨?_, Or.inl (by
          rcases finalAt with lengthEqual | ⟨_, stopped⟩
          · simp [lengthEqual]
          · exact absurd environmentDomain stopped), ?_⟩
        -- Earlier environment equations persist; the last one is the new query.
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (trN environment system rounds).length with
            earlier | last
          · rw [List.take_append_of_le_length (le_of_lt earlier),
              List.getElem_append_left earlier]
            exact environmentConsistent k earlier
          · have kEqual : k = (trN environment system rounds).length := by omega
            subst kEqual
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            refine ⟨environmentDomain, ?_⟩
            simp
        -- Earlier system equations persist; the last one is the new answer.
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (trN environment system rounds).length with
            earlier | last
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
                    [(environment.1
                      ((trN environment system rounds).map Prod.snd)).get
                        environmentDomain]) hdom =
                    output system
                      ((trN environment system rounds).map Prod.fst ++
                        [(environment.1
                          ((trN environment system rounds).map Prod.snd)).get
                            environmentDomain]) systemDomain from
                ⟨systemDomain, rfl⟩)
      -- Environment undefinedness fixes the transcript and witnesses finality.
      · rw [trN_succ_of_stop environmentDomain]
        refine ⟨environmentConsistent, Or.inr ⟨?_, environmentDomain⟩,
          systemConsistent⟩
        rcases finalAt with lengthEqual | ⟨lengthLess, _⟩ <;> omega

private theorem trN_eq_of_consistent (system : DDS X Y)
    (environment : DDE Y X) :
    ∀ (rounds : Nat) (transcript : Transcript X Y),
      TranscriptEnvironmentConsistent environment transcript →
      TranscriptFinalAt environment rounds transcript →
      TranscriptSystemConsistent system transcript →
      trN environment system rounds = transcript := by
  intro rounds
  -- Reconstruct the transcript from the two consistency factors.
  induction rounds with
  -- Finality at zero forces the transcript to be empty.
  | zero =>
      intro transcript _ finalAt _
      rcases finalAt with lengthEqual | ⟨lengthLess, _⟩
      · simpa [trN] using (List.eq_nil_of_length_eq_zero lengthEqual).symm
      · omega
  | succ rounds inductionHypothesis =>
      intro transcript environmentConsistent finalAt systemConsistent
      rcases finalAt with lengthEqual | ⟨lengthLess, stopped⟩
      -- At full length, reconstruct the prefix and append its recorded pair.
      · have roundsLess : rounds < transcript.length := by omega
        -- Restrict both consistency factors to the proper transcript prefix.
        have prefixEqual : trN environment system rounds = transcript.take rounds := by
          apply inductionHypothesis
          · intro k hk
            rw [List.length_take] at hk
            have kLess : k < transcript.length := by omega
            have kRounds : k ≤ rounds :=
              Nat.le_of_lt (lt_of_lt_of_le hk (min_le_left _ _))
            simpa only [List.take_take, min_eq_left kRounds,
              List.getElem_take] using environmentConsistent k kLess
          · exact Or.inl (by
              simp [List.length_take,
                show rounds ≤ transcript.length by omega])
          · intro k hk
            rw [List.length_take] at hk
            have kLess : k < transcript.length := by omega
            have kRounds : k ≤ rounds :=
              Nat.le_of_lt (lt_of_lt_of_le hk (min_le_left _ _))
            simpa only [List.take_take, min_eq_left kRounds,
              List.getElem_take] using systemConsistent k kLess
        obtain ⟨environmentDomain, queryEqual⟩ :=
          environmentConsistent rounds roundsLess
        obtain ⟨systemDomain, answerEqual⟩ := systemConsistent rounds roundsLess
        -- The environment factor recovers the next recorded query.
        have environmentDomain' :
            (trN environment system rounds).map Prod.snd ∈ environment.1.Dom := by
          rwa [prefixEqual]
        have queryEqual' :
            (environment.1
              ((trN environment system rounds).map Prod.snd)).get
                environmentDomain' = transcript[rounds].1 := by
          apply Part.get_eq_of_mem
          rw [prefixEqual]
          exact queryEqual ▸ Part.get_mem environmentDomain
        have systemDomain' :
            (trN environment system rounds).map Prod.fst ++
              [(environment.1
                ((trN environment system rounds).map Prod.snd)).get
                  environmentDomain'] ∈ dom system := by
          rw [queryEqual']
          simpa only [prefixEqual] using systemDomain
        -- The system factor recovers the corresponding recorded answer.
        have answerEqual' :
            output system ((trN environment system rounds).map Prod.fst ++
              [(environment.1
                ((trN environment system rounds).map Prod.snd)).get
                  environmentDomain']) systemDomain' = transcript[rounds].2 := by
          calc
            _ = output system ((transcript.take rounds).map Prod.fst ++
                [transcript[rounds].1]) systemDomain :=
              output_congr system (by rw [queryEqual', prefixEqual]) _ _
            _ = transcript[rounds].2 := answerEqual
        -- The recovered query and answer identify the appended pair.
        have pairEqual :
            ((environment.1
              ((trN environment system rounds).map Prod.snd)).get
                environmentDomain',
              output system ((trN environment system rounds).map Prod.fst ++
                [(environment.1
                  ((trN environment system rounds).map Prod.snd)).get
                    environmentDomain']) systemDomain') = transcript[rounds] := by
          apply Prod.ext
          · exact queryEqual'
          · exact answerEqual'
        -- Append the recovered pair to the reconstructed prefix.
        rw [trN_succ_of_query environmentDomain' systemDomain', pairEqual,
          prefixEqual]
        conv_rhs => rw [← List.take_length (l := transcript), lengthEqual]
        rw [List.take_add_one, List.getElem?_eq_getElem roundsLess]
        simp
      -- If the environment is already terminal, the reconstructed prefix is final.
      · have prefixEqual : trN environment system rounds = transcript := by
          apply inductionHypothesis transcript environmentConsistent
          · rcases Nat.lt_or_ge transcript.length rounds with less | greater
            · exact Or.inr ⟨less, stopped⟩
            · exact Or.inl (by omega)
          · exact systemConsistent
        rw [trN_succ_of_stop (by rwa [prefixEqual]), prefixEqual]

private def transcriptEnvironmentEvent (environment : DDE Y X)
    (transcript : Transcript X Y) : Prop :=
  TranscriptEnvironmentConsistent environment transcript ∧
    transcript.map Prod.snd ∉ environment.1.Dom

private theorem toOption_eq_some_iff_factors
    {environment : DDE Y X} {system : DDS X Y}
    (compatible : Compatible environment system)
    {transcript : Transcript X Y} :
    (tr environment system).toOption = some transcript ↔
      transcriptEnvironmentEvent environment transcript ∧
        TranscriptSystemConsistent system transcript := by
  constructor
  -- A stopped observed transcript inherits both consistency factors.
  · intro equal
    rw [Part.toOption_eq_some_iff] at equal
    obtain ⟨stops, valueEqual⟩ := equal
    have stable := Nat.find_spec stops
    have transcriptEqual : trN environment system (Nat.find stops) = transcript := by
      rw [← tr_get_eq_trN stops stable, valueEqual]
    -- Compatibility supplies the two consistency factors at stabilization.
    have consistent := trN_consistent_of_compatible system environment
      compatible (Nat.find stops)
    -- Stabilization is exactly terminal DDE undefinedness.
    have stopped :=
      (trN_succ_eq_iff_of_compatible compatible (Nat.find stops)).1 stable
    exact ⟨⟨transcriptEqual ▸ consistent.1,
      by rwa [transcriptEqual] at stopped⟩,
      transcriptEqual ▸ consistent.2.2⟩
  -- Conversely, reconstruct the transcript and stop at its recorded endpoint.
  · rintro ⟨⟨environmentConsistent, terminal⟩, systemConsistent⟩
    -- The two consistency factors reconstruct the transcript at its length.
    have transcriptAtLength :
        trN environment system transcript.length = transcript :=
      trN_eq_of_consistent system environment transcript.length transcript
        environmentConsistent (Or.inl rfl) systemConsistent
    -- Terminal DDE undefinedness fixes the following stage.
    have stable : trN environment system (transcript.length + 1) =
        trN environment system transcript.length := by
      apply trN_succ_of_stop
      rwa [transcriptAtLength]
    rw [Part.toOption_eq_some_iff]
    let stops : Stops environment system := ⟨transcript.length, stable⟩
    exact ⟨stops, (tr_get_eq_trN stops stable).trans transcriptAtLength⟩

end System

namespace PDS

/-- In the proof of Lemma 2.18, Appendix A.1 (printed p. 88), “the transcript
`tr(s, ẽ)` is `t̂` if and only if `s(xⁱ) = yᵢ`” together with the corresponding
environment equations.  This is the PDS mass of the system-only condition. -/
def transcriptSystemFactor (S : PDS X Y)
    (transcript : System.Transcript X Y) : ℝ :=
  S.mass (fun system =>
    System.TranscriptSystemConsistent system transcript)

/-- Evaluate the system factor of a law of domain-restricted function
evaluators.  This exposes the literal history predicate and recorded answer
equalities needed by fixed-interface transcript arguments. -/
theorem transcriptSystemFactor_fTransform_filterDom_functionEvaluator
    {A : Type*} (source : Distribution A) (toFunction : A → X → Y)
    (predicate : List X → Prop) (prefixClosed : PrefixClosed predicate)
    (transcript : System.Transcript X Y) :
    transcriptSystemFactor
        (Distribution.fTransform
          (fun value => System.filterDom predicate prefixClosed
            (System.functionEvaluator (toFunction value))) source)
        transcript =
      source.mass (fun value =>
        ∀ k, (hk : k < transcript.length) →
          predicate
              ((transcript.take k).map Prod.fst ++ [transcript[k].1]) ∧
            toFunction value transcript[k].1 = transcript[k].2) := by
  unfold transcriptSystemFactor
  rw [Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro value
  constructor
  · intro consistent k hk
    obtain ⟨admitted, answer⟩ := consistent k hk
    refine ⟨(System.mem_dom_filterDom _ _ _ _).mp admitted |>.2, ?_⟩
    rw [System.output_filterDom, System.functionEvaluator_output] at answer
    exact answer
  · intro consistent k hk
    have atRound := consistent k hk
    have admitted :
        (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈
          System.dom (System.filterDom predicate prefixClosed
            (System.functionEvaluator (toFunction value))) := by
      rw [System.mem_dom_filterDom, System.dom_functionEvaluator]
      exact ⟨by simp, atRound.1⟩
    refine ⟨admitted, ?_⟩
    rw [System.output_filterDom, System.functionEvaluator_output]
    exact atRound.2

private def transcriptEnvironmentFactorPartial (environment : System.DDE Y X)
    (transcript : System.Transcript X Y) : ℝ :=
  if System.transcriptEnvironmentEvent environment transcript then 1 else 0

private theorem transcriptEnvironmentFactorPartial_nonneg
    (environment : System.DDE Y X) (transcript : System.Transcript X Y) :
    0 ≤ transcriptEnvironmentFactorPartial environment transcript := by
  classical
  unfold transcriptEnvironmentFactorPartial
  split <;> norm_num

private theorem trLaw_some_factorization
    (environment : System.DDE Y X) (S : PDS X Y)
    (compatible : Compatible environment S)
    (transcript : System.Transcript X Y) :
    trLaw environment S (some transcript) =
      transcriptEnvironmentFactorPartial environment transcript *
      transcriptSystemFactor S transcript := by
  rw [trLaw, Distribution.fTransform_apply_eq_mass]
  by_cases h : System.transcriptEnvironmentEvent environment transcript
  -- When the DDE supplies the recorded queries, only the system factor remains.
  · rw [transcriptEnvironmentFactorPartial, if_pos h, one_mul,
      transcriptSystemFactor]
    apply Distribution.mass_congr_of_support
    intro system supported
    exact (System.toOption_eq_some_iff_factors
      (compatible system supported)).trans (and_iff_right h)
  -- Otherwise the transcript cell is empty for every compatible DDS.
  · rw [transcriptEnvironmentFactorPartial, if_neg h, zero_mul]
    calc
      S.mass (fun system =>
          (System.tr environment system).toOption = some transcript) =
          S.mass (fun _ => False) := by
        apply Distribution.mass_congr_of_support
        intro system supported
        exact iff_false_intro fun observed =>
          h ((System.toOption_eq_some_iff_factors
            (compatible system supported)).mp observed).1
      _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)

private theorem trLaw_none_eq_zero
    (environment : System.DDE Y X) (S : PDS X Y)
    (stops : Stops environment S) :
    trLaw environment S none = 0 := by
  rw [trLaw, Distribution.fTransform_apply_eq_mass]
  -- Every supported DDS has a stopped transcript, so the `none` fibre is empty.
  calc
    S.mass (fun system => (System.tr environment system).toOption = none) =
        S.mass (fun _ => False) := by
      apply Distribution.mass_congr_of_support
      intro system supported
      constructor
      · intro equal
        exact (Part.toOption_eq_none_iff.mp equal) (stops system supported)
      · intro false
        exact false.elim
    _ = 0 := Distribution.mass_eq_zero_of_forall_not _ (fun _ => id)

/-- Cell-wise transcript bound for partial compatible and stopping DDE
observation.  The ratio premise mentions only the system factor; the common
environment factor cancels. -/
theorem trLaw_partition_finiteSupport_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : PDS X Y) (environment : System.DDE Y X)
    (cell : Option (System.Transcript X Y) → ι) (eps : ι → NNReal)
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight)
    (hSc : Compatible environment S) (hSs : Stops environment S)
    (hTc : Compatible environment T) (hTs : Stops environment T)
    (h_ratio : ∀ transcript,
      (1 - eps (cell (some transcript))) *
          transcriptSystemFactor T transcript ≤
        transcriptSystemFactor S transcript) :
    statDist (trLaw environment S) (trLaw environment T) ≤
      ∑ i, (eps i : ℝ) *
        (trLaw environment T).mass (fun observed => cell observed = i) := by
  -- Apply the finite-support partition inequality to the two transcript laws.
  apply Probability.hTechnique_partition_finiteSupport
  · unfold trLaw
    exact hS.fTransform _
  · unfold trLaw
    exact hT.fTransform _
  · simp only [trLaw, Distribution.weight_fTransform, hw]
  · intro observed
    cases observed with
    -- Stopping removes the undefined-transcript cell from both laws.
    | none =>
        rw [trLaw_none_eq_zero environment S hSs,
          trLaw_none_eq_zero environment T hTs]
        simp
    -- A concrete transcript shares one nonnegative environment factor.
    | some transcript =>
        rw [trLaw_some_factorization environment S hSc,
          trLaw_some_factorization environment T hTc]
        -- Reassociate that common factor, then apply the system-only ratio.
        calc
          (1 - (eps (cell (some transcript)) : ℝ)) *
              (transcriptEnvironmentFactorPartial environment transcript *
                transcriptSystemFactor T transcript) =
              transcriptEnvironmentFactorPartial environment transcript *
                ((1 - (eps (cell (some transcript)) : ℝ)) *
                  transcriptSystemFactor T transcript) := by ring
          _ ≤ transcriptEnvironmentFactorPartial environment transcript *
                transcriptSystemFactor S transcript :=
            mul_le_mul_of_nonneg_left (h_ratio transcript)
              (transcriptEnvironmentFactorPartial_nonneg environment transcript)

/-- A finite partition of transcript observations bounds the pair-specific
auxiliary advantage. Each cell contributes its ratio defect multiplied by a
uniform upper bound on that cell's ideal transcript mass. -/
theorem advantage_le_weighted_cells
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : PDS X Y)
    (cell : Option (System.Transcript X Y) → ι)
    (eps delta : ι → NNReal)
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight)
    (h_ratio : ∀ transcript,
      (1 - eps (cell (some transcript))) *
          transcriptSystemFactor T transcript ≤
        transcriptSystemFactor S transcript)
    (h_cells : ∀ environment : {e : System.DDE Y X //
        (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)},
      ∀ i, (trLaw environment.1 T).mass
        (fun observed => cell observed = i) ≤ delta i) :
    advantage S T ≤ (↑(∑ i, eps i * delta i) : ℝ≥0∞) := by
  unfold advantage
  -- It suffices to prove the weighted bound for each admissible DDE.
  refine iSup_le fun environment => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  calc
    -- The transcript factorization supplies the cellwise partition bound.
    statDist (trLaw environment.1 S) (trLaw environment.1 T) ≤
        ∑ i, (eps i : ℝ) *
          (trLaw environment.1 T).mass (fun observed => cell observed = i) :=
      trLaw_partition_finiteSupport_le S T environment.1 cell eps hS hT hw
        environment.2.1.1 environment.2.1.2
        environment.2.2.1 environment.2.2.2 h_ratio
    -- Replace every ideal cell mass by its uniform upper bound.
    _ ≤ ∑ i, (eps i : ℝ) * (delta i : ℝ) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (h_cells environment i) (eps i).coe_nonneg

/-- A uniform transcript-system-factor ratio bounds distinguishing advantage.
This is the one-cell specialization of `advantage_le_weighted_cells`; normalization
of the ideal PDS makes the cell mass at most one. -/
theorem advantage_le_of_ratio
    (S T : PDS X Y) (eps : NNReal)
    (hS : S.NonNeg) (hT : T.NonNeg)
    (hw : S.weight = T.weight) (hTWeight : T.weight = 1)
    (h_ratio : ∀ transcript,
      (1 - (eps : ℝ)) * transcriptSystemFactor T transcript ≤
        transcriptSystemFactor S transcript) :
    advantage S T ≤ (eps : ENNReal) := by
  have bound := advantage_le_weighted_cells S T
    (fun _ => Unit.unit)
    (fun _ => eps) (fun _ => 1) hS hT hw
    (fun transcript => by simpa using h_ratio transcript)
    (fun environment cell => by
      cases cell
      have nonnegative : (trLaw environment.1 T).NonNeg := by
        unfold trLaw
        exact hT.fTransform _
      calc
        (trLaw environment.1 T).mass
            (fun observed => (fun _ => Unit.unit) observed = Unit.unit) ≤
          (trLaw environment.1 T).weight :=
            Distribution.mass_le_weight nonnegative _
        _ = T.weight := by
          unfold trLaw
          exact Distribution.weight_fTransform _ _
        _ = 1 := hTWeight)
  simpa using bound

end PDS

end RandomSystems
