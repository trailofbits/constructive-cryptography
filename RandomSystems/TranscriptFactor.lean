/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Distance

set_option autoImplicit false

/-!
# Transcript factorization

Lanzenberger's proof of Lemma 2.18 factors an observed transcript into its
environment equations and system equations. The consistency predicates and
transcript reconstruction are provided by `RandomSystems.RandomSystem`; this
module only records the resulting probability factorization.
-/

noncomputable section

namespace RandomSystems

open Probability
open Classical

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-- The environment equations and final stopping condition for one
transcript. -/
def transcriptEnvironmentEvent (environment : DDE Y X)
    (transcript : Transcript X Y) : Prop :=
  EnvConsistent environment transcript ∧
    transcript.map Prod.snd ∉ environment.1.Dom

/-- Consistency with a total function evaluator is pointwise agreement with
the recorded query-answer pairs. -/
lemma systemConsistent_functionEvaluator_iff
    (function : X → Y) (transcript : Transcript X Y) :
    SystemConsistent (functionEvaluator function) transcript ↔
      ∀ entry ∈ transcript, function entry.1 = entry.2 := by
  constructor
  · intro consistent entry member
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem member
    obtain ⟨_, answer⟩ := consistent k hk
    rw [functionEvaluator_output] at answer
    exact answer
  · intro consistent k hk
    have admitted :
        (transcript.take k).map Prod.fst ++ [transcript[k].1] ∈
          dom (functionEvaluator function) := by
      rw [dom_functionEvaluator]
      simp
    refine ⟨admitted, ?_⟩
    rw [functionEvaluator_output]
    exact consistent transcript[k] (List.getElem_mem hk)

/-- An observed transcript factors into the environment event and the system
consistency event. -/
lemma toOption_eq_some_iff_factors
    {environment : DDE Y X} {system : DDS X Y}
    (compatible : Compatible environment system)
    {transcript : Transcript X Y} :
    (tr environment system).toOption = some transcript ↔
      transcriptEnvironmentEvent environment transcript ∧
        SystemConsistent system transcript := by
  constructor
  · intro observed
    have consistent :=
      stopped_consistent_of_toOption_eq_some compatible observed
    exact ⟨⟨consistent.1, consistent.2.1⟩, consistent.2.2⟩
  · rintro ⟨⟨environmentConsistent, terminal⟩, systemConsistent⟩
    exact (toOption_eq_some_iff_systemConsistent compatible
      environmentConsistent terminal).2 systemConsistent

end System

namespace PDS

/-- The system-only factor in Lanzenberger's transcript factorization. -/
def transcriptSystemFactor (system : PDS X Y)
    (transcript : System.Transcript X Y) : ℝ :=
  system.mass fun deterministic =>
    System.SystemConsistent deterministic transcript

/-- The environment-only factor, represented as a zero-one mass. -/
def transcriptEnvironmentFactorPartial (environment : System.DDE Y X)
    (transcript : System.Transcript X Y) : ℝ :=
  if System.transcriptEnvironmentEvent environment transcript then 1 else 0

lemma transcriptEnvironmentFactorPartial_nonneg
    (environment : System.DDE Y X) (transcript : System.Transcript X Y) :
    0 ≤ transcriptEnvironmentFactorPartial environment transcript := by
  unfold transcriptEnvironmentFactorPartial
  split <;> norm_num

/-- The transcript law is the product of its environment and system factors. -/
lemma trLaw_some_factorization
    (environment : System.DDE Y X) (system : PDS X Y)
    (compatible : Compatible environment system)
    (transcript : System.Transcript X Y) :
    trLaw environment system (some transcript) =
      transcriptEnvironmentFactorPartial environment transcript *
      transcriptSystemFactor system transcript := by
  rw [trLaw, Distribution.fTransform_apply_eq_mass]
  by_cases event : System.transcriptEnvironmentEvent environment transcript
  · rw [transcriptEnvironmentFactorPartial, if_pos event, one_mul,
      transcriptSystemFactor]
    apply Distribution.mass_congr_of_support
    intro deterministic supported
    exact (System.toOption_eq_some_iff_factors
      (compatible deterministic supported)).trans (and_iff_right event)
  · rw [transcriptEnvironmentFactorPartial, if_neg event, zero_mul]
    calc
      system.mass (fun deterministic =>
          (System.tr environment deterministic).toOption = some transcript) =
          system.mass (fun _ => False) := by
        apply Distribution.mass_congr_of_support
        intro deterministic supported
        exact iff_false_intro fun observed =>
          event ((System.toOption_eq_some_iff_factors
            (compatible deterministic supported)).mp observed).1
      _ = 0 := Distribution.mass_eq_zero_of_forall_not _ fun _ => id

lemma trLaw_none_eq_zero
    (environment : System.DDE Y X) (system : PDS X Y)
    (stops : Stops environment system) :
    trLaw environment system none = 0 := by
  rw [trLaw, Distribution.fTransform_apply_eq_mass]
  calc
    system.mass (fun deterministic =>
        (System.tr environment deterministic).toOption = none) =
        system.mass (fun _ => False) := by
      apply Distribution.mass_congr_of_support
      intro deterministic supported
      exact iff_false_intro fun equal =>
        (Part.toOption_eq_none_iff.mp equal) (stops deterministic supported)
    _ = 0 := Distribution.mass_eq_zero_of_forall_not _ fun _ => id

end PDS

end RandomSystems
