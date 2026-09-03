/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem

set_option autoImplicit false

/-!
# Fixed-interface DDS restrictions

This optional Random Systems module restricts a DDS domain by a prefix-closed
predicate.  CR18, Definition 3.10 (printed p. 62), states that `[q]s` is the
system `s` “restricted to `q` queries and is undefined as of the `(q+1)`-st
query.”  `filterQueries` is that registered fallback.  The more general
`filterDom` is its repository generalization to an arbitrary prefix-closed
history predicate.

The operation changes only the partial function domain; its interpretation as
a DDC belongs to the optional converter extension.
-/

namespace RandomSystems

universe u

/-- A prefix-closed restriction on query histories. -/
structure DomainFilter (X : Type u) where
  predicate : List X → Prop
  prefixClosed : PrefixClosed predicate

end RandomSystems

namespace RandomSystems.System

universe u v

variable {X : Type u} {Y : Type v}

/-- Restrict a DDS to histories satisfying a prefix-closed predicate. -/
@[reducible] def filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (system : DDS X Y) : DDS X Y :=
  ⟨fun history =>
      ⟨(system.1 history).Dom ∧ P history,
        fun admitted => (system.1 history).get admitted.1⟩,
    by
      refine ⟨fun admitted => empty_not_mem system admitted.1, ?_⟩
      intro initial final isPrefix initialNonempty admitted
      exact ⟨prefix_closed system isPrefix initialNonempty admitted.1,
        hP isPrefix admitted.2⟩⟩

/-- Domain restriction depends only on the extension of its predicate. -/
theorem filterDom_congr {A B : Type u} {P Q : List A → Prop}
    (hP : PrefixClosed P) (hQ : PrefixClosed Q)
    (equal : ∀ history, P history ↔ Q history) (system : DDS A B) :
    filterDom P hP system = filterDom Q hQ system := by
  have predicateEqual : P = Q := funext fun history => propext (equal history)
  subst predicateEqual
  rfl

@[simp]
theorem mem_dom_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (system : DDS X Y) (history : List X) :
    history ∈ dom (filterDom P hP system) ↔
      history ∈ dom system ∧ P history :=
  Iff.rfl

/-- A domain restriction only shrinks the DDS domain. -/
theorem dom_filterDom_subset (P : List X → Prop) (hP : PrefixClosed P)
    (system : DDS X Y) :
    dom (filterDom P hP system) ⊆ dom system :=
  fun _ admitted => admitted.1

/-- Domain restriction preserves every admitted DDS output. -/
theorem output_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (system : DDS X Y) (history : List X)
    (admitted : history ∈ dom (filterDom P hP system)) :
    output (filterDom P hP system) history admitted =
      output system history admitted.1 :=
  rfl

/-- On a nonempty transcript, consistency with a restricted system is
consistency with the original system together with admission of the complete
query history. -/
lemma systemConsistent_filterDom_iff (P : List X → Prop)
    (hP : PrefixClosed P) (system : DDS X Y)
    (transcript : Transcript X Y) (nonempty : transcript ≠ []) :
    SystemConsistent (filterDom P hP system) transcript ↔
      SystemConsistent system transcript ∧ P (transcript.map Prod.fst) := by
  have queryHistoryPrefix (k : Nat) (hk : k < transcript.length) :
      List.IsPrefix
        ((transcript.take k).map Prod.fst ++ [transcript[k].1])
        (transcript.map Prod.fst) := by
    have takeEqual : transcript.take k ++ [transcript[k]] =
        transcript.take (k + 1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk]
      simp only [Option.toList_some]
    have historyPrefix :
        List.IsPrefix (transcript.take k ++ [transcript[k]]) transcript :=
      takeEqual ▸ List.take_prefix (k + 1) transcript
    simpa only [List.map_append, List.map_singleton] using
      historyPrefix.map (fun entry : X × Y => entry.1)
  constructor
  · intro consistent
    have completeAdmitted :
        transcript.map Prod.fst ∈ dom (filterDom P hP system) := by
      rcases systemConsistent_queries_admitted
          (filterDom P hP system) transcript consistent with
        empty | admitted
      · exact (nonempty (List.map_eq_nil_iff.mp empty)).elim
      · exact admitted
    refine ⟨?_, (mem_dom_filterDom P hP system _).mp completeAdmitted |>.2⟩
    intro k hk
    obtain ⟨admitted, outputEqual⟩ := consistent k hk
    refine ⟨(mem_dom_filterDom P hP system _).mp admitted |>.1, ?_⟩
    exact outputEqual
  · rintro ⟨consistent, completeAdmitted⟩ k hk
    obtain ⟨admitted, outputEqual⟩ := consistent k hk
    have prefixAdmitted :
        P ((transcript.take k).map Prod.fst ++ [transcript[k].1]) :=
      hP (queryHistoryPrefix k hk) completeAdmitted
    exact ⟨⟨admitted, prefixAdmitted⟩, outputEqual⟩

/-- CR18, Definition 3.10 (printed p. 62): restrict a DDS to at most `q`
queries. -/
def filterQueries (q : ℕ) (system : DDS X Y) : DDS X Y :=
  filterDom (fun history => history.length ≤ q)
    (prefixClosed_length_le q) system

theorem filterQueries_eq_filterDom (q : ℕ) (system : DDS X Y) :
    filterQueries q system =
      filterDom (fun history => history.length ≤ q)
        (prefixClosed_length_le q) system :=
  rfl

@[simp]
theorem mem_dom_filterQueries (q : ℕ) (system : DDS X Y)
    (history : List X) :
    history ∈ dom (filterQueries q system) ↔
      history ∈ dom system ∧ history.length ≤ q :=
  Iff.rfl

/-- A query restriction only shrinks the DDS domain. -/
theorem dom_filterQueries_subset (q : ℕ) (system : DDS X Y) :
    dom (filterQueries q system) ⊆ dom system :=
  fun _ admitted => admitted.1

/-- Query restriction preserves every admitted DDS output. -/
theorem output_filterQueries (q : ℕ) (system : DDS X Y)
    (history : List X) (admitted : history ∈ dom (filterQueries q system)) :
    output (filterQueries q system) history admitted =
      output system history admitted.1 :=
  rfl

end RandomSystems.System

namespace RandomSystems.PDS

open Probability

universe u v

variable {X : Type u} {Y : Type v}

/-- Restrict every deterministic system in a PDS by one prefix-closed
history predicate. -/
noncomputable def filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (system : PDS X Y) : PDS X Y :=
  Distribution.fTransform (System.filterDom P hP) system

/-- A bundled domain filter acts on a probabilistic system by restriction. -/
noncomputable instance : HSMul (DomainFilter X) (PDS X Y) (PDS X Y) where
  hSMul restriction system :=
    filterDom restriction.predicate restriction.prefixClosed system

/-- Restrict every deterministic system in a PDS to at most `q` queries. -/
noncomputable def filterQueries (q : ℕ) (system : PDS X Y) : PDS X Y :=
  filterDom (fun history => history.length ≤ q)
    (prefixClosed_length_le q) system

lemma filterQueries_eq_filterDom (q : ℕ) (system : PDS X Y) :
    filterQueries q system =
      filterDom (fun history => history.length ≤ q)
        (prefixClosed_length_le q) system :=
  rfl

/-- Restriction preserves a probability law. -/
lemma isProbDist_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    {system : PDS X Y} (probability : system.isProbDist) :
    (filterDom P hP system).isProbDist :=
  Distribution.fTransform_isProbDist _ probability

/-- Restriction intersects a common system domain with its admission
predicate. -/
lemma hasDomain_filterDom (P : List X → Prop) (hP : PrefixClosed P)
    (system : PDS X Y) (domain : Set (List X))
    (hasDomain : HasDomain system domain) :
    HasDomain (filterDom P hP system)
      {history | history ∈ domain ∧ P history} := by
  intro restricted supported
  obtain ⟨original, originalSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      (System.filterDom P hP) system supported
  ext history
  rw [System.mem_dom_filterDom, hasDomain original originalSupported]
  rfl

end RandomSystems.PDS
