/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDS

set_option autoImplicit false

/-!
# Fixed-interface DDS restrictions

This optional Random Systems module restricts a DDS domain by a prefix-closed
predicate.  CR18, Definition 3.10 (printed p. 62), states that `[q]s` is the
system `s` “restricted to `q` queries and is undefined as of the `(q+1)`-st
query.”  `filterQueries` is that registered fallback.  The more general
`filterDom` is its repository generalization to an arbitrary prefix-closed
history predicate.

The operation changes only the partial function domain; it introduces no DDC
or attachment operation.
-/

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
